module Compile exposing (..)
import Lang exposing (..)
import Dict
import Typecheck exposing (..)
import NameGen
import Parser exposing (..)
import CPS
import Refine
import AssemblyTypes

deadEndsToString : List DeadEnd -> String
deadEndsToString deadEnds =
    String.concat (List.intersperse "; " (List.map deadEndToString deadEnds))


deadEndToString : DeadEnd -> String
deadEndToString deadend = 
  problemToString deadend.problem ++ " at row " ++ String.fromInt deadend.row ++ ", col " ++ String.fromInt deadend.col


problemToString : Problem -> String 
problemToString p = 
  case p of 
   Expecting s -> "expecting '" ++ s ++ "'"
   ExpectingInt -> "expecting int" 
   ExpectingHex -> "expecting hex" 
   ExpectingOctal -> "expecting octal" 
   ExpectingBinary -> "expecting binary" 
   ExpectingFloat -> "expecting float" 
   ExpectingNumber -> "expecting number" 
   ExpectingVariable -> "expecting variable" 
   ExpectingSymbol s -> "expecting symbol '" ++ s ++ "'"
   ExpectingKeyword s -> "expecting keyword '" ++ s ++ "'"
   ExpectingEnd -> "expecting end" 
   UnexpectedChar -> "unexpected char" 
   Problem s -> "problem " ++ s 
   BadRepeat -> "bad repeat" 

startingScope : Dict.Dict String Type
startingScope = Dict.fromList 
    [ ("+", TFunc (TTuple [TNum, TNum]) TNum)
    , ("++", TFunc (TTuple [TString, TString]) TString)
    , ("-", TFunc (TTuple [TNum, TNum]) TNum)
    , ("/", TFunc (TTuple [TNum, TNum]) TNum)
    , ("*", TFunc (TTuple [TNum, TNum]) TNum)
    , ("^", TFunc (TTuple [TNum, TNum]) TNum)
    , ("%", TFunc (TTuple [TNum, TNum]) TNum)
    , ("&&", TFunc (TTuple [TBool, TBool]) TBool)
    , ("||", TFunc (TTuple [TBool, TBool]) TBool)
    , ("=>", TFunc (TTuple [TBool, TBool]) TBool)
    , ("==", Forall [TVar "a"] (TFunc (TTuple [TVar "a", TVar "a"]) TBool))
    , ("!=", Forall [TVar "a"] (TFunc (TTuple [TVar "a", TVar "a"]) TBool))
    , ("<=", TFunc (TTuple [TNum, TNum]) TBool)
    , (">=", TFunc (TTuple [TNum, TNum]) TBool)
    , ("<",  TFunc (TTuple [TNum, TNum]) TBool)
    , (">",  TFunc (TTuple [TNum, TNum]) TBool)
    , ("|>", Forall [TVar "a", TVar "b"] (TFunc (TTuple [TVar "a", TFunc (TVar "a") (TVar "b")]) (TVar "b")))
    , ("<|", Forall [TVar "a", TVar "b"] (TFunc (TTuple [TFunc (TVar "a") (TVar "b"), TVar "a"]) (TVar "b")))
    , ("!", TFunc TBool TBool)
    , ("len", Forall [TVar "a"] (TFunc (ADT "Array" [TVar "a"]) TNum))
    ]

go : String -> Result String String
go code = Parser.run (succeed identity |= parse |. end) code |> Result.mapError deadEndsToString |> Result.andThen (\ast->
          typecheck startingScope NameGen.init ast []        |> Result.map (\(scope, _, annotAst)->
          let scope2 = Dict.diff scope startingScope in
          let parts = List.map(\(k, a)->k ++ ": " ++ typeToString a) (Dict.toList scope2) in
          let cps = CPS.toCPS annotAst in
          Refine.refineAST (Dict.empty) cps |> Result.map (\refinedCPS->
          let cps2 = AssemblyTypes.convertRefinedAST refinedCPS in
          String.join ", " parts ++ " -- " ++ Debug.toString cps2) |> Result.withDefault "refinement type error"))
