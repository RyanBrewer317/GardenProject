module Compile exposing (..)
import Lang exposing (Expr(..), Located)
import Dict
import Parser
import Lang exposing (expression)
import Typecheck exposing (typeOf)
import Lang exposing (parse)
import Typecheck exposing (typecheck)
import FTV
import Typecheck exposing (Type(..))
import Parser exposing (..)
import Typecheck exposing (debugTypeToString)

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

type alias Scope = Dict.Dict String (Located Expr)

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

go : String -> Result String (FTV.FTV ())
go code = Parser.run parse code |> Result.mapError (\_->"parser error") |> Result.andThen (\ok->typecheck startingScope (FTV.return ok))

typ : String -> Result String String
typ code = Parser.run (succeed identity |= expression |. end) code |> Result.mapError deadEndsToString |> Result.andThen (\ok->typeOf startingScope (FTV.return ok)) |> Result.map FTV.unwrap |> Result.map debugTypeToString