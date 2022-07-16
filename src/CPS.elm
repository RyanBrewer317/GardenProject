{-
Convert the type-annotated AST from Typecheck.elm to
a Continuation-Passing-Style AST, for easier conversion
to webassembly later on. 
Primary reference is the book "Compiling With Continuations" by Andrew Appel of Princeton
The main divergences from the book are my much more restricted use of CPS control-flow features, 
and how much information I've chosen to keep in the CPS AST from the source code.
Eventually I hope to do refinement-type-checking on the CPS AST, if I can get the mapping to the source code right
-}
module CPS exposing (toCPS, Value(..), CExpr(..), AccessPath(..))
import Typecheck exposing (Type)
import Lang exposing (..)
import NameGen exposing (NameGen)
import Typecheck exposing (Type(..), Annot(..), AnnotStmt(..), locmap)

{- atomic CPS values -}
type Value = Var String Type
        --    | Label String
           | Bool Int
           | Int Int
           | Float Float
           | String String

typeOf : Value -> Type
typeOf val = case val of
    Var _ t -> t
    Bool _ -> TBool
    Int _ -> TNum
    Float _ -> TNum
    String _ -> TString

{-used for pointer operations like offsets-}
type AccessPath = OFFp Int
                -- | SELp Int AccessPath

{-a continuation expression, in term of atomic CPS `Value`s. -}
type CExpr  = Tuple (List (Value, AccessPath)) String (Located CExpr)
            -- | Select Int Value String (Located CExpr)
            -- | Offset Int Value String (Located CExpr)
            | Call Value (List Value)
            | Funcs (List (String, List String, (Located CExpr))) (Located CExpr)
            -- | Switch Value (List Value)
            | PrimOp String (List Value) (List String) (List (Located CExpr))

convertStmt : NameGen -> Located AnnotStmt -> (NameGen -> Value -> (NameGen, Located CExpr)) -> (NameGen, Located CExpr)
convertStmt ftv loc cont = case loc.value of
    AnnotDecl n e -> ftv |> NameGen.withFresh (\ftv2 var->convertExpr ftv2 e (\ftv3 v->let (ftv4, c) = Var var (typeOf v) |> cont ftv3 in (ftv4, PrimOp "=" [Var n (typeOf v), v] [var] [c] |> locmap loc)))

convertExpr : NameGen -> Located Annot -> (NameGen -> Value -> (NameGen, Located CExpr)) -> (NameGen, Located CExpr)
convertExpr ftv loc cont = case loc.value of
    AnnotPrim {val, typ} ->
        case val of
            Ident n -> Var n typ |> cont ftv
            NumberLit n -> Float n |> cont ftv
            CharLit c -> Char.toCode c |> Int |> cont ftv
            StringLit s -> String s |> cont ftv
            _ -> cont ftv (Var "this shouldn't happen..." TBool) -- dummy value
    AnnotTuple {vals, typ} ->
        case vals of
            [] -> Int 0 |> cont ftv
            _ -> ftv |> 
                    NameGen.withFresh (\ftv2 var->
                        convertTupleHelper ftv2 vals (\vars->
                            let (ftv3, c) = Var var typ |> cont ftv2 in 
                            (ftv3, Tuple (List.map (\v->(v, OFFp 0)) vars) var c |> locmap loc)
                        )
                    )
    AnnotPrefix {op, right, typ} -> 
        let oneResult = \_->ftv |> 
                NameGen.withFresh (\ftv2 var->
                    convertExpr ftv2 right (\ftv3 v->
                        let outputType = (case typ of
                                TFunc _ t -> t
                                _ -> TBool) in
                        let (ftv4, c) = Var var outputType |> cont ftv3 in 
                        (ftv4, PrimOp op [v] [var] [c] |> locmap loc)
                    )
                ) in
        let twoBranch = \_->ftv |> 
                NameGen.withTwoFresh (\ftv2 var1 var2->
                    convertExpr ftv2 right (\ftv3 v->
                        let inputType = (case typ of
                                TFunc t _ -> t
                                _ -> TBool) in
                        let (ftv4, c) = Var var2 inputType |> cont ftv3 in 
                        (ftv4, Funcs [(var1, [var2], c)] (PrimOp op [v] [] [Call (Var var1 typ) [Bool 1] |> locmap loc, Call (Var var1 typ) [Bool 0] |> locmap loc] |> locmap loc) |> locmap loc)
                    )
                ) in
        case op of
            "!" -> twoBranch()
            "-" -> oneResult()
            _ -> oneResult() -- this shouldn't happen...
    AnnotInfix {left, op, right, typ} -> 
        let oneResult = \_->ftv |> 
                NameGen.withFresh (\ftv2 var->
                    let outputType = (case typ of
                            TFunc _ t -> t
                            _ -> TBool) in
                    let (ftv3, c) = Var var outputType |> cont ftv2 in 
                    convertTupleHelper ftv3 [left, right] (\a->
                        (ftv3, PrimOp op a [var] [c] |> locmap loc)
                    )
                ) in
        let twoBranch = \_->ftv |> 
                NameGen.withTwoFresh (\ftv2 var1 var2->
                    let (ftv3, c) = Var var2 TBool |> cont ftv2 in 
                    convertTupleHelper ftv3 [left, right] (\a->
                        (ftv3, Funcs [(var1, [var2], c)] (PrimOp op a [] [Call (Var var1 typ) [Bool 1] |> locmap loc, Call (Var var1 typ) [Bool 0] |> locmap loc] |> locmap loc) |> locmap loc)
                    )
                ) in
        case op of
            "+" -> oneResult()
            "<" -> twoBranch()
            _ -> oneResult()
    AnnotFunc {args, block, typ} -> ftv |> 
            NameGen.withTwoFresh (\ftv2 var1 var2->
                let (inputType, outputType) = (case typ of
                        TFunc t u -> (t, u)
                        _ -> (TBool, TBool)
                        ) in
                let (ftv3, c) = Var var2 (addArg inputType outputType (TFunc outputType outputType)) |> cont ftv2 in 
                let (ftv4, bod) = convertExpr ftv3 block (\ftv5 z->(ftv5, Call (Var var1 (TFunc outputType outputType)) [z] |> locmap loc)) in 
                (ftv4, Funcs [(var2, (List.map Tuple.first args++[var1]), bod)] c |> locmap loc)
            )
    AnnotCall {func, args, typ} -> ftv |>
            NameGen.withTwoFresh (\ftv2 var1 var2->
                let (ftv3, c) = Var var2 typ |> cont ftv2 in
                let (ftv4, foo) = convertExpr ftv3 func (\ftv5 f-> convertExpr ftv5 args (\ftv6 e->(ftv6, Call f [e, Var var1 (TFunc typ typ)] |> locmap loc))) in
                (ftv4, Funcs [(var1, [var2], c)] foo |> locmap loc)
            )
    _ -> cont ftv (Var "this shouldn't happen..." TBool)

addArg inputType outputType argType = case inputType of
    TTuple [] -> TFunc argType outputType
    TTuple ts -> TFunc (TTuple (ts++[argType])) outputType
    _ -> TFunc (TTuple ([inputType, argType])) outputType

convertTupleHelper : NameGen -> List (Located Annot) -> (List Value -> (NameGen, Located CExpr)) -> (NameGen, Located CExpr)
convertTupleHelper ftv vals cont =
    let g : NameGen -> List (Located Annot) -> List Value -> (NameGen, Located CExpr)
        g ftv2 exprs vars = (case exprs of
            e::rest -> convertExpr ftv2 e (\ftv3 v->g ftv3 rest (v::vars))
            [] -> cont (List.reverse vars)) in
    g ftv vals []

toCPS annotAST = List.map (\stmt->convertStmt NameGen.init stmt (\ftv val->(ftv, Call val [] |> locmap stmt)) |> Tuple.second) annotAST