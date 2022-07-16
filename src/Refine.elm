module Refine exposing (..)
import CPS
import Dict exposing (Dict)
import Typecheck exposing (Type(..))
import Lang exposing (Located)
import Typecheck exposing (locmap)

type Amt = Num Float
         | Inf
         | NInf

type alias Interval a = {max : Amt, min : Amt, value : a}

type RType = RInt32
           | RInt64
           | RFloat32
           | RFloat64
           | RLength32 String
           | RLength64 String
           | RBool
           | RChar
           | RString
           | RTypeVar String
           | RForall (List (Interval RType)) (Interval RType)
           | RFunc (Interval RType) (Interval RType)
           | RTuple (List (Interval RType))
           | RADT String (List (Interval RType))

type alias RScope = Dict String (Interval RType)

type RValue = RVar String (Interval RType)
        --    | RLabel String (Interval RType)
            | RBoolLit Int
            | RInt Int (Interval RType)
            | RFloat Float (Interval RType)
            | RStringLit String (Interval RType)

typeOf : RValue -> Interval RType
typeOf val = case val of
    RVar _ t -> t
    RBoolLit _ -> Interval NInf Inf RBool
    RInt _ t -> t
    RFloat _ t -> t
    RStringLit _ t -> t

{-a continuation expression, in term of atomic CPS `Value`s. -}
type RCExpr  = RTupleLit (List (RValue, CPS.AccessPath)) String (Located RCExpr)
            -- | RSelect Int RValue String (Located RCExpr)
            -- | ROffset Int RValue String (Located RCExpr)
            | RCall RValue (List RValue)
            | RFuncs (List (String, List String, (Located RCExpr))) (Located RCExpr)
            -- | RSwitch RValue (List RValue)
            | RPrimOp String (List RValue) (List String) (List (Located RCExpr))

refine : RScope -> CPS.Value -> RValue
refine scope val = case val of
    CPS.Var n t -> 
        let try = \ident a->Maybe.withDefault a (Dict.get ident scope) in
        let rt = convertType t in
        RVar n (try n (Interval NInf Inf rt))
    CPS.Bool b -> RBoolLit b
    CPS.Int n -> 
        if n > 2000000000 || n < -2000000000 then
            RInt n <| Interval (Num (toFloat n)) (Num (toFloat n)) RInt64
        else
            RInt n <| Interval (Num <| toFloat n) (Num <| toFloat n) RInt32
    CPS.Float n ->
        if n > 2000000000 || n < -2000000000 then
            RFloat n <| Interval (Num n) (Num n) RFloat64
        else
            RFloat n <| Interval (Num n) (Num n) RFloat32
    CPS.String s -> RStringLit s <| Interval (Num <| toFloat <| String.length s) (Num <| toFloat <| String.length s) RString

convertType : Type -> RType
convertType t = case t of
    TBool -> RBool
    TNum -> RFloat64
    TChar -> RChar
    TString -> RString
    TFunc a b -> RFunc (Interval NInf Inf<|convertType a) (Interval NInf Inf<|convertType b)
    TTuple ts -> RTuple (List.map (\a->Interval NInf Inf<|convertType a) ts)
    TVar n -> RTypeVar n
    Forall vars u -> RForall (List.map (\a->Interval NInf Inf<|convertType a) vars) (Interval NInf Inf<|convertType u)
    ADT n ts -> RADT n (List.map (\a->Interval NInf Inf<|convertType a) ts)

refineCPS : RScope -> Located CPS.CExpr -> Result String (RScope, Located RCExpr)
refineCPS scope cpsExprLoc = case cpsExprLoc.value of
    CPS.Tuple vals n contLoc -> 
        refineCPS scope contLoc |> Result.map (\(scope2, refinedLoc)->
        (scope2, RTupleLit (List.map (\(val,path)->(refine scope val, path)) vals) n refinedLoc |> locmap cpsExprLoc))
    CPS.Call foo args -> Ok <| (scope, locmap cpsExprLoc <| RCall (refine scope foo) (List.map (refine scope) args))
    CPS.Funcs funcs domainLoc ->
        List.foldr (\(n, args, bodyLoc) res -> 
            res                     |> Result.andThen (\(funcs2soFar, scope2soFar)->
            refineCPS scope bodyLoc |> Result.map     (\(scopex, bodyLoc2)->
            ((n, args, bodyLoc2)::funcs2soFar, Dict.union scopex scope2soFar)))
        ) (Ok ([], scope)) funcs   |> Result.andThen (\(funcs2, scope2)->
        refineCPS scope2 domainLoc |> Result.map     (\(scope3, domainLoc2)->
        (scope3, RFuncs funcs2 domainLoc2 |> locmap cpsExprLoc)))
    CPS.PrimOp op args mbvar branches -> 
        case op of
            "=" ->
                case args of
                    [CPS.Var n t, v] ->
                        case branches of
                            [branch] -> 
                                let rt = Interval NInf Inf <| convertType t in
                                refineCPS (Dict.insert n rt scope) branch |> Result.map(\(scope2, refinedBranch)->
                                (scope2, RPrimOp op [RVar n rt, refine scope v] mbvar [refinedBranch] |> locmap cpsExprLoc))
                            _ -> Debug.todo "dummy"
                    _ -> Debug.todo "dummy"
            _ -> List.foldr (\loc branches2soFarRes->
                    branches2soFarRes    |> Result.andThen (\(scopex, branches2soFar)->
                    refineCPS scopex loc |> Result.map     (\(scopex2, refined)->
                    (scopex2, refined::branches2soFar)))
                ) (Ok (scope, [])) branches |> Result.map (\(scope2, branchesOK)->
                (scope2, RPrimOp op (List.map (refine scope) args) mbvar branchesOK |> locmap cpsExprLoc))

refineAST : RScope -> List (Located CPS.CExpr) -> Result String (List (Located RCExpr))
refineAST scope cpsAST = case cpsAST of
    [] -> Ok []
    cps::rest ->
        refineCPS scope cps |> Result.andThen (\(scope2, a)->refineAST scope2 rest|>Result.map(\okRest->a::okRest))
