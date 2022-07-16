module AssemblyTypes exposing (..)
import Refine exposing (..)
import CPS

type Value = Int32 Int
           | Int64 Int
           | Float32 Float
           | Float64 Float
           | String String
           | Var String
        --    | Label String

{-used for pointer operations like offsets-}
type AccessPath = OFFp Int
                -- | SELp Int AccessPath

convertCPSAccessPath : CPS.AccessPath -> AccessPath
convertCPSAccessPath ap = case ap of
    CPS.OFFp i -> OFFp i

type CExpr  = Tuple (List (Value, AccessPath)) String CExpr
            -- | Select Int Value String CExpr
            -- | Offset Int Value String CExpr
            | Call Value (List Value)
            | Funcs (List (String, List String, CExpr)) CExpr
            -- | Switch Value (List Value)
            | PrimOp String (List Value) (List String) (List CExpr)

convertRefinedValue : RValue -> Value
convertRefinedValue val = case val of
    RVar n _ -> Var n
    RBoolLit b -> Int32 b
    RInt n interval -> case interval.value of
        RInt32 -> Int32 n
        _ -> Int64 n
    RFloat f _ -> Float64 f
    RStringLit s _ -> String s

convertRefinedCExpr : RCExpr -> CExpr
convertRefinedCExpr rcexpr = case rcexpr of
    RTupleLit exprs var cont -> Tuple (List.map (\(a,b)->(convertRefinedValue a, convertCPSAccessPath b)) exprs) var (convertRefinedCExpr cont.value)
    RCall a b -> Call (convertRefinedValue a) (List.map convertRefinedValue b)
    RFuncs funcs dom -> Funcs (List.map (\(a, b, c)->(a, b, convertRefinedCExpr c.value)) funcs) (convertRefinedCExpr dom.value)
    RPrimOp op args mbvar branches -> PrimOp op (List.map convertRefinedValue args) mbvar (List.map (\loc->convertRefinedCExpr loc.value) branches)

convertRefinedAST ast = List.map (\loc->convertRefinedCExpr loc.value) ast

convertValue : CPS.Value -> Value
convertValue val = case val of
    CPS.Var n _ -> Var n
    CPS.Bool i -> Int32 i
    CPS.Int i -> Int64 i
    CPS.Float f -> Float64 f
    CPS.String s -> String s

convertCExpr cexpr = case cexpr of
    CPS.Tuple exprs var cont -> Tuple (List.map (\(a, b)->(convertValue a, convertCPSAccessPath b)) exprs) var (convertCExpr cont.value)
    CPS.Call a b -> Call (convertValue a) (List.map convertValue b)
    CPS.Funcs funcs dom -> Funcs (List.map (\(a, b, c)->(a, b, convertCExpr c.value)) funcs) (convertCExpr dom.value)
    CPS.PrimOp op args mbvar branches -> PrimOp op (List.map convertValue args) mbvar (List.map (\loc->convertCExpr loc.value) branches)

convertCPSAST ast = List.map (\loc->convertCExpr loc.value) ast