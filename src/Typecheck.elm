module Typecheck exposing (..)

import Lang
import Dict exposing (Dict)
import Parser

type Type = Unit
          | Bool
          | Number
          | Char
          | Array Type
          | Product Type Type
          | Function Type Type

typeToString : Type -> String
typeToString t = case t of
    Unit -> "Unit"
    Bool -> "Bool"
    Number -> "Number"
    Char -> "Char"
    Array u -> "[]" ++ typeToString u
    Product u v -> typeToString u ++ "*" ++ typeToString v
    Function u v -> typeToString u ++ "->" ++ typeToString v

type alias TypeScope = Dict String Type
type alias Scope = Dict String Type
type alias Lexpr = Lang.Located Lang.Expression
type alias Lstmt = Lang.Located Lang.Statement
type alias Ltype = Lang.Located Lang.TypeLiteral

posToString : Lang.Located a -> String
posToString l = case l.start of (row, col) -> String.fromInt row ++ ", " ++ String.fromInt col

evalType : TypeScope -> Ltype -> Result String Type
evalType scope located = case located.value of
    Lang.TypeIdent n -> Maybe.withDefault (Err <| "TypeError: (" ++ posToString located ++ "): unknown type " ++ n) (Dict.get n scope |> Maybe.andThen (\ok->Just(Ok ok)))
    Lang.TypePrefix op t -> 
        case op of
            "[]" -> evalType scope t |> Result.andThen (\ok->Ok (Array ok))
            _ -> Err <| "NameError: (" ++ posToString located ++ "): unknown operator " ++ op
    Lang.TypeInfix op t u ->
        case op of
            "*" -> evalType scope t
                |> Result.andThen (\ok1
                    -> evalType scope u
                    |> Result.andThen (\ok2
                        -> Ok (Product ok1 ok2)))
            "=>" -> evalType scope t
                 |> Result.andThen (\ok1
                    -> evalType scope u
                    |> Result.andThen (\ok2
                        -> Ok (Function ok1 ok2)))
            _ -> Err <| "NameError: (" ++ posToString located ++ "): unknown operator " ++ op

infixType : Scope -> TypeScope -> String -> Lexpr -> Lexpr -> Result String Type
infixType scope typeScope op l r = 
    exprType scope typeScope l
    |> Result.andThen (\ok1
        -> exprType scope typeScope r
        |> Result.andThen (\ok2
            -> let err = Err ("TypeError (" ++ posToString l ++ "): unknown operation " ++ typeToString ok1 ++ " " ++ op ++ " " ++ typeToString ok2) in
                    case op of
                        "+" ->  if ok1 == Number && ok2 == Number then
                                    Ok Number
                                else if ok1 == Array Char && ok2 == Array Char then
                                    Ok (Array Char)
                                else
                                    err
                        "-" ->  if ok1 == Number && ok2 == Number then
                                    Ok Number
                                else err
                        "*" ->  if ok1 == Number && ok2 == Number then
                                    Ok Number
                                else err
                        "/" ->  if ok1 == Number && ok2 == Number then
                                    Ok Number
                                else err
                        "^" ->  if ok1 == Number && ok2 == Number then
                                    Ok Number
                                else err
                        "%" ->  if ok1 == Number && ok2 == Number then
                                    Ok Number
                                else err
                        "<" ->  if ok1 == Number && ok2 == Number then
                                    Ok Bool
                                else err
                        ">" ->  if ok1 == Number && ok2 == Number then
                                    Ok Bool
                                else err
                        "<=" -> if ok1 == Number && ok2 == Number then
                                    Ok Bool
                                else err
                        ">=" -> if ok1 == Number && ok2 == Number then
                                    Ok Bool
                                else err
                        "==" -> if ok1 == ok2 then
                                    Ok Bool
                                else err
                        "!=" -> if ok1 == ok2 then
                                    Ok Bool
                                else err
                        "&&" -> if ok1 == Bool && ok2 == Bool then
                                    Ok Bool
                                else err
                        "||" -> if ok1 == Bool && ok2 == Bool then
                                    Ok Bool
                                else err
                        "=>" -> if ok1 == Bool && ok2 == Bool then
                                    Ok Bool
                                else err
                        _ -> err
                        ))

prefixType : Scope -> TypeScope -> String -> Lexpr -> Result String Type
prefixType scope typeScope op r = exprType scope typeScope r 
    |> Result.andThen (\ok
    -> let err = Err <| "TypeError (" ++ posToString r ++ "): unknown operation " ++ op ++ typeToString ok in
        case op of
            "!" -> if ok == Bool then Ok Bool else err
            "-" -> if ok == Number then Ok Number else err
            _ -> err)

exprType : Scope -> TypeScope -> Lexpr -> Result String Type
exprType scope typeScope located = case located.value of
    Lang.Ident n -> Maybe.withDefault (Err <| "NameError: (" ++ posToString located ++ "): unknown variable " ++ n) (Dict.get n scope |> Maybe.andThen(\ok->Just(Ok ok)))
    Lang.Bool _ -> Ok Bool
    Lang.Number _ -> Ok Number
    Lang.Char _ -> Ok Char
    Lang.String _ -> Ok <| Array Char
    Lang.Infix op l r -> infixType scope typeScope op l r
    Lang.Prefix op r -> prefixType scope typeScope op r
    Lang.Call func arg  -> exprType scope typeScope func
                        |> Result.andThen (\ok1
                            -> exprType scope typeScope arg
                            |> Result.andThen (\ok2
                                -> case ok1 of
                                    Function a b -> if ok2 == a then Ok b else Err <| "TypeError (" ++ posToString func ++ "): call expects argument type " ++ typeToString a ++ ", not " ++ typeToString ok1
                                    _ -> Err <| "TypeError (" ++ posToString func ++ "): calling non-function"
                                    ))
    Lang.Tuple exprs -> case exprs of
                            [l, r] -> exprType scope typeScope l |> Result.andThen (\ok1->exprType scope typeScope r |> Result.andThen (\ok2->Ok <| Product ok1 ok2))
                            x::xs ->  List.foldr (\a b -> exprType scope typeScope a |> Result.andThen (\ok1 -> b |> Result.andThen (\ok2 -> Ok <| Product ok1 ok2))) (exprType scope typeScope x) xs
                            [] -> Ok Unit -- this shouldn't happen in theory, but a () would have type Unit
    Lang.Unit -> Ok Unit

checkStmt : Scope -> TypeScope -> Lstmt -> Result String Type
checkStmt scope typeScope stmt = case stmt.value of
    Lang.Declaration t n v -> evalType typeScope t |> Result.andThen (\ok1->exprType scope typeScope v |> Result.andThen (\ok2->if ok1==ok2 then Ok ok1 else Err <| "TypeError (" ++ posToString stmt ++ "): cannot assign " ++ typeToString ok2 ++ " to " ++ n ++ ", of type " ++ typeToString ok1))
    Lang.TypeDefinition _ t -> evalType typeScope t

checkStmts : Scope -> TypeScope -> List Lstmt -> Result String ()
checkStmts scope typeScope stmts = case stmts of
    stmt::rest  -> checkStmt scope typeScope stmt
                |> Result.andThen (\t ->
                    case stmt.value of
                        Lang.Declaration _ n _ -> checkStmts (Dict.insert n t scope) typeScope rest
                        Lang.TypeDefinition n _ -> checkStmts scope (Dict.insert n t typeScope) rest)
    [] -> Ok ()

typecheck = checkStmts (Dict.fromList []) (Dict.fromList [("String", Array Char), ("Number", Number), ("Bool", Bool)])

pc : String -> Result (List Parser.DeadEnd) (Result String ())
pc s = Parser.run Lang.parse s |> Result.map (typecheck)