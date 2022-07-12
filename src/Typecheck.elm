module Typecheck exposing (..)
import Lang exposing (..)
import Dict
import FTV

type Type = TBool
          | TNum
          | TChar
          | TString
          | TFunc Type Type
          | TTuple (List Type)
          | TVar String
          | Forall (List Type) Type
          | ADT String (List Type)

-- evalTypeLit : TypeLit -> Type
-- evalTypeLit t = case t of
--     TNumLit -> TNum
--     TBoolLit -> TBool
--     TFuncLit u v -> TFunc (evalTypeLit u) (evalTypeLit v)

type Constraint = Equation Type Type

type alias Scope = Dict.Dict String Type

typeToString : Type -> String
typeToString t = case t of
    TBool -> "Bool"
    TNum -> "Number"
    TChar -> "Char"
    TString -> "String"
    TFunc u v -> typeToString u ++ "->" ++ typeToString v
    TTuple ts -> "(" ++ String.join ", " (ts |> List.map typeToString) ++ ")"
    TVar n -> n
    ADT n ts -> n ++ "<" ++ String.join ", " (ts |> List.map typeToString) ++ ">"
    Forall vars u -> case vars of
        [] -> typeToString u
        _ -> 
            let (showVars, showType, _) = List.foldr (\tvar (showvars, typ, supply)->
                    case tvar of 
                        TVar _->case supply of
                            [] -> ("ba"::showvars, sub tvar (TVar "ba") typ, [])
                            x::xs -> (x :: showvars, sub tvar (TVar x) typ, xs)
                        _->("" :: showvars, typ, supply)) ([], u, String.toList "abcdefghijklmnopqrstuvwxyz" |> List.map String.fromChar) vars in
            "forall " ++ String.join ", " (List.reverse <| showVars) ++ ". " ++ typeToString showType

debugTypeToString : Type -> String
debugTypeToString t = case t of
    Forall _ _ -> typeToString t
    _ -> typeToString <| generalize (Dict.empty) t (Forall [] t)

locToPosString : Located a -> String
locToPosString loc = "("++(
    case loc.start of 
        (row, col)->String.fromInt row++", "++String.fromInt col
    )++")"
typeMismatch : Located a -> Type -> Type -> String
typeMismatch loc t u = "TypeError " ++ locToPosString loc ++ ": expected " ++ typeToString t ++ ", got " ++ typeToString u
nameErr : Located a -> String -> String
nameErr loc n = "NameError " ++ locToPosString loc ++ ": unknown identifier " ++ n

argsToType : List (String, Type) -> Type
argsToType args = case args of
    [(_, t)] -> t
    _ -> TTuple <| List.map Tuple.second args

locmap : Located a -> b -> Located b
locmap loc constraint = case loc of
    {start, end} -> {start=start, value=constraint, end=end}

typecheckExpr : Scope -> FTV.FTV (Located Expr) -> Result String (FTV.FTV Type, List (Located Constraint))
typecheckExpr scope ftvExpr = case (FTV.unwrap ftvExpr).value of
    Ident n -> case Dict.get n scope of
        Just t -> Ok (instantiate(FTV.pass ftvExpr t), [])
        Nothing -> Err <| nameErr (FTV.unwrap ftvExpr) n
    Function args body ->
        let ftvArgTypes = List.foldr (\ident ftvArgsSoFar -> FTV.withFresh(\ftv v-> FTV.pass ftv ((ident, TVar v)::FTV.unwrap ftvArgsSoFar)) ftvArgsSoFar) (FTV.pass ftvExpr []) args in 
        let newScope = Dict.union (Dict.fromList (FTV.unwrap ftvArgTypes)) scope in
        typecheckExpr newScope (FTV.pass ftvArgTypes body) 
        |> Result.map (\(ftvBodyType, bodyConstraints)->
            let argsType = argsToType (FTV.unwrap ftvArgTypes) in
            let bodyType = FTV.unwrap ftvBodyType in
            let exprType = TFunc argsType bodyType in
            let ftvExprType = FTV.pass ftvBodyType exprType in
            (ftvExprType, bodyConstraints)
        )
    Call foo bar -> 
        typecheckExpr scope (FTV.pass ftvExpr    foo) |> Result.andThen (\(ftvFooType, fooConstraints)->
        typecheckExpr scope (FTV.pass ftvFooType bar) 
        |> Result.map (\(ftvBarType, barConstraints)->
            FTV.withFresh (\ftv v-> 
                let expr = FTV.unwrap ftvExpr in
                let exprType = TVar v in
                let ftvExprType = FTV.pass ftv exprType in
                let fooType = FTV.unwrap ftvFooType in
                let barType = FTV.unwrap ftvBarType in
                FTV.pass ftv
                (   ftvExprType 
                ,   locmap expr (Equation fooType (TFunc barType exprType))::
                    fooConstraints++barConstraints
                )
            ) ftvBarType 
            |> FTV.unwrap
        ))
    BoolLit _ -> Ok (FTV.pass ftvExpr TBool, [])
    NumberLit _ -> Ok (FTV.pass ftvExpr TNum, [])
    If cond cons alt ->
        typecheckExpr scope (FTV.pass ftvExpr cond    ) |> Result.andThen (\(ftvCondType, condConstraints)->
        typecheckExpr scope (FTV.pass ftvCondType cons) |> Result.andThen (\(ftvConsType, consConstraints)->
        typecheckExpr scope (FTV.pass ftvConsType alt ) |> Result.map     (\(ftvAltType , altConstraints )->
        FTV.withFresh(\ftv v->
            let exprType = TVar v in
            let ftvExprType = FTV.pass ftv exprType in
            let condType = FTV.unwrap ftvCondType in
            let consType = FTV.unwrap ftvConsType in
            let altType  = FTV.unwrap ftvAltType in
            FTV.pass ftv
            (   ftvExprType
            ,   locmap cond (Equation condType TBool   ) ::
                locmap cons (Equation consType exprType) ::
                locmap alt  (Equation altType  exprType) ::
                condConstraints++consConstraints++altConstraints
            )
        ) ftvAltType 
        |> FTV.unwrap)))
    CharLit _ -> Ok (FTV.pass ftvExpr TChar, [])
    StringLit _ -> Ok (FTV.pass ftvExpr TString, [])
    Infix left op right ->
        case Dict.get op scope of
            Nothing -> Err <| nameErr (FTV.unwrap ftvExpr) op
            Just t -> 
                let ftvOpType = instantiate(FTV.pass ftvExpr t) in
                typecheckExpr scope (FTV.pass ftvOpType   left ) |> Result.andThen (\(ftvLeftType,  leftConstraints )->
                typecheckExpr scope (FTV.pass ftvLeftType right) |> Result.map     (\(ftvRightType, rightConstraints)->
                FTV.withFresh(\ftv v->
                    let expr = FTV.unwrap ftvExpr in
                    let exprType = TVar v in
                    let ftvExprType = FTV.pass ftv exprType in
                    let rightType = FTV.unwrap ftvRightType in
                    let opType    = FTV.unwrap ftvOpType    in
                    let leftType  = FTV.unwrap ftvLeftType  in
                    FTV.pass ftv
                    ( ftvExprType
                    , locmap expr (Equation opType (TFunc (TTuple [leftType, rightType]) exprType)) ::
                      leftConstraints++rightConstraints
                    )
                ) ftvRightType
                |> FTV.unwrap))
    Prefix op right ->
        case Dict.get op scope of
            Nothing -> Err <| nameErr (FTV.unwrap ftvExpr) op
            Just typ ->
                let t = (case op of
                        "-" -> Forall [TVar "a"] (TFunc TNum TNum)
                        _ -> typ) in
                let ftvOpType = instantiate(FTV.pass ftvExpr t) in
                typecheckExpr scope (FTV.pass ftvOpType right) |> Result.map (\(ftvRightType, rightConstraints)->
                FTV.withFresh(\ftv v->
                    let expr = FTV.unwrap ftvExpr in
                    let exprType = TVar v in
                    let ftvExprType = FTV.pass ftv exprType in
                    let opType = FTV.unwrap ftvOpType in
                    let rightType = FTV.unwrap ftvRightType in
                    FTV.pass ftv
                    ( ftvExprType
                    , locmap expr (Equation opType (TFunc rightType exprType))::
                      rightConstraints
                    )
                ) ftvRightType
                |> FTV.unwrap)
    ArrayLit exprs -> 
        FTV.withFresh (\ftv v->
            let res = List.foldr (\a b -> 
                    b                                            |> Result.andThen (\(ftvInnerTyp, prevTypes, prevConstraints)->
                    typecheckExpr scope (FTV.pass ftvInnerTyp a) |> Result.map     (\(ftvType, typeConstraints)->
                    (ftvInnerTyp, (FTV.unwrap ftvType)::prevTypes, locmap a (Equation (FTV.unwrap ftvInnerTyp) (FTV.unwrap ftvType))::typeConstraints++prevConstraints)))) (Ok (FTV.pass ftv (TVar v), [], [])) (List.reverse exprs)
            in
            res |> Result.map(\(ftvInnerType, types, constraints)->
            let exprType = ADT "Array" [FTV.unwrap ftvInnerType] in
            let ftvExprType = FTV.pass ftv exprType in
            ( ftvExprType
            , constraints
            )) |> FTV.pass ftv
        ) ftvExpr |> FTV.unwrap
    Index coll idx -> 
        typecheckExpr scope (FTV.pass ftvExpr coll)     |> Result.andThen (\(ftvCollType, collConstraints)->
        typecheckExpr scope (FTV.pass ftvCollType idx ) |> Result.map (\(ftvIdxType , idxConstraints )->
        FTV.withFresh(\ftv v->
            let exprType = TVar v in
            let ftvExprType = FTV.pass ftv exprType in
            let collType = FTV.unwrap ftvCollType in
            let idxType  = FTV.unwrap ftvIdxType in
            FTV.pass ftv
            ( ftvExprType
            , locmap coll (Equation collType (ADT "Array" [exprType]))::
              locmap idx  (Equation idxType  TNum)::
              collConstraints++idxConstraints
            )
        ) ftvIdxType |> FTV.unwrap))
    _ -> Err ""

typeOf : Scope -> FTV.FTV (Located Expr) -> Result String (FTV.FTV Type)
typeOf scope ftvexpr = typecheckExpr scope ftvexpr |> Result.andThen (\(ftvt, constraints)->
                    solve constraints [] [] |> Result.map (\substitutions->
                    List.foldr (\(Subst t1 t2) ftvb->FTV.fmap(sub (TVar t1) t2) ftvb) ftvt substitutions))

letTypeOf : Scope -> FTV.FTV (Located Expr) -> Result String (Scope, FTV.FTV Type)
letTypeOf scope ftvexpr = Result.andThen (\(t, constraints)->preGeneralize scope constraints t) (typecheckExpr scope ftvexpr)

type Subst = Subst String Type

typeErr : Located a -> String -> Result String value
typeErr loc s = Err <| "TypeError " ++ locToPosString loc ++ ": " ++ s

solve : (List (Located Constraint)) -> (List Subst) -> (List (Located Constraint))-> Result String (List Subst)
solve constraints substitutions skipped = case constraints of
    loc::rest -> case loc.value of
        Equation t1 t2 ->
            let continue = \_->solve rest substitutions (loc::skipped) in
            let err = \_->typeErr loc <| debugTypeToString t1 ++ " can't equal " ++ debugTypeToString t2 in
            let removeAndContinue = \_->solve rest substitutions skipped in
            let handleVarIsolationAndContinue = \v->solve (substituteAll rest t2 t1) (Subst v t1::substitutions) (substituteAll skipped t2 t1) in
            if t1 == t2 then
                solve rest substitutions skipped
            else case t1 of
                TFunc a b ->
                    case t2 of
                        TFunc c d -> solve (locmap loc (Equation a c) :: locmap loc (Equation b d) :: rest) substitutions skipped
                        TVar x -> 
                            if occurs t2 t1 then
                                continue()
                            else
                                solve (substituteAll rest t2 t1) (Subst x t1::substitutions) (substituteAll skipped t2 t1)
                        _ -> err()
                TTuple ts ->
                    case t2 of
                        TTuple ts2 -> 
                            if List.length ts /= List.length ts2 then
                                err()
                            else
                                solve ((List.map2 (\l r->locmap loc (Equation l r)) ts ts2)++rest) substitutions skipped
                        TVar x ->
                            if occurs t2 t1 then
                                continue()
                            else
                                solve (substituteAll rest t2 t1) (Subst x t1::substitutions) (substituteAll skipped t2 t1)
                        _ -> err()
                ADT n ts ->
                    case t2 of
                        ADT n2 ts2 ->
                            if n /= n2 || List.length ts /= List.length ts2 then
                                err()
                            else
                                solve ((List.map2 (\l r ->locmap loc (Equation l r)) ts ts2)++rest) substitutions skipped
                        TVar x ->
                            if occurs t2 t1 then
                                continue()
                            else
                                solve (substituteAll rest t2 t1) (Subst x t1::substitutions) (substituteAll skipped t2 t1)
                        _ -> err()
                TVar x -> 
                    if occurs t1 t2 then
                        continue()
                    else
                        solve (substituteAll rest t1 t2) (Subst x t2::substitutions) (substituteAll skipped t1 t2)
                TBool ->
                    case t2 of
                        TVar v -> handleVarIsolationAndContinue(v)
                        TBool -> removeAndContinue() -- theoretically impossible but this would be the right thing to do if it happened
                        _ -> err()
                TNum ->
                    case t2 of
                        TVar v -> handleVarIsolationAndContinue(v)
                        TNum -> removeAndContinue() -- theoretically impossible but this would be the right thing to do if it happened
                        _ -> err()
                TChar ->
                    case t2 of
                        TVar v -> handleVarIsolationAndContinue(v)
                        TChar -> removeAndContinue()
                        _ -> err()
                TString ->
                    case t2 of
                        TVar v -> handleVarIsolationAndContinue(v)
                        TString -> removeAndContinue()
                        _ -> err()
                _ -> continue()
    [] -> if List.isEmpty skipped then Ok substitutions else solve skipped substitutions []

substituteAll : List (Located Constraint) -> Type -> Type -> List (Located Constraint)
substituteAll constraints var val = case constraints of
    [] -> []
    loc::rest -> case loc.value of
        Equation u v ->
            let u2 = sub var val u in
            let v2 = sub var val v in
            locmap loc (Equation u2 v2)::substituteAll rest var val

sub : Type -> Type -> Type -> Type
sub var val t = case t of
    TVar _ -> if t == var then val else t
    TBool -> t
    TNum -> t
    TChar -> t
    TString -> t
    TFunc a b -> TFunc (sub var val a) (sub var val b)
    TTuple ts -> TTuple (List.map (sub var val) ts)
    ADT n ts -> ADT n (List.map (sub var val) ts)
    Forall vars u -> Forall vars (sub var val u)

occurs : Type -> Type -> Bool
occurs var t = case t of
    TVar _ -> t == var
    TBool -> False
    TNum -> False
    TChar -> False
    TString -> False
    TFunc a b -> occurs var a && occurs var b
    TTuple ts -> List.any (occurs var) ts
    ADT _ ts -> List.any (occurs var) ts
    Forall vars u -> List.any (\v->v==var) vars || occurs var u

instantiate : FTV.FTV Type -> FTV.FTV Type
instantiate ftvt = case FTV.unwrap ftvt of
    TBool -> ftvt
    TNum -> ftvt
    TChar -> ftvt
    TString -> ftvt
    TFunc a b -> 
        let ftva = instantiate (FTV.pass ftvt a) in 
        let ftvb = instantiate (FTV.pass ftva b) in
            FTV.pass ftvb (TFunc (FTV.unwrap ftva) (FTV.unwrap ftvb))
    TTuple ts -> FTV.fmap TTuple <| List.foldr (\t ftvts-> instantiate (FTV.pass ftvts t) |> FTV.fmap (\newt->newt::FTV.unwrap ftvts)) (FTV.pass ftvt []) ts
    TVar _ -> ftvt
    ADT n ts -> FTV.fmap (ADT n) <| List.foldr (\t ftvts-> instantiate (FTV.pass ftvts t) |> FTV.fmap (\newt->newt::FTV.unwrap ftvts)) (FTV.pass ftvt []) ts
    Forall vars u -> List.foldr (\var ftvtype->FTV.flipbind (\typ->FTV.withFresh (\ftv v->FTV.pass ftv <| sub var (TVar v) typ) ftvtype) ftvtype) (FTV.pass ftvt u) vars

generalize : Scope -> Type -> Type -> Type
generalize scope t scheme = 
    case scheme of
        Forall vars typ ->
            case t of
                TVar x -> 
                    if occursInScope scope x || List.member t vars then 
                        scheme 
                    else 
                        Forall (t::vars) typ
                TChar -> scheme
                TBool -> scheme
                TNum -> scheme
                TString -> scheme
                TFunc a b -> 
                    let (varsA, _) = Maybe.withDefault ([], a) <| schemeFrom <| generalize scope a scheme in 
                    let (varsB, _) = Maybe.withDefault ([], b) <| schemeFrom <| generalize scope b scheme in 
                    let set = List.foldr (\item l->if List.member item l then l else item :: l) [] (vars++varsA++varsB) in
                    Forall set typ
                TTuple ts -> List.foldr (\u schem-> generalize scope u schem) scheme ts
                ADT _ ts -> List.foldr (\u schem-> generalize scope u schem) scheme ts
                Forall _ _ -> t
        _ -> Forall [] t -- this shouldn't happen...

schemeFrom : Type -> Maybe (List Type, Type)
schemeFrom t = case t of
    Forall vars u -> Just (vars, u)
    _ -> Nothing

preGeneralize : Scope -> List (Located Constraint) -> FTV.FTV Type -> Result String (Scope, FTV.FTV Type)
preGeneralize scope constraints ftvt = 
    {-substitutions<--}solve constraints [] [] |> Result.map(\substitutions->
    let env = List.foldr (\(Subst x u) scop->Dict.map (\_ v->sub (TVar x) u v) scop) scope substitutions in
    let ftvt2 = List.foldr (\(Subst x u) ftvb->FTV.fmap (sub (TVar x) u) ftvb) ftvt substitutions in 
    let scheme = FTV.fmap (\t2->generalize scope t2 (Forall [] t2)) ftvt2 in
    (env, scheme))

occursInScope : Scope -> String -> Bool
occursInScope scope var = Dict.toList scope |> List.any (\(_, t)->occurs (TVar var) t)

typecheckStmt : Scope -> FTV.FTV Stmt -> Result String (Scope, FTV.FTV Type)
typecheckStmt scope ftvstmt = case FTV.unwrap ftvstmt of
    Declaration _ locx  -> letTypeOf scope (FTV.pass ftvstmt locx)

typecheck : Scope -> FTV.FTV (List (Located Stmt)) -> Result String (FTV.FTV Scope)
typecheck scope ast = case FTV.unwrap ast of
    [] -> Ok (FTV.pass ast scope)
    stmt::rest -> Result.andThen (\(scope2, ftvt)->
        case stmt.value of
            Declaration n _ -> typecheck (Dict.insert n (FTV.unwrap ftvt) scope2) (FTV.pass ftvt rest)
            --_ -> typecheck scope rest
        ) (typecheckStmt scope (FTV.pass ast stmt.value))