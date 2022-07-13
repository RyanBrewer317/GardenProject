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

type Annot = AnnotPrim   {val : (Located Expr), typ : Type}
           | AnnotFunc   {args : (List (String, Type)), block : Annot, typ : Type}
           | AnnotCall   {func : Annot, args : Annot, typ : Type}
           | AnnotIf     {cond : Annot, cons : Annot, alt : Annot, typ : Type}
           | AnnotTuple  {vals : (List Annot), typ : Type}
           | AnnotArray  {vals : (List Annot), typ : Type}
           | AnnotPrefix {op : String, right : Annot, typ : Type}
           | AnnotInfix  {left : Annot, op : String, right : Annot, typ : Type}
           | AnnotIndex  {coll : Annot, idx : Annot, typ : Type}

type AnnotStmt = AnnotDecl String Annot

-- evalTypeLit : TypeLit -> Type
-- evalTypeLit t = case t of
--     TNumLit -> TNum
--     TBoolLit -> TBool
--     TFuncLit u v -> TFunc (evalTypeLit u) (evalTypeLit v)

type Constraint = Equation Type Type

type alias Scope = Dict.Dict String Type

typeToStringHelper : Type -> String
typeToStringHelper t = case t of
    TBool -> "Bool"
    TNum -> "Number"
    TChar -> "Char"
    TString -> "String"
    TFunc u v -> typeToStringHelper u ++ "->" ++ typeToStringHelper v
    TTuple ts -> "(" ++ String.join ", " (ts |> List.map typeToStringHelper) ++ ")"
    TVar n -> n
    ADT n ts -> n ++ "<" ++ String.join ", " (ts |> List.map typeToStringHelper) ++ ">"
    Forall vars u -> case vars of
        [] -> typeToStringHelper u
        _ -> 
            let (showVars, showType, _) = List.foldr (\tvar (showvars, typ, supply)->
                    case tvar of 
                        TVar _->case supply of
                            [] -> ("ba"::showvars, sub tvar (TVar "ba") typ, [])
                            x::xs -> (x :: showvars, sub tvar (TVar x) typ, xs)
                        _->("" :: showvars, typ, supply)) ([], u, String.toList "abcdefghijklmnopqrstuvwxyz" |> List.map String.fromChar) vars in
            "<" ++ String.join ", " (List.reverse <| showVars) ++ ">" ++ typeToStringHelper showType

typeToString : Type -> String
typeToString t = case t of
    Forall _ _ -> typeToStringHelper t
    _ -> typeToStringHelper <| generalize (Dict.empty) t (Forall [] t)

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

typecheckExpr : Scope -> FTV.FTV -> Located Expr -> Result String (FTV.FTV, Annot, List (Located Constraint))
typecheckExpr scope ftv loc = 
    case loc.value of
        Ident n -> case Dict.get n scope of
            Just t -> instantiate ftv t |> (\(ftv2, t2)->Ok (ftv2, AnnotPrim {val=loc, typ=t2}, []))
            Nothing -> Err <| nameErr loc n
        Function args body ->
            let (ftv2, argTypes) = List.foldr (\ident (ftvx, argsSoFar) -> FTV.withFresh(\ftvx2 v-> (ftvx2, ((ident, TVar v)::argsSoFar))) ftvx) (ftv, []) args in 
            let newScope = Dict.union (Dict.fromList (argTypes)) scope in
            typecheckExpr newScope ftv2 body
            |> Result.map (\(ftv3, bodyAnnot, bodyConstraints)->
                let argsType = argsToType argTypes in
                let bodyType = typeOf bodyAnnot in
                let exprType = TFunc argsType bodyType in
                ( ftv3
                , AnnotFunc {args=argTypes, block=bodyAnnot, typ=exprType}
                , bodyConstraints)
            )
        Call foo bar -> 
            typecheckExpr scope ftv foo |> Result.andThen (\(ftv2, fooAnnot, fooConstraints)->
            typecheckExpr scope ftv2 bar
            |> Result.map (\(ftv3, barAnnot, barConstraints)->
                FTV.withFresh (\ftv4 v-> 
                    let exprType = TVar v in
                    let fooType = typeOf fooAnnot in
                    let barType = typeOf barAnnot in
                    ( ftv4
                    , (AnnotCall {func=fooAnnot, args=barAnnot, typ=exprType}
                    , locmap loc (Equation fooType (TFunc barType exprType))::
                      fooConstraints++barConstraints
                    ))
                ) ftv3
                |> (\(ftv4, (annCall, consts))->(ftv4, annCall, consts))
            ))
        BoolLit _ -> Ok (ftv, AnnotPrim {val=loc, typ=TBool}, [])
        NumberLit _ -> Ok (ftv, AnnotPrim {val=loc, typ=TNum}, [])
        If cond cons alt ->
            typecheckExpr scope ftv cond |> Result.andThen (\(ftv2, condAnnot, condConstraints)->
            typecheckExpr scope ftv2 cons |> Result.andThen (\(ftv3, consAnnot, consConstraints)->
            typecheckExpr scope ftv3 alt  |> Result.map     (\(ftv4, altAnnot , altConstraints )->
            FTV.withFresh(\ftv5 v->
                let exprType = TVar v in
                let condType = typeOf condAnnot in
                let consType = typeOf consAnnot in
                let altType  = typeOf altAnnot in
                ( ftv5
                , ( AnnotIf {cond=condAnnot, cons=consAnnot, alt=altAnnot, typ=exprType}
                  , locmap cond (Equation condType TBool   ) ::
                    locmap cons (Equation consType exprType) ::
                    locmap alt  (Equation altType  exprType) ::
                    condConstraints++consConstraints++altConstraints
                ))
            ) ftv4 
            |> (\(ftv5, (annIf, ifConsts))->(ftv5, annIf, ifConsts)))))
        CharLit _ -> Ok (ftv, AnnotPrim {val=loc, typ=TChar}, [])
        StringLit _ -> Ok (ftv, AnnotPrim {val=loc, typ=TString}, [])
        Infix left op right ->
            case Dict.get op scope of
                Nothing -> Err <| nameErr loc op
                Just t -> 
                    let (ftv2, opType) = instantiate ftv t in
                    typecheckExpr scope ftv2 left  |> Result.andThen (\(ftv3, leftAnnot , leftConstraints )->
                    typecheckExpr scope ftv3 right |> Result.map     (\(ftv4, rightAnnot, rightConstraints)->
                    FTV.withFresh(\ftv5 v->
                        let exprType = TVar v in
                        let rightType = typeOf rightAnnot in
                        let leftType  = typeOf leftAnnot in
                        ( ftv5
                        , ( AnnotInfix {right=rightAnnot, op=op, left=leftAnnot, typ=exprType}
                          , locmap loc (Equation opType (TFunc (TTuple [leftType, rightType]) exprType)) ::
                            leftConstraints++rightConstraints
                          )
                        )
                    ) ftv4
                    |> (\(ftv5, (annInfix, consts))->(ftv5, annInfix, consts))))
        Prefix op right ->
            case Dict.get op scope of
                Nothing -> Err <| nameErr loc op
                Just typ ->
                    let t = (case op of
                            "-" -> Forall [TVar "a"] (TFunc TNum TNum)
                            _ -> typ) in
                    let (ftv2, opType) = instantiate ftv t in
                    typecheckExpr scope ftv2 right |> Result.map (\(ftv3, rightAnnot, rightConstraints)->
                    FTV.withFresh(\ftv4 v->
                        let exprType = TVar v in
                        let rightType = typeOf rightAnnot in
                        ( ftv4
                        , ( AnnotPrefix {op=op, right=rightAnnot, typ=exprType}
                          , locmap loc (Equation opType (TFunc rightType exprType))::
                            rightConstraints
                          )
                        )
                    ) ftv3
                    |> (\(ftv4, (annPrefix, consts))->(ftv4, annPrefix, consts)))
        ArrayLit exprs -> 
            FTV.withFresh (\ftv2 v->
                let res = List.foldr (\expr r -> 
                        r                             |> Result.andThen (\{ftvx, innerType, annots, constraints}->
                        typecheckExpr scope ftvx expr |> Result.map     (\(ftvx2, annot, typeConstraints)->
                        {ftvx=ftvx2, innerType=innerType, annots=annot::annots, constraints=locmap expr (Equation innerType (typeOf annot))::typeConstraints++constraints}))) (Ok {ftvx=ftv2, innerType=TVar v, annots=[], constraints=[]}) (List.reverse exprs)
                in
                (ftv, res |> Result.map(\{ftvx, innerType, annots, constraints}->
                let exprType = ADT "Array" [innerType] in
                ( ftvx
                , ( AnnotArray {vals=annots, typ=exprType}
                  , constraints
                  )
                )
                )
            )) ftv 
            |> Tuple.second |> Result.map (\(ftv2, (annArr, consts))->(ftv2, annArr, consts))
        Index coll idx -> 
            typecheckExpr scope ftv coll |> Result.andThen (\(ftv2, collAnnot, collConstraints)->
            typecheckExpr scope ftv2 idx |> Result.map     (\(ftv3, idxAnnot , idxConstraints )->
            FTV.withFresh(\ftv4 v->
                let exprType = TVar v in
                let collType = typeOf collAnnot in
                let idxType  = typeOf idxAnnot in
                ( ftv4
                , ( AnnotIndex {coll=collAnnot, idx=idxAnnot, typ=exprType}
                  , locmap coll (Equation collType (ADT "Array" [exprType]))::
                    locmap idx  (Equation idxType  TNum)::
                    collConstraints++idxConstraints
                  )
                )
            ) ftv3 
            |> (\(ftv4, (annIndex, consts))->(ftv4, annIndex, consts))))
        _ -> Err ""

typeOf : Annot -> Type
typeOf a = case a of
    AnnotPrim   {typ} -> typ
    AnnotFunc   {typ} -> typ
    AnnotCall   {typ} -> typ
    AnnotIf     {typ} -> typ
    AnnotTuple  {typ} -> typ
    AnnotArray  {typ} -> typ
    AnnotPrefix {typ} -> typ
    AnnotInfix  {typ} -> typ
    AnnotIndex  {typ} -> typ

updateType : (Type -> Type) -> Annot -> Annot
updateType f a = case a of
    AnnotPrim   {val, typ} -> AnnotPrim {val=val, typ=f typ}
    AnnotFunc   {args, block, typ} -> AnnotFunc {args=args, block=block, typ=f typ}
    AnnotCall   {func, args, typ} -> AnnotCall {func=func, args=args, typ=f typ}
    AnnotIf     {cond, cons, alt, typ} -> AnnotIf {cond=cond, cons=cons, alt=alt, typ=f typ}
    AnnotTuple  {vals, typ} -> AnnotTuple {vals=vals, typ=f typ}
    AnnotArray  {vals, typ} -> AnnotArray {vals=vals, typ=f typ}
    AnnotPrefix {op, right, typ} -> AnnotPrefix {op=op, right=right, typ=f typ}
    AnnotInfix  {left, op, right, typ} -> AnnotInfix {left=left, op=op, right=right, typ=f typ}
    AnnotIndex  {coll, idx, typ} -> AnnotIndex {coll=coll, idx=idx, typ=f typ}

updateTypes : (Type -> Type) -> Annot -> Annot
updateTypes f a = case a of
    AnnotPrim   {val, typ} -> AnnotPrim {val=val, typ=f typ}
    AnnotFunc   {args, block, typ} -> AnnotFunc {args=args, block=updateTypes f block, typ=f typ}
    AnnotCall   {func, args, typ} -> AnnotCall {func=updateTypes f func, args=updateTypes f args, typ=f typ}
    AnnotIf     {cond, cons, alt, typ} -> AnnotIf {cond=updateTypes f cond, cons=updateTypes f cons, alt=updateTypes f alt, typ=f typ}
    AnnotTuple  {vals, typ} -> AnnotTuple {vals=List.map (updateTypes f) vals, typ=f typ}
    AnnotArray  {vals, typ} -> AnnotArray {vals=List.map (updateTypes f) vals, typ=f typ}
    AnnotPrefix {op, right, typ} -> AnnotPrefix {op=op, right=updateTypes f right, typ=f typ}
    AnnotInfix  {left, op, right, typ} -> AnnotInfix {left=updateTypes f left, op=op, right=updateTypes f right, typ=f typ}
    AnnotIndex  {coll, idx, typ} -> AnnotIndex {coll=updateTypes f coll, idx=updateTypes f idx, typ=f typ}

-- typeOf : Scope -> FTV.FTV (Located Expr) -> Result String (FTV.FTV Type)
-- typeOf scope ftvexpr = typecheckExpr scope ftvexpr |> Result.andThen (\(ftvt, constraints)->
--                     solve constraints [] [] |> Result.map (\substitutions->
--                     List.foldr (\(Subst t1 t2) ftvb->FTV.fmap(sub (TVar t1) t2) ftvb) ftvt substitutions))

letTypeOf : Scope -> FTV.FTV -> Located Expr -> Result String (Scope, FTV.FTV, Annot)
letTypeOf scope ftv expr = typecheckExpr scope ftv expr |> Result.andThen (\(ftv2, annot, constraints)->preGeneralize scope constraints annot|>Result.map(\(s, a)->(s, ftv2, a)))

type Subst = Subst String Type

typeErr : Located a -> String -> Result String value
typeErr loc s = Err <| "TypeError " ++ locToPosString loc ++ ": " ++ s

solve : (List (Located Constraint)) -> (List Subst) -> (List (Located Constraint))-> Result String (List Subst)
solve constraints substitutions skipped = case constraints of
    loc::rest -> case loc.value of
        Equation t1 t2 ->
            let continue = \_->solve rest substitutions (loc::skipped) in
            let err = \_->typeErr loc <| typeToString t1 ++ " can't equal " ++ typeToString t2 in
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
                Forall _ _ -> Err "something went wrong, Forall found after it should be instantiated"
                -- _ -> continue()
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

instantiate : FTV.FTV  -> Type -> (FTV.FTV, Type)
instantiate ftv t = case t of
    TBool -> (ftv, t)
    TNum -> (ftv, t)
    TChar -> (ftv, t)
    TString -> (ftv, t)
    TFunc a b -> 
        let (ftv2, a2) = instantiate ftv a in 
        let (ftv3, b2) = instantiate ftv2 b in
            (ftv3, (TFunc a2 b2))
    TTuple ts -> Tuple.mapSecond TTuple <| List.foldr (\typ (ftvx, types)-> instantiate ftvx typ |> Tuple.mapSecond (\newt->newt::types)) (ftv, []) ts
    TVar _ -> (ftv, t)
    ADT n ts -> Tuple.mapSecond (ADT n) <| List.foldr (\typ (ftvx, types)-> instantiate ftvx typ |> Tuple.mapSecond (\newt->newt::types)) (ftv, []) ts
    Forall vars u -> List.foldr (\var (ftvx, typ)->FTV.withFresh (\ftvx2 v->(ftvx2, sub var (TVar v) typ)) ftvx) (ftv, u) vars

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

preGeneralize : Scope -> List (Located Constraint) -> Annot -> Result String (Scope, Annot)
preGeneralize scope constraints annot = 
    solve constraints [] [] |> Result.map(\substitutions->
    let env = List.foldr (\(Subst x u) scop->Dict.map (\_ v->sub (TVar x) u v) scop) scope substitutions in
    let annot2 = List.foldr (\(Subst x u) annotx->updateTypes (\t->sub (TVar x) u t) annotx) annot substitutions in 
    let scheme = updateType (\t->generalize scope t (Forall [] t)) annot2 in
    (env, scheme))

occursInScope : Scope -> String -> Bool
occursInScope scope var = Dict.toList scope |> List.any (\(_, t)->occurs (TVar var) t)

typecheckStmt : Scope -> FTV.FTV -> Stmt -> Result String (Scope, FTV.FTV, AnnotStmt)
typecheckStmt scope ftv stmt = case stmt of
    Declaration n locx  -> letTypeOf scope ftv locx |> Result.map (\(s, ftv2, a)->(s, ftv2, AnnotDecl n a))

typecheck : Scope -> FTV.FTV -> List (Located Stmt) -> List AnnotStmt -> Result String (Scope, FTV.FTV, List AnnotStmt)
typecheck scope ftv ast sofar = case ast of
    [] -> Ok (scope, ftv, List.reverse sofar)
    stmt::rest -> typecheckStmt scope ftv stmt.value |> Result.andThen (\(scope2, ftv2, annot)->
        case stmt.value of
            Declaration n _ -> 
                case annot of
                    AnnotDecl _ a -> typecheck (Dict.insert n (typeOf a) scope2) ftv2 rest (annot :: sofar)
            --_ -> typecheck scope rest
        )