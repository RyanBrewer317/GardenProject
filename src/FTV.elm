module FTV exposing (..)

type FTV a = FTV a Int

return : a -> FTV a
return a = FTV a -1

flipbind : (a -> FTV b) -> FTV a -> FTV b
flipbind f ftv = case ftv of
    FTV a lastvar -> 
        let (FTV result var) = f(a) in
            if var == -1 then 
                FTV result lastvar
            else
                FTV result var

bind : FTV a -> (a -> FTV b) -> FTV b
bind ftv f = flipbind f ftv

fmap : (a -> b) -> FTV a -> FTV b
fmap f ftv = bind ftv (\a->return(f(a)))

withFresh : (FTV a -> String -> FTV b) -> FTV a -> FTV b
withFresh f ftv = case ftv of
    FTV a i ->
        let newvar = "a" ++ String.fromInt (i + 1) in
        let newftv = FTV a (i + 1) in
        f newftv newvar

unwrap : FTV a -> a
unwrap ftv = case ftv of
    FTV v _ -> v

pass : FTV a -> b -> FTV b
pass ftv a = bind ftv (\_->return a)