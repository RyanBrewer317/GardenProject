module FTV exposing (..)

type FTV = FTV Int

init : FTV
init = FTV -1

withFresh : (FTV -> String -> (FTV, a)) -> FTV -> (FTV, a)
withFresh f ftv = case ftv of
    FTV i ->
        let newvar = "a" ++ String.fromInt (i + 1) in
        let newftv = FTV (i + 1) in
        f newftv newvar
