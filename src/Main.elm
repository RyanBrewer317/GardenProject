port module Main exposing (..)

import Browser
import Html exposing (..)
import Html.Attributes exposing (..)
import Html.Events exposing (..)
import Json.Decode as D

main : Program () Model Update
main = Browser.element { 
      init = init
    , view = view
    , update = update
    , subscriptions = subscriptions
    }

port requestPage : String -> Cmd msg
port pageReceiver : (String -> msg) -> Sub msg

type alias Model = { code : String, searchDraft : String}

init : () -> ( Model, Cmd Update )
init _ = ({code = "", searchDraft = ""}, Cmd.none)

type Update = Receive String
            | SearchbarTyping String
            | Search

update : Update -> Model -> ( Model, Cmd Update )
update msg model = case msg of
    Receive code -> ({model | code = code}, Cmd.none)
    SearchbarTyping text -> ({model | searchDraft = text}, Cmd.none)
    Search -> ({model | searchDraft = ""}, requestPage model.searchDraft)

subscriptions : Model -> Sub Update
subscriptions _ = pageReceiver (Receive)

view : Model -> Html Update
view model = div [] [ 
        nav [id "nav"] [
            input [type_ "text", placeholder "search...", onInput SearchbarTyping, on "keydown" (ifIsEnter Search), id "searchbar"] []
        ],
        div [class "p"] [text model.code]
    ]

ifIsEnter : msg -> D.Decoder msg
ifIsEnter msg =
  D.field "key" D.string
    |> D.andThen (\key -> if key == "Enter" then D.succeed msg else D.fail "some other key")