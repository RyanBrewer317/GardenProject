module Lang exposing (..)

import Parser exposing (..)
import Set
import Array

type Expression = Ident String
                | Type String
                | Bool Bool
                | Number Float
                | Char Char
                | String String
                | Infix String (Located Expression) (Located Expression)
                | Prefix String (Located Expression)
                | Call (Located Expression) (Located Expression)

keywords : Set.Set String
keywords = Set.fromList ["true", "false"]

type alias Located a =
  { start : (Int, Int)
  , value : a
  , end : (Int, Int)
  }

located : Parser a -> Parser (Located a)
located parser =
  succeed Located
    |= getPosition
    |= parser
    |= getPosition

parseIdent : Parser (Located Expression)
parseIdent = map Ident (variable
    { start = Char.isLower
    , inner = \c -> Char.isAlphaNum c || c == '_'
    , reserved = keywords
    }) |> located

parseType : Parser (Located Expression)
parseType = map Type (variable
    { start = Char.isUpper
    , inner = \c -> Char.isAlphaNum c || c == '_'
    , reserved = keywords
    }) |> located

parseBool : Parser (Located Expression)
parseBool = oneOf 
    [ keyword "true"  |> map (\_ -> Bool True )
    , keyword "false" |> map (\_ -> Bool False)
    ] |> located

parseNumber : Parser (Located Expression)
parseNumber = map Number float |> located

parseChar : Parser (Located Expression)
parseChar = (token "'"
         |. oneOf [token "\\" |. chompIf (\_->True), chompIf (\_->True)]
         |. token "'")
         |> getChompedString
         |> map (String.slice 1 -1)
         |> map String.toList
         |> map Array.fromList
         |> map (\a-> 
                if Array.get 0 a == Just '\\' then
                    case Array.get 1 a of
                        Just 'n' -> '\n'
                        Just 't' -> '\t'
                        Just 'r' -> '\r'
                        Just c -> c
                        Nothing -> 'r'
                else 
                    Maybe.withDefault 'r' (Array.get 0 a))
         |> map Char
         |> located

parseString : Parser (Located Expression)
parseString = succeed String
            |. token "\""
            |= loop [] (\revChunks->
                oneOf 
                    [ succeed (\chunk -> Loop (chunk::revChunks))
                        |. token "\\"
                        |= oneOf
                            [ map (\_->"\n") (token "n")
                            , map (\_->"\t") (token "t")
                            , map (\_->"\r") (token "r")
                            -- , map (\_->"\"") (token "\"")
                            , chompIf (\_->True) |> getChompedString
                            ]
                    , token "\""
                        |> map (\_->Done (String.join "" (List.reverse revChunks)))
                    , chompWhile (\c->c/='"'&&c/='\\')
                        |> getChompedString
                        |> map (\chunk->Loop(chunk::revChunks))
                    ]
            ) |> located

literal : Parser (Located Expression)
literal = oneOf [parseIdent, parseType, parseBool, parseNumber, parseChar, parseString]

isSymbol : Char -> Bool
isSymbol s = case s of
    '+' -> True
    '-' -> True
    '/' -> True
    '*' -> True
    '^' -> True
    '%' -> True
    '?' -> True
    ':' -> True
    '=' -> True
    '>' -> True
    '<' -> True
    '!' -> True
    '&' -> True
    '|' -> True
    _ -> False

ws : Parser ()
ws = chompWhile (\c -> c == ' ' || c == '\n' || c == '\r' || c == '\t') |> getChompedString |> map (\_->())

compoundExpr : Located Expression -> Parser (Located Expression)
compoundExpr lit = loop lit (\left 
            -> succeed identity
            |= oneOf 
                [ chompIf isSymbol 
                    |. chompWhile isSymbol 
                    |> getChompedString 
                    |> andThen (\op-> succeed (Infix op left) |= expression |> located)
                    |> map Loop
                , parenthetical expression
                    |> map (Call lit)
                    |> located
                    |> map Loop
                , succeed left
                    |> map Done
                ]
            |. ws
    )

parenthetical : Parser a -> Parser a
parenthetical p = succeed identity |. token "(" |= p |. token ")"

expression : Parser (Located Expression)
expression = succeed identity
          |. ws
          |= oneOf [parenthetical (lazy (\_->expression)), literal] 
          |. ws
          |> andThen compoundExpr