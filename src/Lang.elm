module Lang exposing (..)

import Parser exposing (..)
import Set
import Array

type Expression = Ident String
                | Bool Bool
                | Number Float
                | Char Char
                | String String
                | Infix String (Located Expression) (Located Expression)
                | Prefix String (Located Expression)
                | Call (Located Expression) (Located Expression)
                | Tuple (List (Located Expression))
                | Unit

type Statement = Declaration (Located TypeLiteral) String (Located Expression)
               | TypeDefinition String (Located TypeLiteral)

type TypeLiteral = TypeIdent String
                 | TypeInfix String (Located TypeLiteral) (Located TypeLiteral)
                 | TypePrefix String (Located TypeLiteral)

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

parseIdentString : Parser String
parseIdentString = variable
    { start = Char.isLower
    , inner = \c -> Char.isAlphaNum c || c == '_'
    , reserved = keywords
    }

parseIdent : Parser (Located Expression)
parseIdent = map Ident parseIdentString |> located

parseTypeString : Parser String
parseTypeString = variable
    { start = Char.isUpper
    , inner = \c -> Char.isAlphaNum c || c == '_'
    , reserved = keywords
    }

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

parseTuple : Parser (Located Expression)
parseTuple = succeed Tuple
          |= sequence
            { start = "("
            , item = expression
            , separator = ","
            , end = ")"
            , spaces = ws
            , trailing = Forbidden
            }
          |> located
          |> map (\expr->
            case expr of
              { value } -> 
                case value of
                  Tuple [x] -> x
                  Tuple [] -> { expr | value = Unit}
                  _ -> expr)

literal : Parser (Located Expression)
literal = oneOf [parseIdent, parseBool, parseNumber, parseChar, parseString, parseTuple]

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
                , parseTuple
                    |> map (Call lit)
                    |> located
                    |> map Loop
                , succeed left
                    |> map Done
                ]
            |. ws
    )

expression : Parser (Located Expression)
expression = succeed identity
          |. ws
          |= lazy (\_->literal)
          |. ws
          |> andThen compoundExpr

parseDeclaration : Parser (Located Statement)
parseDeclaration = succeed Declaration
                |= parseType
                |= parseIdentString
                |. ws
                |. token "="
                |. ws
                |= expression
                |> located

parseTypeDef : Parser (Located Statement)
parseTypeDef = succeed TypeDefinition
            |. backtrackable (keyword "typedef")
            |. ws
            |= parseTypeString
            |. ws
            |= parseType
            |> located


parseTypeName : Parser (Located TypeLiteral)
parseTypeName = map TypeIdent parseTypeString |> located

typeLit : Parser (Located TypeLiteral)
typeLit = oneOf [parseTypeName]

compoundType lit = loop lit (\left
        -> succeed identity
        |= oneOf 
            [ chompIf isSymbol
                |. chompWhile isSymbol
                |> getChompedString
                |> andThen (\op->succeed (TypeInfix op left) |= parseType |> located)
                |> map Loop
            , succeed left
                |> map Done
            ])
        |. ws

parseType = succeed identity
         |. ws
         |= typeLit
         |. ws
         |> andThen compoundType

parse : Parser (List (Located Statement))
parse = sequence
        { start = ""
        , item = oneOf [parseDeclaration, parseTypeDef]
        , separator = ";"
        , end = ""
        , spaces = ws
        , trailing = Mandatory
        }