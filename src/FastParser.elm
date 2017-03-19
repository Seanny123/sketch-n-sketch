module FastParser exposing (test)

import Parser exposing (..)
import Debug

type FrozenState = Frozen | Thawed | Restricted
type Range = Range Float Float

type Exp
  = ENumber FrozenState (Maybe Range) Float
  | EString String
  | EBool Bool

numParser : Parser Float
numParser =
  let
    negative =
      oneOf
        [ succeed (-1)
            |. symbol "-"
        , succeed 1
        ]
  in
    succeed (\sign n -> sign * n)
      |= negative
      |= float

number : Parser Exp
number =
  let
    frozenAnnotation =
      oneOf
        [ succeed Frozen
            |. symbol "!"
        , succeed Thawed
            |. symbol "?"
        , succeed Restricted
            |. symbol "~"
        , succeed Thawed -- default
        ]
    rangeAnnotation =
      oneOf
        [ map Just <|
            succeed Range
              |. symbol "{"
              |= numParser
              |. symbol "-"
              |= numParser
              |. symbol "}"
        , succeed Nothing
        ]
  in
    succeed (\val frozen range -> ENumber frozen range val)
      |= numParser
      |= frozenAnnotation
      |= rangeAnnotation

string : Parser Exp
string =
  succeed EString
    |. symbol "'"
    |= keep zeroOrMore (\c -> c /= '\'')
    |. symbol "'"

bool : Parser Exp
bool =
  oneOf
    [ succeed (EBool True)
        |. keyword "true"
    , succeed (EBool False)
        |. keyword "false"
    ]

constant : Parser Exp
constant =
  oneOf
    [ number
    , string
    , bool
    ]

testProgram = "3.14!{-10.1--3.45}"

test _ = Debug.log (toString (parse testProgram)) 0

parse = run constant
