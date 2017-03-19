module FastParser exposing (test)

import Parser exposing (..)
import Parser.LanguageKit exposing (..)
import Debug

--------------------------------------------------------------------------------
-- Parser Combinators
--------------------------------------------------------------------------------

try : Parser a -> Parser a
try parser =
  delayedCommitMap always parser (succeed ())

--------------------------------------------------------------------------------
-- Data Types
--------------------------------------------------------------------------------

type FrozenState = Frozen | Thawed | Restricted
type Range = Range Float Float

type Op0
  = Pi

type Op1
  = Cos
  | Sin
  | Arccos
  | Arcsin
  | Floor
  | Ceiling
  | Round
  | ToString
  | Sqrt
  | Explode

type Op2
  = Plus
  | Minus
  | Multiply
  | Divide
  | LessThan
  | Equal
  | Mod
  | Pow
  | Arctan2

type Exp
  = ENumber FrozenState (Maybe Range) Float
  | EString String
  | EBool Bool
  | EOp0 Op0
  | EOp1 Op1 Exp
  | EOp2 Op2 Exp Exp
  | EIf Exp Exp Exp
  -- heads / tail
  | EList (List Exp) (Maybe Exp)

--------------------------------------------------------------------------------
-- Whitespace
--------------------------------------------------------------------------------

isSpace : Char -> Bool
isSpace c =
  c == ' ' || c == '\n'

space : Parser ()
space =
  ignore (Exactly 1) isSpace

spaces : Parser ()
spaces =
  whitespace
    { allowTabs = False
    , lineComment = LineComment ";"
    , multiComment = NoMultiComment
    }

spaces1 : Parser ()
spaces1 =
  succeed identity
    |= space
    |. spaces

--------------------------------------------------------------------------------
-- Constant Expressions
--------------------------------------------------------------------------------

numParser : Parser Float
numParser =
  let
    sign =
      oneOf
        [ succeed (-1)
            |. symbol "-"
        , succeed 1
        ]
  in
    succeed (\s n -> s * n)
      |= sign
      |= float

number : Parser Exp
number =
  let
    frozenAnnotation =
      inContext "frozen annotation" <|
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
      inContext "range annotation" <|
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
    inContext "number" <|
      succeed (\val frozen range -> ENumber frozen range val)
        |= numParser
        |= frozenAnnotation
        |= rangeAnnotation

string : Parser Exp
string =
  inContext "string" <|
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

--------------------------------------------------------------------------------
-- Primitive Operators
--------------------------------------------------------------------------------

op0 : Parser Exp
op0 =
  inContext "nullary operator" <|
    succeed (EOp0 Pi)
      |. keyword "pi"

op1 : Parser Exp
op1 =
  let
    op =
      oneOf
        [ succeed Cos
          |. keyword "cos"
        , succeed Sin
          |. keyword "sin"
        , succeed Arccos
          |. keyword "arccos"
        , succeed Arcsin
          |. keyword "arcsin"
        , succeed Floor
          |. keyword "floor"
        , succeed Ceiling
          |. keyword "ceiling"
        , succeed Round
          |. keyword "round"
        , succeed ToString
          |. keyword "toString"
        , succeed Sqrt
          |. keyword "sqrt"
        , succeed Explode
          |. keyword "explode"
        ]
  in
    inContext "unary operator" <|
      succeed EOp1
        |= op
        |. spaces1
        |= exp

op2 : Parser Exp
op2 =
  let
    op =
      oneOf
        [ succeed Plus
          |. keyword "+"
        , succeed Minus
          |. keyword "-"
        , succeed Multiply
          |. keyword "*"
        , succeed Divide
          |. keyword "/"
        , succeed LessThan
          |. keyword "<"
        , succeed Equal
          |. keyword "="
        , succeed Mod
          |. keyword "mod"
        , succeed Pow
          |. keyword "pow"
        , succeed Arctan2
          |. keyword "arctan2"
        ]
  in
    inContext "binary operator" <|
      succeed EOp2
        |= op
        |. spaces1
        |= exp
        |. spaces1
        |= exp

operator : Parser Exp
operator =
  inContext "operator" <|
    lazy <| \_ ->
      let
        inner =
          oneOf
            [ op0
            , op1
            , op2
            ]
      in
        delayedCommit (symbol "(") <|
          succeed identity
            |= inner
            |. symbol ")"

--------------------------------------------------------------------------------
-- Conditionals
--------------------------------------------------------------------------------

conditional : Parser Exp
conditional =
  inContext "conditional" <|
    delayedCommit (symbol "(") <|
      lazy <| \_ ->
        succeed EIf
          |. keyword "if"
          |. spaces1
          |= exp
          |. spaces1
          |= exp
          |. spaces1
          |= exp
          |. symbol ")"

--------------------------------------------------------------------------------
-- Lists
--------------------------------------------------------------------------------

listLiteral : Parser Exp
listLiteral =
  inContext "list literal" <|
    try <|
      succeed (\heads -> EList heads Nothing)
        |. symbol "["
        |= repeat zeroOrMore exp
        |. spaces
        |. symbol "]"

multiCons : Parser Exp
multiCons =
  inContext "multi cons literal" <|
    delayedCommitMap
      (\heads tail -> EList heads (Just tail))
      ( succeed identity
          |. symbol "["
          |= repeat oneOrMore exp
          |. spaces
          |. symbol "|"
      )
      ( succeed identity
          |= exp
          |. spaces
          |. symbol "]"
      )

list : Parser Exp
list =
  inContext "list" <|
    lazy <| \_ ->
      oneOf
        [ listLiteral
        , multiCons
        ]

--------------------------------------------------------------------------------
-- General Expression
--------------------------------------------------------------------------------

exp : Parser Exp
exp =
  inContext "expression" <|
    delayedCommit spaces <|
      oneOf
        [ constant
        , lazy (\_ -> operator)
        , lazy (\_ -> conditional)
        , lazy (\_ -> list)
        ]

--------------------------------------------------------------------------------
-- Tester
--------------------------------------------------------------------------------

testProgram = "[ (if (= (+ 2 4) (* 2 3)) 2 3) 2 3    4  \n 5 6 | 7]"

test _ = Debug.log (toString (parse testProgram)) 0

parse = run exp
