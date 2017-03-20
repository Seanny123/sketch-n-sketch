module FastParser exposing (parse)

import Char

import Parser exposing (..)
import Parser.LanguageKit exposing (..)

--------------------------------------------------------------------------------
-- Helper Functions
--------------------------------------------------------------------------------

singleton : a -> List a
singleton x = [x]

--------------------------------------------------------------------------------
-- Parser Combinators
--------------------------------------------------------------------------------

try : Parser a -> Parser a
try parser =
  delayedCommitMap always parser (succeed ())

sepBy : Parser sep -> Count -> Parser a -> Parser (List a)
sepBy separator count parser =
  let
    separatorThenParser =
      delayedCommit separator parser
  in
    case count of
      AtLeast n ->
        let
          otherOptions =
            if n == 0 then
              [ succeed [] ]
            else
              []
        in
          oneOf <|
            [ succeed (\head tail -> head :: tail)
                |= parser
                |= repeat (AtLeast (n - 1)) separatorThenParser
            ] ++ otherOptions
      Exactly n ->
        succeed (\head tail -> head :: tail)
          |= parser
          |= repeat (Exactly (n - 1)) separatorThenParser

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

type CasePath =
  -- pattern / value
  CasePath Exp Exp

type Exp
  = EIdentifier String
  | ENumber FrozenState (Maybe Range) Float
  | EString String
  | EBool Bool
  | EOp0 Op0
  | EOp1 Op1 Exp
  | EOp2 Op2 Exp Exp
  | EIf Exp Exp Exp
  -- heads / tail
  | EList (List Exp) (Maybe Exp)
  | ECase Exp (List CasePath)
  | EFunction (List Exp) Exp
  | EFunctionApplication Exp (List Exp)

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

sepBySpaces : Count -> Parser a -> Parser (List a)
sepBySpaces = sepBy spaces1

--------------------------------------------------------------------------------
-- Block Helper
--------------------------------------------------------------------------------

openBlock : String -> Parser ()
openBlock openSymbol =
  succeed identity
    |. spaces
    |= symbol openSymbol
    |. spaces

closeBlock : String -> Parser ()
closeBlock closeSymbol =
  succeed identity
    |. spaces
    |= symbol closeSymbol

block : String -> String -> Parser a -> Parser a
block open close p =
  delayedCommit (openBlock open) <|
    succeed identity
      |= p
      |. closeBlock close

parenBlock : Parser a -> Parser a
parenBlock = block "(" ")"

bracketBlock : Parser a -> Parser a
bracketBlock = block "[" "]"

--------------------------------------------------------------------------------
-- Identifier
--------------------------------------------------------------------------------

validIdentifierChar : Char -> Bool
validIdentifierChar c = Char.isLower c || Char.isUpper c

identifier : Parser Exp
identifier =
  succeed EIdentifier
    |. spaces
    |= keep oneOrMore validIdentifierChar

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
    delayedCommit spaces <|
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
    delayedCommit spaces <|
      succeed EString
        |. symbol "'"
        |= keep zeroOrMore (\c -> c /= '\'')
        |. symbol "'"

bool : Parser Exp
bool =
  delayedCommit spaces <|
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
    delayedCommit spaces <|
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
      delayedCommit spaces <|
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
      delayedCommit spaces <|
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
        parenBlock inner

--------------------------------------------------------------------------------
-- Conditionals
--------------------------------------------------------------------------------

conditional : Parser Exp
conditional =
  inContext "conditional" <|
      lazy <| \_ ->
        parenBlock <|
          succeed EIf
            |. keyword "if"
            |. spaces1
            |= exp
            |. spaces1
            |= exp
            |. spaces1
            |= exp

--------------------------------------------------------------------------------
-- Lists
--------------------------------------------------------------------------------

listLiteralInternal : Parser Exp -> Parser Exp
listLiteralInternal elemParser =
  inContext "list literal" <|
    map (\heads -> EList heads Nothing) <|
      sepBySpaces zeroOrMore elemParser

multiConsInternal : Parser Exp -> Parser Exp
multiConsInternal elemParser =
  inContext "multi cons literal" <|
    delayedCommitMap
      (\heads tail -> EList heads (Just tail))
      ( succeed identity
          |= sepBySpaces oneOrMore elemParser
          |. spaces
          |. symbol "|"
      )
      elemParser

list : Parser Exp -> Parser Exp
list elemParser =
  inContext "list" <|
    lazy <| \_ ->
      bracketBlock <|
        oneOf
          [ multiConsInternal elemParser
          , listLiteralInternal elemParser
          ]

--------------------------------------------------------------------------------
-- Patterns
--------------------------------------------------------------------------------

pattern : Parser Exp
pattern =
  inContext "pattern" <|
    oneOf
      [ identifier
      , constant
      , lazy (\_ -> list pattern)
      ]

--------------------------------------------------------------------------------
-- Case Expressions
--------------------------------------------------------------------------------

caseExpression : Parser Exp
caseExpression =
  let
    casePath =
      inContext "case expression path" <|
        lazy <| \_ ->
          parenBlock <|
            succeed CasePath
              |= pattern
              |. spaces1
              |= exp
  in
    inContext "case expression" <|
      lazy <| \_ ->
        parenBlock <|
          succeed ECase
            |. keyword "case"
            |. spaces1
            |= exp
            |= sepBySpaces oneOrMore casePath

--------------------------------------------------------------------------------
-- Functions
--------------------------------------------------------------------------------

function : Parser Exp
function =
  let
    parameters =
      oneOf
        [ map singleton pattern
          -- TODO determine if should be zeroOrMore or oneOrMore
        , parenBlock <| sepBySpaces oneOrMore pattern
        ]
  in
    inContext "function" <|
      lazy <| \_ ->
        parenBlock <|
          succeed EFunction
            |. symbol "\\"
            |= parameters
            |= exp

--------------------------------------------------------------------------------
-- Function Applications
--------------------------------------------------------------------------------

functionApplication : Parser Exp
functionApplication =
  inContext "function application" <|
    lazy <| \_ ->
      parenBlock <|
        succeed EFunctionApplication
          |= exp
          |. spaces1
          |= sepBySpaces oneOrMore exp

--------------------------------------------------------------------------------
-- General Expression
--------------------------------------------------------------------------------

exp : Parser Exp
exp =
  inContext "expression" <|
    oneOf
      [ constant
      , lazy (\_ -> operator)
      , lazy (\_ -> conditional)
      , lazy (\_ -> list exp)
      , lazy (\_ -> caseExpression)
      , lazy (\_ -> function)
      , lazy (\_ -> functionApplication)
      , identifier
      ]

--------------------------------------------------------------------------------
-- Exports
--------------------------------------------------------------------------------

parse = run exp
