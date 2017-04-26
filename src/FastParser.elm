module FastParser exposing (parse)

import List
import Char

import String exposing (fromChar)
import Set exposing (Set)

import Parser exposing (..)
import Parser.LanguageKit exposing (..)

--==============================================================================
--= HELPERS
--==============================================================================

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

---

optional : Parser a -> a -> Parser a
optional p default =
  oneOf
    [ p
    , succeed default
    ]

sepByGeneral
  : (sep -> a -> b) -> sep -> Parser sep -> Count -> Parser a -> Parser (List b)
sepByGeneral combiner defaultSeparator separator count parser =
  let
    optionalSeparatorThenParser =
      delayedCommitMap combiner (optional separator defaultSeparator) parser
    separatorThenParser =
      delayedCommitMap combiner separator parser
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
                |= optionalSeparatorThenParser
                |= repeat (AtLeast (n - 1)) separatorThenParser
            ] ++ otherOptions
      Exactly n ->
        succeed (\head tail -> head :: tail)
          |= optionalSeparatorThenParser
          |= repeat (Exactly (n - 1)) separatorThenParser

--------------------------------------------------------------------------------
-- Whitespace
--------------------------------------------------------------------------------

type alias WS = String

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

---

blank : Parser WS
blank =
  keep (Exactly 1) isSpace

blanks : Parser WS
blanks =
  keep zeroOrMore isSpace

blanks1 : Parser WS
blanks1 =
  keep oneOrMore isSpace

sepByBlanks : Count -> Parser a -> Parser (List a)
sepByBlanks = sepBy spaces1

blankMap : (WS -> a -> b) -> Parser a -> Parser b
blankMap combiner p =
  delayedCommitMap combiner blanks p

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

---

openBlankBlock : String -> Parser WS
openBlankBlock openSymbol =
  succeed identity
    |= blanks
    |. symbol openSymbol

closeBlankBlock : String -> Parser WS
closeBlankBlock closeSymbol =
  succeed identity
    |= blanks
    |. symbol closeSymbol

blankBlock : (WS -> a -> WS -> b) -> String -> String -> Parser a -> Parser b
blankBlock combiner open close p =
    delayedCommitMap
      (\wsStart (result, wsEnd) -> combiner wsStart result wsEnd)
      (openBlankBlock open)
      ( succeed (,)
          |= p
          |= closeBlankBlock close
      )

parenBlankBlock : (WS -> a -> WS -> b) -> Parser a -> Parser b
parenBlankBlock combiner = blankBlock combiner "(" ")"

bracketBlankBlock : (WS -> a -> WS -> b) -> Parser a -> Parser b
bracketBlankBlock combiner = blankBlock combiner "[" "]"

--------------------------------------------------------------------------------
-- List Helper
--------------------------------------------------------------------------------

listLiteralInternal : String -> (List a -> a) -> Parser a -> Parser a
listLiteralInternal context combiner parser  =
  inContext context <|
    succeed combiner
      |= sepBySpaces zeroOrMore parser

multiConsInternal : String -> (List a -> a -> a) -> Parser a -> Parser a
multiConsInternal context combiner parser =
  inContext context <|
    delayedCommitMap combiner
      ( succeed identity
          |= sepBySpaces oneOrMore parser
          |. spaces
          |. symbol "|"
      )
      parser

genericList
  : { generalContext : String
    , listLiteralContext : String
    , multiConsContext : String
    , listLiteralCombiner : List a -> a
    , multiConsCombiner : List a -> a -> a
    , parser : Parser a
    }
  -> Parser a
genericList args =
  inContext args.generalContext <|
    bracketBlock <|
      oneOf
        [ multiConsInternal
            args.multiConsContext
            args.multiConsCombiner
            args.parser
        , listLiteralInternal
            args.listLiteralContext
            args.listLiteralCombiner
            args.parser
        ]

---

blankListLiteralInternal
  : String -> (WS -> List elem -> WS -> list) -> Parser elem -> Parser list
blankListLiteralInternal context combiner elem  =
  inContext context <|
    bracketBlankBlock combiner (repeat zeroOrMore elem)

blankMultiConsInternal
  :  String
  -> (WS -> List elem -> WS -> elem -> WS -> list)
  -> Parser elem
  -> Parser list
blankMultiConsInternal context combiner elem =
  inContext context <|
    bracketBlankBlock
      ( \wsStart (heads, wsBar, tail) wsEnd ->
          combiner wsStart heads wsBar tail wsEnd
      )
      ( delayedCommitMap
          ( \(heads, wsBar) tail ->
              (heads, wsBar, tail)
          )
          ( succeed (,)
              |= repeat oneOrMore elem
              |= blanks
              |. symbol "|"
          )
          elem
      )


--     delayedCommitMap (\(heads, wsBar) tail -> listCombiner heads wsBar tail)
--       ( succeed (,)
--           |= sepByGeneral elemCombiner "" blanks1 oneOrMore parser
--           |= blanks
--           |. symbol "|"
--       )
--       ( succeed elemCombiner
--           |= blanks
--           |= parser
--       )

genericBlankList
  :  { generalContext : String
     , listLiteralContext : String
     , multiConsContext : String
     , listLiteralCombiner : WS -> List elem -> WS -> list
     , multiConsCombiner : WS -> List elem -> WS -> elem -> WS -> list
     , elem : Parser elem
     }
  -> Parser list
genericBlankList args =
  inContext args.generalContext <|
    oneOf
      [ blankMultiConsInternal
          args.multiConsContext
          args.multiConsCombiner
          args.elem
      , blankListLiteralInternal
          args.listLiteralContext
          args.listLiteralCombiner
          args.elem
      ]

--==============================================================================
--= CONSTANTS
--==============================================================================

--------------------------------------------------------------------------------
-- Data Types
--------------------------------------------------------------------------------

type Constant
  = CNumber FrozenState (Maybe Range) Float
  | CString String
  | CBool Bool

--------------------------------------------------------------------------------
-- Numbers
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
    try <|
      succeed (\s n -> s * n)
        |. spaces
        |= sign
        |= float

number : Parser Constant
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
      succeed (\val frozen range -> CNumber frozen range val)
        |= try numParser
        |= frozenAnnotation
        |= rangeAnnotation

--------------------------------------------------------------------------------
-- Strings
--------------------------------------------------------------------------------

string : Parser Constant
string =
  let
    stringHelper quoteChar =
      let
        quoteString = fromChar quoteChar
      in
        succeed CString
          |. symbol quoteString
          |= keep zeroOrMore (\c -> c /= quoteChar)
          |. symbol quoteString
  in
    inContext "string" <|
      delayedCommit spaces <|
        oneOf <| List.map stringHelper ['\'', '"']

--------------------------------------------------------------------------------
-- Bools
--------------------------------------------------------------------------------

bool : Parser Constant
bool =
  delayedCommit spaces <|
    oneOf
      [ succeed (CBool True)
          |. keyword "true"
      , succeed (CBool False)
          |. keyword "false"
      ]

--------------------------------------------------------------------------------
-- General Constants
--------------------------------------------------------------------------------

constant : Parser Constant
constant =
  oneOf
    [ number
    , string
    , bool
    ]

--==============================================================================
--= IDENTIFIERS
--==============================================================================

validIdentifierFirstChar : Char -> Bool
validIdentifierFirstChar c =
  Char.isLower c || Char.isUpper c || c == '_'

validIdentifierRestChar : Char -> Bool
validIdentifierRestChar c =
  Char.isLower c || Char.isUpper c || Char.isDigit c || c == '_' || c == '\''

keywords : Set String
keywords =
  Set.fromList
    [ "true"
    , "false"
    , "pi"
    , "cos"
    , "sin"
    , "arccos"
    , "arcsin"
    , "floor"
    , "ceiling"
    , "round"
    , "toString"
    , "sqrt"
    , "explode"
    , "mod"
    , "pow"
    , "arctan2"
    , "if"
    , "case"
    , "typecase"
    , "let"
    , "letrec"
    , "def"
    , "defrec"
    , "typ"
    ]

-- identifierString : Parser Identifier
-- identifierString =
--   delayedCommit spaces <|
--     variable validIdentifierFirstChar validIdentifierRestChar keywords

identifierString : Parser Identifier
identifierString =
  variable validIdentifierFirstChar validIdentifierRestChar keywords

--==============================================================================
--= PATTERNS
--==============================================================================

--------------------------------------------------------------------------------
-- Data Types
--------------------------------------------------------------------------------

type alias Identifier = String

type Pattern
  = PIdentifier WS Identifier
  | PConstant WS Constant
  | PList WS (List Pattern) WS (Maybe Pattern) WS
  | PAs Identifier Pattern

-- type Pattern
--   = PIdentifier WS Identifier
--   | PConstant WS Constant
--   | PList WS (List Pattern) WS (Maybe Pattern) WS
--   | PAs WS Identifier WS Pattern

identifier : Parser Pattern
identifier =
  blankMap PIdentifier identifierString

--------------------------------------------------------------------------------
-- Constant Pattern
--------------------------------------------------------------------------------

constantPattern : Parser Pattern
constantPattern =
  blankMap PConstant constant

--------------------------------------------------------------------------------
-- Pattern Lists
--------------------------------------------------------------------------------

patternList : Parser Pattern
patternList =
  lazy <| \_ ->
    genericBlankList
      { generalContext =
          "pattern list"
      , listLiteralContext =
          "pattern list literal"
      , multiConsContext =
          "pattern multi cons literal"
      , listLiteralCombiner =
          ( \wsStart heads wsEnd ->
              PList wsStart heads "" Nothing wsEnd
          )
      , multiConsCombiner =
          ( \wsStart heads wsBar tail wsEnd ->
              PList wsStart heads wsBar (Just tail) wsEnd
          )
      , elem =
          pattern
      }

--------------------------------------------------------------------------------
-- As-Patterns (@-Patterns)
--------------------------------------------------------------------------------

asPattern : Parser Pattern
asPattern =
  inContext "as pattern" <|
    lazy <| \_ ->
      delayedCommitMap
      (\name pat -> PAs name pat)
      ( succeed identity
          |= identifierString
          |. spaces
          |. symbol "@"
      )
      pattern

--------------------------------------------------------------------------------
-- General Patterns
--------------------------------------------------------------------------------

pattern : Parser Pattern
pattern =
  inContext "pattern" <|
    oneOf
      [ lazy (\_ -> patternList)
      , lazy (\_ -> asPattern)
      , constantPattern
      , identifier
      ]

--==============================================================================
--= TYPES
--==============================================================================

--------------------------------------------------------------------------------
-- Data Types
--------------------------------------------------------------------------------

type Type
  = TNull
  | TNum
  | TBool
  | TString
  | TAlias Identifier
  | TFunction (List Type)
  | TList Type
  -- heads / tail
  | TTuple (List Type) (Maybe Type)
  | TForall (List Identifier) Type
  | TUnion (List Type)
  | TWildcard

--------------------------------------------------------------------------------
-- Base Types
--------------------------------------------------------------------------------

nullType : Parser Type
nullType =
  inContext "null type" <|
    delayedCommit spaces <|
      succeed TNull
        |. keyword "Null"

numType : Parser Type
numType =
  inContext "number type" <|
    delayedCommit spaces <|
      succeed TNum
        |. keyword "Num"

boolType : Parser Type
boolType =
  inContext "bool type" <|
    delayedCommit spaces <|
      succeed TBool
        |. keyword "Bool"

stringType : Parser Type
stringType =
  inContext "string type" <|
    delayedCommit spaces <|
      succeed TString
        |. keyword "String"

--------------------------------------------------------------------------------
-- Aliased Types
--------------------------------------------------------------------------------

aliasType : Parser Type
aliasType =
  inContext "alias type" <|
    map TAlias identifierString

--------------------------------------------------------------------------------
-- Function Type
--------------------------------------------------------------------------------

functionType : Parser Type
functionType =
  inContext "function type" <|
    lazy <| \_ ->
      parenBlock <|
        succeed TFunction
          |. keyword "->"
          |. spaces1
          |= sepBySpaces oneOrMore typ

--------------------------------------------------------------------------------
-- List Type
--------------------------------------------------------------------------------

listType : Parser Type
listType =
  inContext "list type" <|
    lazy <| \_ ->
      parenBlock <|
        succeed TList
          |. keyword "List"
          |. spaces1
          |= typ

--------------------------------------------------------------------------------
-- Tuple Type
--------------------------------------------------------------------------------

tupleType : Parser Type
tupleType =
  lazy <| \_ ->
    genericList
      { generalContext = "tuple type"
      , listLiteralContext = "tuple type list literal"
      , multiConsContext = "tuple type multi cons literal"
      , listLiteralCombiner = (\heads -> TTuple heads Nothing)
      , multiConsCombiner = (\heads tail -> TTuple heads (Just tail))
      , parser = typ
      }

--------------------------------------------------------------------------------
-- Forall Type
--------------------------------------------------------------------------------

forallType : Parser Type
forallType =
  let
    quantifiers =
      oneOf
        [ map singleton identifierString
        , parenBlock <| sepBySpaces oneOrMore identifierString
        ]
  in
    inContext "forall type" <|
      lazy <| \_ ->
        parenBlock <|
          succeed TForall
            |. keyword "forall"
            |= quantifiers
            |= typ

--------------------------------------------------------------------------------
-- Union Type
--------------------------------------------------------------------------------

unionType : Parser Type
unionType =
  inContext "union type" <|
    lazy <| \_ ->
      parenBlock <|
        succeed TFunction
          |. keyword "union"
          |. spaces1
          |= sepBySpaces oneOrMore typ

--unionType : Parser Type
--unionType =
--  let
--    separator =
--      succeed identity
--        |. spaces
--        |. symbol "|"
--  in
--    inContext "union type" <|
--      lazy <| \_ ->
--        succeed TUnion
--          |= sepBy separator oneOrMore typ

--------------------------------------------------------------------------------
-- Wildcard Type
--------------------------------------------------------------------------------

wildcardType : Parser Type
wildcardType =
  inContext "wildcard type" <|
    delayedCommit spaces <|
      succeed TWildcard
        |. symbol "_"

--------------------------------------------------------------------------------
-- General Types
--------------------------------------------------------------------------------

typ : Parser Type
typ =
  inContext "type" <|
    oneOf
      [ nullType
      , numType
      , boolType
      , stringType
      , wildcardType
      , lazy (\_ -> functionType)
      , lazy (\_ -> listType)
      , lazy (\_ -> tupleType)
      , lazy (\_ -> forallType)
      , lazy (\_ -> unionType)
      , aliasType
      ]

--==============================================================================
--= EXPRESSIONS
--==============================================================================

--------------------------------------------------------------------------------
-- Data Types
--------------------------------------------------------------------------------

type FrozenState
  = Frozen
  | Thawed
  | Restricted

type Range
  = Range Float Float

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

type CaseBranch
  = CaseBranch Pattern Exp

type TypeCaseBranch
  = TypeCaseBranch Type Exp

type LetKind
  = Let | Def

type Exp
  = EIdentifier Identifier
  | EConstant Constant
  | EOp0 Op0
  | EOp1 Op1 Exp
  | EOp2 Op2 Exp Exp
  | EIf Exp Exp Exp
  -- heads / tail
  | EList (List Exp) (Maybe Exp)
  | ECase Exp (List CaseBranch)
  | ETypeCase Pattern (List TypeCaseBranch)
  | EFunction (List Pattern) Exp
  | EFunctionApplication Exp (List Exp)
  -- type of let / recursive / pattern / value / inner
  | ELet LetKind Bool Pattern Exp Exp
  | EOption String String
  | ETypeDeclaration Pattern Type Exp
  | ETypeAnnotation Exp Type

--------------------------------------------------------------------------------
-- Identifier Expressions
--------------------------------------------------------------------------------

identifierExpression : Parser Exp
identifierExpression =
  map EIdentifier identifierString

--------------------------------------------------------------------------------
-- Constant Expressions
--------------------------------------------------------------------------------

constantExpression : Parser Exp
constantExpression =
  map EConstant constant

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
      delayedCommitMap
      (\op e -> EOp1 op e)
      ( succeed identity
          |= op
          |. spaces1
      )
      exp

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
      delayedCommitMap
      (\op (e1, e2) -> EOp2 op e1 e2)
      ( succeed identity
          |= op
          |. spaces1
      )
      ( succeed (\e1 e2 -> (e1, e2))
          |= exp
          |. spaces1
          |= exp
      )

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
-- TODO cleanup

-- listLiteralInternal : Parser Exp -> Parser Exp
-- listLiteralInternal elemParser =
--   inContext "list literal" <|
--     map (\heads -> EList heads Nothing) <|
--       sepBySpaces zeroOrMore elemParser
--
-- multiConsInternal : Parser Exp -> Parser Exp
-- multiConsInternal elemParser =
--   inContext "multi cons literal" <|
--     delayedCommitMap
--       (\heads tail -> EList heads (Just tail))
--       ( succeed identity
--           |= sepBySpaces oneOrMore elemParser
--           |. spaces
--           |. symbol "|"
--       )
--       elemParser

list : Parser Exp
list =
  lazy <| \_ ->
    genericList
      { generalContext = "list"
      , listLiteralContext = "list literal"
      , multiConsContext = "multi cons literal"
      , listLiteralCombiner = (\heads -> EList heads Nothing)
      , multiConsCombiner = (\heads tail -> EList heads (Just tail))
      , parser = exp
      }

--list : Parser Exp -> Parser Exp
--list elemParser =
--  inContext "list" <|
--    lazy <| \_ ->
--      bracketBlock <|
--        oneOf
--          [ multiConsInternal elemParser
--          , listLiteralInternal elemParser
--          ]

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
            succeed CaseBranch
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
-- Type Case Expressions
--------------------------------------------------------------------------------

typeCaseExpression : Parser Exp
typeCaseExpression =
  let
    typeCasePath =
      inContext "type case expression path" <|
        lazy <| \_ ->
          parenBlock <|
            succeed TypeCaseBranch
              |= typ
              |. spaces1
              |= exp
  in
    inContext "type case expression" <|
      lazy <| \_ ->
        parenBlock <|
          succeed ETypeCase
            |. keyword "typecase"
            |. spaces1
            |= pattern
            |= sepBySpaces oneOrMore typeCasePath

--------------------------------------------------------------------------------
-- Functions
--------------------------------------------------------------------------------

function : Parser Exp
function =
  let
    parameters =
      oneOf
        [ map singleton pattern
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
-- Let Bindings
--------------------------------------------------------------------------------

recursiveLetBinding : Parser Exp
recursiveLetBinding =
  inContext "recursive let binding" <|
    parenBlock <|
      succeed (ELet Let True)
        |. keyword "letrec"
        |. spaces1
        |= identifier
        |. spaces1
        |= function
        |. spaces1
        |= exp

simpleLetBinding : Parser Exp
simpleLetBinding =
  inContext "non-recursive let binding" <|
    parenBlock <|
      succeed (ELet Let False)
        |. keyword "let"
        |. spaces1
        |= pattern
        |. spaces1
        |= exp
        |. spaces1
        |= exp

recursiveDefBinding : Parser Exp
recursiveDefBinding =
  inContext "recursive def binding" <|
    delayedCommit (openBlock "(") <|
      succeed (ELet Def True)
        |. keyword "defrec"
        |. spaces1
        |= identifier
        |. spaces1
        |= function
        |. closeBlock ")"
        |. spaces1
        |= exp

simpleDefBinding : Parser Exp
simpleDefBinding =
  inContext "non-recursive def binding" <|
    delayedCommit (openBlock "(") <|
      succeed (ELet Def False)
        |. keyword "def"
        |. spaces1
        |= pattern
        |. spaces1
        |= exp
        |. closeBlock ")"
        |. spaces1
        |= exp

letBinding : Parser Exp
letBinding =
  inContext "let binding" <|
    lazy <| \_ ->
      oneOf
        [ recursiveLetBinding
        , simpleLetBinding
        , recursiveDefBinding
        , simpleDefBinding
        ]

--------------------------------------------------------------------------------
-- Options
--------------------------------------------------------------------------------

-- TODO fix options (and comments!)

validOptionChar : Char -> Bool
validOptionChar c =
  Char.isLower c || Char.isUpper c || Char.isDigit c

option : Parser Exp
option =
  succeed EOption
    |. symbol "#"
    |= keep oneOrMore validOptionChar
    |= keep oneOrMore validOptionChar
    |. ignoreUntil "\n"

--------------------------------------------------------------------------------
-- Type Declarations
--------------------------------------------------------------------------------

typeDeclaration : Parser Exp
typeDeclaration =
  inContext "type declaration" <|
    lazy <| \_ ->
      delayedCommit (openBlock "(") <|
        succeed ETypeDeclaration
          |. keyword "typ"
          |. spaces1
          |= pattern
          |. spaces1
          |= typ
          |. closeBlock ")"
          |. spaces1
          |= exp

--------------------------------------------------------------------------------
-- Type Annotation
--------------------------------------------------------------------------------

typeAnnotation : Parser Exp
typeAnnotation =
  inContext "type annotation" <|
    lazy <| \_ ->
      parenBlock <|
        delayedCommitMap
        (\e t -> ETypeAnnotation e t)
        ( succeed identity
            |= exp
            |. spaces
            |. symbol ":"
        )
        typ


--------------------------------------------------------------------------------
-- General Expressions
--------------------------------------------------------------------------------

exp : Parser Exp
exp =
  inContext "expression" <|
    oneOf
      [ constantExpression
      , lazy (\_ -> operator)
      , lazy (\_ -> conditional)
      , lazy (\_ -> letBinding)
      , lazy (\_ -> caseExpression)
      , lazy (\_ -> typeCaseExpression)
      , lazy (\_ -> typeDeclaration)
      , lazy (\_ -> typeAnnotation)
      , lazy (\_ -> list)
      , lazy (\_ -> function)
      , lazy (\_ -> functionApplication)
      , identifierExpression
      ]

--==============================================================================
--= EXPORTS
--==============================================================================

parse : String -> Result Error Exp
parse = run exp
