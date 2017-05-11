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
    ( \wsStart (result, wsEnd) ->
        combiner wsStart result wsEnd
    )
    ( openBlankBlock open )
    ( succeed (,)
        |= p
        |= closeBlankBlock close
    )

parenBlankBlock : (WS -> a -> WS -> b) -> Parser a -> Parser b
parenBlankBlock combiner = blankBlock combiner "(" ")"

bracketBlankBlock : (WS -> a -> WS -> b) -> Parser a -> Parser b
bracketBlankBlock combiner = blankBlock combiner "[" "]"

blockIgnoreWS : String -> String -> Parser a -> Parser a
blockIgnoreWS = blankBlock (\wsStart x wsEnd -> x)

parenBlockIgnoreWS : Parser a -> Parser a
parenBlockIgnoreWS = block "(" ")"

bracketBlockIgnoreWS : Parser a -> Parser a
bracketBlockIgnoreWS = block "[" "]"

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
      oneOf <| List.map stringHelper ['\'', '"']

--------------------------------------------------------------------------------
-- Bools
--------------------------------------------------------------------------------

bool : Parser Constant
bool =
  map CBool <|
    oneOf <|
      [ map (always True) <| keyword "true"
      , map (always False) <| keyword "false"
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
  | PAs WS Identifier WS Pattern

--------------------------------------------------------------------------------
-- Identifier Pattern
--------------------------------------------------------------------------------

identifierPattern : Parser Pattern
identifierPattern =
  delayedCommitMap PIdentifier blanks identifierString

--------------------------------------------------------------------------------
-- Constant Pattern
--------------------------------------------------------------------------------

constantPattern : Parser Pattern
constantPattern =
  delayedCommitMap PConstant blanks constant

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
      ( \(wsStart, name, wsAt) pat ->
          PAs wsStart name wsAt pat
      )
      ( succeed (,,)
          |= blanks
          |= identifierString
          |= blanks
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
      , identifierPattern
      ]

--==============================================================================
--= TYPES
--==============================================================================

--------------------------------------------------------------------------------
-- Data Types
--------------------------------------------------------------------------------

type OneOrMany a
  = One a
  | Many WS (List a) WS

type Type
  = TNull WS
  | TNum WS
  | TBool WS
  | TString WS
  | TAlias WS Identifier
  | TFunction WS (List Type) WS
  | TList WS Type WS
  | TTuple WS (List Type) WS (Maybe Type) WS
  | TForall WS (OneOrMany (WS, Identifier)) Type WS
  | TUnion WS (List Type) WS
  | TWildcard WS

--------------------------------------------------------------------------------
-- Base Types
--------------------------------------------------------------------------------

baseType : String -> (WS -> Type) -> String -> Parser Type
baseType context combiner token =
  inContext context <|
    delayedCommitMap always
      (map combiner blanks)
      (keyword token)

nullType : Parser Type
nullType =
  baseType "null type" TNull "Null"

numType : Parser Type
numType =
  baseType "num type" TNum "Num"

boolType : Parser Type
boolType =
  baseType "boool type" TBool "Bool"

stringType : Parser Type
stringType =
  baseType "string type" TString "String"

--------------------------------------------------------------------------------
-- Aliased Types
--------------------------------------------------------------------------------

aliasType : Parser Type
aliasType =
  inContext "alias type" <|
    delayedCommitMap TAlias blanks identifierString

--------------------------------------------------------------------------------
-- Function Type
--------------------------------------------------------------------------------

functionType : Parser Type
functionType =
  inContext "function type" <|
    lazy <| \_ ->
      parenBlankBlock TFunction <|
        succeed identity
          |. keyword "->"
          |= repeat oneOrMore typ

--------------------------------------------------------------------------------
-- List Type
--------------------------------------------------------------------------------

listType : Parser Type
listType =
  inContext "list type" <|
    lazy <| \_ ->
      parenBlankBlock TList <|
        succeed identity
          |. keyword "List"
          |= typ

--------------------------------------------------------------------------------
-- Tuple Type
--------------------------------------------------------------------------------

tupleType : Parser Type
tupleType =
  lazy <| \_ ->
    genericBlankList
      { generalContext =
          "tuple type"
      , listLiteralContext =
          "tuple type list literal"
      , multiConsContext =
          "tuple type multi cons literal"
      , listLiteralCombiner =
          ( \wsStart heads wsEnd ->
              TTuple wsStart heads "" Nothing wsEnd
          )
      , multiConsCombiner =
          ( \wsStart heads wsBar tail wsEnd ->
              TTuple wsStart heads wsBar (Just tail) wsEnd
          )
      , elem =
          typ
      }

--------------------------------------------------------------------------------
-- Forall Type
--------------------------------------------------------------------------------

forallType : Parser Type
forallType =
  let
    wsIdentifierPair =
      delayedCommitMap (,) blanks identifierString
    quantifiers =
      oneOf
        [ inContext "forall type (one)" <|
            map One wsIdentifierPair
        , inContext "forall type (many) "<|
            parenBlankBlock Many <|
              repeat zeroOrMore wsIdentifierPair
        ]
  in
    inContext "forall type" <|
      lazy <| \_ ->
        parenBlankBlock
        ( \wsStart (qs, t) wsEnd -> TForall wsStart qs t wsEnd
        )
        ( succeed (,)
            |. keyword "forall"
            |= quantifiers
            |= typ
        )

--------------------------------------------------------------------------------
-- Union Type
--------------------------------------------------------------------------------

unionType : Parser Type
unionType =
  inContext "union type" <|
    lazy <| \_ ->
      parenBlankBlock TUnion <|
        succeed identity
          |. keyword "union"
          |= repeat oneOrMore typ

--------------------------------------------------------------------------------
-- Wildcard Type
--------------------------------------------------------------------------------

wildcardType : Parser Type
wildcardType =
  inContext "wildcard type" <|
    delayedCommitMap (always << TWildcard) blanks (symbol "_")

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

type Op
  = Pi
  | Cos
  | Sin
  | Arccos
  | Arcsin
  | Floor
  | Ceiling
  | Round
  | ToString
  | Sqrt
  | Explode
  | Plus
  | Minus
  | Multiply
  | Divide
  | LessThan
  | Equal
  | Mod
  | Pow
  | Arctan2

type Branch
  = Branch WS Pattern Exp WS

type TBranch
  = TBranch WS Type Exp WS

type LetKind
  = Let | Def

type Exp
  = EIdentifier WS Identifier
  | EConstant WS Constant
  | EOp WS Op (List Exp) WS
  | EIf WS Exp Exp Exp WS
  -- heads / tail
  | EList WS (List Exp) WS (Maybe Exp) WS
  | ECase WS Exp (List Branch) WS
  | ETypeCase WS Pattern (List TBranch) WS
  | EFunction WS (List Pattern) Exp WS
  | EFunctionApplication WS Exp (List Exp) WS
  -- type of let / recursive / pattern / value / inner
  | ELet WS LetKind Bool Pattern Exp Exp WS
  | EOption String String
  | ETypeDeclaration WS Pattern Type Exp WS
  | ETypeAnnotation WS Exp WS Type WS

--------------------------------------------------------------------------------
-- Identifier Expressions
--------------------------------------------------------------------------------

identifierExpression : Parser Exp
identifierExpression =
  delayedCommitMap EIdentifier blanks identifierString

--------------------------------------------------------------------------------
-- Constant Expressions
--------------------------------------------------------------------------------

constantExpression : Parser Exp
constantExpression =
  delayedCommitMap EConstant blanks constant

--------------------------------------------------------------------------------
-- Primitive Operators
--------------------------------------------------------------------------------

operator : Parser Exp
operator =
  let
    op =
      oneOf
        [ succeed Pi
          |. keyword "pi"
        , succeed Cos
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
        , succeed Plus
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
    inContext "operator" <|
      lazy <| \_ ->
        parenBlankBlock
          ( \wsStart (op, args) wsEnd ->
              EOp wsStart op args wsEnd
          )
          ( succeed (,)
              |= op
              |= repeat zeroOrMore exp
          )

--------------------------------------------------------------------------------
-- Conditionals
--------------------------------------------------------------------------------

conditional : Parser Exp
conditional =
  inContext "conditional" <|
    lazy <| \_ ->
      parenBlankBlock
        ( \wsStart (c, a, b) wsEnd ->
            EIf wsStart c a b wsEnd
        )
        ( succeed (,,)
           |. keyword "if "
           |= exp
           |= exp
           |= exp
        )

--------------------------------------------------------------------------------
-- Lists
--------------------------------------------------------------------------------

list : Parser Exp
list =
  lazy <| \_ ->
    genericBlankList
      { generalContext =
          "list"
      , listLiteralContext =
          "list literal"
      , multiConsContext =
          "multi cons literal"
      , listLiteralCombiner =
          ( \wsStart heads wsEnd ->
              EList wsStart heads "" Nothing wsEnd
          )
      , multiConsCombiner =
          ( \wsStart heads wsBar tail wsEnd ->
              EList wsStart heads wsBar (Just tail) wsEnd
          )
      , elem =
          exp
      }

--------------------------------------------------------------------------------
-- Branch Helper
--------------------------------------------------------------------------------

genericCase
  :  String
  -> String
  -> (WS -> a -> (List c) -> WS -> Exp)
  -> (WS -> b -> Exp -> WS -> c)
  -> Parser a
  -> Parser b
  -> Parser Exp
genericCase context kword combiner branchCombiner parser branchParser =
  let
    path =
      inContext (context ++ " path") <|
        lazy <| \_ ->
          parenBlankBlock
            ( \wsStart (p, e) wsEnd ->
                branchCombiner wsStart p e wsEnd
            )
            ( succeed (,)
                |= branchParser
                |= exp
            )
  in
    inContext context <|
      lazy <| \_ ->
        parenBlankBlock
          ( \wsStart (c, branches) wsEnd ->
              combiner wsStart c branches wsEnd
          )
          ( succeed (,)
              |. keyword (kword ++ " ")
              |= parser
              |= repeat zeroOrMore path
          )

--------------------------------------------------------------------------------
-- Case Expressions
--------------------------------------------------------------------------------

caseExpression : Parser Exp
caseExpression =
  lazy <| \_ ->
    genericCase "case expression" "case" ECase Branch exp pattern

--------------------------------------------------------------------------------
-- Type Case Expressions
--------------------------------------------------------------------------------

typeCaseExpression : Parser Exp
typeCaseExpression =
  lazy <| \_ ->
    genericCase "type case expression" "typecase" ETypeCase TBranch pattern typ

--------------------------------------------------------------------------------
-- Functions
--------------------------------------------------------------------------------

function : Parser Exp
function =
  let
    parameters =
      oneOf
        [ map singleton pattern
        , parenBlockIgnoreWS <| repeat oneOrMore pattern
        ]
  in
    inContext "function" <|
      lazy <| \_ ->
        parenBlankBlock
          ( \wsStart (params, body) wsEnd ->
              EFunction wsStart params body wsEnd
          )
          ( succeed (,)
              |. symbol "\\"
              |= parameters
              |= exp
          )

--------------------------------------------------------------------------------
-- Function Applications
--------------------------------------------------------------------------------

functionApplication : Parser Exp
functionApplication =
  inContext "function application" <|
    lazy <| \_ ->
      parenBlankBlock
        ( \wsStart (f, x) wsEnd ->
            EFunctionApplication wsStart f x wsEnd
        )
        ( succeed (,)
            |= exp
            |= repeat oneOrMore exp
        )

--------------------------------------------------------------------------------
-- Let Bindings
--------------------------------------------------------------------------------

genericLetBinding : String -> String -> Bool -> Parser Exp
genericLetBinding context kword isRec =
  inContext context <|
    parenBlankBlock
      ( \wsStart (pat, val, rest) wsEnd ->
          ELet wsStart Let isRec pat val rest wsEnd
      )
      ( succeed (,,)
          |. keyword (kword ++ " ")
          |= identifierPattern
          |= exp
          |= exp
      )

genericDefBinding : String -> String -> Bool -> Parser Exp
genericDefBinding context kword isRec =
  inContext context <|
    delayedCommitMap
      ( \wsStart (pat, val, wsEnd, rest) ->
          ELet wsStart Def isRec pat val rest wsEnd
      )
      ( openBlankBlock "(" )
      ( succeed (,,,)
          |. keyword (kword ++ " ")
          |= identifierPattern
          |= exp
          |= closeBlankBlock ")"
          |= exp
      )

recursiveLetBinding : Parser Exp
recursiveLetBinding =
  lazy <| \_ ->
    genericLetBinding "recursive let binding" "letrec" True

simpleLetBinding : Parser Exp
simpleLetBinding =
  lazy <| \_ ->
    genericLetBinding "non-recursive let binding" "let" False

recursiveDefBinding : Parser Exp
recursiveDefBinding =
  lazy <| \_ ->
    genericDefBinding "recursive def binding" "defrec" True

simpleDefBinding : Parser Exp
simpleDefBinding =
  lazy <| \_ ->
    genericDefBinding "non-recursive def binding" "def" False

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
    delayedCommitMap
      ( \wsStart (pat, t, wsEnd, rest) ->
          ETypeDeclaration wsStart pat t rest wsEnd
      )
      ( openBlankBlock "(" )
      ( succeed (,,,)
          |. keyword "typ "
          |= identifierPattern
          |= typ
          |= closeBlankBlock ")"
          |= exp
      )

--------------------------------------------------------------------------------
-- Type Annotation
--------------------------------------------------------------------------------

typeAnnotation : Parser Exp
typeAnnotation =
  inContext "type annotation" <|
    lazy <| \_ ->
      parenBlankBlock
        ( \wsStart (e, wsColon, t) wsEnd ->
            ETypeAnnotation wsStart e wsColon t wsEnd
        )
        ( delayedCommitMap
            ( \(e, wsColon) t ->
                (e, wsColon, t)
            )
            ( succeed (,)
                |= exp
                |= blanks
                |. symbol ":"
            )
            typ
        )

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
