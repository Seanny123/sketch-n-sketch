module FastParser exposing (parse)

import List
import Char

import String exposing (fromChar)
import Set exposing (Set)

import Parser exposing (..)
import Parser.LanguageKit exposing (..)
import Parser.LowLevel exposing (getPosition)

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

--------------------------------------------------------------------------------
-- Whitespace
--------------------------------------------------------------------------------

type alias WS = String

isSpace : Char -> Bool
isSpace c =
  c == ' ' || c == '\n'

spaces : Parser WS
spaces =
  keep zeroOrMore isSpace

--------------------------------------------------------------------------------
-- Block Helper
--------------------------------------------------------------------------------

openBlock : String -> Parser WS
openBlock openSymbol =
  succeed identity
    |= spaces
    |. symbol openSymbol

closeBlock : String -> Parser WS
closeBlock closeSymbol =
  succeed identity
    |= spaces
    |. symbol closeSymbol

block : (WS -> a -> WS -> b) -> String -> String -> Parser a -> Parser b
block combiner open close p =
  delayedCommitMap
    ( \wsStart (result, wsEnd) ->
        combiner wsStart result wsEnd
    )
    ( openBlock open )
    ( succeed (,)
        |= p
        |= closeBlock close
    )

parenBlock : (WS -> a -> WS -> b) -> Parser a -> Parser b
parenBlock combiner = block combiner "(" ")"

bracketBlock : (WS -> a -> WS -> b) -> Parser a -> Parser b
bracketBlock combiner = block combiner "[" "]"

blockIgnoreWS : String -> String -> Parser a -> Parser a
blockIgnoreWS = block (\wsStart x wsEnd -> x)

parenBlockIgnoreWS : Parser a -> Parser a
parenBlockIgnoreWS = blockIgnoreWS "(" ")"

bracketBlockIgnoreWS : Parser a -> Parser a
bracketBlockIgnoreWS = blockIgnoreWS "[" "]"

--------------------------------------------------------------------------------
-- List Helper
--------------------------------------------------------------------------------

blankListLiteralInternal
  : String -> (WS -> List elem -> WS -> list) -> Parser elem -> Parser list
blankListLiteralInternal context combiner elem  =
  inContext context <|
    bracketBlock combiner (repeat zeroOrMore elem)

blankMultiConsInternal
  :  String
  -> (WS -> List elem -> WS -> elem -> WS -> list)
  -> Parser elem
  -> Parser list
blankMultiConsInternal context combiner elem =
  inContext context <|
    bracketBlock
      ( \wsStart (heads, wsBar, tail) wsEnd ->
          combiner wsStart heads wsBar tail wsEnd
      )
      ( delayedCommitMap
          ( \(heads, wsBar) tail ->
              (heads, wsBar, tail)
          )
          ( succeed (,)
              |= repeat oneOrMore elem
              |= spaces
              |. symbol "|"
          )
          elem
      )

genericList
  :  { generalContext : String
     , listLiteralContext : String
     , multiConsContext : String
     , listLiteralCombiner : WS -> List elem -> WS -> list
     , multiConsCombiner : WS -> List elem -> WS -> elem -> WS -> list
     , elem : Parser elem
     }
  -> Parser list
genericList args =
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
--= POSITION INFO
--==============================================================================

--------------------------------------------------------------------------------
-- Pos
--------------------------------------------------------------------------------

type alias Pos =
  { line : Int
  , col : Int
  }

startPos : Pos
startPos =
  { line = 1
  , col = 1
  }

dummyPos : Pos
dummyPos =
  { line = -1
  , col = -1
  }

posFromRowCol : (Int, Int) -> Pos
posFromRowCol (row, col) =
  { line = row
  , col = col
  }

--------------------------------------------------------------------------------
-- WithPos
--------------------------------------------------------------------------------

type alias WithPos a =
  { val : a
  , pos : Pos
  }

getPos : Parser Pos
getPos =
  map posFromRowCol getPosition

--------------------------------------------------------------------------------
-- WithInfo
--------------------------------------------------------------------------------

type alias WithInfo a =
  { val : a
  , start : Pos
  , end : Pos
  }

withInfo : a -> Pos -> Pos -> WithInfo a
withInfo x start end =
  { val = x
  , start = start
  , end = end
  }

mapInfo : (a -> b) -> WithInfo a -> WithInfo b
mapInfo f w =
  { w | val = f w.val }

trackInfo : Parser a -> Parser (WithInfo a)
trackInfo p =
  delayedCommitMap
    ( \start (a, end) ->
        withInfo a start end
    )
    getPos
    ( succeed (,)
        |= p
        |= getPos
    )

-- TODO remove
--delayedCommitMapWI
--  : (a -> b -> value) -> Parser a -> Parser b -> Parser (WithInfo value)
--delayedCommitMapWI combiner pa pb =
--  delayedCommitMap
--    ( \(start, a) (b, end) ->
--        withInfo (combiner a b) start end
--    )
--    ( succeed (,)
--        |= getPos
--        |= pa
--    )
--    ( succeed (,)
--        |= pb
--        |= getPos
--    )

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

number_ : Parser Constant
number_ =
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

number : Parser (WithInfo Constant)
number =
  trackInfo number_

--------------------------------------------------------------------------------
-- Strings
--------------------------------------------------------------------------------

string_ : Parser Constant
string_ =
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
      oneOf <| List.map stringHelper ['\'', '"'] -- " -- fix syntax highlighting

string : Parser (WithInfo Constant)
string =
  trackInfo string_

--------------------------------------------------------------------------------
-- Bools
--------------------------------------------------------------------------------

bool_ : Parser Constant
bool_ =
  map CBool <|
    oneOf <|
      [ map (always True) <| keyword "true"
      , map (always False) <| keyword "false"
      ]

bool : Parser (WithInfo Constant)
bool =
  trackInfo bool_

--------------------------------------------------------------------------------
-- General Constants
--------------------------------------------------------------------------------

constant_ : Parser Constant
constant_ =
  oneOf
    [ number_
    , string_
    , bool_
    ]

constant : Parser (WithInfo Constant)
constant =
  trackInfo constant_

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

identifierString_ : Parser Identifier
identifierString_ =
  variable validIdentifierFirstChar validIdentifierRestChar keywords

identifierString : Parser (WithInfo Identifier)
identifierString =
  trackInfo identifierString_

--==============================================================================
--= PATTERNS
--==============================================================================

--------------------------------------------------------------------------------
-- Data Types
--------------------------------------------------------------------------------

type alias Identifier = String

type Pat__
  = PIdentifier WS Identifier
  | PConstant WS Constant
  | PList WS (List Pat) WS (Maybe Pat) WS
  | PAs WS Identifier WS Pat

type alias PId  = Int
type alias Pat_ = { p__ : Pat__, pid : PId  }
type alias Pat = WithInfo Pat_

pat_ : Pat__ -> Pat_
pat_ p = { p__ = p, pid = -1 }

mapPat_ : Parser Pat__ -> Parser Pat_
mapPat_ = map pat_

--------------------------------------------------------------------------------
-- Identifier Pattern
--------------------------------------------------------------------------------

identifierPattern : Parser Pat
identifierPattern =
  trackInfo << mapPat_ <|
    delayedCommitMap PIdentifier spaces identifierString_

--------------------------------------------------------------------------------
-- Constant Pattern
--------------------------------------------------------------------------------

constantPattern : Parser Pat
constantPattern =
  trackInfo << mapPat_ <|
    delayedCommitMap PConstant spaces constant_

--------------------------------------------------------------------------------
-- Pattern Lists
--------------------------------------------------------------------------------

patternList : Parser Pat
patternList =
  trackInfo << mapPat_ <|
    lazy <| \_ ->
      genericList
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

asPattern : Parser Pat
asPattern =
  trackInfo << mapPat_ <|
    inContext "as pattern" <|
      lazy <| \_ ->
        delayedCommitMap
        ( \(wsStart, name, wsAt) pat ->
            PAs wsStart name wsAt pat
        )
        ( succeed (,,)
            |= spaces
            |= identifierString_
            |= spaces
            |. symbol "@"
        )
        pattern

--------------------------------------------------------------------------------
-- General Patterns
--------------------------------------------------------------------------------

pattern : Parser Pat
pattern =
  inContext "pattern" <|
    oneOf
      [ lazy <| \_ -> patternList
      , lazy <| \_ -> asPattern
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
      (map combiner spaces)
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
    delayedCommitMap TAlias spaces identifierString_

--------------------------------------------------------------------------------
-- Function Type
--------------------------------------------------------------------------------

functionType : Parser Type
functionType =
  inContext "function type" <|
    lazy <| \_ ->
      parenBlock TFunction <|
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
      parenBlock TList <|
        succeed identity
          |. keyword "List"
          |= typ

--------------------------------------------------------------------------------
-- Tuple Type
--------------------------------------------------------------------------------

tupleType : Parser Type
tupleType =
  lazy <| \_ ->
    genericList
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
      delayedCommitMap (,) spaces identifierString_
    quantifiers =
      oneOf
        [ inContext "forall type (one)" <|
            map One wsIdentifierPair
        , inContext "forall type (many) "<|
            parenBlock Many <|
              repeat zeroOrMore wsIdentifierPair
        ]
  in
    inContext "forall type" <|
      lazy <| \_ ->
        parenBlock
          ( \wsStart (qs, t) wsEnd ->
              TForall wsStart qs t wsEnd
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
      parenBlock TUnion <|
        succeed identity
          |. keyword "union"
          |= repeat oneOrMore typ

--------------------------------------------------------------------------------
-- Wildcard Type
--------------------------------------------------------------------------------

wildcardType : Parser Type
wildcardType =
  inContext "wildcard type" <|
    delayedCommitMap (always << TWildcard) spaces (symbol "_")

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
      , lazy <| \_ -> functionType
      , lazy <| \_ -> listType
      , lazy <| \_ -> tupleType
      , lazy <| \_ -> forallType
      , lazy <| \_ -> unionType
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
  = Branch WS Pat Exp WS

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
  | ETypeCase WS Pat (List TBranch) WS
  | EFunction WS (List Pat) Exp WS
  | EFunctionApplication WS Exp (List Exp) WS
  -- type of let / recursive / pattern / value / inner
  | ELet WS LetKind Bool Pat Exp Exp WS
  | ETypeDeclaration WS Pat Type Exp WS
  | ETypeAnnotation WS Exp WS Type WS
  | EComment WS String Exp
  | EOption String String

--------------------------------------------------------------------------------
-- Identifier Expressions
--------------------------------------------------------------------------------

identifierExpression : Parser Exp
identifierExpression =
  delayedCommitMap EIdentifier spaces identifierString_

--------------------------------------------------------------------------------
-- Constant Expressions
--------------------------------------------------------------------------------

constantExpression : Parser Exp
constantExpression =
  delayedCommitMap EConstant spaces constant_

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
        parenBlock
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
      parenBlock
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
    genericList
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
          parenBlock
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
        parenBlock
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
        parenBlock
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
      parenBlock
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
    parenBlock
      ( \wsStart (pat, val, rest) wsEnd ->
          ELet wsStart Let isRec pat val rest wsEnd
      )
      ( succeed (,,)
          |. keyword (kword ++ " ")
          |= pattern
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
      ( openBlock "(" )
      ( succeed (,,,)
          |. keyword (kword ++ " ")
          |= pattern
          |= exp
          |= closeBlock ")"
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

-- TODO fix options

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
      ( openBlock "(" )
      ( succeed (,,,)
          |. keyword "typ "
          |= identifierPattern
          |= typ
          |= closeBlock ")"
          |= exp
      )

--------------------------------------------------------------------------------
-- Type Annotations
--------------------------------------------------------------------------------

typeAnnotation : Parser Exp
typeAnnotation =
  inContext "type annotation" <|
    lazy <| \_ ->
      parenBlock
        ( \wsStart (e, wsColon, t) wsEnd ->
            ETypeAnnotation wsStart e wsColon t wsEnd
        )
        ( delayedCommitMap
            ( \(e, wsColon) t ->
                (e, wsColon, t)
            )
            ( succeed (,)
                |= exp
                |= spaces
                |. symbol ":"
            )
            typ
        )

--------------------------------------------------------------------------------
-- Comments
--------------------------------------------------------------------------------

comment : Parser Exp
comment =
  inContext "comment" <|
    lazy <| \_ ->
      delayedCommitMap
        ( \wsStart (text, rest) ->
            EComment wsStart text rest
        )
        spaces
        ( succeed (,)
            |. symbol ";"
            |= keep zeroOrMore (\c -> c /= '\n')
            |. symbol "\n"
            |= exp
        )

--------------------------------------------------------------------------------
-- General Expressions
--------------------------------------------------------------------------------

exp : Parser Exp
exp =
  inContext "expression" <|
    oneOf
      [ constantExpression
      , lazy <| \_ -> operator
      , lazy <| \_ -> conditional
      , lazy <| \_ -> letBinding
      , lazy <| \_ -> caseExpression
      , lazy <| \_ -> typeCaseExpression
      , lazy <| \_ -> typeDeclaration
      , lazy <| \_ -> typeAnnotation
      , lazy <| \_ -> list
      , lazy <| \_ -> function
      , lazy <| \_ -> functionApplication
      , lazy <| \_ -> comment
      , identifierExpression
      ]

--==============================================================================
--= EXPORTS
--==============================================================================

parse : String -> Result Error Pat
parse = run pattern
