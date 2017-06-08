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

--==============================================================================
--= CONSTANTS
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

identifierPattern_ : Parser Pat_
identifierPattern_ =
  mapPat_ <|
    delayedCommitMap PIdentifier spaces identifierString_

identifierPattern : Parser Pat
identifierPattern =
  trackInfo identifierPattern_

--------------------------------------------------------------------------------
-- Constant Pattern
--------------------------------------------------------------------------------

constantPattern_ : Parser Pat_
constantPattern_ =
  mapPat_ <|
    delayedCommitMap PConstant spaces constant_

constantPattern : Parser Pat
constantPattern =
  trackInfo constantPattern_

--------------------------------------------------------------------------------
-- Pattern Lists
--------------------------------------------------------------------------------

patternList_ : Parser Pat_
patternList_ =
  mapPat_ <|
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

patternList : Parser Pat
patternList =
  trackInfo patternList_

--------------------------------------------------------------------------------
-- As-Patterns (@-Patterns)
--------------------------------------------------------------------------------

asPattern_ : Parser Pat_
asPattern_ =
  mapPat_ <|
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

asPattern : Parser Pat
asPattern =
  trackInfo asPattern_

--------------------------------------------------------------------------------
-- General Patterns
--------------------------------------------------------------------------------

pattern_ : Parser Pat_
pattern_ =
  inContext "pattern" <|
    oneOf
      [ lazy <| \_ -> patternList_
      , lazy <| \_ -> asPattern_
      , constantPattern_
      , identifierPattern_
      ]

pattern : Parser Pat
pattern =
  trackInfo pattern_

--==============================================================================
--= TYPES
--==============================================================================

--------------------------------------------------------------------------------
-- Data Types
--------------------------------------------------------------------------------

type OneOrMany a
  = One a
  | Many WS (List a) WS

type Type_
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

type alias Type = WithInfo Type_

--------------------------------------------------------------------------------
-- Base Types
--------------------------------------------------------------------------------

baseType_ : String -> (WS -> Type_) -> String -> Parser Type_
baseType_ context combiner token =
  inContext context <|
    delayedCommitMap always
      (map combiner spaces)
      (keyword token)

baseType : String -> (WS -> Type_) -> String -> Parser Type
baseType context combiner token =
  trackInfo (baseType_ context combiner token)

nullType_ : Parser Type_
nullType_ =
  baseType_ "null type" TNull "Null"

nullType : Parser Type
nullType =
  trackInfo nullType_

numType_ : Parser Type_
numType_ =
  baseType_ "num type" TNum "Num"

numType : Parser Type
numType =
  trackInfo numType_

boolType_ : Parser Type_
boolType_ =
  baseType_ "boool type" TBool "Bool"

boolType : Parser Type
boolType =
  trackInfo boolType_

stringType_ : Parser Type_
stringType_ =
  baseType_ "string type" TString "String"

stringType : Parser Type
stringType =
  trackInfo stringType_

--------------------------------------------------------------------------------
-- Aliased Types
--------------------------------------------------------------------------------

aliasType_ : Parser Type_
aliasType_ =
  inContext "alias type" <|
    delayedCommitMap TAlias spaces identifierString_

aliasType : Parser Type
aliasType =
  trackInfo aliasType_

--------------------------------------------------------------------------------
-- Function Type
--------------------------------------------------------------------------------

functionType_ : Parser Type_
functionType_ =
  inContext "function type" <|
    lazy <| \_ ->
      parenBlock TFunction <|
        succeed identity
          |. keyword "->"
          |= repeat oneOrMore typ

functionType : Parser Type
functionType =
  trackInfo functionType_

--------------------------------------------------------------------------------
-- List Type
--------------------------------------------------------------------------------

listType_ : Parser Type_
listType_ =
  inContext "list type" <|
    lazy <| \_ ->
      parenBlock TList <|
        succeed identity
          |. keyword "List"
          |= typ

listType : Parser Type
listType =
  trackInfo listType_

--------------------------------------------------------------------------------
-- Tuple Type
--------------------------------------------------------------------------------

tupleType_ : Parser Type_
tupleType_ =
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

tupleType : Parser Type
tupleType =
  trackInfo tupleType_

--------------------------------------------------------------------------------
-- Forall Type
--------------------------------------------------------------------------------

forallType_ : Parser Type_
forallType_ =
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

forallType : Parser Type
forallType =
  trackInfo forallType_

--------------------------------------------------------------------------------
-- Union Type
--------------------------------------------------------------------------------

unionType_ : Parser Type_
unionType_ =
  inContext "union type" <|
    lazy <| \_ ->
      parenBlock TUnion <|
        succeed identity
          |. keyword "union"
          |= repeat oneOrMore typ

unionType : Parser Type
unionType =
  trackInfo unionType_

--------------------------------------------------------------------------------
-- Wildcard Type
--------------------------------------------------------------------------------

wildcardType_ : Parser Type_
wildcardType_ =
  inContext "wildcard type" <|
    delayedCommitMap (always << TWildcard) spaces (symbol "_")

wildcardType : Parser Type
wildcardType =
  trackInfo wildcardType_

--------------------------------------------------------------------------------
-- General Types
--------------------------------------------------------------------------------

typ_ : Parser Type_
typ_ =
  inContext "type" <|
    oneOf
      [ nullType_
      , numType_
      , boolType_
      , stringType_
      , wildcardType_
      , lazy <| \_ -> functionType_
      , lazy <| \_ -> listType_
      , lazy <| \_ -> tupleType_
      , lazy <| \_ -> forallType_
      , lazy <| \_ -> unionType_
      , aliasType_
      ]

typ : Parser Type
typ =
  trackInfo typ_

--==============================================================================
--= EXPRESSIONS
--==============================================================================

--------------------------------------------------------------------------------
-- Data Types
--------------------------------------------------------------------------------

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

type Exp__
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

type alias EId  = Int
type alias Exp_ = { e__ : Exp__, eid : EId  }
type alias Exp = WithInfo Exp_

exp_ : Exp__ -> Exp_
exp_ e = { e__ = e, eid = -1 }

mapExp_ : Parser Exp__ -> Parser Exp_
mapExp_ = map exp_

--------------------------------------------------------------------------------
-- Identifier Expressions
--------------------------------------------------------------------------------

identifierExpression_ : Parser Exp_
identifierExpression_ =
  mapExp_ <|
    delayedCommitMap EIdentifier spaces identifierString_

identifierExpression : Parser Exp
identifierExpression =
  trackInfo identifierExpression_

--------------------------------------------------------------------------------
-- Constant Expressions
--------------------------------------------------------------------------------

constantExpression_ : Parser Exp_
constantExpression_ =
  mapExp_ <|
    delayedCommitMap EConstant spaces constant_

constantExpression : Parser Exp
constantExpression =
  trackInfo constantExpression_

--------------------------------------------------------------------------------
-- Primitive Operators
--------------------------------------------------------------------------------

operator_ : Parser Exp_
operator_ =
  mapExp_ <|
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
                |= repeat zeroOrMore expr
            )

operator : Parser Exp
operator =
  trackInfo operator_

--------------------------------------------------------------------------------
-- Conditionals
--------------------------------------------------------------------------------

conditional_ : Parser Exp_
conditional_ =
  mapExp_ <|
    inContext "conditional" <|
      lazy <| \_ ->
        parenBlock
          ( \wsStart (c, a, b) wsEnd ->
              EIf wsStart c a b wsEnd
          )
          ( succeed (,,)
             |. keyword "if "
             |= expr
             |= expr
             |= expr
          )

conditional : Parser Exp
conditional =
  trackInfo conditional_

--------------------------------------------------------------------------------
-- Lists
--------------------------------------------------------------------------------

list_ : Parser Exp_
list_ =
  mapExp_ <|
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
            expr
        }

list : Parser Exp
list =
  trackInfo list_

--------------------------------------------------------------------------------
-- Branch Helper
--------------------------------------------------------------------------------

genericCase_
  :  String
  -> String
  -> (WS -> a -> (List c) -> WS -> Exp__)
  -> (WS -> b -> Exp -> WS -> c)
  -> Parser a
  -> Parser b
  -> Parser Exp_
genericCase_ context kword combiner branchCombiner parser branchParser =
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
                |= expr
            )
  in
    mapExp_ <|
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

caseExpression_ : Parser Exp_
caseExpression_ =
    lazy <| \_ ->
      genericCase_ "case expression" "case" ECase Branch expr pattern

caseExpression : Parser Exp
caseExpression =
  trackInfo caseExpression_

--------------------------------------------------------------------------------
-- Type Case Expressions
--------------------------------------------------------------------------------

typeCaseExpression_ : Parser Exp_
typeCaseExpression_ =
    lazy <| \_ ->
      genericCase_ "type case expression" "typecase" ETypeCase TBranch pattern typ

typeCaseExpression : Parser Exp
typeCaseExpression =
  trackInfo typeCaseExpression_

--------------------------------------------------------------------------------
-- Functions
--------------------------------------------------------------------------------

function_ : Parser Exp_
function_ =
  let
    parameters =
      oneOf
        [ map singleton pattern
        , parenBlockIgnoreWS <| repeat oneOrMore pattern
        ]
  in
    mapExp_ <|
      inContext "function" <|
        lazy <| \_ ->
          parenBlock
            ( \wsStart (params, body) wsEnd ->
                EFunction wsStart params body wsEnd
            )
            ( succeed (,)
                |. symbol "\\"
                |= parameters
                |= expr
            )

function : Parser Exp
function =
  trackInfo function_

--------------------------------------------------------------------------------
-- Function Applications
--------------------------------------------------------------------------------

functionApplication_ : Parser Exp_
functionApplication_ =
  mapExp_ <|
    inContext "function application" <|
      lazy <| \_ ->
        parenBlock
          ( \wsStart (f, x) wsEnd ->
              EFunctionApplication wsStart f x wsEnd
          )
          ( succeed (,)
              |= expr
              |= repeat oneOrMore expr
          )

functionApplication : Parser Exp
functionApplication =
  trackInfo functionApplication_

--------------------------------------------------------------------------------
-- Let Bindings
--------------------------------------------------------------------------------

genericLetBinding_ : String -> String -> Bool -> Parser Exp_
genericLetBinding_ context kword isRec =
  mapExp_ <|
    inContext context <|
      parenBlock
        ( \wsStart (pat, val, rest) wsEnd ->
            ELet wsStart Let isRec pat val rest wsEnd
        )
        ( succeed (,,)
            |. keyword (kword ++ " ")
            |= pattern
            |= expr
            |= expr
        )

genericDefBinding_ : String -> String -> Bool -> Parser Exp_
genericDefBinding_ context kword isRec =
  mapExp_ <|
    inContext context <|
      delayedCommitMap
        ( \wsStart (pat, val, wsEnd, rest) ->
            ELet wsStart Def isRec pat val rest wsEnd
        )
        ( openBlock "(" )
        ( succeed (,,,)
            |. keyword (kword ++ " ")
            |= pattern
            |= expr
            |= closeBlock ")"
            |= expr
        )

recursiveLetBinding_ : Parser Exp_
recursiveLetBinding_ =
  lazy <| \_ ->
    genericLetBinding_ "recursive let binding" "letrec" True

simpleLetBinding_ : Parser Exp_
simpleLetBinding_ =
  lazy <| \_ ->
    genericLetBinding_ "non-recursive let binding" "let" False

recursiveDefBinding_ : Parser Exp_
recursiveDefBinding_ =
  lazy <| \_ ->
    genericDefBinding_ "recursive def binding" "defrec" True

simpleDefBinding_ : Parser Exp_
simpleDefBinding_ =
  lazy <| \_ ->
    genericDefBinding_ "non-recursive def binding" "def" False

letBinding_ : Parser Exp_
letBinding_ =
  inContext "let binding" <|
    lazy <| \_ ->
      oneOf
        [ recursiveLetBinding_
        , simpleLetBinding_
        , recursiveDefBinding_
        , simpleDefBinding_
        ]

letBinding : Parser Exp
letBinding =
  trackInfo letBinding_

--------------------------------------------------------------------------------
-- Options
--------------------------------------------------------------------------------

-- TODO fix options

validOptionChar : Char -> Bool
validOptionChar c =
  Char.isLower c || Char.isUpper c || Char.isDigit c

option_ : Parser Exp_
option_ =
  mapExp_ <|
    succeed EOption
      |. symbol "#"
      |= keep oneOrMore validOptionChar
      |= keep oneOrMore validOptionChar
      |. ignoreUntil "\n"

option : Parser Exp
option =
  trackInfo option_

--------------------------------------------------------------------------------
-- Type Declarations
--------------------------------------------------------------------------------

typeDeclaration_ : Parser Exp_
typeDeclaration_ =
  mapExp_ <|
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
            |= expr
        )

typeDeclaration : Parser Exp
typeDeclaration =
  trackInfo typeDeclaration_

--------------------------------------------------------------------------------
-- Type Annotations
--------------------------------------------------------------------------------

typeAnnotation_ : Parser Exp_
typeAnnotation_ =
  mapExp_ <|
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
                  |= expr
                  |= spaces
                  |. symbol ":"
              )
              typ
          )

typeAnnoation : Parser Exp
typeAnnoation =
  trackInfo typeAnnotation_

--------------------------------------------------------------------------------
-- Comments
--------------------------------------------------------------------------------

comment_ : Parser Exp_
comment_ =
  mapExp_ <|
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
              |= expr
          )

comment : Parser Exp
comment =
  trackInfo comment_

--------------------------------------------------------------------------------
-- General Expressions
--------------------------------------------------------------------------------

expr_ : Parser Exp_
expr_ =
  inContext "expression" <|
    oneOf
      [ constantExpression_
      , lazy <| \_ -> operator_
      , lazy <| \_ -> conditional_
      , lazy <| \_ -> letBinding_
      , lazy <| \_ -> caseExpression_
      , lazy <| \_ -> typeCaseExpression_
      , lazy <| \_ -> typeDeclaration_
      , lazy <| \_ -> typeAnnotation_
      , lazy <| \_ -> list_
      , lazy <| \_ -> function_
      , lazy <| \_ -> functionApplication_
      , lazy <| \_ -> comment_
      , identifierExpression_
      ]

expr : Parser Exp
expr =
  trackInfo expr_

--==============================================================================
--= EXPORTS
--==============================================================================

parse : String -> Result Error Exp
parse = run expr
