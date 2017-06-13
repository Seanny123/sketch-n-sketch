module FastParser exposing
  ( prelude, isPreludeLoc, isPreludeLocId, isPreludeEId
  , substOf, substStrOf, substPlusOf
  , parseE, parseT
  , freshen
  )

import List
import Char

import String exposing (fromChar)
import Set exposing (Set)
import Dict exposing (Dict)

import Parser exposing (..)
import Parser.LanguageKit exposing (..)
import Parser.LowLevel exposing (getPosition)

import Utils as U
import PreludeGenerated as Prelude
import Lang exposing (..)

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

token : String -> Parser String
token s =
  map (always s) (keyword s)

--------------------------------------------------------------------------------
-- Info Helpers
--------------------------------------------------------------------------------

getPos : Parser Pos
getPos =
  map posFromRowCol getPosition

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

--------------------------------------------------------------------------------
-- Whitespace
--------------------------------------------------------------------------------

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
--= NUMBERS
--==============================================================================

--------------------------------------------------------------------------------
-- Raw Numbers
--------------------------------------------------------------------------------

num_ : Parser Num
num_ =
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

num : Parser (WithInfo Num)
num =
  trackInfo num_

--------------------------------------------------------------------------------
-- Widget Declarations
--------------------------------------------------------------------------------

isInt : Num -> Bool
isInt n = n == toFloat (floor n)

widgetDecl_ : Caption -> Parser WidgetDecl_
widgetDecl_ cap =
  let
    combiner a tok b =
      if List.all isInt [a.val, b.val] then
        IntSlider (mapInfo floor a) tok (mapInfo floor b) cap
      else
        NumSlider a tok b cap
  in
    inContext "widget declaration" <|
      oneOf
        [ succeed combiner
            |. symbol "{"
            |= num
            |= trackInfo (token "-")
            |= num
            |. symbol "}"
        , succeed NoWidgetDecl
        ]

widgetDecl : Caption -> Parser WidgetDecl
widgetDecl cap =
  trackInfo <| widgetDecl_ cap

--------------------------------------------------------------------------------
-- Frozen Annotations
--------------------------------------------------------------------------------

frozenAnnotation : Parser Frozen
frozenAnnotation =
  inContext "frozen annotation" <|
    oneOf <|
      List.map token [frozen, unann, thawed, assignOnlyOnce]

--==============================================================================
--= BASE VALUES
--==============================================================================

--------------------------------------------------------------------------------
-- Strings
--------------------------------------------------------------------------------

string_ : Parser EBaseVal
string_ =
  let
    stringHelper quoteChar =
      let
        quoteString = fromChar quoteChar
      in
        succeed (EString quoteString)
          |. symbol quoteString
          |= keep zeroOrMore (\c -> c /= quoteChar)
          |. symbol quoteString
  in
    inContext "string" <|
      oneOf <| List.map stringHelper ['\'', '"'] -- " -- fix syntax highlighting

string : Parser (WithInfo EBaseVal)
string =
  trackInfo string_

--------------------------------------------------------------------------------
-- Bools
--------------------------------------------------------------------------------

bool_ : Parser EBaseVal
bool_ =
  map EBool <|
    oneOf <|
      [ map (always True) <| keyword "true"
      , map (always False) <| keyword "false"
      ]

bool : Parser (WithInfo EBaseVal)
bool =
  trackInfo bool_

--------------------------------------------------------------------------------
-- Nulls
--------------------------------------------------------------------------------

null_ : Parser EBaseVal
null_ =
  map (always ENull) <| keyword "null"

null : Parser (WithInfo EBaseVal)
null =
  trackInfo null_

--------------------------------------------------------------------------------
-- General Base Values
--------------------------------------------------------------------------------

baseValue_ : Parser EBaseVal
baseValue_ =
  oneOf
    [ string_
    , bool_
    , null_
    ]

baseValue : Parser (WithInfo EBaseVal)
baseValue =
  trackInfo baseValue_

--==============================================================================
--= IDENTIFIERS
--==============================================================================

--------------------------------------------------------------------------------
-- General Identifiers
--------------------------------------------------------------------------------

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

identifierString_ : Parser Ident
identifierString_ =
  variable validIdentifierFirstChar validIdentifierRestChar keywords

identifierString : Parser (WithInfo Ident)
identifierString =
  trackInfo identifierString_

--------------------------------------------------------------------------------
-- Lower Identifiers
--------------------------------------------------------------------------------

lowerIdentifierString_ : Parser Ident
lowerIdentifierString_ =
  variable Char.isLower validIdentifierRestChar keywords

lowerIdentifierString : Parser (WithInfo Ident)
lowerIdentifierString =
  trackInfo lowerIdentifierString_

--------------------------------------------------------------------------------
-- Upper Identifiers
--------------------------------------------------------------------------------

upperIdentifierString_ : Parser Ident
upperIdentifierString_ =
  variable Char.isUpper validIdentifierRestChar keywords

upperIdentifierString : Parser (WithInfo Ident)
upperIdentifierString =
  trackInfo upperIdentifierString_

--==============================================================================
--= PATTERNS
--==============================================================================

--------------------------------------------------------------------------------
-- Variable Pattern
--------------------------------------------------------------------------------

variablePattern_ : Parser Pat_
variablePattern_ =
  delayedCommitMap
    (\ws name -> PVar ws name noWidgetDecl)
    spaces
    identifierString_

variablePattern : Parser Pat
variablePattern =
  trackInfo variablePattern_

--------------------------------------------------------------------------------
-- Constant Pattern
--------------------------------------------------------------------------------

constantPattern_ : Parser Pat_
constantPattern_ =
  delayedCommitMap PConst spaces num_

constantPattern : Parser Pat
constantPattern =
  trackInfo constantPattern_

--------------------------------------------------------------------------------
-- Base Value Pattern
--------------------------------------------------------------------------------

baseValuePattern_ : Parser Pat_
baseValuePattern_ =
  delayedCommitMap PBase spaces baseValue_

baseValuePattern : Parser Pat
baseValuePattern =
  trackInfo baseValuePattern_

--------------------------------------------------------------------------------
-- Pattern Lists
--------------------------------------------------------------------------------

patternList_ : Parser Pat_
patternList_ =
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
      , baseValuePattern_
      , variablePattern_
      ]

pattern : Parser Pat
pattern =
  trackInfo pattern_

--==============================================================================
--= TYPES
--==============================================================================

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
-- Named Types
--------------------------------------------------------------------------------

namedType_ : Parser Type_
namedType_ =
  inContext "named type" <|
    delayedCommitMap TNamed spaces upperIdentifierString_

namedType : Parser Type
namedType =
  trackInfo namedType_

--------------------------------------------------------------------------------
-- Variable Types
--------------------------------------------------------------------------------

variableType_ : Parser Type_
variableType_ =
  inContext "variable type" <|
    delayedCommitMap TVar spaces lowerIdentifierString_

variableType : Parser Type
variableType =
  trackInfo variableType_

--------------------------------------------------------------------------------
-- Function Type
--------------------------------------------------------------------------------

functionType_ : Parser Type_
functionType_ =
  lazy <| \_ ->
    inContext "function type" <|
      parenBlock TArrow <|
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
      , namedType_
      , variableType_
      ]

typ : Parser Type
typ =
  lazy <| \_ ->
    trackInfo typ_

--==============================================================================
--= EXPRESSIONS
--==============================================================================

--------------------------------------------------------------------------------
-- General Expression Helpers
--------------------------------------------------------------------------------

mapExp_ : Parser Exp__ -> Parser Exp_
mapExp_ = map exp_

--------------------------------------------------------------------------------
-- Identifier Expressions
--------------------------------------------------------------------------------

variableExpression_ : Parser Exp_
variableExpression_ =
  mapExp_ <|
    delayedCommitMap EVar spaces identifierString_

variableExpression : Parser Exp
variableExpression =
  trackInfo variableExpression_

--------------------------------------------------------------------------------
-- Constant Expressions
--------------------------------------------------------------------------------

-- TODO interacts badly with auto-abstracted variable names...
dummyLocWithDebugInfo : Frozen -> Num -> Loc
dummyLocWithDebugInfo b n = (0, b, "")

constantExpression_ : Parser Exp_
constantExpression_ =
  mapExp_ <|
    delayedCommitMap
      ( \ws (n, fa, w) ->
          EConst ws n (dummyLocWithDebugInfo fa n) w
      )
      ( spaces )
      ( succeed (,,)
          |= num_
          |= frozenAnnotation
          |= widgetDecl Nothing
      )

constantExpression : Parser Exp
constantExpression =
  trackInfo constantExpression_

--------------------------------------------------------------------------------
-- Base Value Expressions
--------------------------------------------------------------------------------

baseValueExpression_ : Parser Exp_
baseValueExpression_ =
  mapExp_ <|
    delayedCommitMap EBase spaces baseValue_

baseValueExpression : Parser Exp
baseValueExpression =
  trackInfo baseValueExpression_

--------------------------------------------------------------------------------
-- Primitive Operators
--------------------------------------------------------------------------------

operator_ : Parser Exp_
operator_ =
  mapExp_ <|
    let
      op_ =
        oneOf
          [ succeed Pi
            |. keyword "pi"
          , succeed Cos
            |. keyword "cos"
          , succeed Sin
            |. keyword "sin"
          , succeed ArcCos
            |. keyword "arccos"
          , succeed ArcSin
            |. keyword "arcsin"
          , succeed Floor
            |. keyword "floor"
          , succeed Ceil
            |. keyword "ceiling"
          , succeed Round
            |. keyword "round"
          , succeed ToStr
            |. keyword "toString"
          , succeed Sqrt
            |. keyword "sqrt"
          , succeed Explode
            |. keyword "explode"
          , succeed Plus
            |. keyword "+"
          , succeed Minus
            |. keyword "-"
          , succeed Mult
            |. keyword "*"
          , succeed Div
            |. keyword "/"
          , succeed Lt
            |. keyword "<"
          , succeed Eq
            |. keyword "="
          , succeed Mod
            |. keyword "mod"
          , succeed Pow
            |. keyword "pow"
          , succeed ArcTan2
            |. keyword "arctan2"
          ]
      op =
        trackInfo op_
    in
      inContext "operator" <|
        lazy <| \_ ->
          parenBlock
            ( \wsStart (opName, args) wsEnd ->
                EOp wsStart opName args wsEnd
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
  -> (WS -> a -> (List (WithInfo branch)) -> WS -> Exp__)
  -> (WS -> b -> Exp -> WS -> branch)
  -> Parser a
  -> Parser b
  -> Parser Exp_
genericCase_ context kword combiner branchCombiner parser branchParser =
  let
    path =
      inContext (context ++ " path") <|
        lazy <| \_ ->
          trackInfo <|
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
      genericCase_ "case expression" "case"
                   ECase Branch_ expr pattern

caseExpression : Parser Exp
caseExpression =
  trackInfo caseExpression_

--------------------------------------------------------------------------------
-- Type Case Expressions
--------------------------------------------------------------------------------

typeCaseExpression_ : Parser Exp_
typeCaseExpression_ =
    lazy <| \_ ->
      genericCase_ "type case expression" "typecase"
                   ETypeCase TBranch_ pattern typ

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
                EFun wsStart params body wsEnd
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
              EApp wsStart f x wsEnd
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
        ( \wsStart (name, binding, rest) wsEnd ->
            ELet wsStart Let isRec name binding rest wsEnd
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
        ( \wsStart (name, binding, wsEnd, rest) ->
            ELet wsStart Def isRec name binding rest wsEnd
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
      |= spaces
      |= trackInfo (keep oneOrMore validOptionChar)
      |= spaces
      |= trackInfo (keep oneOrMore validOptionChar)
      |= expr

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
            ETyp wsStart pat t rest wsEnd
        )
        ( openBlock "(" )
        ( succeed (,,,)
            |. keyword "typ "
            |= variablePattern
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
              EColonType wsStart e wsColon t wsEnd
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
      , baseValueExpression_
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
      , variableExpression_
      ]

expr : Parser Exp
expr =
  lazy <| \_ ->
    trackInfo expr_

--==============================================================================
--= TOP-LEVEL EXPRESSIONS
--==============================================================================

--------------------------------------------------------------------------------
-- Data Types
--------------------------------------------------------------------------------

type alias TopLevelExp_ = Exp -> Exp_
type alias TopLevelExp = WithInfo TopLevelExp_

--------------------------------------------------------------------------------
-- Top-Level Expression Fusing
--------------------------------------------------------------------------------

fuseTopLevelExp : TopLevelExp -> Exp -> Exp
fuseTopLevelExp tld rest =
  withInfo (tld.val rest) tld.start tld.end

fuseTopLevelExps : (List TopLevelExp) -> Exp -> Exp
fuseTopLevelExps tlds rest =
  List.foldr fuseTopLevelExp rest tlds

--------------------------------------------------------------------------------
-- Top-Level Defs
--------------------------------------------------------------------------------

genericTopLevelDef_ : String -> String -> Bool -> Parser TopLevelExp_
genericTopLevelDef_ context kword isRec =
  inContext context <|
    parenBlock
      ( \wsStart (name, binding) wsEnd ->
          ( \rest ->
              exp_ <| ELet wsStart Def isRec name binding rest wsEnd
          )
      )
      ( succeed (,)
          |. keyword (kword ++ " ")
          |= pattern
          |= expr
      )

recursiveTopLevelDef_ : Parser TopLevelExp_
recursiveTopLevelDef_ =
  genericTopLevelDef_ "top-level recursive def binding" "defrec" True

simpleTopLevelDef_ : Parser TopLevelExp_
simpleTopLevelDef_ =
  genericTopLevelDef_ "top-level non-recursive def binding" "def" False

topLevelDef_ : Parser TopLevelExp_
topLevelDef_ =
  inContext "top-level def binding" <|
    oneOf
      [ recursiveTopLevelDef_
      , simpleTopLevelDef_
      ]

topLevelDef : Parser TopLevelExp
topLevelDef =
  trackInfo topLevelDef_

--------------------------------------------------------------------------------
-- Top-Level Type Declarations
--------------------------------------------------------------------------------

topLevelTypeDeclaration_ : Parser TopLevelExp_
topLevelTypeDeclaration_ =
  inContext "top-level type declaration" <|
    parenBlock
      ( \wsStart (pat, t) wsEnd ->
          ( \rest ->
              exp_ <| ETyp wsStart pat t rest wsEnd
          )
      )
      ( succeed (,)
          |. keyword "typ "
          |= variablePattern
          |= typ
      )

topLevelTypeDeclaration : Parser TopLevelExp
topLevelTypeDeclaration =
  trackInfo topLevelTypeDeclaration_

--------------------------------------------------------------------------------
-- Top-Level Comments
--------------------------------------------------------------------------------

topLevelComment_ : Parser TopLevelExp_
topLevelComment_ =
  inContext "top-level comment" <|
    delayedCommitMap
      ( \wsStart text ->
          ( \rest ->
              exp_ <| EComment wsStart text rest
          )
      )
      spaces
      ( succeed identity
          |. symbol ";"
          |= keep zeroOrMore (\c -> c /= '\n')
          |. symbol "\n"
      )

topLevelComment : Parser TopLevelExp
topLevelComment =
  trackInfo topLevelComment_

--------------------------------------------------------------------------------
-- General Top-Level Expressions
--------------------------------------------------------------------------------

topLevelExp_ : Parser TopLevelExp_
topLevelExp_ =
  inContext "top-level expression" <|
    oneOf
      [ topLevelDef_
      , topLevelTypeDeclaration_
      , topLevelComment_
      ]

topLevelExp : Parser TopLevelExp
topLevelExp =
  trackInfo topLevelExp_

allTopLevelExps : Parser (List TopLevelExp)
allTopLevelExps =
  repeat zeroOrMore topLevelExp

--==============================================================================
--= PROGRAMS
--==============================================================================

program : Parser Exp
program =
  succeed fuseTopLevelExps
    |= allTopLevelExps
    |= expr

--==============================================================================
--= EXPORTS
--==============================================================================

parseE_ : (Exp -> Exp) -> String -> Result Error Exp
parseE_ f = run (map f program)

parseE : String -> Result Error Exp
parseE = parseE_ freshen

parseT : String -> Result Error Type
parseT = run typ

--------------------------------------------------------------------------------
-- Code from old parser
--------------------------------------------------------------------------------

(prelude, initK) =
  freshenClean 1 <| U.fromOkay "parse prelude" <| parseE_ identity Prelude.src

preludeIds = allIds prelude

isPreludeLoc : Loc -> Bool
isPreludeLoc (k,_,_) = isPreludeLocId k

isPreludeLocId : LocId -> Bool
isPreludeLocId k = k < initK

isPreludeEId : EId -> Bool
isPreludeEId k = k < initK

------------------------------------------------------------------------------

-- assign EId's and locId's
-- existing unique EId's/locId's are preserved
-- duplicated and dummy EId's/locId's are reassigned

freshen : Exp -> Exp
freshen e =
  -- let _ = Debug.log ("To Freshen:\n" ++ LangUnparser.unparseWithIds e) () in
  let (duplicateIds, allIds) = duplicateAndAllIds e in
  -- let _ = Debug.log "Duplicate Ids" duplicateIds in
  -- let _ = Debug.log "All Ids" allIds in
  let idsToPreserve = Set.diff allIds duplicateIds in
  -- let _ = Debug.log "Ids to preserve" idsToPreserve in
  let result = Tuple.first (freshenPreserving idsToPreserve initK e) in
  -- let _ = Debug.log ("Freshened result:\n" ++ LangUnparser.unparseWithIds result) () in
  result

-- Overwrite any existing EId's/locId's
freshenClean : Int -> Exp -> (Exp, Int)
freshenClean initK e = freshenPreserving Set.empty initK e

-- Reassign any id not in idsToPreserve
freshenPreserving : Set.Set Int -> Int -> Exp -> (Exp, Int)
freshenPreserving idsToPreserve initK e =
  let getId k =
    if Set.member k idsToPreserve
    then getId (k+1)
    else k
  in
  let assignIds exp k =
    let e__ = exp.val.e__ in
    let (newE__, newK) =
      case e__ of
        EConst ws n (locId, frozen, ident) wd ->
          if Set.member locId idsToPreserve then
            (e__, k)
          else
            let locId = getId k in
            (EConst ws n (locId, frozen, ident) wd, locId + 1)

        ELet ws1 kind b p e1 e2 ws2 ->
          let newE1 = recordIdentifiers (p, e1) in
          (ELet ws1 kind b p newE1 e2 ws2, k)

        _ ->
          (e__, k)
    in
    if Set.member exp.val.eid idsToPreserve then
      (replaceE__ exp newE__, newK)
    else
      let eid = getId newK in
      (WithInfo (Exp_ newE__ eid) exp.start exp.end, eid + 1)
  in
  mapFoldExp assignIds initK e

allIds : Exp -> Set.Set Int
allIds exp = duplicateAndAllIds exp |> Tuple.first

-- Excludes EIds and locIds less than initK (i.e. no prelude locs or dummy EIds)
duplicateAndAllIds : Exp -> (Set.Set Int, Set.Set Int)
duplicateAndAllIds exp =
  let gather exp (duplicateIds, seenIds) =
    let eid = exp.val.eid in
    let (duplicateIds_, seenIds_) =
      if eid >= initK then
        if Set.member eid seenIds
        then (Set.insert eid duplicateIds, seenIds)
        else (duplicateIds, Set.insert eid seenIds)
      else
        (duplicateIds, seenIds)
    in
    case exp.val.e__ of
      EConst ws n (locId, frozen, ident) wd ->
        if locId >= initK then
          if Set.member locId seenIds
          then (Set.insert locId duplicateIds_, seenIds_)
          else (duplicateIds_, Set.insert locId seenIds_)
        else
          (duplicateIds_, seenIds_)

      _ ->
        (duplicateIds_, seenIds_)
  in
  let (duplicateIds, seenIds) =
    foldExp
        gather
        (Set.empty, Set.empty)
        exp
  in
  (duplicateIds, seenIds)


preludeSubst = substPlusOf_ Dict.empty prelude

substPlusOf : Exp -> SubstPlus
substPlusOf e =
  substPlusOf_ preludeSubst e

substOf : Exp -> Subst
substOf = Dict.map (always .val) << substPlusOf

substStrOf : Exp -> SubstStr
substStrOf = Dict.map (always toString) << substOf


-- Record the primary identifier in the EConsts_ Locs, where appropriate.
recordIdentifiers : (Pat, Exp) -> Exp
recordIdentifiers (p,e) =
 let ret e__ = WithInfo (Exp_ e__ e.val.eid) e.start e.end in
 case (p.val, e.val.e__) of

  -- (PVar _ x _, EConst ws n (k, b, "") wd) -> ret <| EConst ws n (k, b, x) wd
  (PVar _ x _, EConst ws n (k, b, _) wd) -> ret <| EConst ws n (k, b, x) wd

  (PList _ ps _ mp _, EList ws1 es ws2 me ws3) ->
    case U.maybeZip ps es of
      Nothing  -> ret <| EList ws1 es ws2 me ws3
      Just pes -> let es_ = List.map recordIdentifiers pes in
                  let me_ =
                    case (mp, me) of
                      (Just p1, Just e1) -> Just (recordIdentifiers (p1,e1))
                      _                  -> me in
                  ret <| EList ws1 es_ ws2 me_ ws3

  (PAs _ _ _ p_, _) -> recordIdentifiers (p_,e)

  (_, EColonType ws1 e1 ws2 t ws3) ->
    ret <| EColonType ws1 (recordIdentifiers (p,e1)) ws2 t ws3

  (_, e__) -> ret e__

-- this will be done while parsing eventually...

substPlusOf_ : SubstPlus -> Exp -> SubstPlus
substPlusOf_ substPlus exp =
  let accumulator e s =
    case e.val.e__ of
      EConst _ n (locId,_,_) _ ->
        case Dict.get locId s of
          Nothing ->
            Dict.insert locId { e | val = n } s
          Just existing ->
            if n == existing.val then s else Debug.crash <| "substPlusOf_ Constant: " ++ (toString n)
      _ -> s
  in
  foldExp accumulator substPlus exp
