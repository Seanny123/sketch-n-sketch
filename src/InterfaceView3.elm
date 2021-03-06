module InterfaceView3 exposing (view)

-- Sketch-n-Sketch Libraries ---------------------------------------------------

import Config exposing (params) -- TODO remove
import ExamplesGenerated as Examples
import Utils
import HtmlUtils exposing (handleEventAndStop)
import Either exposing (..)
import Lang

import InterfaceModel as Model exposing
  ( Msg(..), Model, Tool(..), ShapeToolKind(..), Mode(..)
  , ReplicateKind(..), LambdaTool(..)
  , Caption(..), MouseMode(..)
  , runAndResolve, mkLive_
  , DialogBox(..)
  , SynthesisResult(..)
  )
import InterfaceController as Controller
import Layout
import Canvas
import LangUnparser exposing (unparse)
import LangSvg exposing (attr)
import LangTools
import Sync
import DependenceGraph
import CodeMotion
import DeuceWidgets exposing (..) -- TODO

-- Elm Libraries ---------------------------------------------------------------

import Set
import Dict
import Regex

import Svg exposing (Svg)
import Svg.Events exposing (onMouseDown, onMouseUp, onMouseOver, onMouseOut)
import Html exposing (Html)
import Html.Attributes as Attr
import Html.Events exposing
  ( onClick, onInput, on, onMouseEnter, onMouseLeave
  , onWithOptions, defaultOptions
  )
import Html.Lazy
import Json.Decode


--------------------------------------------------------------------------------

pixels n = toString n ++ "px"
unpixels str = Result.withDefault 0 <| String.toFloat (String.dropRight 2 str)

imgPath s = "img/" ++ s


--------------------------------------------------------------------------------
-- Configuration Parameters

showRawShapeTools = False


--------------------------------------------------------------------------------
-- Top-Level View Function

view : Model -> Html Msg
view model =
  let layout = Layout.computeLayout model in

  let fileTools = fileToolBox model layout in
  let codeTools = codeToolBox model layout in
  let drawTools = drawToolBox model layout in
  let stretchyDrawTools = stretchyDrawToolBox model layout in
  let lambdaDrawTools = lambdaDrawToolBoxWithIcons model layout in
  let attributeTools = attributeToolBox model layout in
  let blobTools = blobToolBox model layout in
  let moreBlobTools = moreBlobToolBox model layout in
  let outputTools = outputToolBox model layout in
  let (deuceWidgets, extremePoint) = deuceLayer model layout in
  let maybeNotPinnedAnchor = addSomeOffsetToExtremePoint extremePoint in
  let deuceTools = deuceToolBoxNested model layout maybeNotPinnedAnchor in
  let textTools = textToolBox model layout maybeNotPinnedAnchor in
  let synthesisResultsSelect = synthesisResultsSelectBox model layout in

  let
    dialogBoxes =
      [ fileNewDialogBox model
      , fileSaveAsDialogBox model
      , fileOpenDialogBox model
      , alertSaveDialogBox model
      , importCodeDialogBox model
      ]
  in

  let
    needsSaveString =
      if model.needsSave then
        "true"
      else
        "false"
    onbeforeunloadDataElement =
      Html.input
        [ Attr.type_ "hidden"
        , Attr.id "onbeforeunload-data"
        , Attr.attribute "data-needs-save" needsSaveString
        , Attr.attribute "data-filename" (Model.prettyFilename model)
        ]
        []
  in

  let animationTools =
    if model.slideCount > 1 || model.movieCount > 1
    then [ animationToolBox model layout ]
    else [] in

  let synthesisResultsSelect =
    if List.length model.synthesisResults > 0
    then [ synthesisResultsSelectBox model layout ]
    else [] in

  let codeBox =
    if model.basicCodeBox
      then basicCodeBox model layout.codeBox
      else aceCodeBox model layout.codeBox in

  let outputBox = outputArea model layout in

  let resizeCodeBox =
    resizeWidget "resizeCodeBox" model layout Layout.getPutCodeBox
       (layout.codeBox.left + layout.codeBox.width)
       (layout.codeBox.top + layout.codeBox.height) in

  let resizeCanvas =
    resizeWidget "resizeCanvas" model layout Layout.getPutCanvas
       layout.canvas.left
       layout.canvas.top in

  let caption = captionArea model layout in

  let everything = -- z-order in decreasing order
     -- bottom-most
     [ onbeforeunloadDataElement
     , codeBox
     , deuceWidgets
     , outputBox

     -- toolboxes in reverse order
     , outputTools] ++ animationTools ++

     (if model.showOnlyBasicTools then [] else
       [ moreBlobTools
       , blobTools
       , attributeTools
       , lambdaDrawTools
       , stretchyDrawTools
       ]
     ) ++

     [ drawTools
     , textTools, deuceTools
     , codeTools, fileTools
     ] ++ synthesisResultsSelect ++

     -- top-most
     [ resizeCodeBox
     , resizeCanvas
     -- , caption
     ] ++ dialogBoxes
  in

  Html.div
    [ Attr.id "containerDiv"
    , Attr.style
        [ ("position", "fixed")
        , ("width", pixels model.dimensions.width)
        , ("height", pixels model.dimensions.height)
        , ("background", "white")
        ]
    ]
    everything

--------------------------------------------------------------------------------
-- Tool Boxes

fileToolBox model layout =
  let icon =
     Html.img
       [ Attr.src "img/light_logo.svg"
       , Attr.title <| "Sketch-n-Sketch " ++ params.strVersion
       , Attr.style
           [ ("width", pixels (Layout.buttonHeight - 5))
           , ("height", pixels (Layout.buttonHeight - 5))
           , ("vertical-align", "middle")
           ]
       ] []
  in
  toolBox model "fileToolBox" [] Layout.getPutFileToolBox layout.fileTools
    [ icon
    , fileIndicator model
    , fileNewDialogBoxButton
    , fileSaveAsDialogBoxButton
    , fileSaveButton model
    , fileOpenDialogBoxButton
    , exportCodeButton
    , exportSvgButton
    , importCodeButton
    , importSvgButton
    ]

codeToolBox model layout =
  toolBox model "codeToolBox" [] Layout.getPutCodeToolBox layout.codeTools
    [ runButton
    , undoButton model
    , redoButton model
    , cleanButton model
    ]

drawToolBox model layout =
  toolBox model "drawToolBox" [] Layout.getPutDrawToolBox layout.drawTools
    [ toolButton model Cursor
    -- , toolButton model PointOrOffset
    , toolButton model Text
    , toolButton model (Line Raw)
    , toolButton model (Rect Raw)
    , toolButton model (Oval Raw)
    , toolButton model (Poly Raw)
    , toolButton model (Path Raw)
    ]

stretchyDrawToolBox model layout =
  toolBox model "stretchyDrawToolBox" [] Layout.getPutDrawToolBox layout.stretchyDrawTools
    [ toolButton model (Rect Stretchy)
    , toolButton model (Oval Stretchy)
    , toolButton model (Poly Stretchy)
    , toolButton model (Path Stretchy)
    ]

{-
lambdaDrawToolBox model layout =
  toolBox model "lambdaDrawToolBox" [] Layout.getPutDrawToolBox layout.lambdaDrawTools
    [ toolButton model Lambda
    , dropdownLambdaTool model
    ]
-}

attributeToolBox model layout =
  toolBox model "attributeToolBox" [] Layout.getPutAttributeToolBox layout.attributeTools
    [ relateButton model "Dig Hole" Controller.msgDigHole
    , relateButton model "Make Equal" Controller.msgMakeEqual
    , relateButton model "Relate" Controller.msgRelate
    , relateButton model "Indexed Relate" Controller.msgIndexedRelate
    ]

textToolBox model layout maybeNotPinnedAnchor =
  toolBox model "textToolBox" [] Layout.getPutTextToolBox layout.textTools
    [ fontSizeButton model
    , pinButton model layout maybeNotPinnedAnchor
    ]

blobToolBox model layout =
  toolBox model "blobToolBox" [] Layout.getPutBlobToolBox layout.blobTools
    [ groupButton model "Dupe" Controller.msgDuplicateBlobs True
    , groupButton model "Merge" Controller.msgMergeBlobs True
    , groupButton model "Group" Controller.msgGroupBlobs False
    , groupButton model "Abstract" Controller.msgAbstractBlobs True
    ]

moreBlobToolBox model layout =
  toolBox model "moreBlobToolBox" [] Layout.getPutMoreBlobToolBox layout.moreBlobTools
    [ groupButton model "Repeat Right" (Controller.msgReplicateBlob HorizontalRepeat) True
    , groupButton model "Repeat To" (Controller.msgReplicateBlob LinearRepeat) True
    , groupButton model "Repeat Around" (Controller.msgReplicateBlob RadialRepeat) True
    ]

outputToolBox model layout =
  toolBox model "outputToolBox" [] Layout.getPutOutputToolBox layout.outputTools
    [ -- codeBoxButton model
      heuristicsButton model
    , outputButton model
    , ghostsButton model
    , autoSynthesisButton model
    , showOnlyBasicsButton model
    ]

animationToolBox model layout =
  toolBox model "animationToolBox" [] Layout.getPutAnimationToolBox layout.animationTools
    [ previousSlideButton model
    , previousMovieButton model
    , pauseResumeMovieButton model
    , nextMovieButton model
    , nextSlideButton model
    ]

synthesisResultsSelectBox model layout =
  let desc description exp isSafe sortKey =
    (if isSafe then "" else "[UNSAFE] ") ++
    (Regex.replace Regex.All (Regex.regex "^Original -> | -> Cleaned$") (\_ -> "") description) ++
    " (" ++ toString (LangTools.nodeCount exp) ++ ")" ++ " " ++ toString sortKey
  in
  let extraButtonStyles =
    Attr.style
        [ ("width", "100%")
        , ("text-align", "left")
        , ("padding-top", "8px")
        , ("padding-bottom", "8px")
        ]
  in
  let cancelButton =
    htmlButtonExtraAttrs [extraButtonStyles, Attr.style [("text-align", "center")]] "Cancel" (Controller.msgClearSynthesisResults) Regular False
  in
  let extraStyles =
    [ ("display", "block")
    ]
  in
  let resultButtonList priorPathByIndices remainingPathByIndices results =
    let buttons =
      results
      |> Utils.mapi0
          (\(i, Model.SynthesisResult {description, exp, isSafe, sortKey, children}) ->
            let thisElementPath = priorPathByIndices ++ [i] in
            let (isHovered, nextMenu) =
              case remainingPathByIndices of
                nexti::is ->
                  if i == nexti then
                    case children of
                      Just childResults -> (True, [resultButtonList thisElementPath is childResults])
                      Nothing           -> (True, [])
                  else
                    (False, [])
                [] ->
                  (False, [])
            in
            nextMenu ++
            [ htmlButtonExtraAttrs
                  [ extraButtonStyles
                  , Attr.style [("background-color", if isHovered then buttonSelectedColor else buttonRegularColor)]
                  , Html.Events.onMouseEnter (Controller.msgHoverSynthesisResult thisElementPath)
                  , Html.Events.onMouseLeave (Controller.msgHoverSynthesisResult [])
                  ]
                  (desc description exp isSafe sortKey)
                  (Controller.msgSelectSynthesisResult exp)
                  Regular
                  False
            ]
          )
      |> List.concat
    in
    Html.div
        [ Attr.style <|
          [ ("position", if priorPathByIndices == [] then "relative" else "absolute")
          -- , ("max-height", "325px")
          , ("width", "325px")
          , ("overflow", "visible")
          -- , ("overflow-y", "auto")
          , ("left", if priorPathByIndices == [] then "0" else "-325px")
          ]
        ]
        buttons
  in
  let resultsMenuTree =
    resultButtonList [] model.hoveredSynthesisResultPathByIndices model.synthesisResults
  in
  toolBox model "synthesisResultsSelect" extraStyles Layout.getPutSynthesisResultsSelectBox layout.synthesisResultsSelect [resultsMenuTree, cancelButton]

-- Make Tool Box Helper
toolBox model id extraStyles (getOffset, putOffset) leftRightTopBottom elements =
  Html.div
    [ Attr.id id
    -- , Attr.title id
    , Attr.style <|
        [ ("position", "fixed")
        , ("padding", "0px 0px 0px 15px")
        , ("background", Layout.strInterfaceColor) -- "#444444")
        , ("border-radius", "10px 0px 0px 10px")
        , ("box-shadow", "6px 6px 3px #888888")
        , ("cursor", "move")
        ] ++ extraStyles ++ Layout.fixedPosition leftRightTopBottom
    , onMouseDown <| Layout.dragLayoutWidgetTrigger (getOffset model) putOffset
    ]
    elements


--------------------------------------------------------------------------------
-- Code Box

aceCodeBox model dim =
  Html.div
    [ Attr.id "editor"
    -- parent div as relative to have hover div on top
    , Attr.style [ ("position", "relative")
                 , ("width", pixels dim.width)
                 , ("height", pixels dim.height)
                 , ("left", pixels dim.left)
                 , ("top", pixels dim.top)
                 , ("pointer-events", "auto")
                 , ("z-index", "-1")
                 ]
    , onMouseEnter Controller.msgMouseEnterCodeBox
    , onMouseLeave Controller.msgMouseLeaveCodeBox
    , onClick Controller.msgMouseClickCodeBox
    ]
    [ ]
    {- Html.Lazy.lazy ... -}

basicCodeBox model dim =
  textArea (Model.codeToShow model) <|
    [ onInput Controller.msgCodeUpdate
    , Attr.style [ ("width", pixels dim.width)
                 ]
    ]

textArea text attrs =
  textArea_ [Html.text text] attrs

textArea_ children attrs =
  let innerPadding = 4 in
  -- NOTE: using both Attr.value and Html.text seems to allow read/write...
  let commonAttrs =
    [ Attr.spellcheck False
    , Attr.style
        [ ("font-family", params.mainSection.codebox.font)
        , ("font-size", params.mainSection.codebox.fontSize)
        , ("whiteSpace", "pre")
        , ("height", "100%")
        , ("resize", "none")
        , ("overflow", "auto")
        , ("border-radius", "0px 10px 10px 10px") -- like outputArea
        -- Horizontal Scrollbars in Chrome
        , ("word-wrap", "normal")
        -- , ("background-color", "whitesmoke")
        , ("background-color", "white")
        , ("padding", toString innerPadding ++ "px")
        -- Makes the 100% for width/height work as intended
        , ("box-sizing", "border-box")
        ]
    ]
  in
  Html.div (commonAttrs ++ attrs) children


--------------------------------------------------------------------------------
-- Output Box

outputArea model layout =
  let output =
    case (model.errorBox, model.mode, model.preview) of

      (_, _, Just (_, Err errorMsg)) ->
        textArea errorMsg
          [ Attr.style [ ("width", pixels layout.canvas.width) ] ]

      (Just errorMsg, _, Nothing) ->
        textArea errorMsg
          [ Attr.style [ ("width", pixels layout.canvas.width) ] ]

      (Nothing, Print svgCode, Nothing) ->
        textArea svgCode
          [ Attr.style [ ("width", pixels layout.canvas.width) ] ]

      (_, _, Just (_, Ok _)) ->
        Canvas.build layout.canvas.width layout.canvas.height model

      (Nothing, Live _, Nothing) ->
        Canvas.build layout.canvas.width layout.canvas.height model

      (Nothing, PrintScopeGraph maybeImageData, Nothing) ->
        let srcAttr =
          case maybeImageData of
            Nothing   -> []
            Just data -> [Attr.src data]
        in
        textArea_
          [ Html.img (srcAttr ++
              [ Attr.alt "Dot rendering should appear here..."
              , Attr.style [ ("max-width", pixels layout.canvas.width)
                           , ("max-height", pixels layout.canvas.height) ]
              ]) []
          , Html.br [] [], Html.br [] []
          , DependenceGraph.printHtml model.scopeGraph
          ]
          [ Attr.style [ ("width", pixels layout.canvas.width) ] ]

  in
  let (border, boxShadow) =
    if Model.needsRun model
      then ("2px solid rgba(220,20,60,1)", "10px 10px 5px rgba(220,20,60,0.3)")
      else (params.mainSection.canvas.border, "10px 10px 5px #888888")
  in
  Html.div
     [ Attr.id "outputArea"
     , Attr.style
         [ ("width", pixels layout.canvas.width)
         , ("height", pixels layout.canvas.height)
         , ("position", "fixed")
         , ("border", border)
         , ("left", pixels layout.canvas.left)
         , ("top", pixels layout.canvas.top)
         , ("background", "white")
         , ("border-radius", "0px 10px 10px 10px")
         , ("box-shadow", boxShadow)
         , ("-ms-user-select", "none")
         , ("-moz-user-select", "none")
         , ("-webkit-user-select", "none")
         , ("user-select", "none")
         ]
     ]
     [ output ]


--------------------------------------------------------------------------------
-- Resizing Widgets

rResizeWidgetBall = 5

resizeWidget id model layout (getOffset, putOffset) left top =
  Svg.svg
    [ Attr.id id
    , Attr.style
        [ ("position", "fixed")
        , ("left", pixels (left - 2 * rResizeWidgetBall))
        , ("top", pixels (top - 2 * rResizeWidgetBall))
        , ("width", pixels (4 * rResizeWidgetBall))
        , ("height", pixels (4 * rResizeWidgetBall))
        ]
    ]
    [ flip Svg.circle [] <|
        [ attr "stroke" "black" , attr "stroke-width" "2px"
        , attr "fill" Layout.strButtonTopColor
        , attr "r" (pixels rResizeWidgetBall)
        , attr "cx" (toString (2 * rResizeWidgetBall))
        , attr "cy" (toString (2 * rResizeWidgetBall))
        , attr "cursor" "move"
        , onMouseDown <| Layout.dragLayoutWidgetTrigger (getOffset model) putOffset
        ]
    ]


--------------------------------------------------------------------------------
-- Buttons

type ButtonKind = Regular | Selected | Unselected

buttonRegularColor = "white"
buttonSelectedColor = "lightgray"

htmlButton text onClickHandler btnKind disabled =
  htmlButtonExtraAttrs [] text onClickHandler btnKind disabled

htmlButtonExtraAttrs extraAttrs text onClickHandler btnKind disabled =
  let color =
    case btnKind of
      Regular    -> buttonRegularColor
      Unselected -> buttonRegularColor
      Selected   -> buttonSelectedColor
  in
  -- let lineHeight = 1 + 1.1735 * unpixels params.mainSection.widgets.fontSize |> ((*) 2) |> round |> toFloat |> ((*) 0.5) in -- My best guess based on sampling Firefox's behavior.
  let commonAttrs =
    [ Attr.disabled disabled
    , Attr.style [ ("font", params.mainSection.widgets.font)
                 , ("fontSize", params.mainSection.widgets.fontSize)
                 , ("box-sizing", "border-box") -- Strangely, Firefox and Chrome on Mac differ on this default.
                 , ("min-height", pixels Layout.buttonHeight)
                 , ("background", color)
                 , ("cursor", "pointer")
                 , ("-ms-user-select", "none")
                 , ("-moz-user-select", "none")
                 , ("-webkit-user-select", "none")
                 , ("user-select", "none")
                 ] ]
  in
  Html.button
    (commonAttrs ++
      [ handleEventAndStop "mousedown" Controller.msgNoop
      , onClick onClickHandler
      ] ++
      extraAttrs)
    [ Html.text text ]

iconButton model iconName onClickHandler btnKind disabled =
  iconButtonExtraAttrs model iconName [] onClickHandler btnKind disabled

iconButtonExtraAttrs model iconName extraAttrs onClickHandler btnKind disabled =
  let
    color =
      case btnKind of
        Regular    -> buttonRegularColor
        Unselected -> buttonRegularColor
        Selected   -> buttonSelectedColor
    iconHtml =
      case Dict.get (Utils.naturalToCamelCase iconName) model.icons of
        Just h -> h
        Nothing -> Html.text ""
  in
  let commonAttrs =
    [ Attr.disabled disabled
    , Attr.style [ ("font", params.mainSection.widgets.font)
                 , ("fontSize", params.mainSection.widgets.fontSize)
                 , ("height", pixels Layout.iconButtonHeight)
                 , ("background", color)
                 , ("cursor", "pointer")
                 , ("-ms-user-select", "none")
                 , ("-moz-user-select", "none")
                 , ("-webkit-user-select", "none")
                 , ("user-select", "none")
                 ] ]
  in
  Html.button
    (commonAttrs ++
      [ handleEventAndStop "mousedown" Controller.msgNoop
      , onClick onClickHandler
      , Attr.title iconName
      ] ++
      extraAttrs)
    [ iconHtml ]

runButton =
  htmlButton "Run" Controller.msgRun Regular False

cleanButton model =
  let disabled =
    case model.mode of
      Live _ -> False
      _      -> True
  in
  htmlButton "Clean Up" Controller.msgCleanCode Regular disabled

undoButton model =
  let past = Tuple.first model.history in
  let extraAttrs =
    case past of
      _ :: prevCode :: _ ->
        [ Html.Events.onMouseEnter (Controller.msgPreview (Right prevCode))
        , Html.Events.onMouseLeave Controller.msgClearPreview ]
      _ ->
       []
  in
  htmlButtonExtraAttrs extraAttrs
    "Undo" Controller.msgUndo Regular (List.length past <= 1)

redoButton model =
  let future = Tuple.second model.history in
  let extraAttrs =
    case future of
      futureCode :: _ ->
        [ Html.Events.onMouseEnter (Controller.msgPreview (Right futureCode))
        , Html.Events.onMouseLeave Controller.msgClearPreview ]
      _ ->
       []
  in
  htmlButtonExtraAttrs extraAttrs
    "Redo" Controller.msgRedo Regular (List.length future == 0)

heuristicsButton model =
  let foo old =
    let so = old.syncOptions in
    let so_ = { so | feelingLucky = Sync.toggleHeuristicMode so.feelingLucky } in
    case old.mode of
      Live _ ->
        case mkLive_ so_ old.slideNumber old.movieNumber old.movieTime old.inputExp of
          Ok m_ -> { old | syncOptions = so_, mode = m_ }
          Err s -> { old | syncOptions = so_, errorBox = Just s }
      _ -> { old | syncOptions = so_ }
  in
  let yesno =
    let hm = model.syncOptions.feelingLucky in
    if hm == Sync.heuristicsNone then "None"
    else if hm == Sync.heuristicsFair then "Fair"
    else "Biased"
  in
  htmlButton ("[Heuristics] " ++ yesno)
    (Msg "Toggle Heuristics" foo) Regular False

outputButton model =
  let cap =
     case model.mode of
       Print _ -> "[Out] SVG"
       Live _  -> "[Out] Canvas"
       PrintScopeGraph _ -> "[Out] Scope Graph"
  in
  htmlButton cap Controller.msgToggleOutput Regular False

ghostsButton model =
  let cap =
     case model.showGhosts of
       True  -> "[Ghosts] Shown"
       False -> "[Ghosts] Hidden"
  in
  let foo old =
    let showGhosts_ = not old.showGhosts in
    let mode_ =
      case old.mode of
        Print _ -> Print (LangSvg.printSvg showGhosts_ old.slate)
        _       -> old.mode
    in
    { old | showGhosts = showGhosts_, mode = mode_ }
  in
  htmlButton cap (Msg "Toggle Ghosts" foo) Regular False

autoSynthesisButton model =
  let cap =
     case model.autoSynthesis of
       True  -> "[Auto-Search] On"
       False -> "[Auto-Search] Off"
  in
  htmlButton cap
    (Msg "Toggle Auto-Search" (\m -> { m | autoSynthesis = not m.autoSynthesis }))
    Regular False

codeBoxButton model =
  let text = "[Code Box] " ++ if model.basicCodeBox then "Basic" else "Fancy" in
  htmlButton text Controller.msgToggleCodeBox Regular False

toolButton model tool =
  let capStretchy s = if showRawShapeTools then "BB" else s in
  let capSticky = Utils.uniPlusMinus in -- Utils.uniDelta in
  let capRaw = "(Raw)" in
  let cap = case tool of
    Cursor        -> "Cursor"
    Line Raw      -> "Line"
    Rect Raw      -> "Rect"
    Rect Stretchy -> capStretchy "Rect" -- "Box"
    Oval Raw      -> "Ellipse"
    Oval Stretchy -> capStretchy "Ellipse" -- "Oval"
    Poly Raw      -> "Polygon"
    Poly Stretchy -> capStretchy "Polygon"
    Poly Sticky   -> capSticky
    Path Raw      -> "Path"
    Path Stretchy -> capStretchy "Path"
    Path Sticky   -> capSticky
    Text          -> "Text"
    HelperLine    -> "(Rule)"
    PointOrOffset -> "Point Or Offset"
    Lambda _      -> "Lambda" -- Utils.uniLambda
    _             -> Debug.crash ("toolButton: " ++ toString tool)
  in
  -- TODO temporarily disabling a couple tools
  let (btnKind, disabled) =
    case (model.tool == tool, tool) of
      (True, _)            -> (Selected, False)
      (False, Path Sticky) -> (Regular, True)
      (False, _)           -> (Unselected, False)
  in
  --htmlButton cap (Msg cap (\m -> { m | tool = tool })) btnKind disabled
  iconButton model cap (Msg cap (\m -> { m | tool = tool })) btnKind disabled

relateButton model text handler =
  let noFeatures = Set.isEmpty model.selectedFeatures in
  htmlButton text handler Regular noFeatures

groupButton model text handler disallowSelectedFeatures =
  let noFeatures = Set.isEmpty model.selectedFeatures in
  let noBlobs = Dict.isEmpty model.selectedBlobs in
  htmlButton text handler Regular
    (noBlobs || (disallowSelectedFeatures && (not noFeatures)))

previousSlideButton model =
  htmlButton "◀◀" Controller.msgPreviousSlide Regular
    (model.slideNumber == 1 && model.movieNumber == 1)

nextSlideButton model =
  htmlButton "▶▶" Controller.msgNextSlide Regular
    (model.slideNumber == model.slideCount
      && model.movieNumber == model.movieCount)

previousMovieButton model =
  htmlButton "◀" Controller.msgPreviousMovie Regular
    (model.slideNumber == 1 && model.movieNumber == 1)

nextMovieButton model =
  htmlButton "▶" Controller.msgNextMovie Regular
    (model.slideNumber == model.slideCount
      && model.movieNumber == model.movieCount)

pauseResumeMovieButton model =
  let enabled = model.movieTime < model.movieDuration in
  let caption =
    if enabled && not model.runAnimation then "Play"
    else "Pause"
  in
  htmlButton caption Controller.msgPauseResumeMovie Regular (not enabled)

fileNewDialogBoxButton =
  htmlButton "New" (Controller.msgOpenDialogBox New) Regular False

fileSaveAsDialogBoxButton =
  htmlButton "Save As" (Controller.msgOpenDialogBox SaveAs) Regular False

fileSaveButton model =
  htmlButton "Save" Controller.msgSave Regular (not model.needsSave)

fileOpenDialogBoxButton =
  htmlButton "Open" (Controller.msgOpenDialogBox Open) Regular False

closeDialogBoxButton db model =
  htmlButton
    "X"
    (Controller.msgCloseDialogBox db)
    Regular
    (Model.isDialogBoxShowing AlertSave model)

exportCodeButton =
  htmlButton "Export Code" Controller.msgExportCode Regular False

importCodeButton =
    htmlButton "Import Code" (Controller.msgOpenDialogBox ImportCode) Regular False

exportSvgButton =
  htmlButton "Export SVG" Controller.msgExportSvg Regular False

importSvgButton =
   htmlButton "Import SVG" Controller.msgNoop Regular True

-- autosaveButton model =
--     let cap = case model.autosave of
--       True  -> "[Autosave] Yes"
--       False -> "[Autosave] No"
--     in
--       htmlButton cap Controller.msgToggleAutosave Regular True

fontSizeButton model =
  let cap = "Font Size " ++ Utils.bracks (toString model.codeBoxInfo.fontSize) in
  let msg = Msg "Update Font Size" <| \m ->
    let codeBoxInfo = m.codeBoxInfo in
    let (minSize, maxSize) = (10, 24) in
    let fontSize =
      if codeBoxInfo.fontSize + 2 <= maxSize
        then codeBoxInfo.fontSize + 2
        else minSize
    in
    { m | codeBoxInfo = { codeBoxInfo | fontSize = fontSize } }
  in
  htmlButton cap msg Regular False

showOnlyBasicsButton model =
  let cap = "[Tools] " ++ (if model.showOnlyBasicTools then "Basics" else "All") in
  let foo m = { m | showOnlyBasicTools = not m.showOnlyBasicTools } in
  htmlButton cap (Msg "Toggle Ghosts" foo) Regular False

{-
deuceWidgetsButton model =
  let text =
    if model.showAllDeuceWidgets
      then "[Show Widgets] Always"
      else "[Show Widgets] On Shift" in
  let handler = Msg "Toggle Ace Deuce" <| \m ->
    if m.showAllDeuceWidgets then
      { m | showAllDeuceWidgets = not m.showAllDeuceWidgets
            -- TODO: factor these three elsewhere for reuse
          , selectedEIds = Set.empty
          , selectedExpTargets = Set.empty
          , selectedPats = Set.empty
          , selectedPatTargets = Set.empty
          }
    else { m | showAllDeuceWidgets = not m.showAllDeuceWidgets }
  in
  htmlButton text handler Regular False
-}

{-
deuceMoveExpButton model =
  htmlButton "Move Exp" Controller.msgMoveExp Regular (not model.showAllDeuceWidgets)
-}


--------------------------------------------------------------------------------
-- Lambda Tool Dropdown Menu

{-
dropdownLambdaTool model =
  let options =
    let (selectedIdx, exps) = model.lambdaTools in
    Utils.mapi1 (\(i,lambdaTool) ->
      let s = strLambdaTool lambdaTool in
      Html.option
         [ Attr.value s, Attr.selected (i == selectedIdx) ]
         [ Html.text s ]
      ) exps
  in
  let handler selected =
    Msg "Select Lambda Option" <| \model ->
      let (_, exps) = model.lambdaTools in
      let indexedStrings = Utils.mapi1 (\(i,lt) -> (i, strLambdaTool lt)) exps in
      let newSelectedIdx =
        case Utils.findFirst ((==) selected << Tuple.second) indexedStrings of
          Just (i, _) -> i
          Nothing     -> Debug.crash "dropdownLambdaTools"
      in
      { model | tool = Lambda, lambdaTools = (newSelectedIdx, exps) }
  in
  Html.select
    [ on "change" (Json.Decode.map handler Html.Events.targetValue)
    , handleEventAndStop "mousedown" Controller.msgNoop
        -- to prevent underlying toolBox from starting dragLayoutWidgetTrigger
    , Attr.style
        [ ("pointer-events", "auto")
        , ("border", "0 solid")
        , ("width", "140px")
        , ("height", pixels Layout.buttonHeight)
        , ("font-family", params.mainSection.widgets.font)
        , ("font-size", params.mainSection.widgets.fontSize)

        -- https://stackoverflow.com/questions/24210132/remove-border-radius-from-select-tag-in-bootstrap-3
        , ("outline", "1px solid #CCC")
        , ("outline-offset", "-1px")
        , ("background-color", "white")
        ]
    ]
    options
-}

lambdaDrawToolBoxWithIcons model layout =
  let buttons =
    Utils.mapi1 (\(i, lambdaTool) ->
      let iconName = Model.strLambdaTool lambdaTool in
      iconButton model iconName
        (Msg iconName (\m -> { m | tool = Lambda i }))
        (if model.tool == Lambda i then Selected else Unselected)
        False
      ) model.lambdaTools
  in
  toolBox model "lambdaDrawToolBox" []
    Layout.getPutDrawToolBox layout.lambdaDrawTools
    buttons


--------------------------------------------------------------------------------
-- Hover Caption

captionArea model layout =
  let (text, color) =
    case (model.caption, model.mode, model.mouseMode) of
      (Just (Hovering zoneKey), Live info, MouseNothing) ->
        case Sync.hoverInfo zoneKey info of
          (line1, Nothing) ->
            (line1 ++ " (INACTIVE)", "red")
          (line1, Just line2) ->
            (line1 ++ " (ACTIVE)\n" ++ line2, "green")

      (Just (LangError err), _, _) ->
        (err, "black")

      _ ->
        if model.slideCount > 1 then
          let
            s1 = toString model.slideNumber ++ "/" ++ toString model.slideCount
            s2 = toString model.movieNumber ++ "/" ++ toString model.movieCount
            s3 = truncateFloat model.movieTime ++ "/" ++ truncateFloat model.movieDuration
          in
          (Utils.spaces ["Slide", s1, ":: Movie", s2, ":: Time", s3], "black")

        else
          ("", "white")

  in
  Html.span
    [ Attr.id "captionArea"
    , Attr.style <|
        [ ("color", color)
        , ("position", "fixed")
        ] ++ Layout.fixedPosition layout.captionArea
    ]
    [ Html.text text ]

truncateFloat : Float -> String
truncateFloat n =
  case String.split "." (toString n) of
    [whole]           -> whole ++ "." ++ String.padRight 1 '0' ""
    [whole, fraction] -> whole ++ "." ++ String.left 1 (String.padRight 1 '0' fraction)
    _                 -> Debug.crash "truncateFloat"

--------------------------------------------------------------------------------
-- Dialog Boxes

dialogBox
  zIndex
  width
  height
  closable
  db
  model
  headerStyles
  headerElements
  parentStyles
  elements =
    let
      closeButton =
        if closable then
          [ closeDialogBoxButton db model ]
        else
          []
      displayStyle =
        if (Model.isDialogBoxShowing db model) then
          "flex"
        else
          "none"
    in
      Html.div
        [ Attr.style
            [ ("position", "fixed")
            , ("top", "50%")
            , ("left", "50%")
            , ("width", width)
            , ("height", height)
            , ("font-family", "sans-serif")
            , ("background-color", "#F8F8F8")
            , ("border", "2px solid " ++ Layout.strInterfaceColor)
            , ("border-radius", "10px")
            , ("box-shadow", "0 0 10px 0 #888888")
            , ("transform", "translateY(-50%) translateX(-50%)")
            , ("margin", "auto")
            , ("z-index", zIndex)
            , ("display", displayStyle)
            , ("flex-direction", "column")
            ]
        ] <|
        [ Html.h2
            [ Attr.style <|
                [ ("margin", "0")
                , ("padding", "0 20px")
                , ("border-bottom", "1px solid black")
                , ("flex", "0 0 60px")
                , ("display", "flex")
                , ("justify-content", "space-between")
                , ("align-items", "center")
                ] ++ headerStyles
            ] <|
            [ Html.div [] headerElements
            , Html.div [] closeButton
            ]
        , Html.div
            [ Attr.style <|
                [ ("overflow", "scroll")
                , ("flex-grow", "1")
                ] ++ parentStyles
            ]
            elements
        ]

bigDialogBox = dialogBox "100" "85%" "85%"

smallDialogBox = dialogBox "101" "35%" "35%"

fileNewDialogBox model =
  let
    viewTemplate (name, _) =
      Html.div
        [ Attr.style
            [ ("font-family", "monospace")
            , ("font-size", "1.2em")
            , ("margin-bottom", "10px")
            , ("padding", "10px 20px")
            --, ("border-top", "1px solid black")
            --, ("border-bottom", "1px solid black")
            , ("background-color", "rgba(0, 0, 0, 0.1)")
            ]
        ]
        [ htmlButton
            name
            (Controller.msgAskNew name model.needsSave)
            Regular
            False
        ]
    viewCategory (categoryName, templates) =
      Html.div
        []
        ( [ Html.h1
              [ Attr.style
                [ ("padding", "10px 20px")
                --, ("border-top", "2px solid black")
                --, ("border-bottom", "2px solid black")
                , ("background-color", "rgba(0, 0, 0, 0.2)")
                ]
              ]
              [ Html.text categoryName ]
          ]
          ++ List.map viewTemplate templates
        )
  in
    bigDialogBox
      True
      New
      model
      []
      [Html.text "New..."]
      []
      (List.map viewCategory Examples.templateCategories)

fileSaveAsDialogBox model =
  let saveAsInput =
        Html.div
          [ Attr.style
            [ ("font-family", "monospace")
            , ("font-size", "1.2em")
            , ("padding", "20px")
            , ("text-align", "right")
            ]
          ]
          [ Html.input
              [ Attr.type_ "text"
              , onInput Controller.msgUpdateFilenameInput
              ]
              []
          , Html.text ".little"
          , Html.span
              [ Attr.style
                  [ ("margin-left", "20px")
                  ]
              ]
              [ htmlButton "Save" Controller.msgSaveAs Regular False ]
          ]
  in
    bigDialogBox
      True
      SaveAs
      model
      []
      [Html.text "Save As..."]
      []
      ((List.map viewFileIndexEntry model.fileIndex) ++ [saveAsInput])

fileOpenDialogBox model =
  let fileOpenRow filename =
        Html.div
          [ Attr.style
            [ ("font-family", "monospace")
            , ("font-size", "1.2em")
            , ("padding", "20px")
            , ("border-bottom", "1px solid black")
            , ("overflow", "hidden")
            ]
          ]
          [ Html.span []
              [ Html.b [] [ Html.text filename ]
              , Html.text ".little"
              ]
          , Html.span
              [ Attr.style
                  [ ("float", "right")
                  ]
              ]
              [ htmlButton "Open"
                           (Controller.msgAskOpen filename model.needsSave)
                           Regular
                           False
              , Html.span
                  [ Attr.style
                    [ ("margin-left", "30px")
                    ]
                  ]
                  [ htmlButton "Delete"
                               (Controller.msgDelete filename)
                               Regular
                               False
                  ]
              ]
          ]
  in
    bigDialogBox
      True
      Open
      model
      []
      [Html.text "Open..."]
      []
      (List.map fileOpenRow model.fileIndex)

viewFileIndexEntry filename =
  Html.div
    [ Attr.style
        [ ("font-family", "monospace")
        , ("font-size", "1.2em")
        , ("padding", "20px")
        , ("border-bottom", "1px solid black")
        ]
    ]
    [ Html.span []
        [ Html.b [] [ Html.text filename ]
        , Html.text ".little"
        ]
    ]

fileIndicator model =
  let
    filenameHtml =
      Html.text (Model.prettyFilename model)
    wrapper =
      if model.needsSave then
        Html.i [] [ filenameHtml, Html.text " *" ]
      else
        filenameHtml
  in
    Html.span
      [ Attr.style
          [ ("color", "white")
          , ("font-family", "sans-serif")
          , ("padding", "7px")
          ]
      ]
      [ wrapper ]
{-
      [ Html.u [] [ Html.text "File" ]
      , Html.text ": "
      , wrapper
      ]
-}

alertSaveDialogBox model =
  smallDialogBox
    False
    AlertSave
    model
    []
    [ Html.span
        [ Attr.style [("color", "#550000")] ]
        [ Html.text "Warning" ]
    ]
    [ ("display", "flex") ]
    [ Html.div
        [ Attr.style
            [ ("padding", "20px")
            , ("flex-grow", "1")
            , ("display", "flex")
            , ("flex-direction", "column")
            , ("justify-content", "space-between")
            ]
        ]
        [ Html.div
            []
            [ Html.i []
                [ Html.text <| Model.prettyFilename model ]
            , Html.text
                " has unsaved changes. Would you like to continue anyway?"
            ]
        , Html.div
            [ Attr.style
                [ ("text-align", "right")
                ]
            ]
            [ htmlButton "Cancel" Controller.msgCancelFileOperation Regular False
            , Html.span
                [ Attr.style
                    [ ("margin-left", "30px")
                    ]
                ]
                [ htmlButton "Yes (Discard Changes)" Controller.msgConfirmFileOperation Regular False ]
            ]
        ]
    ]

importCodeDialogBox model =
  bigDialogBox
    True
    ImportCode
    model
    []
    [ Html.text "Import Code..." ]
    []
    [ Html.div
        [ Attr.style
            [ ("padding", "20px")
            , ("text-align", "center")
            ]
        ]
        [ Html.input
            [ Attr.type_ "file"
            , Attr.id Model.importCodeFileInputId
            ]
            []
        , htmlButton
            "Import"
            (Controller.msgAskImportCode model.needsSave)
            Regular
            False
        ]
    ]


--------------------------------------------------------------------------------
-- Deuce Widgets

deuceLayer model layout =
  let find e acc =
    [e] ++ acc
  in
  let
    (widgets1, point1) = expBoundingPolygonPoints (Lang.foldExp find [] model.inputExp) model
    (widgets2, point2) = patBoundingPolygonPoints (findPats model.inputExp) model
  in
  -- for now, not considering target positions when computing extremePoint
  let extremePoint =
    rightmostBottommostPoint [point1, point2]
  in
  let widgets =
    widgets1 ++
    widgets2 ++
    expTargetIndicator (computeExpTargets model.inputExp) model ++
    patTargetIndicator (findPatTargets model.inputExp) model
  in
  let svgWidgets =
    [Svg.svg [Attr.id "polygons",
         Attr.style
          [ ("position", "fixed")
          , ("left", pixels (round(model.codeBoxInfo.gutterWidth) + layout.codeBox.left))
          , ("top", pixels layout.codeBox.top)
          , ("width", pixels (layout.codeBox.width - round(model.codeBoxInfo.offsetLeft + model.codeBoxInfo.gutterWidth)))
          , ("height", pixels (layout.codeBox.height))
          -- , ("height", pixels (layout.codeBox.height - round(model.codeBoxInfo.offsetHeight)))
          ]] widgets ]
  in
  let pointerEvents =
    if showDeuceWidgets model
    then "auto"
    else "none"
  in
  let shapes =
    Html.div
            [ Attr.id "hoveredItem"
            , Attr.style
                -- child div as absolute to overlay on parent div
                -- https://stackoverflow.com/questions/2941189/how-to-overlay-one-div-over-another-div
                [ ("position", "absolute")
                , ("left", pixels layout.codeBox.left)
                , ("top", pixels layout.codeBox.top)
                -- TODO don't want this layer to block clicks to change Ace cursor
                -- , ("width", pixels layout.codeBox.width)
                -- , ("height", pixels layout.codeBox.height)
                , ("width", "0")
                , ("height", "0")
                , ("user-select", "none")
                , ("pointer-events", pointerEvents)
                ]
            -- TODO why are these events here and aceCodeBox?
            , onMouseEnter Controller.msgMouseEnterCodeBox
            , onMouseLeave Controller.msgMouseLeaveCodeBox
            , onClick Controller.msgMouseClickCodeBox
            ] (List.reverse svgWidgets)
  in
  (shapes, extremePoint)

computePolygonPoints rcs model =
  let pad = 3 in
  let traverse leftSide =
    let maybeReverse = if leftSide then identity else List.reverse in
    let things = maybeReverse (Dict.toList rcs) in
    let n = List.length things in
    flip Utils.concatMapi1 things <| \(i,(k,(c1,c2))) ->
      let c = if leftSide then c1 else c2 in
      let topOffset = rowColToPixelPos {line = k, col = c} model in
      let dx = if leftSide then -pad else pad in
       let dyTop = if (leftSide && i == 1) || (not (leftSide) && i == n) then -pad else 0 in
       let dyBot = if (leftSide && i == n) || (not (leftSide) && i == 1) ||
                      (leftSide && i == 1) || (not (leftSide) && i == n) then  pad else 0 in
      let top =
         { x = topOffset.x - model.codeBoxInfo.gutterWidth + dx
         , y = topOffset.y - model.codeBoxInfo.offsetHeight + dyTop
         } in
      let bottom =
         { x = top.x
         , y = top.y + model.codeBoxInfo.lineHeight + dyBot
         } in
      if leftSide then [top, bottom] else [bottom, top]
  in
  let left = traverse True in
  let right = traverse False in
  let pointsAttribute =
    let combine point acc = toString(point.x) ++ "," ++ toString(point.y) ++ " " ++ acc in
    List.foldr combine  "" (left ++ right)
  in
  let rightBotPoint =
    left ++ right
    |> List.map (\{x,y} -> {x = round x, y = round y})
    |> rightmostBottommostPoint
  in
  (pointsAttribute, rightBotPoint)

isDefExp exp =
  case exp.val.e__ of
    Lang.ELet wsBef letKind rec pat exp1 exp2 wsAft ->
      case letKind of
        Lang.Def -> (True, exp2)
        _ -> (False, exp)
    _ -> (False, exp)

findFirstNonDef exp =
  case isDefExp exp of
    (True, secondExp) -> findFirstNonDef secondExp
    _ -> exp

expBoundingPolygonPoints =
  boundingPolygonPoints List.reverse
     (\exp ->
      case exp.val.e__ of
        Lang.ELet wsBef letKind rec pat exp1 exp2 wsAft ->
          case letKind of
            Lang.Let ->
              [expBoundingPolygon (DeuceLetBindingEquation exp.val.eid) exp exp1,
               expBoundingPolygon (DeuceExp exp.val.eid) exp exp]
            Lang.Def -> [expBoundingPolygon (DeuceLetBindingEquation exp.val.eid) exp exp,
                         expBoundingPolygon (DeuceExp exp.val.eid) exp (findFirstNonDef exp)]
        _ ->
          [expBoundingPolygon (DeuceExp exp.val.eid) exp exp])

patBoundingPolygonPoints =
  boundingPolygonPoints identity
     (\(pat,ppid,_,_,_) -> [patBoundingPolygon (DeucePat ppid) pat pat])

boundingPolygonPoints :
    (List (Svg Msg) -> List (Svg Msg))
    -> (c -> List ( DeuceWidget, Dict.Dict Int ( Int, Int ) ))
    -> List c
    -> Model
    -> (List (Svg Msg), {x:Int, y:Int})
boundingPolygonPoints maybeReverse deuceWidgetAndBoundingPolygonOf exps model =
  let calculate (deuceWidget, boundingPolygon) =
    let (pointsAttribute, extremePoint) = computePolygonPoints boundingPolygon model in
    let extremeSelectedPoint =
      if List.member deuceWidget model.deuceState.selectedWidgets
        then [extremePoint]
        else []
    in
    let color =
      if showSelectedDeuceWidgets model && List.member deuceWidget model.deuceState.selectedWidgets then
        if List.member deuceWidget model.deuceState.hoveredWidgets
        then "green"
        else "orange"
      else if List.member deuceWidget model.deuceState.hoveredWidgets && showDeuceWidgets model
        then "yellow"
        else ""
    in
    let textPolygon =
        [ flip Svg.polygon []
            [LangSvg.attr "stroke" color
            , LangSvg.attr "stroke-width" "5"
            , Attr.style [("fill-opacity", "0")]
            , LangSvg.attr "points" pointsAttribute
            , onClick (Controller.msgMouseClickDeuceWidget deuceWidget)
            , onMouseOver (Controller.msgMouseEnterDeuceWidget deuceWidget)
            , onMouseLeave (Controller.msgMouseLeaveDeuceWidget deuceWidget)
            ]
          ] in
    (textPolygon, extremeSelectedPoint)
  in
  let calculatePolygons exp =
    let polygons = deuceWidgetAndBoundingPolygonOf exp in
    let (list, points) = List.unzip (List.map calculate polygons) in
    (List.concat list, rightmostBottommostPoint (List.concat points))
  in
  let (list, points) = List.unzip (List.map calculatePolygons exps) in
  (maybeReverse (List.concat list), rightmostBottommostPoint points)

expTargetIndicator = targetIndicator DeuceExpTarget
patTargetIndicator = targetIndicator DeucePatTarget

targetIndicator deuceWidgetConstructor targets model =
  let drawTarget deuceWidget pixelPos color opacity numRings =
    let rDot = 4 in
    let (cx, cy) =
      ( toString <|
          pixelPos.x - model.codeBoxInfo.gutterWidth
                     - model.codeBoxInfo.offsetLeft
                     + model.codeBoxInfo.characterWidth / 2
      -- TODO should pixelPos calculations take care of all these offsets?
      , toString <|
          pixelPos.y - model.codeBoxInfo.offsetHeight
                     + model.codeBoxInfo.lineHeight / 2
      )
    in
    let rings =
      flip List.map (List.range 1 numRings) <| \i ->
        flip Svg.circle [] <|
          [ LangSvg.attr "fill" "none"
          , LangSvg.attr "fill-opacity" opacity
          , LangSvg.attr "stroke" color
          , LangSvg.attr "stroke-width" (toString (rDot//2))
          , LangSvg.attr "cx" cx, LangSvg.attr "cy" cy
          , LangSvg.attr "r" (toString ((i+1) * rDot))
          ]
    in
    let center =
      flip Svg.circle [] <|
        [ LangSvg.attr "fill" color
        , LangSvg.attr "fill-opacity" opacity
        , LangSvg.attr "cx" cx, LangSvg.attr "cy" cy
        , LangSvg.attr "r" (toString rDot)
        , onClick (Controller.msgMouseClickDeuceWidget deuceWidget)
        , onMouseOver (Controller.msgMouseEnterDeuceWidget deuceWidget)
        , onMouseLeave (Controller.msgMouseLeaveDeuceWidget deuceWidget)
        ]
    in
    center :: rings
  in
  flip List.concatMap targets <| \(id, start, end) ->
    let deuceWidget = deuceWidgetConstructor id in
    let pixelPos = rowColToPixelPos start model in
    if showSelectedDeuceWidgets model && List.member deuceWidget model.deuceState.selectedWidgets then
      if List.member deuceWidget model.deuceState.hoveredWidgets
      then drawTarget deuceWidget pixelPos "darkgreen" "1.0" 3
      else drawTarget deuceWidget pixelPos "orange" "1.0" 3
    else if List.member deuceWidget model.deuceState.hoveredWidgets && showDeuceWidgets model then
      drawTarget deuceWidget pixelPos "red" "1.0" 3
    else
      -- TODO: want to return [], but then targets are never drawn
      -- []
      drawTarget deuceWidget pixelPos "white" "0.0" 0

getBoxWidth start end m =
  let offSet = if start.line == end.line then 0 else 1 in
  let characters = end.col - start.col - offSet in
  toFloat(characters) * m.codeBoxInfo.characterWidth

getBoxHeight start end m =
  let lines = end.line - start.line + 1 in
  toFloat(lines) * m.codeBoxInfo.lineHeight

rightmostBottommostPoint : List {x:Int, y:Int} -> {x:Int, y:Int}
rightmostBottommostPoint =
  List.foldl (\point acc ->
    if point.y > acc.y then point
    else if point.y == acc.y && point.x > acc.x then point
    else acc
  ) {x=0, y=0}


--------------------------------------------------------------------------------
-- Deuce Tool Menu

-- extremePoint is the right-most, bottom-most point among the Deuce widgets.
-- It is computed earlier in the view function and, hence, not stored in Model.
--
addSomeOffsetToExtremePoint extremePoint =
  if extremePoint == {x=0,y=0} then Nothing
  else
{-
    let (xOffset, yOffset) = (60, 10) in
-}
    -- TODO: added extra slop offsets here, when changing layout
    -- of aceCodeBox and deuceTools. figure out how to remove the
    -- need for this.
    let (xOffset, yOffset) = (70, 80) in
    Just { leftRight = Left       <| extremePoint.x + xOffset
         , topBottom = Layout.Top <| extremePoint.y + yOffset }

deuceToolBoxNested model layout maybeNotPinnedAnchor =
{-
  let icon =
     Html.img
       [ Attr.src "img/deuce_logo.png"
       , Attr.style
           [ ("width", pixels (Layout.buttonHeight - 0))
           , ("height", pixels (Layout.buttonHeight - 0))
           , ("vertical-align", "middle")
           ]
       ] []
  in
-}
  let extraStyles =
    [ ("display", "block")
    ]
  in
  let tools = deuceTools model in
  let spacer =
    if tools == [] then []
    else [Html.div [Attr.style [("height", "7px")]] []]
  in
  let leftRight =
    let anchor =
      case (model.layoutOffsets.deuceToolBox.pinned, maybeNotPinnedAnchor) of
        (True,  _)                    -> layout.deuceToolsPinnedAnchor
        (False, Nothing)              -> layout.deuceToolsPinnedAnchor
        (False, Just notPinnedAnchor) -> notPinnedAnchor
    in
    Layout.offset model Layout.getDeuceToolBox anchor
  in
  toolBox model "deuceToolBox" extraStyles Layout.getPutDeuceToolBox leftRight <|
    spacer ++ tools

pinButton model layout maybeNotPinnedAnchor =
  let attrs =
    [ Attr.title "To use Deuce, hold Shift while hovering over the code box."
    ]
  in
  let caption =
    "Deuce Tools " ++
    if model.layoutOffsets.deuceToolBox.pinned
      then "[Pinned]"
      else "[Auto-Positioned]"
  in
  let msgTogglePin =
    Msg "Toogle Pin Deuce Tools" <| \m ->
      let layoutOffsets = m.layoutOffsets in
      let deuceToolBox = layoutOffsets.deuceToolBox in
      let newOffsets =
        case maybeNotPinnedAnchor of
          Nothing ->
            {dx=0, dy=0}

          Just notPinnedAnchor ->
            let (ddx, ddy) =
              let (a, b) =
                if deuceToolBox.pinned
                  then (layout.deuceToolsPinnedAnchor, notPinnedAnchor)
                  else (notPinnedAnchor, layout.deuceToolsPinnedAnchor)
              in
              case (a.leftRight, a.topBottom, b.leftRight, b.topBottom) of
                (Left x1, Layout.Top y1, Left x2, Layout.Top y2) ->
                  (x1 - x2, y1 - y2)
                _ ->
                  Debug.log "msgTogglePin: shouldn't happen" (0, 0)
            in
            { dx = deuceToolBox.offsets.dx + ddx
            , dy = deuceToolBox.offsets.dy + ddy
            }
      in
      { m | layoutOffsets =
        { layoutOffsets | deuceToolBox =
          { pinned = not deuceToolBox.pinned , offsets = newOffsets } } }
  in
  htmlButtonExtraAttrs attrs caption msgTogglePin Regular False

deuceTools model =
  let chop = Utils.removeLastElement in
  let hoveredPath = model.deuceState.hoveredMenuPath in
  let extraButtonStyles path maybeWidth =
    Attr.style
        [ ("width", Maybe.withDefault "100%" maybeWidth)
        , ("text-align", "left")
        , ("padding-top", "0px")
        , ("padding-bottom", "0px")
        , ("opacity",
            if path == hoveredPath then "1.0"
            else if path == chop hoveredPath then "1.0"
            else if chop path == hoveredPath then "0.9"
            else if chop path == chop hoveredPath then "0.9"
            else if List.length path == 1 then "0.9"
            else "0.0"
          )
        ]
  in
  let oneTool (i, (toolName, func)) =
    let previewAndColor result =
      case (result.isSafe, runAndResolve model result.exp) of
        (True, Err err) ->
          let _ = Debug.log "not safe after all!" () in
          (Just (unparse result.exp, Err err), "red")

        (True, Ok (val, widgets, slate, code)) ->
          (Just (code, Ok (val, widgets, slate)), "white")

        (False, Ok (val, widgets, slate, code)) ->
          (Just (code, Ok (val, widgets, slate)), "khaki")

        (False, Err err) ->
          (Just (unparse result.exp, Err err), "salmon")
    in
    -- could refactor deadButton and previewButton...
    let deadButton path caption maybeWidth =
      let attrs =
        [extraButtonStyles path maybeWidth] ++
        deuceMenuButtonHoverEvents path Nothing
      in
      htmlButtonExtraAttrs attrs caption Controller.msgNoop Regular False
    in
    let previewButton path maybeCaption (SynthesisResult result) =
      let (preview, color) = previewAndColor result in
      let attrs =
        [Attr.style [("background-color", color)]] ++
        [extraButtonStyles path Nothing] ++
        deuceMenuButtonHoverEvents path (Just preview)
      in
      let caption = Maybe.withDefault result.description maybeCaption in
      htmlButtonExtraAttrs attrs caption
         (Controller.msgChooseDeuceExp result.exp) Regular False
    in
    let buttonAndMaybeMenu oneOrMoreResults =
      -- parent tool button is "relative", so that its descendants
      -- (the next menu) can be positioned "absolute"ly in terms
      -- of the parent
      let divAttrs isParent =
        let width = "250px" in -- "100%"
        Attr.style <|
          [ ("position", if isParent then "relative" else "absolute")
          , ("overflow", "visible")
          , ("width", width)
          , ("background", Layout.strInterfaceColor)
          ] ++ (if isParent then [] else [("left", width)])
      in
      case oneOrMoreResults of
        Left result ->
          let toolButton = previewButton [i] (Just toolName) result in
          Html.div [divAttrs True] [toolButton]

        Right results ->
          let toolButtonAndExtras =
            let caption =
              toolName
              -- toolName ++ " " ++ Utils.parens (toString (List.length results))
            in
            if String.startsWith "Rename" toolName
            then [deadButton [i] caption (Just "150px"), renameVarTextBox [i]]
            else [deadButton [i] caption Nothing]
          in
          let nextMenu =
            if hoveredPath == [i] || chop hoveredPath == [i] then
              Html.div [divAttrs False]
                (Utils.mapi1 (\(j,result) -> previewButton [i,j] Nothing result)
                             results)
            else
              Html.div [] []
          in
          -- nextMenu first, so it pops out at same y-position as toolButton
          Html.div [divAttrs True] (nextMenu :: toolButtonAndExtras)
    in
    let results = func () in

    if String.startsWith "Rename" toolName then
      if model.deuceState.renameVarTextBox == ""
      then buttonAndMaybeMenu (Right [])
      else buttonAndMaybeMenu (Right results)

    else case results of
      [SynthesisResult result] ->
        if result.isSafe
          then buttonAndMaybeMenu (Left (SynthesisResult result))
          else buttonAndMaybeMenu (Right results)
      _ ->
        buttonAndMaybeMenu (Right results)
  in
  Utils.mapi1 oneTool (Controller.contextSensitiveDeuceTools model)

renameVarTextBox path =
  flip Html.input [] <|
     [ Attr.type_ "text"
     , Attr.style <|
         [ ("width", "100px") -- in sync with 250px - 150px above
         -- the following are the same as for htmlButton
         , ("font", params.mainSection.widgets.font)
         , ("fontSize", params.mainSection.widgets.fontSize)
         , ("box-sizing", "border-box") -- Strangely, Firefox and Chrome on Mac differ on this default.
         , ("min-height", pixels Layout.buttonHeight)
         ]
     , onInput <| \str ->
         Msg ("Update Rename Var Textbox: " ++ str) <| \m ->
           let deuceState = m.deuceState in
           { m | deuceState = { deuceState | renameVarTextBox = str } }
     ] ++
    deuceMenuButtonHoverEvents path Nothing

deuceMenuButtonHoverEvents path maybePreview =
  [ Html.Events.onMouseEnter <|
      Msg ("Hover Deuce Tool " ++ toString path)
          (setHoveredMenuPath path >>
           case maybePreview of
             Just preview -> \m -> { m | preview = preview }
             Nothing      -> \m -> m
          )
  , Html.Events.onMouseLeave <|
      Msg ("Leave Deuce Tool " ++ toString path)
          (clearHoveredMenuPath >>
           case maybePreview of
             Just preview -> \m -> { m | preview = Nothing }
             Nothing      -> \m -> m
          )
  ]
