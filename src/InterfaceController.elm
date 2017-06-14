module InterfaceController exposing
  ( update
  , msgNoop
  , msgWindowDimensions
  , msgCodeUpdate
  , msgKeyPress, msgKeyDown, msgKeyUp
  , msgMouseIsDown, msgMousePosition
  , msgRun, upstateRun, msgTryParseRun
  , msgAceUpdate
  , msgUndo, msgRedo, msgCleanCode
  , msgDigHole, msgMakeEqual, msgRelate, msgIndexedRelate
  , msgSelectSynthesisResult, msgClearSynthesisResults
  , msgHoverSynthesisResult, msgPreview, msgClearPreview
  , msgGroupBlobs, msgDuplicateBlobs, msgMergeBlobs, msgAbstractBlobs
  , msgReplicateBlob
  , msgToggleCodeBox, msgToggleOutput
  , msgStartAnimation, msgRedraw, msgTickDelta
  , msgNextSlide, msgPreviousSlide
  , msgNextMovie, msgPreviousMovie
  , msgPauseResumeMovie
  , msgOpenDialogBox, msgCloseDialogBox
  , msgUpdateFilenameInput
  , msgConfirmWrite, msgConfirmDelete
  , msgReadFile, msgReadFileFromInput, msgUpdateFileIndex
  , msgLoadIcon
  , msgNew, msgSaveAs, msgSave, msgOpen, msgDelete
  , msgAskNew, msgAskOpen
  , msgConfirmFileOperation, msgCancelFileOperation
  , msgToggleAutosave
  , msgExportCode, msgExportSvg
  , msgImportCode, msgAskImportCode
  )

import Lang exposing (..) --For access to what makes up the Vals
import Types
import Ace
import FastParser exposing (parseE)
import LangUnparser exposing (unparse)
import LangTools
import LangTransform
import ValueBasedTransform
import Blobs exposing (..)
import Draw
import ExpressionBasedTransform as ETransform
import Sync
import Eval
import Utils
import Keys
import InterfaceModel as Model exposing (..)
import Layout exposing (clickToCanvasPoint)
import AceCodeBox
import AnimationLoop
import FileHandler
-- import InterfaceStorage exposing (installSaveState, removeDialog)
import LangSvg
import ShapeWidgets exposing (RealZone(..), PointFeature(..), OtherFeature(..))
import ExamplesGenerated as Examples
import Config exposing (params)
import Either exposing (Either(..))
import Canvas
import DefaultIconTheme

import VirtualDom

--Core Libraries
import List
import Dict exposing (Dict)
import Set
import String
import Char

--Html Libraries
import Html
import Html.Attributes as Attr
import Html.Events as Events

--Svg Libraries
import Svg
import Svg.Attributes
import Svg.Events
import Svg.Lazy

--Error Checking Libraries
import Debug

--------------------------------------------------------------------------------

debugLog = Config.debugLog Config.debugController

--------------------------------------------------------------------------------

refreshMode model e =
  case model.mode of
    Live _  -> Utils.fromOk "refreshMode" <| mkLive_ model.syncOptions model.slideNumber model.movieNumber model.movieTime e
    Print _ -> Utils.fromOk "refreshMode" <| mkLive_ model.syncOptions model.slideNumber model.movieNumber model.movieTime e

refreshMode_ model = refreshMode model model.inputExp

-- TODO refresh type highlights, too
refreshHighlights zoneKey model =
  let codeBoxInfo = model.codeBoxInfo in
  let hi = liveInfoToHighlights zoneKey model in
  { model | codeBoxInfo = { codeBoxInfo | highlights = hi } }

-- may want to eventually have a maximum history length
addToHistory currentCode h =
  let (past, _) = h in
  case past of
    [] ->
      (currentCode::past, [])

    last::older ->
      if currentCode == last
      then h
      else (currentCode::past, [])


between1 i (j,k) = Utils.between i (j+1, k+1)

{-
cleanExp =
  mapExpViaExp__ <| \e__ -> case e__ of
    EApp _ e0 [e1,_,_] _ -> case e0.val.e__ of
      EVar _ "inferred"  -> e1.val.e__
      _                  -> e__
    EApp _ e0 [_,e1] _   -> case e0.val.e__ of
      EVar _ "flow"      -> e1.val.e__
      _                  -> e__
    EOp _ op [e1,e2] _   ->
      case (op.val, e2.val.e__) of
        (Plus, EConst _ 0 _ _) -> e1.val.e__
        _                      -> e__
    _                    -> e__
-}

{-
addSlateAndCode old (exp, val) =
  slateAndCode old (exp, val)
  |> Result.map (\(slate, code) -> (exp, val, slate, code))
-}

-- We may want to revisit our error handling so we don't have different error types floating around.
discardErrorAnnotations : Result (String, Ace.Annotation) a -> Result String a
discardErrorAnnotations result =
  result |> Result.mapError (\(string, annot) -> string)

slateAndCode old (exp, val) =
  LangSvg.resolveToIndexedTree old.slideNumber old.movieNumber old.movieTime val
  |> Result.map (\slate -> (slate, unparse exp))

runAndResolve model exp =
  Eval.run exp
  |> Result.andThen (\(val, widgets) ->
    slateAndCode model (exp, val)
    |> Result.map (\(slate, code) -> (val, widgets, slate, code))
  )

runWithErrorHandling model exp onOk =
  let result =
    -- runWithErrorHandling is called after synthesis. Recompute line numbediscardErrorAnnotationsrs.
    -- TODO RESULTERROR
    let reparsedResult = unparse exp |> parseE |> (Result.mapError toString) in
    reparsedResult
    |> Result.andThen (\reparsed ->
      runAndResolve model reparsed
      |> Result.map (\(val, widgets, slate, code) -> onOk reparsed val widgets slate code)
    )
  in
  handleError model result

handleError : Model -> Result String Model -> Model
handleError oldModel result =
  case result of
    Ok newModel -> newModel
    Err s       -> { oldModel | errorBox = Just s }

updateCodeBoxWithTypes : Types.AceTypeInfo -> CodeBoxInfo -> CodeBoxInfo
updateCodeBoxWithTypes ati codeBoxInfo =
  { codeBoxInfo | annotations = ati.annotations
                , highlights = ati.highlights
                , tooltips = ati.tooltips }

updateCodeBoxWithParseError annot codeBoxInfo =
  { codeBoxInfo | annotations = [annot] , highlights = [] , tooltips = [] }

switchToCursorTool old =
  { old | mouseMode = MouseNothing , tool = Cursor }

-- rewrite the innermost let-body eInner to (let main eInner main).
-- note that there's nothing special about calling this temp binding "main".
--
rewriteInnerMostExpToMain exp =
  case exp.val.e__ of
    ELet ws1 lk rec p1 e1 e2 ws2 ->
      replaceE__ exp (ELet ws1 lk rec p1 e1 (rewriteInnerMostExpToMain e2) ws2)
    _ ->
      eLets [("main", exp)] (eVar "main")


--------------------------------------------------------------------------------
-- Mouse Events

onMouseClick click old =
  case (old.tool, old.mouseMode) of

    -- Inactive zone
    (Cursor, MouseDragZone (i, k, z) Nothing) ->
      onClickPrimaryZone i k z { old | mouseMode = MouseNothing }

    -- Active zone but not dragged
    (Cursor, MouseDragZone (i, k, z) (Just (_, _, False))) ->
      onClickPrimaryZone i k z { old | mouseMode = MouseNothing }

    (Poly stk, MouseDrawNew points) ->
      let pointOnCanvas = clickToCanvasPoint old click in
      let add () =
        let points_ = (old.keysDown, pointOnCanvas) :: points in
        { old | mouseMode = MouseDrawNew points_ }
      in
      if points == [] then add ()
      else
        let (_,initialPoint) = Utils.last_ points in
        if Utils.distanceInt pointOnCanvas initialPoint > Draw.drawDotSize then add ()
        else if List.length points == 2 then { old | mouseMode = MouseNothing }
        else if List.length points == 1 then switchToCursorTool old
        else upstateRun <| Draw.addPolygon stk old points

    (Path stk, MouseDrawNew points) ->
      let pointOnCanvas = clickToCanvasPoint old click in
      let add new =
        let points_ = (old.keysDown, new) :: points in
        (points_, { old | mouseMode = MouseDrawNew points_ })
      in
      case points of
        [] -> Tuple.second (add pointOnCanvas)
        (_,firstClick) :: [] ->
          if Utils.distanceInt pointOnCanvas firstClick < Draw.drawDotSize
          then switchToCursorTool old
          else Tuple.second (add pointOnCanvas)
        (_,lastClick) :: _ ->
          if Utils.distanceInt pointOnCanvas lastClick < Draw.drawDotSize
          then upstateRun <| Draw.addPath stk old points
          else
            let (_,firstClick) = Utils.last_ points in
            if Utils.distanceInt pointOnCanvas firstClick < Draw.drawDotSize
            then
              let (points_,old_) = add firstClick in
              upstateRun <| Draw.addPath stk old_ points_
            else
              Tuple.second (add pointOnCanvas)

    (HelperDot, MouseDrawNew []) ->
      let pointOnCanvas = (old.keysDown, clickToCanvasPoint old click) in
      { old | mouseMode = MouseDrawNew [pointOnCanvas] }

    (_, MouseDrawNew []) -> switchToCursorTool old

    _ ->
      old

onClickPrimaryZone : LangSvg.NodeId -> LangSvg.ShapeKind -> ShapeWidgets.ZoneName -> Model -> Model
onClickPrimaryZone i k z old =
  let realZone = ShapeWidgets.parseZone z in
  let hoveredCrosshairs_ =
    case ShapeWidgets.zoneToCrosshair k realZone of
      Just (xFeature, yFeature) ->
        Set.insert (i, xFeature, yFeature) old.hoveredCrosshairs
      _ ->
        old.hoveredCrosshairs
  in
  let (selectedFeatures_, selectedShapes_, selectedBlobs_) =
    if i < -2 then -- Clicked a widget
      if z == "Offset1D" then
        let update = if Set.member (i,"offset") old.selectedFeatures then Set.remove else Set.insert in
        (update (i,"offset") old.selectedFeatures, old.selectedShapes, old.selectedBlobs)
      else
        (old.selectedFeatures, old.selectedShapes, old.selectedBlobs)
    else
      let selectThisShape () =
        Set.insert i <|
          if old.keysDown == Keys.shift
          then old.selectedShapes
          else Set.empty
      in
      let selectBlob blobId =
        Dict.insert blobId i <|
          if old.keysDown == Keys.shift
          then old.selectedBlobs
          else Dict.empty
      in
      let maybeBlobId =
        case Dict.get i (Tuple.second old.slate) of
          Just (LangSvg.SvgNode _ l _) -> LangSvg.maybeFindBlobId l
          _                            -> Debug.crash "onClickPrimaryZone"
      in
      case (k, realZone, maybeBlobId) of
        ("line", ZLineEdge, Just blobId) -> (old.selectedFeatures, selectThisShape (), selectBlob blobId)
        (_,      ZInterior, Just blobId) -> (old.selectedFeatures, selectThisShape (), selectBlob blobId)
        ("line", ZLineEdge, Nothing)     -> (old.selectedFeatures, selectThisShape (), old.selectedBlobs)
        (_,      ZInterior, Nothing)     -> (old.selectedFeatures, selectThisShape (), old.selectedBlobs)
        _                                -> (old.selectedFeatures, old.selectedShapes, old.selectedBlobs)
  in
  { old | hoveredCrosshairs = hoveredCrosshairs_
        , selectedFeatures = selectedFeatures_
        , selectedShapes = selectedShapes_
        , selectedBlobs = selectedBlobs_
        }

onMouseMove newPosition old =
  let (mx0, my0) = (newPosition.x, newPosition.y) in
  let (mx, my) = clickToCanvasPoint old newPosition in
  case old.mouseMode of

    MouseNothing -> old

    MouseDragLayoutWidget f ->
      f (mx0, my0) old

    MouseDragZone zoneKey Nothing ->
      old

    MouseDragZone zoneKey (Just (trigger, (mx0, my0), _)) ->
      let dx = if old.keysDown == Keys.y then 0 else (mx - mx0) in
      let dy = if old.keysDown == Keys.x then 0 else (my - my0) in

      let (newExp, highlights) = trigger (mx0, my0) (dx, dy) in

      let codeBoxInfo_ =
        let codeBoxInfo = old.codeBoxInfo in
        { codeBoxInfo | highlights = highlights }
      in
      let dragInfo_ = (trigger, (mx0, my0), True) in

      Eval.run newExp |> Result.andThen (\(newVal, newWidgets) ->
      LangSvg.resolveToIndexedTree old.slideNumber old.movieNumber old.movieTime newVal |> Result.map (\newSlate ->
        { old | code = unparse newExp
              , inputExp = newExp
              , inputVal = newVal
              , slate = newSlate
              , widgets = newWidgets
              , codeBoxInfo = codeBoxInfo_
              , mouseMode = MouseDragZone zoneKey (Just dragInfo_)
              }
      )) |> handleError old

    MouseDrawNew points ->
      case (old.tool, points) of
        (Poly _, _) -> old -- handled by onMouseClick instead
        (Path _, _) -> old -- handled by onMouseClick instead
        (_, []) ->
          let pointOnCanvas = (old.keysDown, (mx, my)) in
          { old | mouseMode = MouseDrawNew [pointOnCanvas, pointOnCanvas] }
        (_, (_::points)) ->
          let pointOnCanvas = (old.keysDown, (mx, my)) in
          { old | mouseMode = MouseDrawNew (pointOnCanvas::points) }

onMouseUp old =
  case (old.mode, old.mouseMode) of

    (Print _, _) -> old

    (_, MouseDragZone zoneKey (Just _)) ->
      let e = Utils.fromOkay "onMouseUp" <| parseE old.code in
      let old_ = { old | inputExp = e } in
      refreshHighlights zoneKey
        { old_ | mouseMode = MouseNothing, mode = refreshMode_ old_
               , history = addToHistory old.code old_.history }

    (_, MouseDrawNew points) ->
      case (old.tool, points, old.keysDown == Keys.shift) of

        (Line _,     [pt2, pt1], _) -> upstateRun <| Draw.addLine old pt2 pt1
        (HelperLine, [pt2, pt1], _) -> upstateRun <| Draw.addLine old pt2 pt1

        (Rect Raw,      [pt2, pt1], False) -> upstateRun <| Draw.addRawRect old pt2 pt1
        (Rect Raw,      [pt2, pt1], True)  -> upstateRun <| Draw.addRawSquare old pt2 pt1
        (Rect Stretchy, [pt2, pt1], False) -> upstateRun <| Draw.addStretchyRect old pt2 pt1
        (Rect Stretchy, [pt2, pt1], True)  -> upstateRun <| Draw.addStretchySquare old pt2 pt1

        (Oval Raw,      [pt2, pt1], False) -> upstateRun <| Draw.addRawOval old pt2 pt1
        (Oval Raw,      [pt2, pt1], True)  -> upstateRun <| Draw.addRawCircle old pt2 pt1
        (Oval Stretchy, [pt2, pt1], False) -> upstateRun <| Draw.addStretchyOval old pt2 pt1
        (Oval Stretchy, [pt2, pt1], True)  -> upstateRun <| Draw.addStretchyCircle old pt2 pt1

        (HelperDot, [pt], _) -> upstateRun <| Draw.addHelperDot old pt

        (Lambda i, [pt2, pt1], _) -> upstateRun <| Draw.addLambda i old pt2 pt1

        (Poly _, _, _) -> old
        (Path _, _, _) -> old

        (Text, [pt2, pt1], _) -> upstateRun <| Draw.addTextBox old pt2 pt1

        (_, [], _)     -> switchToCursorTool old

        _              -> old

    _ -> { old | mouseMode = MouseNothing, mode = refreshMode_ old }


tryRun : Model -> Result (String, Maybe Ace.Annotation) Model
tryRun old =
  case parseE old.code of
    -- TODO RESULTERROR
    Err err -> Err (toString err, Nothing)
    Ok e ->
      let result =
        -- let aceTypeInfo = Types.typecheck e in
        let aceTypeInfo = Types.dummyAceTypeInfo in

        -- want final environment of top-level definitions when evaluating e,
        -- for the purposes of running Little code to generate icons.
        -- but can't just use the output environment from eval directly.
        -- for example, if the last expression was a function call (either
        -- within the program or in Prelude), the final environment is from
        -- that function body. so instead, calling rewriteInnerMostExpToMain
        -- because the output environment from (let main eFinalBody main)
        -- will be the top-level definitions (and main).
        --
        let rewrittenE = rewriteInnerMostExpToMain e in

        Eval.doEval Eval.initEnv rewrittenE |>
        Result.andThen (\((newVal,ws),finalEnv) ->
          LangSvg.fetchEverything old.slideNumber old.movieNumber 0.0 newVal
          |> Result.map (\(newSlideCount, newMovieCount, newMovieDuration, newMovieContinue, newSlate) ->
            let newCode = unparse e in
            let lambdaTools_ =
              -- TODO should put program into Model
              -- TODO actually, ideally not. caching introduces bugs
              let program = splitExp e in
              Draw.lambdaToolOptionsOf program ++ initModel.lambdaTools
            in
            let new =
              loadLambdaToolIcons finalEnv { old | lambdaTools = lambdaTools_ }
            in
            let new_ =
              { new | inputExp      = e
                    , inputVal      = newVal
                    , code          = newCode
                    , slideCount    = newSlideCount
                    , movieCount    = newMovieCount
                    , movieTime     = 0
                    , movieDuration = newMovieDuration
                    , movieContinue = newMovieContinue
                    , runAnimation  = newMovieDuration > 0
                    , slate         = newSlate
                    , widgets       = ws
                    , history       = addToHistory newCode old.history
                    , caption       = Nothing
                    , syncOptions   = Sync.syncOptionsOf old.syncOptions e
                    , codeBoxInfo   = updateCodeBoxWithTypes aceTypeInfo old.codeBoxInfo
                    , preview       = Nothing
                    , synthesisResults = maybeRunAutoSynthesis old e
              }
            in
            { new_ | mode = refreshMode_ new_
                   , errorBox = Nothing }
          )
        )
      in
      case result of
        Err s    -> Err (s, Nothing)
        Ok model -> Ok model


--------------------------------------------------------------------------------
-- Updating the Model

-- 1. Compute a "pure" update (only the newModel), and then
-- 2. Decide whether to issue a command based on simple predicates
--    (name of Msg, and simple comparison of oldModel and newModel).
--
update : Msg -> Model -> (Model, Cmd Msg)
update msg oldModel =
  case (oldModel.pendingFileOperation, oldModel.fileOperationConfirmed) of
    (Just msg2, True) ->
      update
        msg2
        { oldModel | pendingFileOperation = Nothing
                   , fileOperationConfirmed = False }
    _ ->
      let newModel = upstate msg oldModel in
      let cmd = issueCommand msg oldModel newModel in
      (newModel, cmd)


upstate : Msg -> Model -> Model
upstate (Msg caption updateModel) old =
  let _ = debugLog "Msg" caption in
  updateModel old


issueCommand : Msg -> Model -> Model -> Cmd Msg
issueCommand (Msg kind _) oldModel newModel =
  case kind of
    "Toggle Code Box" ->
      if newModel.basicCodeBox
        then Cmd.none
        else AceCodeBox.initializeAndDisplay newModel
          -- TODO crash: "Uncaught Error: ace.edit can't find div #editor"

    "Save As" ->
      if newModel.filename /= Model.bufferName then
        FileHandler.write <| getFile newModel
      else
        Cmd.none

    "Save" ->
      if newModel.filename /= Model.bufferName then
        FileHandler.write <| getFile newModel
      else
        FileHandler.requestFileIndex ()

    "Confirm Write" ->
      Cmd.batch <| iconCommand newModel.filename

    "Open" ->
      FileHandler.requestFile newModel.filename

    "Delete" ->
      FileHandler.delete newModel.fileToDelete

    "Confirm Delete" ->
      Cmd.batch <| iconCommand newModel.fileToDelete

    "Export Code" ->
      FileHandler.download
        { filename = (Model.prettyFilename newModel) ++ ".little"
        , text = newModel.code
        }

    "Export SVG" ->
      FileHandler.download
        { filename = (Model.prettyFilename newModel) ++ ".svg"
        , text = LangSvg.printSvg newModel.showGhosts newModel.slate
        }

    "Import Code" ->
      FileHandler.requestFileFromInput Model.importCodeFileInputId

    -- Do not send changes back to the editor, because this is the command where
    -- we receieve changes (if this is removed, an infinite feedback loop
    -- occurs).
    "Ace Update" ->
        if newModel.autosave && newModel.needsSave then
          FileHandler.write <| getFile newModel
        else
          Cmd.none

    "Open Dialog Box" ->
      FileHandler.requestFileIndex ()

    _ ->
      if kind == "Update Font Size" then
        AceCodeBox.updateFontSize newModel
      else
      if newModel.code /= oldModel.code ||
         newModel.codeBoxInfo /= oldModel.codeBoxInfo ||
         newModel.preview /= oldModel.preview ||
         kind == "Turn Off Caption"
           -- ideally this last condition would not be necessary.
           -- and onMouseLeave from point/crosshair zones still leave
           -- stale yellow highlights.
      then
        AceCodeBox.display newModel
      else if kind == "Drag Layout Widget Trigger" then
        -- TODO: only want to do this for resize code box widget.
        -- and need to resize during and after the MouseDragLayout trigger.
        -- (onMouseUp). workaround for now: click widget again.
        AceCodeBox.resize newModel
      else if newModel.runAnimation then
        AnimationLoop.requestFrame ()
      else
        Cmd.none

iconCommand filename =
  let
    potentialIconName =
      String.dropLeft 6 filename -- __ui__
  in
    if List.member potentialIconName Model.iconNames then
      [ FileHandler.requestIcon potentialIconName ]
    else
      []

--------------------------------------------------------------------------------

msgNoop = Msg "Noop" identity

msgWindowDimensions wh = Msg "Window Dimensions" <| \old ->
  { old | dimensions = wh }

msgCodeUpdate s = Msg "Code Update" <| \old ->
  { old | code = s }

--------------------------------------------------------------------------------

msgRun = Msg "Run" <| \old -> upstateRun old

msgAceUpdate aceCodeBoxInfo = Msg "Ace Update" <| \old ->
    if old.preview /= Nothing then
      old
    else
      let isSame = old.lastSaveState == (Just aceCodeBoxInfo.code) in
      { old | code = aceCodeBoxInfo.code
            , codeBoxInfo = aceCodeBoxInfo.codeBoxInfo
            , needsSave = not isSame }

upstateRun old =
  case tryRun old of
    Err (err, Just annot) ->
      { old | errorBox = Just err
            , codeBoxInfo = updateCodeBoxWithParseError annot old.codeBoxInfo }
    Err (err, Nothing) ->
      { old | errorBox = Just err }
    Ok newModel -> newModel

msgTryParseRun newModel = Msg "Try Parse Run" <| \old ->
  case tryRun newModel of
    Err (err, Just annot) ->
      { old | caption = Just (LangError err)
            , codeBoxInfo = updateCodeBoxWithParseError annot old.codeBoxInfo }
    Err (err, Nothing) ->
      { old | caption = Just (LangError err) }
    Ok modelAfterRun ->
      modelAfterRun

--------------------------------------------------------------------------------

msgUndo = Msg "Undo" <| \old ->
  case old.history of
    ([],_)         -> old
    ([firstRun],_) -> old
    (lastRun::secondToLast::older, future) ->
      let new = { old | history = (secondToLast::older, lastRun::future)
                      , code    = secondToLast } in
      upstateRun new

msgRedo = Msg "Redo" <| \old ->
  case old.history of
    (_,[]) -> old
    (past, next::future) ->
      let new = { old | history = (next::past, future)
                      , code    = next } in
      upstateRun new

--------------------------------------------------------------------------------

msgMouseIsDown b = Msg ("MouseIsDown " ++ toString b) <| \old ->
  let new =
    let {x,y} = Tuple.second old.mouseState in
    let lightestColor = 470 in
    { old | randomColor = (old.randomColor + x + y) % lightestColor }
  in
  case (b, new.mouseState) of

    (True, (Nothing, pos)) -> -- mouse down
      let _ = debugLog "mouse down" () in
      { new | mouseState = (Just False, pos) }

    (False, (Just False, pos)) -> -- click (mouse up after not being dragged)
      let _ = debugLog "mouse click" () in
      onMouseClick pos { new | mouseState = (Nothing, pos) }

    (False, (Just True, pos)) -> -- mouse up (after being dragged)
      let _ = debugLog "mouse up" () in
      onMouseUp { new | mouseState = (Nothing, pos) }

    (False, (Nothing, _)) ->
      let _ = debugLog "mouse down was preempted by a handler in View" () in
      new

    -- (True, (Just _, _)) -> Debug.crash "upstate MouseIsDown: impossible"
    (True, (Just _, _)) ->
      let _ = Debug.log "upstate MouseIsDown: impossible" () in
      new

msgMousePosition pos_ = Msg ("MousePosition " ++ toString pos_) <| \old ->
  case old.mouseState of
    (Nothing, _)    -> { old | mouseState = (Nothing, pos_) }
    (Just False, _) -> onMouseMove pos_ { old | mouseState = (Just True, pos_) }
    (Just True, _)  -> onMouseMove pos_ { old | mouseState = (Just True, pos_) }

--------------------------------------------------------------------------------

msgKeyPress keyCode = Msg ("Key Press " ++ toString keyCode) <| \old ->
  old

msgKeyDown keyCode = Msg ("Key Down " ++ toString keyCode) <| \old ->
  if [keyCode] == Keys.escape then
    case (old.tool, old.mouseMode) of
      (Cursor, _) ->
        { old | selectedFeatures = Set.empty
              , selectedShapes = Set.empty
              , selectedBlobs = Dict.empty
              }
      (_, MouseNothing)   -> { old | tool = Cursor }
      (_, MouseDrawNew _) -> { old | mouseMode = MouseNothing }
      _                   -> old
  else if List.member Keys.keyMeta old.keysDown then
    -- when keyMeta is down and another key k is downed,
    -- there will not be a key up event for k. so, not putting
    -- k in keysDown. if want to handle keyMeta + k, keep track
    -- of this another way.
    old
  else if not (List.member keyCode old.keysDown) then
    { old | keysDown = keyCode :: old.keysDown }
  else
    old

msgKeyUp keyCode = Msg ("Key Up " ++ toString keyCode) <| \old ->
  { old | keysDown = Utils.removeFirst keyCode old.keysDown }

--------------------------------------------------------------------------------

cleanSynthesisResult (SynthesisResult {description, exp, sortKey, children}) =
  SynthesisResult <|
    { description = description ++ " -> Cleaned"
    , exp         = LangTransform.cleanCode exp
    , sortKey     = sortKey
    , children    = children
    }

cleanDedupSortSynthesisResults synthesisResults =
  synthesisResults
  |> List.map cleanSynthesisResult
  |> Utils.dedupBy (\(SynthesisResult {description, exp, sortKey, children}) -> unparse exp)
  |> List.sortBy (\(SynthesisResult {description, exp, sortKey, children}) -> (LangTools.nodeCount exp, sortKey, description))

maybeRunAutoSynthesis m e =
  if m.autoSynthesis
    then cleanDedupSortSynthesisResults (ETransform.passiveSynthesisSearch e)
    else []

msgCleanCode = Msg "Clean Code" <| \old ->
  case parseE old.code of
    -- TODO RESULTERROR
    Err err ->
      { old | caption = Just (LangError ("PARSE ERROR!\n" ++ toString err)) }
    Ok reparsed ->
      let cleanedExp = LangTransform.cleanCode reparsed in
      let code_ = unparse cleanedExp in
      if old.code == code_ then old
      else
        let _ = debugLog "Cleaned: " code_ in
        upstateRun { old | inputExp = cleanedExp, code = code_ }

msgDigHole = Msg "Dig Hole" <| \old ->
  let newExp =
    ValueBasedTransform.digHole old.inputExp old.selectedFeatures old.slate old.widgets old.syncOptions
  in
  runWithErrorHandling old newExp (\reparsed newVal newWidgets newSlate newCode ->
    debugLog "new model" <|
      { old | code             = newCode
            , inputExp         = reparsed
            , inputVal         = newVal
            , history          = addToHistory newCode old.history
            , slate            = newSlate
            , widgets          = newWidgets
            , preview          = Nothing
              -- we already ran it successfully once so it shouldn't crash the second time
            , mode             = Utils.fromOk "DigHole MkLive" <|
                                   mkLive old.syncOptions
                                     old.slideNumber old.movieNumber old.movieTime reparsed
                                     (newVal, newWidgets)
            , selectedFeatures = Set.empty
      }
  )

msgMakeEqual = Msg "Make Equal" <| \old ->
  let synthesisResults =
    ValueBasedTransform.makeEqual
        old.inputExp
        old.selectedFeatures
        old.slideNumber
        old.movieNumber
        old.movieTime
        old.syncOptions
  in
  { old | synthesisResults = cleanDedupSortSynthesisResults synthesisResults }

msgRelate = Msg "Relate" <| \old ->
  let synthesisResults =
    ValueBasedTransform.relate
        old.inputExp
        old.selectedFeatures
        old.slideNumber
        old.movieNumber
        old.movieTime
        old.syncOptions
  in
  { old | synthesisResults = cleanDedupSortSynthesisResults synthesisResults }

msgIndexedRelate = Msg "Indexed Relate" <| \old ->
  let synthesisResults =
    ValueBasedTransform.indexedRelate
        old.inputExp
        old.selectedFeatures
        old.selectedShapes
        old.slideNumber
        old.movieNumber
        old.movieTime
        old.syncOptions
  in
  { old | synthesisResults = cleanDedupSortSynthesisResults synthesisResults }

-- msgMakeEquidistant = Msg "Make Equidistant" <| \old ->
--   let newExp =
--     ValueBasedTransform.makeEquidistant
--         old.inputExp
--         old.selectedFeatures
--         old.slideNumber
--         old.movieNumber
--         old.movieTime
--         old.slate
--         old.syncOptions
--   in
--   runWithErrorHandling old newExp (\reparsed newVal newWidgets newSlate newCode ->
--     debugLog "new model" <|
--       { old | code             = newCode
--             , inputExp         = reparsed
--             , inputVal         = newVal
--             , history          = addToHistory old.code old.history
--             , slate            = newSlate
--             , widgets          = newWidgets
--             , preview          = Nothing
--               -- we already ran it successfully once so it shouldn't crash the second time
--             , mode             = Utils.fromOk "MakeEquidistant MkLive" <|
--                                    mkLive old.syncOptions
--                                      old.slideNumber old.movieNumber old.movieTime reparsed
--                                      (newVal, newWidgets)
--             , selectedFeatures = Set.empty
--       }
--   )

--------------------------------------------------------------------------------

msgSelectSynthesisResult newExp = Msg "Select Synthesis Result" <| \old ->
  runWithErrorHandling old newExp (\reparsed newVal newWidgets newSlate newCode ->
    debugLog "new model" <|
      { old | code             = newCode
            , inputExp         = reparsed
            , inputVal         = newVal
            , history          = addToHistory newCode old.history
            , slate            = newSlate
            , widgets          = newWidgets
            , preview          = Nothing
            , synthesisResults = maybeRunAutoSynthesis old reparsed
            , mode             = Utils.fromOk "SelectSynthesisResult MkLive" <|
                                   mkLive old.syncOptions
                                     old.slideNumber old.movieNumber old.movieTime reparsed
                                     (newVal, newWidgets)
            , selectedFeatures = Set.empty
      }
  )

msgClearSynthesisResults = Msg "Clear Synthesis Results" <| \old ->
  { old | preview = Nothing, synthesisResults = [] }

--------------------------------------------------------------------------------

msgGroupBlobs = Msg "Group Blobs" <| \old ->
    case Blobs.isSimpleProgram old.inputExp of
      Nothing -> old
      Just simple ->
        let maybeAnchorPoint = ETransform.anchorOfSelectedFeatures old.selectedFeatures in
        let multipleSelectedBlobs = Dict.size old.selectedBlobs > 1 in
        case (maybeAnchorPoint, multipleSelectedBlobs) of
          (Ok Nothing, False)   -> old
          (Ok Nothing, True)    -> upstateRun <| ETransform.groupSelectedBlobs old simple
          (Ok (Just anchor), _) -> upstateRun <| ETransform.groupSelectedBlobsAround old simple anchor
          (Err err, _)          -> let _ = Debug.log "bad anchor" err in old

msgDuplicateBlobs = Msg "Duplicate Blobs" <| \old ->
  upstateRun <| ETransform.duplicateSelectedBlobs old

msgMergeBlobs = Msg "Merge Blobs" <| \old ->
  if Dict.size old.selectedBlobs <= 1 then old
  else upstateRun <| ETransform.mergeSelectedBlobs old

msgAbstractBlobs = Msg "Abstract Blobs" <| \old ->
  upstateRun <| ETransform.abstractSelectedBlobs old

msgReplicateBlob option = Msg "Replicate Blob" <| \old ->
  case Blobs.isSimpleProgram old.inputExp of
    Nothing     -> old
    Just simple -> upstateRun <| ETransform.replicateSelectedBlob option old simple

--------------------------------------------------------------------------------

msgToggleCodeBox = Msg "Toggle Code Box" <| \old ->
  { old | basicCodeBox = not old.basicCodeBox }

msgToggleOutput = Msg "Toggle Output" <| \old ->
  let m = case old.mode of
    Print _ -> refreshMode_ old
    _       -> Print (LangSvg.printSvg old.showGhosts old.slate)
  in
  { old | mode = m }

--------------------------------------------------------------------------------

msgStartAnimation = Msg "Start Animation" <| \old ->
  upstate msgRedraw { old | movieTime = 0, runAnimation = True }

msgRedraw = Msg "Redraw" <| \old ->
  case LangSvg.fetchEverything old.slideNumber old.movieNumber old.movieTime old.inputVal of
    Ok (newSlideCount, newMovieCount, newMovieDuration, newMovieContinue, newSlate) ->
      { old | slideCount    = newSlideCount
            , movieCount    = newMovieCount
            , movieDuration = newMovieDuration
            , movieContinue = newMovieContinue
            , slate         = newSlate }
    Err s -> { old | errorBox = Just s }

msgTickDelta deltaT = Msg ("Tick Delta " ++ toString deltaT) <| \old ->
  if old.movieTime < old.movieDuration then
    -- Prevent "jump" after slow first frame render.
    let adjustedDeltaT = if old.movieTime == 0.0 then clamp 0.0 50 deltaT else deltaT in
    let newMovieTime = clamp 0.0 old.movieDuration (old.movieTime + (adjustedDeltaT / 1000)) in
    upstate msgRedraw { old | movieTime = newMovieTime }
  else if old.movieContinue == True then
    upstate msgNextMovie old
  else
    { old | runAnimation = False }

msgNextSlide = Msg "Next Slide" <| \old ->
  if old.slideNumber >= old.slideCount then
    upstate msgStartAnimation
      { old | slideNumber = old.slideNumber
            , movieNumber = old.movieCount }
  else
    upstate msgStartAnimation
      { old | slideNumber = old.slideNumber + 1
            , movieNumber = 1 }

msgPreviousSlide = Msg "Previous Slide" <| \old ->
  if old.slideNumber <= 1 then
    upstate msgStartAnimation
      { old | slideNumber = 1, movieNumber = 1 }
  else
    let previousSlideNumber = old.slideNumber - 1 in
    let result =
      Eval.run old.inputExp |>
      Result.andThen (\(previousVal, _) ->
        LangSvg.resolveToMovieCount previousSlideNumber previousVal
        |> Result.map (\previousMovieCount ->
             upstate msgStartAnimation
               { old | slideNumber = previousSlideNumber
                     , movieNumber = previousMovieCount }
        )
      )
    in
    handleError old result

msgNextMovie = Msg "Next Movie" <| \old ->
  if old.movieNumber == old.movieCount && old.slideNumber < old.slideCount then
    upstate msgNextSlide old
  else if old.movieNumber < old.movieCount then
    upstate msgStartAnimation { old | movieNumber = old.movieNumber + 1 }
  else
    -- Last movie of slide show; skip to its end.
    upstate msgRedraw { old | movieTime    = old.movieDuration
                            , runAnimation = False }

msgPreviousMovie = Msg "Previous Movie" <| \old ->
  if old.movieNumber == 1 then
    upstate msgPreviousSlide old
  else
    upstate msgStartAnimation { old | movieNumber = old.movieNumber - 1 }

msgPauseResumeMovie = Msg "Pause/Resume Movie" <| \old ->
  { old | runAnimation = not old.runAnimation }

--------------------------------------------------------------------------------

showExpPreview old exp =
  let previewCode = unparse exp in
  case runAndResolve old exp of
    Ok (val, widgets, slate, _) ->
      { old | preview = Just (previewCode, Ok (val, widgets, slate)) }

    Err s ->
      { old | preview = Just (previewCode, Err s) }

msgSelectOption (exp, val, slate, code) = Msg "Select Option..." <| \old ->
  { old | code          = code
        , inputExp      = exp
        , inputVal      = val
        , history       = addToHistory code old.history
        , slate         = slate
        , preview       = Nothing
        , synthesisResults = []
        , tool          = Cursor
        , mode          = Utils.fromOk "SelectOption mkLive" <|
                            mkLive old.syncOptions old.slideNumber old.movieNumber old.movieTime exp
                              (val, []) -- TODO
        }

msgHoverSynthesisResult pathByIndices = Msg "Hover SynthesisResult" <| \old ->
  let maybeFindResult path results =
    case path of
      []    -> Nothing
      [i]   -> Utils.maybeGet0 i results
      i::is -> Utils.maybeGet0 i results |> Maybe.andThen (\(SynthesisResult {children}) -> children |> Maybe.andThen (maybeFindResult is))
  in
  let setResultChildren path childResults oldResults =
    case path of
      []    -> oldResults
      [i]   -> oldResults |> Utils.getReplacei0 i (\(SynthesisResult attrs) -> SynthesisResult { attrs | children = Just childResults})
      i::is -> oldResults |> Utils.getReplacei0 i (\(SynthesisResult attrs) -> SynthesisResult { attrs | children = Just (setResultChildren is childResults (attrs.children |> Maybe.withDefault []))})
  in
  case maybeFindResult pathByIndices old.synthesisResults of
    Just (SynthesisResult {description, exp, sortKey, children}) ->
      let newModel = { old | hoveredSynthesisResultPathByIndicies = pathByIndices } in
      let newModel2 =
        case (old.autoSynthesis, children) of
          (_, Just _)  -> newModel -- Children already computed.
          (False, _)   -> newModel -- Don't compute children if auto-synth off
          _            ->
            -- Compute child results.
            let childResults = cleanDedupSortSynthesisResults (ETransform.passiveSynthesisSearch exp) in
            let newTopLevelResults = setResultChildren pathByIndices childResults old.synthesisResults in
            { newModel | synthesisResults = newTopLevelResults
                       , hoveredSynthesisResultPathByIndicies = pathByIndices }
      in
      showExpPreview newModel2 exp

    Nothing ->
      { old | preview = Nothing
            , hoveredSynthesisResultPathByIndicies = [] }

msgPreview exp = Msg "Preview" <| (\old -> showExpPreview old exp)

msgClearPreview = Msg "Clear Preview" <| \old ->
  { old | preview = Nothing }

msgCancelSync = Msg "Cancel Sync" <| \old ->
  upstateRun
    { old | mode = Utils.fromOk "CancelSync mkLive_" <|
              mkLive_ old.syncOptions old.slideNumber old.movieNumber old.movieTime old.inputExp }

--------------------------------------------------------------------------------

requireSaveAsker ((Msg name _) as msg) needsSave =
  if needsSave then
    Msg ("Ask " ++ name) <| (\old ->
      { old | pendingFileOperation = Just <| msg
            , fileOperationConfirmed = False })
        >> Model.openDialogBox AlertSave
  else
    msg

--------------------------------------------------------------------------------

-- Dialog Box

msgOpenDialogBox db =
  Msg "Open Dialog Box" <| Model.openDialogBox db

msgCloseDialogBox db =
  Msg "Close Dialog Box" <| Model.closeDialogBox db

msgUpdateFilenameInput str = Msg "Update Filename Input" <| \old ->
  { old | filenameInput = str }

--------------------------------------------------------------------------------
-- File Handling API

confirmWrite savedFilename old =
  { old | needsSave = False
        , lastSaveState = Just old.code }

confirmDelete deletedFilename = identity

requestFile requestedFilename old =
  { old | filename = requestedFilename }

readFile file old =
  { old | filename = file.filename
        , code = file.code
        , history = ([file.code], [])
        , lastSaveState = Just file.code
        , needsSave = False }

loadIcon env icon old =
  let
    iconNameLower =
      String.toLower icon.iconName
    actualCode =
      if icon.code /= "" then
        icon.code
      else
        case Dict.get iconNameLower DefaultIconTheme.icons of
          Just c ->
            c
          Nothing ->
            "(blobs [])"
    oldIcons =
      old.icons
    iconHtml =
      Canvas.iconify env actualCode
    newIcons =
      Dict.insert icon.iconName iconHtml oldIcons
  in
    { old | icons = newIcons }

loadLambdaToolIcons finalEnv old =
  let foo tool acc =
    let icon = lambdaToolIcon tool in
    if Dict.member (String.toLower icon.iconName) old.icons
      then acc
      else loadIcon finalEnv icon old
  in
  List.foldl foo old old.lambdaTools

readFileFromInput file old =
  { old | filename = file.filename
        , code = file.code
        , history = ([file.code], [])
        , lastSaveState = Nothing
        , needsSave = True }

updateFileIndex fileIndex old =
  { old | fileIndex = fileIndex }

-- Subscription Handlers

msgConfirmWrite savedFilename =
  Msg "Confirm Write" <| confirmWrite savedFilename

msgConfirmDelete deletedFilename =
  Msg "Confirm Delete" <| confirmDelete deletedFilename

msgReadFile file =
  Msg "Read File" <| readFile file >> upstateRun

msgLoadIcon file =
  Msg "Load Icon" <| loadIcon Eval.initEnv file

msgReadFileFromInput file =
  Msg "Read File From Input" <| readFileFromInput file >> upstateRun

msgUpdateFileIndex fileIndex =
  Msg "Update File Index" <| updateFileIndex fileIndex

--------------------------------------------------------------------------------
-- File Operations

msgNew template = Msg "New" <| (\old ->
  case Utils.maybeFind template Examples.list of
    Nothing -> let _ = Debug.log "WARN: not found:" template in old
    Just (_, thunk) ->
      let {e,v,ws,ati} = thunk () in
      let (so, m) =
        case old.mode of
          Live _  -> let so = Sync.syncOptionsOf old.syncOptions e in
                     (so, Utils.fromOk "SelectExample mkLive_" <|
                        mkLive so old.slideNumber old.movieNumber old.movieTime e (v,ws))
          Print _ -> let so = Sync.syncOptionsOf old.syncOptions e in
                     (so, Utils.fromOk "SelectExample mkLive_" <|
                        mkLive so old.slideNumber old.movieNumber old.movieTime e (v,ws))
      in
      LangSvg.fetchEverything old.slideNumber old.movieNumber old.movieTime v
      |> Result.map (\(slideCount, movieCount, movieDuration, movieContinue, slate) ->
        let code = unparse e in
        { initModel | inputExp      = e
                    , inputVal      = v
                    , code          = code
                    , history       = ([code],[])
                    , mode          = m
                    , syncOptions   = so
                    , slideNumber   = 1
                    , slideCount    = slideCount
                    , movieCount    = movieCount
                    , movieTime     = 0
                    , movieDuration = movieDuration
                    , movieContinue = movieContinue
                    , runAnimation  = movieDuration > 0
                    , slate         = slate
                    , widgets       = ws
                    , codeBoxInfo   = updateCodeBoxWithTypes ati old.codeBoxInfo
                    , filename      = Model.bufferName
                    , needsSave     = True
                    , lastSaveState = Nothing
                    , dimensions    = old.dimensions
                    , syncOptions   = old.syncOptions
                    , localSaves    = old.localSaves
                    , basicCodeBox  = old.basicCodeBox
                    , randomColor   = old.randomColor
                    , layoutOffsets = old.layoutOffsets
                    , fileIndex     = old.fileIndex
                    , icons         = old.icons
                    }
      ) |> handleError old) >> closeDialogBox New

msgAskNew template = requireSaveAsker (msgNew template)

msgSaveAs =
  let
    switchFilenameToInput old =
      { old | filename = old.filenameInput }
    closeDialogBoxIfNecessary old =
      if old.filename /= Model.bufferName then
        Model.closeDialogBox SaveAs old
      else
        old
  in
    Msg "Save As" (switchFilenameToInput >> closeDialogBoxIfNecessary)

msgSave = Msg "Save" <| \old ->
  if old.filename == Model.bufferName then
    Model.openDialogBox SaveAs old
  else
    old

msgOpen filename =
  Msg "Open" (requestFile filename >> closeDialogBox Open)

msgAskOpen filename = requireSaveAsker (msgOpen filename)

msgDelete filename =
  Msg "Delete" <| \old ->
    if filename == old.filename then
      { old | fileToDelete = filename
            , needsSave = True
            , lastSaveState = Nothing }
    else
      { old | fileToDelete = filename }

msgCancelFileOperation = Msg "Cancel File Operation" <| (\old ->
  { old | pendingFileOperation = Nothing
        , fileOperationConfirmed = False })
    >> Model.closeDialogBox AlertSave

msgConfirmFileOperation = Msg "Confirm File Operation" <| (\old ->
  { old | fileOperationConfirmed = True })
    >> Model.closeDialogBox AlertSave

msgToggleAutosave = Msg "Toggle Autosave" <| \old ->
  { old | autosave = not old.autosave }

--------------------------------------------------------------------------------
-- Exporting

msgExportCode = Msg "Export Code" identity

msgExportSvg = Msg "Export SVG" identity

--------------------------------------------------------------------------------
-- Importing

msgImportCode = Msg "Import Code" <| closeDialogBox ImportCode

msgAskImportCode = requireSaveAsker msgImportCode
