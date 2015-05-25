--A set of functions to assist with viewing in
--Interface.elm
module InterfaceView where
--imports copied from Interface.elm
--TODO: some of these could probably be cleaned up

--Import the little language and its parsing utilities
import Lang exposing (..) --For access to what makes up the Vals
import LangParser exposing (parseE, parseV)
import Sync exposing (sync, Triggers)
import Eval exposing (run)
import MainSvg
import Utils
import MicroTests
import InterfaceUtils exposing (..)
import LangSvg exposing (IndexedTree, NodeId, ShapeKind, Attr, toNum, addi)
import VirtualDom

--Core Libraries
import List 
import Dict
import String 
import Graphics.Element as GE 
import Graphics.Collage as GC

--Signaling Libraries
import Mouse 
import Window 

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

-- View --
codeBox : String -> Bool -> Html.Html
codeBox code switch =
    let
        --depending on switch, toggle manipulatability
        event = case switch of
            True -> []
            False ->  [(Events.on "input" Events.targetValue
                (Signal.message events.address << CodeUpdate))]
    in
        --build text area
        Html.textarea
            ([ Attr.id "codeBox"
            , Attr.style
                [ ("height", "100%")
                , ("width",  "100%")
                , ("resize", "none")
                , ("overflow", "scroll")
                ]
            , Attr.value code
            ]
            ++
            --add event, if it exsists
            event)
            []

--Build viusal pane and populate with the model's objects
visualsBox : List Object -> Float -> Bool -> Html.Html
visualsBox objects dim switch =
  Svg.svg [ Attr.style [ ("width", "100%"), ("height", "100%") ] ]
          (List.map fst objects)

--Umbrella function for taking and indexed tree and calling buildSvg over it
buildVisual : LangSvg.IndexedTree -> List (Svg.Svg, List Attr)
buildVisual valDict = List.map buildSvg (Dict.toList valDict)

--Function for handling attributes and children of an indexed tree and building them
--into Svgs with attr lists to be updated as necessary
buildSvg : (LangSvg.NodeId, LangSvg.IndexedTreeNode) -> (Svg.Svg, List Attr)
buildSvg (nodeID, node) = case node of
    LangSvg.TextNode text ->
      let str = LangSvg.AString in
      (VirtualDom.text text, [("shape", str "TEXT"), ("text", str text)])
    LangSvg.SvgNode shape attrs childrenids ->
      let zones = makeZones shape nodeID attrs in
      let mainshape = (LangSvg.svg shape) (LangSvg.compileAttrs attrs) [] in
      (Svg.svg [] (mainshape :: zones), attrs)

attrNum k v = LangSvg.compileAttr k (LangSvg.ANum v)

onMouseDown = Svg.Events.onMouseDown << Signal.message events.address
onMouseUp   = Svg.Events.onMouseUp   << Signal.message events.address

zoneEvents id shape zone =
  [ onMouseDown (SelectObject id shape zone)
  , onMouseUp (DeselectObject id) ]

zone svgFunc id shape zone l =
  svgFunc (zoneEvents id shape zone ++ l) []

-- TODO use zone
zoneBorder svgFunc id shape zone flag =
  flip svgFunc [] <<
  (++) (zoneEvents id shape zone) <<
  (++) [ LangSvg.attr "stroke" "rgba(255,0,0,0.5)"
       , LangSvg.attr "strokeWidth" (if flag then "5" else "0")
       , LangSvg.attr "fill" "rgba(0,0,0,0)"
       ]

zonePoint id shape zone =
  flip Svg.circle [] <<
  (++) (zoneEvents id shape zone) <<
  (++) [ LangSvg.attr "r" "6"
       , LangSvg.attr "fill" "rgba(255,0,0,0.5)"
       ]

zonePoints id shape (LangSvg.APoints pts) =
  flip Utils.mapi pts <| \(i, (x,y)) ->
    zonePoint id shape (addi "Point" i) [ attrNum "cx" x, attrNum "cy" y ]

--Zone building function (still under construction/prone to change)                
makeZones : String -> LangSvg.NodeId -> List Attr -> List Svg.Svg
makeZones shape id l =
  case shape of

    "circle" ->
        let [cx,cy,r] = List.map (toNum << Utils.find_ l) ["cx","cy","r"] in
        let gutterPct = 0.100 in
        let zInterior =
          zoneBorder Svg.circle id shape "Interior" False [
              attrNum "cx" cx , attrNum "cy" cy
            , attrNum "r" (r * (1 - 2*gutterPct))
            ] in
        let zEdge =
          zoneBorder Svg.circle id shape "Edge" True [
              attrNum "cx" cx , attrNum "cy" cy
            , attrNum "r" (r * (1))
            ] in
        [zEdge, zInterior]

    "rect" ->
        let mk zone x_ y_ w_ h_ =
          zoneBorder Svg.rect id shape zone True [
              attrNum "x" x_ , attrNum "y" y_
            , attrNum "width" w_ , attrNum "height" h_
            ]
        in
        let
          [x,y,w,h]     = List.map (toNum << Utils.find_ l) ["x","y","width","height"]
          gut           = 0.125
          (x0,x1,x2)    = (x, x + gut*w, x + (1-gut)*w)
          (y0,y1,y2)    = (y, y + gut*h, y + (1-gut)*h)
          (wSlim,wWide) = (gut*w, (1-2*gut)*w)
          (hSlim,hWide) = (gut*h, (1-2*gut)*h)
        in
          [ mk "Interior"       x1 y1 wWide hWide
          , mk "RightEdge"      x2 y1 wSlim hWide
          , mk "BotRightCorner" x2 y2 wSlim hSlim
          , mk "BotEdge"        x1 y2 wWide hSlim
          , mk "BotLeftCorner"  x0 y2 wSlim hSlim
          , mk "LeftEdge"       x0 y1 wSlim hWide
          , mk "TopLeftCorner"  x0 y0 wSlim hSlim
          , mk "TopEdge"        x1 y0 wWide hSlim
          , mk "TopRightCorner" x2 y0 wSlim hSlim
          ]

    "ellipse" ->
        let [cx,cy,rx,ry] = List.map (toNum << Utils.find_ l) ["cx","cy","rx","ry"] in
        let gutterPct = 0.100 in
        let zInterior =
          zoneBorder Svg.ellipse id shape "Interior" False [
              attrNum "cx" cx , attrNum "cy" cy
            , attrNum "rx" (rx * (1 - 2*gutterPct))
            , attrNum "ry" (ry * (1 - 2*gutterPct))
            ] in
        let zEdge =
          zoneBorder Svg.ellipse id shape "Edge" True [
              attrNum "cx" cx , attrNum "cy" cy
            , attrNum "rx" (rx * (1))
            , attrNum "ry" (ry * (1))
            ] in
        [zEdge, zInterior]

    "line" ->
        let [x1,y1,x2,y2] = List.map (toNum << Utils.find_ l) ["x1","y1","x2","y2"] in
        let zPts = zonePoints id shape (LangSvg.APoints [(x1,y1),(x2,y2)]) in
        let zLine =
          -- TODO use zone instead, since stroke* is getting defined here
          zoneBorder Svg.line id shape "Edge" False [
              attrNum "x1" x1 , attrNum "y1" y1
            , attrNum "x2" x2 , attrNum "y2" y2
            , LangSvg.compileAttr "stroke" (Utils.find_ l "stroke")
            , LangSvg.compileAttr "strokeWidth" (Utils.find_ l "strokeWidth")
            ] in
        zLine :: zPts

    "polygon" ->
        let pts = Utils.find_ l "points" in
        let zPts = zonePoints id shape pts in
        let zInterior =
          zoneBorder Svg.polygon id shape "Interior" False [
              LangSvg.compileAttr "points" pts
            ] in
        zInterior :: zPts

    _ -> []

--Umbrella function for viewing a given model
view : (Int, Int) -> Model -> Html.Html
view wh model =
  case model.mode of
    AdHoc        -> regularView wh model
    Live _       -> regularView wh model
    SyncSelect l -> selectView wh model l

regularView (w,h) model =
    let
        testlist = 
            List.reverse <| List.map (\(i,s) -> Html.option 
                [ Events.onClick events.address (CodeUpdate (sExpK 1 s.e))
                --, Events.onClick events.address Render
                ] 
                [Html.text ("test"++ (toString (i + 14)))]) 
                -- TODO: not a good idea to render all examples all the time...
                --       should only render an example when it is selected.
                -- (Utils.mapi identity (List.map Utils.thd3 MainSvg.tests))
                []
    in
                  Html.div
                    [ Attr.style
                        [ ("width", toString w)
                        , ("height", toString h)
                        ]
                    ]
                    --display code & visuals
                    ([renderView (w,h) model
                    , Html.button
                        [ Attr.style
                            [ ("position", "absolute")
                            , ("left", String.append (toString <| w // 8) "px")
                            , ("top", String.append (toString <| h - 40) "px")
                            , ("type", "button")
                            , ("width", "100px")
                            , ("height", "40px")
                            ]
                        , Events.onClick events.address Render
                        , Attr.value "Render"
                        , Attr.name "Render the Code"
                        ]
                        [Html.text "render"]
                    , Html.select
                        [ Attr.style
                            [ ("position", "absolute")
                            , ("left", String.append (toString <| (w // 8 + 200)) "px")
                            , ("top", String.append (toString <| h - 40) "px")
                            , ("type", "button")
                            , ("width", "100px")
                            , ("height", "40px")
                            ]
                        ]
                        [ let e = Utils.fromJust model.inputExp in
                          let v = Eval.run e in
                          let mode = Live <| Sync.prepareLiveUpdates e v in
                            Html.option [Events.onClick events.address (SwitchMode mode)]
                                [Html.text "live"]
                            , Html.option [Events.onClick events.address (SwitchMode AdHoc)] 
                                [Html.text "ad hoc"]
                        ]  
                    , Html.select
                        [ Attr.style
                            [ ("position", "absolute")
                            , ("left", String.append (toString <| w // 8 + 400) "px")
                            , ("top", String.append (toString <| h - 40) "px")
                            , ("type", "button")
                            , ("width", "100px")
                            , ("height", "40px")
                            ]
                        ]
                        testlist
                    ]
                    ++
                    (case model.mode of
                        SyncSelect _ -> []
                        Live _ -> []
                        AdHoc -> 
                            [Html.button
                                [ Attr.style
                                    [ ("position", "absolute")
                                    , ("left", String.append (toString <| w // 8 + 600) "px")
                                    , ("top", String.append (toString <| h - 40) "px")
                                    , ("type", "button")
                                    , ("width", "100px")
                                    , ("height", "40px")
                                    ]
                                , Events.onClick events.address Sync
                                , Attr.value "Sync"
                                , Attr.name "Sync the code to the canvas"
                                ]
                                [Html.text "sync"]
                            ]
                    ))

--When view is manipulatable, call this function for code & visuals
--to build corresponding panes
renderView : (Int, Int) -> Model -> Html.Html
renderView (w,h) model = 
    let
        dim = (Basics.toFloat (Basics.min w h)) / 2
    in
        Html.div
            [ Attr.style
                [ ("width", toString w)
                , ("height", toString h)
                ]
            ]
            [ Html.div 
                [ Attr.style
                    [ ("width", String.append (toString <| w // 2 - 1) "px")
                    , ("height", String.append (toString <| h - 60) "px")
                    , ("margin", "0")
                    , ("position", "absolute")
                    , ("left", "0px")
                    , ("top", "0px")
                    ]
                ]
                [codeBox model.code (syncBool model.mode)]
            , Html.div
                [ Attr.style
                    [ ("width", String.append (toString <| w // 2 - 1) "px")
                    , ("height", String.append (toString h) "px")
                    , ("margin", "0")
                    , ("position", "absolute")
                    , ("left", String.append (toString <| w // 2) "px")
                    , ("top", "0px")
                    ]
                ]    
                [visualsBox (buildVisual model.workingSlate) dim (syncBool model.mode)]
            ]

--Build an Html of the iterations of renderOption over the possibleChanges
selectView : (Int, Int) -> Model -> PossibleChanges -> Html.Html
selectView (w,h) model possibleChanges =
    let
        dim = (Basics.toFloat (Basics.min w h)) / 2
    in
        Html.div
        []
        --index the possible changes and render these options
        (renderOption (w, h // 4) (Utils.mapi (\x -> x) possibleChanges) model dim)
            
--Given a possible Change, build code from Expr and visuals from the val, rank by priority w/ mapi
renderOption : (Int, Int) -> List (Int, ((Exp, Val), Float)) -> Model -> Float -> List Html.Html
renderOption (w,h) possiblechanges model dim =
    case possiblechanges of
        --if there is a possible change remaining, display this option
        (i, ((e,v), f))::ps -> 
            (Html.div
                [ Attr.style
                    [ ("width", toString w)
                    , ("height", toString h)
                    , ("top", String.append (toString <| h * (i-1)) "px")
                    , ("position", "absolute")
                    ]
                ]
                [ Html.div 
                    [ Attr.style
                        [ ("width", String.append (toString <| w // 2 - 30) "px")
                        , ("height", String.append (toString <| h) "px")
                        , ("margin", "0")
                        , ("position", "absolute")
                        , ("left", "0px")
                        , ("top", "0px") -- String.append (toString <| h * (i-1)) "px")
                        ]
                    ]
                    [codeBox (sExpK 1 e) (syncBool model.mode)]
                , Html.div
                    [ Attr.style
                        [ ("width", String.append (toString <| w // 2 - 50) "px")
                        , ("height", String.append (toString h) "px")
                        , ("margin", "0")
                        , ("position", "absolute")
                        , ("left", String.append (toString <| w // 2) "px")
                        , ("top", "0px") --String.append (toString <| h * (i-1)) "px")
                        ]
                    ]    
                    [visualsBox (buildVisual <| LangSvg.valToIndexedTree v) dim (syncBool model.mode)] --TODO: parse val to svgs
--                , Html.button
--                    [ Attr.style
--                        [ ("position", "absolute")
--                        , ("left", String.append (toString <| w // 4) "px")
--                        , ("top", "0px) --String.append (toString <| h - 40) "px")
--                        , ("type", "button")
--                        , ("width", "100px")
--                        , ("height", "40px")
--                        ]
--                    , Events.onClick events.address (SelectOption ((e,v), f))
--                    , Attr.value "Select"
--                    , Attr.name "Select this codebox and visualbox"
--                    ]
--                    [Html.text "select"]
                --attach remaining option htmls
                ]) :: renderOption (w,h) ps model dim
        [] -> []