module Main exposing (main)

-- import InterfaceModel as Model exposing (Msg, Model)
-- import InterfaceView3 as View
-- import InterfaceController as Controller
-- import AceCodeBox
-- import AnimationLoop
-- import FileHandler
--
-- import Html exposing (Html)
-- import Mouse
-- import Window
-- import Keyboard
-- import Time
--
-- import Task exposing (Task, andThen)
--
--
-- --------------------------------------------------------------------------------
-- -- Main
--
-- main : Program Never Model Msg
-- main =
--   Html.program
--     { init = init
--     , view = view
--     , update = update
--     , subscriptions = subscriptions
--     }
--
-- init : (Model, Cmd Msg)
-- init = (Model.initModel, initCmd)
--
-- view : Model -> Html Msg
-- view = View.view
--
-- update : Msg -> Model -> (Model, Cmd Msg)
-- update = Controller.update
--
-- initCmd : Cmd Msg
-- initCmd =
--   Cmd.batch
--     [ Task.perform Controller.msgWindowDimensions Window.size
--     , AceCodeBox.initializeAndDisplay Model.initModel
--     , Task.perform Controller.msgNew (Task.succeed "BLANK")
--     , Cmd.batch <| List.map FileHandler.requestIcon Model.iconNames
--     , Task.perform Controller.msgLoadIcon (Task.succeed (Model.starLambdaToolIcon))
--     ]
--
-- subscriptions : Model -> Sub Msg
-- subscriptions model =
--   Sub.batch
--     [ Window.resizes Controller.msgWindowDimensions
--     , Mouse.downs (always (Controller.msgMouseIsDown True))
--     , Mouse.ups (always (Controller.msgMouseIsDown False))
--     , Mouse.moves Controller.msgMousePosition
--     , Keyboard.presses Controller.msgKeyPress
--     , Keyboard.downs Controller.msgKeyDown
--     , Keyboard.ups Controller.msgKeyUp
--     , AceCodeBox.receiveEditorState Controller.msgAceUpdate
--     , AnimationLoop.receiveFrame Controller.msgTickDelta
--     , FileHandler.writeConfirmation Controller.msgConfirmWrite
--     , FileHandler.deleteConfirmation Controller.msgConfirmDelete
--     , FileHandler.receiveFile Controller.msgReadFile
--     , FileHandler.receiveIcon Controller.msgLoadIcon
--     , FileHandler.receiveFileFromInput Controller.msgReadFileFromInput
--     , FileHandler.receiveFileIndex Controller.msgUpdateFileIndex
--     ]


import Html exposing (Html)
import Html.Attributes exposing (..)
import Html.Events exposing (..)
import Task exposing (Task, andThen)

import Parser
import FastParser

--------------------------------------------------------------------------------
-- Model
--------------------------------------------------------------------------------

type alias Model = String

init =
  ("", Cmd.none)

--------------------------------------------------------------------------------
-- Update
--------------------------------------------------------------------------------

type Msg
  = TextUpdate String
  | NoUpdate

update msg model =
  case msg of
    (TextUpdate s) ->
      (s, Cmd.none)
    NoUpdate ->
      (model, Cmd.none)

--------------------------------------------------------------------------------
-- View
--------------------------------------------------------------------------------

displayModel model =
  let
    showContext c =
      Html.p
        []
        [ Html.text <|
            "(row: " ++ (toString c.row) ++ ", col: " ++ (toString c.col)
              ++ ") Error trying to parse '" ++ c.description ++ "'."
        ]
    (color, status, body) =
      case (FastParser.parse model) of
        (Ok exp) ->
          ("#008800"
          , "Success"
          , Html.p [] [ Html.text <| toString exp ]
          )
        (Err err) ->
          ("#880000"
          , "Error"
          , Html.div
              []
              [ Html.h3 [] [ Html.text "Position" ]
              , Html.p [] [ Html.text <| "Row: " ++ toString err.row ]
              , Html.p [] [ Html.text <| "Col: " ++ toString err.col ]
              , Html.h3 [] [ Html.text "Problem" ]
              , Html.p [] [ Html.text <| toString err.problem ]
              , Html.h3 [] [ Html.text "Context Stack" ]
              , Html.p [] <| List.map showContext err.context
              ]
          )
  in
    Html.div
      [ style [ ("color", color) ] ]
      [ Html.h2 [] [ Html.text <| "Output (" ++ status ++ ")"]
      , body
      ]

view model =
  Html.div
    [ style
        [ ("padding", "20px")
        , ("font-family", "monospace")
        ]
    ]
    [ Html.h1 [] [ Html.text "FastParser" ]
    , Html.h2 [] [ Html.text "Input" ]
    , Html.textarea
        [ onInput TextUpdate
        , cols 80
        , rows 20
        ]
        []
    , Html.div
        [ style
          [ ("margin-top", "20px")
          ]
        ]
        [ displayModel model ]
    ]

--------------------------------------------------------------------------------
-- Subscriptions
--------------------------------------------------------------------------------

subscriptions model =
  Sub.none

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main : Program Never Model Msg
main =
  Html.program
    { init = init
    , view = view
    , update = update
    , subscriptions = subscriptions
    }
