module FastParser exposing (test)

import Parser exposing (..)
import Debug


--testProgram = "(blobs [])"
testProgram = " [ 1 , 2 , 3 ] "

test _ = Debug.log (parse testProgram) 0

parse = run intList

nextInt : Parser Int
nextInt =
  delayedCommit spaces <|
    succeed identity
    |. symbol ","
    |. spaces
    |= int

intListHelp : List Int -> Parser (List Int)
intListHelp revInts =
  oneOf
    [ nextInt
        |> andThen (\n -> intListHelp (n :: revInts))
    , succeed (List.reverse revInts)
    ]

intList : Parser (List Int)
intList =
  succeed identity
  |. symbol "["
  |. spaces
  |= andThen (\n -> intListHelp [n]) int
  |. spaces
  |. symbol "]"
