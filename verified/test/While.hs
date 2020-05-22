module While where

import Lib
import FormatPareto

w = 50

testData = besideDoc w (choiceDoc (besideDoc w (constructDoc "if (a == 3) ") (constructDoc "then "))
                     (aboveDoc w (constructDoc "if (a == 3)") (constructDoc "then")))
                     (fillDoc w (constructDoc "a = 6; ") (aboveDoc w (constructDoc "b = 5; ") (constructDoc "c = 8; ")) 4)
