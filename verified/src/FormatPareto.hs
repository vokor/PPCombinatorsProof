module FormatPareto where

import qualified Prelude
import BaseFun
import Format

map_filter :: (T0 -> T0) -> (T0 -> Prelude.Bool) -> (([]) T0) -> ([]) T0
map_filter mapf filterf l =
  fold_right (\a lst ->
    let {b = mapf a} in
    case filterf b of {
     Prelude.True -> (:) b lst;
     Prelude.False -> lst}) ([]) l

is_less_exist :: T0 -> (([]) T0) -> Prelude.Bool
is_less_exist a lst =
  existsb (flip is_less_than a) lst

pareto_by_elem :: T0 -> (([]) T0) -> ([]) T0
pareto_by_elem a lst =
  filter (compose Prelude.not (is_less_than a)) lst

pareto_exec :: (([]) T0) -> (([]) T0) -> ([]) T0
pareto_exec acc mas =
  case mas of {
   ([]) -> acc;
   (:) x xs ->
    case is_less_exist x acc of {
     Prelude.True -> pareto_exec acc xs;
     Prelude.False ->
      pareto_exec (app (pareto_by_elem x acc) ((:) x ([]))) xs}}

pareto :: (([]) T0) -> ([]) T0
pareto lst =
  pareto_exec ([]) lst

add_general :: (T0 -> T0 -> T0) -> Prelude.Int -> (([]) T0) -> T0 -> ([]) T0
add_general op width fl f =
  map_filter (\f' -> op f' f) (\f0 -> (Prelude.<=) (total_width f0) width) fl

cross_general :: (T0 -> T0 -> T0) -> Prelude.Int -> (([]) T0) -> (([])
                 T0) -> ([]) T0
cross_general op width fl1 fl2 =
  let {cross_lst = concat (map (add_general op width fl1) fl2)} in
  pareto cross_lst

constructDoc :: Prelude.String -> ([]) T0
constructDoc s =
  (:) (of_string s) ([])

indentDoc :: Prelude.Int -> Prelude.Int -> (([]) T0) -> ([]) T0
indentDoc width shift0 fs =
  map_filter (indent' shift0) (\f -> (Prelude.<=) (total_width f) width) fs

besideDoc :: Prelude.Int -> (([]) T0) -> (([]) T0) -> ([]) T0
besideDoc width fs1 fs2 =
  cross_general add_beside width fs1 fs2

aboveDoc :: Prelude.Int -> (([]) T0) -> (([]) T0) -> ([]) T0
aboveDoc width fs1 fs2 =
  cross_general add_above width fs1 fs2

fillDoc :: Prelude.Int -> (([]) T0) -> (([]) T0) -> Prelude.Int -> ([]) T0
fillDoc width fs1 fs2 shift0 =
  cross_general (\fs f -> add_fill fs f shift0) width fs1 fs2

choiceDoc :: (([]) T0) -> (([]) T0) -> ([]) T0
choiceDoc fs1 fs2 =
  pareto (app fs1 fs2)
