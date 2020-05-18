module FormatPareto where

import BaseFun
import Format
import Data.Type.Natural

map_filter :: (T0 -> T0) -> (T0 -> Bool) -> [T0] -> [T0]
map_filter mapf filterf l =
  foldr (\a lst ->
    let {b = mapf a} in case filterf b of {
                         True -> b:lst;
                         False -> lst}) [] l

is_less_exist :: T0 -> [T0] -> Bool
is_less_exist a lst =
  existsb (flip is_less_than a) lst

pareto_by_elem :: T0 -> [T0] -> [T0]
pareto_by_elem a lst =
  filter (compose negb (is_less_than a)) lst

pareto_exec :: [T0] -> [T0] -> [T0]
pareto_exec acc mas =
  case mas of {
   [] -> acc;
   x:xs ->
    case is_less_exist x acc of {
     True -> pareto_exec acc xs;
     False -> pareto_exec (app (pareto_by_elem x acc) (x:[])) xs}}

pareto :: [T0] -> [T0]
pareto lst =
  pareto_exec [] lst

add_general :: (T0 -> T0 -> T0) -> Nat -> [T0] -> T0 -> [T0]
add_general op width fl f =
  map_filter (\f' -> op f' f) (\f0 -> leb (total_width f0) width) fl

cross_general :: (T0 -> T0 -> T0) -> Nat -> [T0] -> [T0] -> [T0]
cross_general op width fl1 fl2 =
  let {cross_lst = concat (map (add_general op width fl1) fl2)} in
  pareto cross_lst

constructDoc :: String -> [T0]
constructDoc s = (of_string s):[]

indentDoc :: Nat -> Nat -> [T0] -> [T0]
indentDoc width shift fs =
  map_filter (indent' shift) (\f -> leb (total_width f) width) fs

besideDoc :: Nat -> [T0] -> [T0] -> [T0]
besideDoc width fs1 fs2 =
  cross_general add_beside width fs1 fs2

aboveDoc :: Nat -> [T0] -> [T0] -> [T0]
aboveDoc width fs1 fs2 =
  cross_general add_above width fs1 fs2

fillDoc :: Nat -> [T0] -> [T0] -> Nat -> [T0]
fillDoc width fs1 fs2 shift =
  cross_general (\fs f -> add_fill fs f shift) width fs1 fs2

choiceDoc :: [T0] -> [T0] -> [T0]
choiceDoc fs1 fs2 =
  pareto (app fs1 fs2)
