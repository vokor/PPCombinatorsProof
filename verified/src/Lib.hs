module Lib
    ( pretty
    ) where

import FormatPareto
import BaseFun
import Format
import Data.Type.Natural

get_min_height :: [T0] -> Nat -> (Option Nat) -> Option Nat
get_min_height lst w res =
  case lst of {
   [] -> res;
   hd:tl ->
    case leb (total_width hd) w of {
     True ->
      case res of {
       Some n -> get_min_height tl w (Some (min n (height hd)));
       None -> get_min_height tl w (Some (height hd))};
     False -> get_min_height tl w res}}

pick_best_list :: [T0] -> Nat -> [T0]
pick_best_list lst w =
  case lst of {
   [] -> [];
   _:_ ->
    case get_min_height lst w None of {
     Some n ->
      filter (\f -> andb (leb (total_width f) w) (eqb (height f) n)) lst;
     None -> []}}

pretty :: [T0] -> Nat -> IO ()
pretty d w = putStrLn (foldr (\f m ->
    ((to_text f 0 "") ++ "----------------\n" ++ m))
    ""
    (pick_best_list d w))
