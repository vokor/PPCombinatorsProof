module Lib
    ( pretty
    ) where

import qualified Prelude

import FormatPareto
import BaseFun
import Format

get_min_height :: (([]) T0) -> Prelude.Int -> (Prelude.Maybe Prelude.Int) ->
                  Prelude.Maybe Prelude.Int
get_min_height lst w res =
  case lst of {
   ([]) -> res;
   (:) hd tl ->
    case (Prelude.<=) (total_width hd) w of {
     Prelude.True ->
      case res of {
       Prelude.Just n ->
        get_min_height tl w (Prelude.Just (Prelude.min n (height hd)));
       Prelude.Nothing -> get_min_height tl w (Prelude.Just (height hd))};
     Prelude.False -> get_min_height tl w res}}

pick_best_list :: (([]) T0) -> Prelude.Int -> ([]) T0
pick_best_list lst w =
  case lst of {
   ([]) -> ([]);
   (:) _ _ ->
    case get_min_height lst w Prelude.Nothing of {
     Prelude.Just n ->
      filter (\f ->
        (Prelude.&&) ((Prelude.<=) (total_width f) w)
          ((Prelude.==) (height f) n)) lst;
     Prelude.Nothing -> ([])}}

pretty :: [T0] -> Prelude.Int -> Prelude.IO ()
pretty d w = Prelude.putStrLn (Prelude.foldr (\f m ->
    ((to_text f 0 "") Prelude.++ "\n----------------\n" Prelude.++ m))
    ""
    (pick_best_list d w))
