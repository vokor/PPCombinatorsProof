module Format where

import BaseFun
import Data.Type.Natural

data T0 =
   T Nat Nat Nat Nat (Nat -> String -> String)

height :: T0 -> Nat
height t =
  case t of {
   T height0 _ _ _ _ -> height0}

first_line_width :: T0 -> Nat
first_line_width t =
  case t of {
   T _ first_line_width0 _ _ _ -> first_line_width0}

middle_width :: T0 -> Nat
middle_width t =
  case t of {
   T _ _ middle_width0 _ _ -> middle_width0}

last_line_width :: T0 -> Nat
last_line_width t =
  case t of {
   T _ _ _ last_line_width0 _ -> last_line_width0}

to_text :: T0 -> Nat -> String -> String
to_text t =
  case t of {
   T _ _ _ _ to_text0 -> to_text0}

less_components :: T0 -> T0 -> Bool
less_components g g' =
  andb
    (andb
      (andb (leb (height g) (height g'))
        (leb (first_line_width g) (first_line_width g')))
      (leb (middle_width g) (middle_width g')))
    (leb (last_line_width g) (last_line_width g'))

is_less_than :: T0 -> T0 -> Bool
is_less_than g g' =
  case height g of {
   Z ->
    case height g' of {
     Z -> less_components g g';
     S n -> case n of {
             Z -> False;
             S _ -> less_components g g'}};
   S n ->
    case n of {
     Z ->
      case height g' of {
       Z -> False;
       S n0 -> case n0 of {
                Z -> less_components g g';
                S _ -> False}};
     S _ ->
      case height g' of {
       Z -> less_components g g';
       S n0 -> case n0 of {
                Z -> False;
                S _ -> less_components g g'}}}}

empty :: T0
empty =
  T Z Z Z Z (\_ t -> t)

line :: String -> T0
line nt =
  let {length0 = intToNat (length nt)} in
  T (S Z) length0 length0 length0 (\_ t -> append nt t)

sp :: Nat -> String
sp n =
  case n of {
   Z -> "";
   S n' ->
    append "" (sp n')}

add_above :: T0 -> T0 -> T0
add_above g g' =
  case height g of {
   Z -> g';
   S _ ->
    case height g' of {
     Z -> g;
     S _ ->
      let {
       middle_with_new = case height g of {
                          Z ->
                           case height g' of {
                            Z ->
                             max (middle_width g)
                               (max (last_line_width g)
                                 (max (first_line_width g')
                                   (middle_width g')));
                            S n ->
                             case n of {
                              Z -> max (last_line_width g) (middle_width g);
                              S _ ->
                               max (middle_width g)
                                 (max (last_line_width g)
                                   (max (first_line_width g')
                                     (middle_width g')))}};
                          S n ->
                           case n of {
                            Z ->
                             case height g' of {
                              Z ->
                               max (first_line_width g') (middle_width g');
                              S n0 ->
                               case n0 of {
                                Z -> first_line_width g;
                                S _ ->
                                 max (first_line_width g') (middle_width g')}};
                            S n0 ->
                             case n0 of {
                              Z ->
                               case height g' of {
                                Z ->
                                 max (last_line_width g)
                                   (max (first_line_width g')
                                     (middle_width g'));
                                S n1 ->
                                 case n1 of {
                                  Z -> last_line_width g;
                                  S _ ->
                                   max (last_line_width g)
                                     (max (first_line_width g')
                                       (middle_width g'))}};
                              S _ ->
                               case height g' of {
                                Z ->
                                 max (middle_width g)
                                   (max (last_line_width g)
                                     (max (first_line_width g')
                                       (middle_width g')));
                                S n1 ->
                                 case n1 of {
                                  Z ->
                                   max (last_line_width g) (middle_width g);
                                  S _ ->
                                   max (middle_width g)
                                     (max (last_line_width g)
                                       (max (first_line_width g')
                                         (middle_width g')))}}}}}}
      in
      T (add (height g) (height g')) (first_line_width g) middle_with_new
      (last_line_width g') (\s t ->
      to_text g s
        (append "\n" (append (sp s) (to_text g' s t))))}}

add_beside :: T0 -> T0 -> T0
add_beside g g' =
  case height g of {
   Z -> g';
   S _ ->
    case height g' of {
     Z -> g;
     S _ ->
      let {
       middle_width_new = case height g of {
                           Z ->
                            case height g' of {
                             Z ->
                              max (middle_width g)
                                (max
                                  (add (last_line_width g)
                                    (first_line_width g'))
                                  (add (last_line_width g) (middle_width g')));
                             S n ->
                              case n of {
                               Z -> middle_width g;
                               S _ ->
                                max (middle_width g)
                                  (max
                                    (add (last_line_width g)
                                      (first_line_width g'))
                                    (add (last_line_width g)
                                      (middle_width g')))}};
                           S n ->
                            case n of {
                             Z ->
                              case height g' of {
                               Z -> add (last_line_width g) (middle_width g');
                               S n0 ->
                                case n0 of {
                                 Z ->
                                  add (first_line_width g)
                                    (first_line_width g');
                                 S n1 ->
                                  case n1 of {
                                   Z ->
                                    add (first_line_width g)
                                      (first_line_width g');
                                   S _ ->
                                    add (last_line_width g) (middle_width g')}}};
                             S n0 ->
                              case n0 of {
                               Z ->
                                case height g' of {
                                 Z ->
                                  max
                                    (add (last_line_width g)
                                      (first_line_width g'))
                                    (add (last_line_width g)
                                      (middle_width g'));
                                 S n1 ->
                                  case n1 of {
                                   Z -> middle_width g;
                                   S _ ->
                                    max
                                      (add (last_line_width g)
                                        (first_line_width g'))
                                      (add (last_line_width g)
                                        (middle_width g'))}};
                               S _ ->
                                case height g' of {
                                 Z ->
                                  max (middle_width g)
                                    (max
                                      (add (last_line_width g)
                                        (first_line_width g'))
                                      (add (last_line_width g)
                                        (middle_width g')));
                                 S n1 ->
                                  case n1 of {
                                   Z -> middle_width g;
                                   S _ ->
                                    max (middle_width g)
                                      (max
                                        (add (last_line_width g)
                                          (first_line_width g'))
                                        (add (last_line_width g)
                                          (middle_width g')))}}}}}}
      in
      let {
       first_line_width_new = case eqb (height g) (S Z) of {
                               True ->
                                add (first_line_width g)
                                  (first_line_width g');
                               False -> first_line_width g}}
      in
      T (sub (add (height g) (height g')) (S Z)) first_line_width_new
      middle_width_new (add (last_line_width g) (last_line_width g'))
      (\s t -> to_text g s (to_text g' (add s (last_line_width g)) t))}}

add_fill :: T0 -> T0 -> Nat -> T0
add_fill g g' shift =
  case height g of {
   Z -> g';
   S _ ->
    case height g' of {
     Z -> g;
     S _ ->
      let {
       middle_width_new = case height g of {
                           Z ->
                            case height g' of {
                             Z ->
                              max (middle_width g)
                                (max
                                  (add (last_line_width g)
                                    (first_line_width g'))
                                  (add shift (middle_width g')));
                             S n ->
                              case n of {
                               Z -> middle_width g;
                               S n0 ->
                                case n0 of {
                                 Z ->
                                  max (middle_width g)
                                    (add (last_line_width g)
                                      (first_line_width g'));
                                 S _ ->
                                  max (middle_width g)
                                    (max
                                      (add (last_line_width g)
                                        (first_line_width g'))
                                      (add shift (middle_width g')))}}};
                           S n ->
                            case n of {
                             Z ->
                              case height g' of {
                               Z -> add shift (middle_width g');
                               S n0 ->
                                case n0 of {
                                 Z ->
                                  add (first_line_width g)
                                    (first_line_width g');
                                 S n1 ->
                                  case n1 of {
                                   Z ->
                                    add (first_line_width g)
                                      (first_line_width g');
                                   S _ -> add shift (middle_width g')}}};
                             S n0 ->
                              case n0 of {
                               Z ->
                                case height g' of {
                                 Z ->
                                  max
                                    (add (last_line_width g)
                                      (first_line_width g'))
                                    (add shift (middle_width g'));
                                 S n1 ->
                                  case n1 of {
                                   Z -> first_line_width g;
                                   S n2 ->
                                    case n2 of {
                                     Z ->
                                      add (last_line_width g)
                                        (first_line_width g');
                                     S _ ->
                                      max
                                        (add (last_line_width g)
                                          (first_line_width g'))
                                        (add shift (middle_width g'))}}};
                               S _ ->
                                case height g' of {
                                 Z ->
                                  max (middle_width g)
                                    (max
                                      (add (last_line_width g)
                                        (first_line_width g'))
                                      (add shift (middle_width g')));
                                 S n1 ->
                                  case n1 of {
                                   Z -> middle_width g;
                                   S n2 ->
                                    case n2 of {
                                     Z ->
                                      max (middle_width g)
                                        (add (last_line_width g)
                                          (first_line_width g'));
                                     S _ ->
                                      max (middle_width g)
                                        (max
                                          (add (last_line_width g)
                                            (first_line_width g'))
                                          (add shift (middle_width g')))}}}}}}}
      in
      let {
       first_line_width_new = case eqb (height g) (S Z) of {
                               True ->
                                add (first_line_width g)
                                  (first_line_width g');
                               False -> first_line_width g}}
      in
      let {
       last_line_width_new = case eqb (height g') (S Z) of {
                              True ->
                               add (last_line_width g') (last_line_width g);
                              False -> add (last_line_width g') shift}}
      in
      T (sub (add (height g) (height g')) (S Z)) first_line_width_new
      middle_width_new last_line_width_new (\s t ->
      to_text g s (to_text g' (add s shift) t))}}

total_width :: T0 -> Nat
total_width f =
  case f of {
   T _ fw m lw _ -> max fw (max m lw)}

split :: String -> String -> [String]
split regexp =
  let {
   sp_helper pos s =
     case s of {
      "" -> "":[];
      _:s' ->
       case pos of {
        Z ->
         case index Z regexp s of {
          Some n -> (substring Z n s):(sp_helper (add n (S Z)) s');
          None -> s:[]};
        S _ -> sp_helper (sub pos (S Z)) s'}}}
  in sp_helper Z

of_string :: String -> T0
of_string s =
  let {
   lines = split "\n" s}
  in
  let {lineFormats = map line lines} in foldl add_above empty lineFormats

indent' :: Nat -> T0 -> T0
indent' shift f =
  case f of {
   T h fw m lw to_text0 -> T h (add fw shift) (add m shift) (add lw shift)
    (\s t -> append (sp shift) (to_text0 (add s shift) t))}
