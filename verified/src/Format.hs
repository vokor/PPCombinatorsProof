module Format where

import qualified Prelude
import BaseFun


data T0 =
   T Prelude.Int Prelude.Int Prelude.Int Prelude.Int (Prelude.Int ->
                                                     Prelude.String ->
                                                     Prelude.String)

height :: T0 -> Prelude.Int
height t =
  case t of {
   T height0 _ _ _ _ -> height0}

first_line_width :: T0 -> Prelude.Int
first_line_width t =
  case t of {
   T _ first_line_width0 _ _ _ -> first_line_width0}

middle_width :: T0 -> Prelude.Int
middle_width t =
  case t of {
   T _ _ middle_width0 _ _ -> middle_width0}

last_line_width :: T0 -> Prelude.Int
last_line_width t =
  case t of {
   T _ _ _ last_line_width0 _ -> last_line_width0}

to_text :: T0 -> Prelude.Int -> Prelude.String -> Prelude.String
to_text t =
  case t of {
   T _ _ _ _ to_text0 -> to_text0}

less_components :: T0 -> T0 -> Prelude.Bool
less_components g g' =
  (Prelude.&&)
    ((Prelude.&&)
      ((Prelude.&&) ((Prelude.<=) (height g) (height g'))
        ((Prelude.<=) (first_line_width g) (first_line_width g')))
      ((Prelude.<=) (middle_width g) (middle_width g')))
    ((Prelude.<=) (last_line_width g) (last_line_width g'))

is_less_than :: T0 -> T0 -> Prelude.Bool
is_less_than g g' =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> less_components g g')
      (\n ->
      (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
        (\_ -> Prelude.False)
        (\_ -> less_components g g')
        n)
      (height g'))
    (\n ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ ->
      (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
        (\_ -> Prelude.False)
        (\n0 ->
        (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
          (\_ -> less_components g g')
          (\_ -> Prelude.False)
          n0)
        (height g'))
      (\_ ->
      (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
        (\_ -> less_components g g')
        (\n0 ->
        (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
          (\_ -> Prelude.False)
          (\_ -> less_components g g')
          n0)
        (height g'))
      n)
    (height g)

empty :: T0
empty =
  T 0 0 0 0 (\_ t -> t)

line :: Prelude.String -> T0
line nt =
  let {length0 = length nt} in
  T (Prelude.succ 0) length0 length0 length0 (\_ t -> append nt t)

newline :: Prelude.String
newline =
  (:) (ascii_of_N (Npos (XO (XI (XO XH))))) ([])

sp :: Prelude.Int -> Prelude.String
sp n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> ([]))
    (\n' -> append ((:) ' ' ([])) (sp n'))
    n

add_above :: T0 -> T0 -> T0
add_above g g' =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> g')
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> g)
      (\_ ->
      let {
       middle_with_new = (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                           (\_ ->
                           (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                             (\_ ->
                             Prelude.max (middle_width g)
                               (Prelude.max (last_line_width g)
                                 (Prelude.max (first_line_width g')
                                   (middle_width g'))))
                             (\n ->
                             (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                               (\_ ->
                               Prelude.max (last_line_width g)
                                 (middle_width g))
                               (\_ ->
                               Prelude.max (middle_width g)
                                 (Prelude.max (last_line_width g)
                                   (Prelude.max (first_line_width g')
                                     (middle_width g'))))
                               n)
                             (height g'))
                           (\n ->
                           (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                             (\_ ->
                             (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                               (\_ ->
                               Prelude.max (first_line_width g')
                                 (middle_width g'))
                               (\n0 ->
                               (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                 (\_ -> first_line_width g)
                                 (\_ ->
                                 Prelude.max (first_line_width g')
                                   (middle_width g'))
                                 n0)
                               (height g'))
                             (\n0 ->
                             (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                               (\_ ->
                               (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                 (\_ ->
                                 Prelude.max (last_line_width g)
                                   (Prelude.max (first_line_width g')
                                     (middle_width g')))
                                 (\n1 ->
                                 (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                   (\_ -> last_line_width g)
                                   (\_ ->
                                   Prelude.max (last_line_width g)
                                     (Prelude.max (first_line_width g')
                                       (middle_width g')))
                                   n1)
                                 (height g'))
                               (\_ ->
                               (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                 (\_ ->
                                 Prelude.max (middle_width g)
                                   (Prelude.max (last_line_width g)
                                     (Prelude.max (first_line_width g')
                                       (middle_width g'))))
                                 (\n1 ->
                                 (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                   (\_ ->
                                   Prelude.max (last_line_width g)
                                     (middle_width g))
                                   (\_ ->
                                   Prelude.max (middle_width g)
                                     (Prelude.max (last_line_width g)
                                       (Prelude.max (first_line_width g')
                                         (middle_width g'))))
                                   n1)
                                 (height g'))
                               n0)
                             n)
                           (height g)}
      in
      T ((Prelude.+) (height g) (height g')) (first_line_width g)
      middle_with_new (last_line_width g') (\s t ->
      to_text g s (append newline (append (sp s) (to_text g' s t)))))
      (height g'))
    (height g)

add_beside :: T0 -> T0 -> T0
add_beside g g' =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> g')
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> g)
      (\_ ->
      let {
       middle_width_new = (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                            (\_ ->
                            (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                              (\_ ->
                              Prelude.max (middle_width g)
                                (Prelude.max
                                  ((Prelude.+) (last_line_width g)
                                    (first_line_width g'))
                                  ((Prelude.+) (last_line_width g)
                                    (middle_width g'))))
                              (\n ->
                              (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                (\_ -> middle_width g)
                                (\_ ->
                                Prelude.max (middle_width g)
                                  (Prelude.max
                                    ((Prelude.+) (last_line_width g)
                                      (first_line_width g'))
                                    ((Prelude.+) (last_line_width g)
                                      (middle_width g'))))
                                n)
                              (height g'))
                            (\n ->
                            (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                              (\_ ->
                              (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                (\_ ->
                                (Prelude.+) (last_line_width g)
                                  (middle_width g'))
                                (\n0 ->
                                (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                  (\_ ->
                                  (Prelude.+) (first_line_width g)
                                    (first_line_width g'))
                                  (\n1 ->
                                  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                    (\_ ->
                                    (Prelude.+) (first_line_width g)
                                      (first_line_width g'))
                                    (\_ ->
                                    (Prelude.+) (last_line_width g)
                                      (middle_width g'))
                                    n1)
                                  n0)
                                (height g'))
                              (\n0 ->
                              (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                (\_ ->
                                (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                  (\_ ->
                                  Prelude.max
                                    ((Prelude.+) (last_line_width g)
                                      (first_line_width g'))
                                    ((Prelude.+) (last_line_width g)
                                      (middle_width g')))
                                  (\n1 ->
                                  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                    (\_ -> middle_width g)
                                    (\_ ->
                                    Prelude.max
                                      ((Prelude.+) (last_line_width g)
                                        (first_line_width g'))
                                      ((Prelude.+) (last_line_width g)
                                        (middle_width g')))
                                    n1)
                                  (height g'))
                                (\_ ->
                                (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                  (\_ ->
                                  Prelude.max (middle_width g)
                                    (Prelude.max
                                      ((Prelude.+) (last_line_width g)
                                        (first_line_width g'))
                                      ((Prelude.+) (last_line_width g)
                                        (middle_width g'))))
                                  (\n1 ->
                                  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                    (\_ -> middle_width g)
                                    (\_ ->
                                    Prelude.max (middle_width g)
                                      (Prelude.max
                                        ((Prelude.+) (last_line_width g)
                                          (first_line_width g'))
                                        ((Prelude.+) (last_line_width g)
                                          (middle_width g'))))
                                    n1)
                                  (height g'))
                                n0)
                              n)
                            (height g)}
      in
      let {
       first_line_width_new = case (Prelude.==) (height g) (Prelude.succ 0) of {
                               Prelude.True ->
                                (Prelude.+) (first_line_width g)
                                  (first_line_width g');
                               Prelude.False -> first_line_width g}}
      in
      T (sub ((Prelude.+) (height g) (height g')) (Prelude.succ 0))
      first_line_width_new middle_width_new
      ((Prelude.+) (last_line_width g) (last_line_width g')) (\s t ->
      to_text g s (to_text g' ((Prelude.+) s (last_line_width g)) t)))
      (height g'))
    (height g)

add_fill :: T0 -> T0 -> Prelude.Int -> T0
add_fill g g' shift0 =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> g')
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> g)
      (\_ ->
      let {
       middle_width_new = (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                            (\_ ->
                            (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                              (\_ ->
                              Prelude.max (middle_width g)
                                (Prelude.max
                                  ((Prelude.+) (last_line_width g)
                                    (first_line_width g'))
                                  ((Prelude.+) shift0 (middle_width g'))))
                              (\n ->
                              (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                (\_ -> middle_width g)
                                (\n0 ->
                                (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                  (\_ ->
                                  Prelude.max (middle_width g)
                                    ((Prelude.+) (last_line_width g)
                                      (first_line_width g')))
                                  (\_ ->
                                  Prelude.max (middle_width g)
                                    (Prelude.max
                                      ((Prelude.+) (last_line_width g)
                                        (first_line_width g'))
                                      ((Prelude.+) shift0 (middle_width g'))))
                                  n0)
                                n)
                              (height g'))
                            (\n ->
                            (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                              (\_ ->
                              (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                (\_ ->
                                (Prelude.+) shift0 (middle_width g'))
                                (\n0 ->
                                (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                  (\_ ->
                                  (Prelude.+) (first_line_width g)
                                    (first_line_width g'))
                                  (\n1 ->
                                  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                    (\_ ->
                                    (Prelude.+) (first_line_width g)
                                      (first_line_width g'))
                                    (\_ ->
                                    (Prelude.+) shift0 (middle_width g'))
                                    n1)
                                  n0)
                                (height g'))
                              (\n0 ->
                              (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                (\_ ->
                                (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                  (\_ ->
                                  Prelude.max
                                    ((Prelude.+) (last_line_width g)
                                      (first_line_width g'))
                                    ((Prelude.+) shift0 (middle_width g')))
                                  (\n1 ->
                                  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                    (\_ -> first_line_width g)
                                    (\n2 ->
                                    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                      (\_ ->
                                      (Prelude.+) (last_line_width g)
                                        (first_line_width g'))
                                      (\_ ->
                                      Prelude.max
                                        ((Prelude.+) (last_line_width g)
                                          (first_line_width g'))
                                        ((Prelude.+) shift0
                                          (middle_width g')))
                                      n2)
                                    n1)
                                  (height g'))
                                (\_ ->
                                (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                  (\_ ->
                                  Prelude.max (middle_width g)
                                    (Prelude.max
                                      ((Prelude.+) (last_line_width g)
                                        (first_line_width g'))
                                      ((Prelude.+) shift0 (middle_width g'))))
                                  (\n1 ->
                                  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                    (\_ -> middle_width g)
                                    (\n2 ->
                                    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
                                      (\_ ->
                                      Prelude.max (middle_width g)
                                        ((Prelude.+) (last_line_width g)
                                          (first_line_width g')))
                                      (\_ ->
                                      Prelude.max (middle_width g)
                                        (Prelude.max
                                          ((Prelude.+) (last_line_width g)
                                            (first_line_width g'))
                                          ((Prelude.+) shift0
                                            (middle_width g'))))
                                      n2)
                                    n1)
                                  (height g'))
                                n0)
                              n)
                            (height g)}
      in
      let {
       first_line_width_new = case (Prelude.==) (height g) (Prelude.succ 0) of {
                               Prelude.True ->
                                (Prelude.+) (first_line_width g)
                                  (first_line_width g');
                               Prelude.False -> first_line_width g}}
      in
      let {
       last_line_width_new = case (Prelude.==) (height g') (Prelude.succ 0) of {
                              Prelude.True ->
                               (Prelude.+) (last_line_width g')
                                 (last_line_width g);
                              Prelude.False ->
                               (Prelude.+) (last_line_width g') shift0}}
      in
      T (sub ((Prelude.+) (height g) (height g')) (Prelude.succ 0))
      first_line_width_new middle_width_new last_line_width_new (\s t ->
      to_text g s (to_text g' ((Prelude.+) s shift0) t)))
      (height g'))
    (height g)

total_width :: T0 -> Prelude.Int
total_width f =
  case f of {
   T _ fw m lw _ -> Prelude.max fw (Prelude.max m lw)}

split :: Prelude.String -> Prelude.String -> ([]) Prelude.String
split regexp =
  let {
   sp_helper pos s =
     case s of {
      ([]) -> (:) ([]) ([]);
      (:) _ s' ->
       (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
         (\_ ->
         case index 0 regexp s of {
          Prelude.Just n -> (:) (substring 0 n s)
           (sp_helper ((Prelude.+) (sub n (Prelude.succ 0)) (length regexp))
             s');
          Prelude.Nothing -> (:) s ([])})
         (\_ -> sp_helper (sub pos (Prelude.succ 0)) s')
         pos}}
  in sp_helper 0

of_string :: Prelude.String -> T0
of_string s =
  let {lines = split newline s} in
  let {lineFormats = map line lines} in fold_left add_above lineFormats empty

indent' :: Prelude.Int -> T0 -> T0
indent' shift0 f =
  case f of {
   T h fw m lw to_text0 -> T h ((Prelude.+) fw shift0) ((Prelude.+) m shift0)
    ((Prelude.+) lw shift0) (\s t ->
    append (sp shift0) (to_text0 ((Prelude.+) s shift0) t))}
