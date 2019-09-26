(*type -> record*)
(*let -> definition*)

Require Import ZArith Int.
Require Import String.

Record t : Type := T {
  height           : Z;
  first_line_width : Z;
  middle_width     : Z;
  last_line_width  : Z;
  to_text          : Z -> string -> string
}.

Definition is_less_than  (a:t) (b:t): bool := 
  match a, b with
  | T h1 fw1 m1 lw1 t1, T h2 fw2 m2 lw2 t2 => 
      andb (Z.leb h1 h2) (andb (Z.leb fw1 fw2)
      (andb (Z.leb m1 m2) (Z.leb lw1 lw2)))
  end.

Definition compare (f1:t) (f2:t): Z :=
  match is_less_than f1 f2, is_less_than f2 f1 with
  | true, _ => -1 
  | _, true =>  1 
  | _,_     =>  0
  end.

Definition empty: t := T 0 0 0 0 (fun s t => t).

Definition line (nt:string): t := T 1 (Z.of_nat (length nt)) 1 1 (fun s t => append nt t).

(*
undefined!

Fixpoint sp (n:Z):string :=
  match n with
  | Z0 => ""
  | n => append " " (sp (Z.of_nat (pred (Z.to_nat n))))
  end.

let list_max = function
  | [] ->
    failwith "Empty list as argument of list_max."
  | hd :: tl ->
     List.fold_left max hd tl

How to use foldl in Coq?
*)


Definition add_above (f1:t) (f2:t):t :=
  match f1, f2 with
  | T h1 fw1 m1 lw1 t1, T h2 fw2 m2 lw2 t2 => 
      match h1, h2 with
       | Z0, _ => f2
       | _, Z0 => f1   (*Does Z0 equivalence 0?*)
       | _, _ => match h1, h2 with
          1
      end
  end.


  match f1.height, f2.height with
     let middle_width_new :=
       match f1.height, f2.height with
         1, 1            -> f1.first_line_width
       | 1, 2            -> f2.first_line_width
       | 1, x when x > 2 -> max f2.first_line_width
                                f2.middle_width 
       | 2, 1            -> f1.last_line_width
       | x, 1 when x > 2 -> max f1.middle_width
                                f1.last_line_width
       | _               ->
          list_max [f1.middle_width;
                    f1.last_line_width;
                    f2.first_line_width;
                    f2.middle_width
                   ]
     in {
         height           = f1.height + f2.height;
         first_line_width = f1.first_line_width;
         middle_width     = middle_width_new;
         last_line_width  = f2.last_line_width;
         to_text          =
           fun s t ->
           f1.to_text
             s
             ("\n" ^ (sp s) ^ (f2.to_text s t))
       }















