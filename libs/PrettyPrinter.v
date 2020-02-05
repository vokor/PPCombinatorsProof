Require Import Format.
Require Import Doc.

Require Import ZArith Int.
Require Import Coq.Lists.List.
Require Import String.

Definition is_better_than (a:t) (b:t) :=
  if (a.(height) <? b.(height))
  then a
  else if (andb
             (a.(height) =? b.(height))
             (negb (total_width b <=? total_width a)))
       then a
       else b.
         
(* Pick with minimum height *)
Definition pick_best (in_list : {in_list : list t | nil <> in_list}) :=
  match in_list with
  | exist _ x _ =>
    match x with
    | nil => empty
    | hd :: tl => fold_right is_better_than hd tl
    end
  end.

Program Definition best_to_str (lst: list t) :=
  match lst with
  | nil => "Empty set of strings to choose from."%string
  | _ => to_string (pick_best lst)
  end.

Definition pretty (docToVar: nat -> Doc -> list t) (width: nat) (doc: Doc): string :=
  best_to_str (docToVar width doc).
