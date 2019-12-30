Require Import Format.
Require Import Doc.

Require Import ZArith Int.
Require Import Coq.Lists.List.
Require Import String.

(* Pick with minimum height *)
Definition pick_best (in_list : {in_list : list t | nil <> in_list}) :=
  match in_list with
  | exist _ x _ =>
    match x with
    | nil => empty
    | hd :: tl => fold_left (fun best f =>
        if f.(height) <? best.(height)
        then f
        else best)
      tl hd
    end
  end.

Program Definition to_string' (lst: list t) :=
  match lst with
  | nil => "Empty set of strings to choose from."%string
  | _ => to_string (pick_best lst)
  end.

Definition pretty (docToVar: nat -> Doc -> list t) (width: nat) (doc: Doc): string :=
  to_string' (docToVar width doc).
