Require Import Format.
Require Import Doc.

Require Import ZArith Int.
Require Import Coq.Lists.List.
Require Import String.

Definition is_better_than (a:t) (b:t) :=
  match a.(height) ?= b.(height) with
  | Lt => a
  | Eq => match total_width a ?= total_width b with
          | Lt => a
          | Eq => if (is_less_than b a)
                  then b
                  else a
          | Gt => b
          end
  | Gt => b
  end.

(* Pick with minimum height *)
(* FIXME: add <> nil *)
Definition pick_best (lst: list t):=
  match lst with
  | nil => empty
  | hd :: tl => fold_left is_better_than tl hd
  end.

(*
Definition pick_best (lst : {lst : list t | nil <> lst}) :=
  match lst with
  | exist _ x _ =>
    match x with
    | nil => empty
    | hd :: tl => fold_right is_better_than hd tl
    end
  end.
*)

Program Definition best_to_str (lst: list t) :=
  match lst with
  | nil => "Empty set of strings to choose from."%string
  | _ => to_string (pick_best lst)
  end.

Definition pretty (docToVar: nat -> Doc -> list t) (width: nat) (doc: Doc): string :=
  best_to_str (docToVar width doc).
