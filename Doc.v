Require Import String.
Open Scope list_scope.
Require Import ZArith Int.
Require Import Coq.Lists.List.
Require Import format.

Inductive Doc : Type :=
  | Text (s: string)
  | Indent (t: nat) (d: Doc)
  | Beside (d: Doc) (d: Doc)
  | Above (d: Doc) (d: Doc)
  | Choice (d: Doc) (d: Doc)
  | Fill (d: Doc) (d: Doc) (s: nat).


Definition filter_map (filterf: t -> bool) (mapf: t -> t) (l: list t): list t :=
  fold_left
    (fun lst a => if filterf a
                  then cons (mapf a) lst
                  else lst
    )
    l nil.

Definition main_pred (width: nat) (shift: nat) (elem: t) :=
  total_width elem + shift <=? width.

(* Shift each block to 'shift' positions right *)
Definition indentDoc (width: nat) (shift: nat) (fs: list t) :=
   filter_map (fun f => main_pred width shift f)
                       (indent' shift)
                       fs.

