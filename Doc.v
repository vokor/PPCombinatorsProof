Require Import String.

Inductive Doc : Type :=
  | Text (s: string)
  | Indent (t: nat) (d: Doc)
  | Beside (d: Doc) (d: Doc)
  | Above (d: Doc) (d: Doc)
  | Choice (d: Doc) (d: Doc)
  | Fill (d: Doc) (d: Doc) (s: nat).

(*
Notation "a >|< b"  := (Beside a b) (at level 70).
Notation "a >-< b"  := (Above a b) (at level 70).
Notation "a >//< b" := (Choice a b) (at level 70).

Definition text   := Text.
Definition indent := Indent.
*)