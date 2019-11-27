Require Import String.

Inductive Doc : Type :=
  | Text (s: string)
  | Indent (t: nat) (d: Doc)
  | Beside (d: Doc) (d: Doc)
  | Above (d: Doc) (d: Doc)
  | Choice (d: Doc) (d: Doc)
  | Fill (d: Doc) (d: Doc) (s: nat).