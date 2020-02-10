Require Import IsLess.
Require Import Format.
Require Import Coq.Program.Basics.

Lemma beside_correct : func_correct add_beside.
Proof.
Admitted.

Lemma above_correct : func_correct add_above.
Proof.
Admitted.


Lemma fill_correct n: func_correct (fun fs f : t => add_fill fs f n).
Proof.
Admitted.

Lemma indent_correct w :  func_correct (fun _ a : t => indent' w a).
Proof.
Admitted.
