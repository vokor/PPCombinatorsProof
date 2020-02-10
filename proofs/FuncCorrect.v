From hahn Require Import Hahn.
Require Import IsLess.
Require Import Format.
Require Import Coq.Program.Basics.
Require Import Lia.
Require Import Coq.ssr.ssrbool.
Require Import ZArith Int.
Require Import Coq.Bool.Bool.

Lemma beside_correct : func_correct add_beside.
Proof. (*
  unfold func_correct.
  split.
  all: red.
  { unfold func_correct1.
    ins.
    destruct (is_less_than (add_beside u w) (add_beside v w)) eqn:E1.
    { unfold is_less_than in *.
      andb_split.
      repeat (apply andb_true_iff; split).
      unfold add_beside in H.
      destruct u.
      simpl in H.
      s
    unfold add_beside.
    destruct u.
    destruct v.
    simpl.
    desf.
    { simpl.
      a *)
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
