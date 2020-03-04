From hahn Require Import Hahn.
Require Import IsLess.
Require Import Format.
Require Import Coq.Program.Basics.
Require Import Lia.
Require Import Coq.ssr.ssrbool.
Require Import ZArith Int.
Require Import Coq.Bool.Bool.              

Lemma beside_correct : fun_correct add_beside.
Proof.
  unfold fun_correct.
  split.
  { red.
    unfold fun_correct1.
    ins.
    desf.
    unfold add_beside.
    desf; ins.
    all: lia. }
  red.
  unfold fun_correct2.
  ins.
  desf.
  unfold total_width in *.
  unfold add_beside.
  desf; ins.
 
Admitted.


Lemma fill_correct n : fun_correct (fun fs f : t => add_fill fs f n).
Proof.
Admitted.

Lemma indent_correct w :  fun_correct (fun _ a : t => indent' w a).
Proof.
Admitted.
