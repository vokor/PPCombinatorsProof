From hahn Require Import Hahn.
Require Import IsLess.
Require Import Format.
Require Import Coq.Program.Basics.
Require Import Lia.
Require Import Coq.ssr.ssrbool.
Require Import ZArith Int.
Require Import Coq.Bool.Bool.              

(*
Lemma beside_correct : fun_correct add_beside.
Proof. (*
  unfold fun_correct.
  split.
  { red.
    unfold fun_correct1.
    ins.
    unfold triple_correct in H.
    unfold format_correct in H.
    unfold format_correct3 in H. 
    desf.
    unfold is_less_than in H0.
    andb_split.
    apply leb_complete in H.
    apply leb_complete in H0.
    apply leb_complete in H2.
    apply leb_complete in H3.
    unfold total_width in *.
    unfold add_beside in *.
    desf; ins.
    all: try lia.
    { assert (first_line_width c = middle_width c /\
              middle_width c = last_line_width c).
      { apply F2; auto. }
      assert (first_line_width a = middle_width a /\
              middle_width a = last_line_width a).
      { apply F7; auto. }
      desf.
      lia. }
    { assert (first_line_width c = middle_width c /\
              middle_width c = last_line_width c).
      { apply F2; auto. }
      assert (first_line_width a = middle_width a /\
              middle_width a = last_line_width a).
      { apply F7; auto. }
      desf.
      lia. }
    { assert (first_line_width a = middle_width a /\
              middle_width a = last_line_width a).
      { apply F7; auto. }
      desf.
      lia. }
    { assert (first_line_width a = middle_width a /\
              middle_width a = last_line_width a).
      { apply F7; auto. }
      desf.
      lia. }
    { assert (first_line_width a = middle_width a /\
              middle_width a = last_line_width a).
      { apply F7; auto. }
      desf.
      lia. }
    assert (first_line_width a = middle_width a /\
            middle_width a = last_line_width a).
    { apply F7; auto. }
    desf.
    lia. }
  red.
  unfold fun_correct2.
  ins.
  unfold triple_correct in H.
  unfold format_correct in H.
  unfold format_correct3 in H. 
  desf.
  unfold is_less_than in H0.
  andb_split.
  apply leb_complete in H.
  apply leb_complete in H0.
  apply leb_complete in H2.
  apply leb_complete in H3.
  unfold total_width in *.
  unfold add_beside in *.
  desf; ins.
  all: try lia.
  assert (first_line_width b = middle_width b /\
              middle_width b = last_line_width b).
  { apply Nat.eqb_eq in Heq3.
    desf.
    apply F4; auto. }
    desf.
    lia.
Qed. *)
Admitted.

Lemma fill_correct n : fun_correct (fun fs f : t => add_fill fs f n).
Proof.
Admitted.

Lemma indent_correct w :  fun_correct (fun _ a : t => indent' w a).
Proof.
Admitted. *)
