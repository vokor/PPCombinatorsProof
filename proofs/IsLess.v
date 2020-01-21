Require Import FormatTrivial.
Require Import FormatList.
Require Import Format.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import Coq.ssr.ssrbool.
Require Import ZArith Int.
Require Import Coq.Bool.Bool.

Lemma eq_conv_is_less :
  forall a b,
    (compose negb (is_less_than a)) b = negb (is_less_than a b).
Proof.
  intros a b.
  unfold compose.
  reflexivity.
Qed.

Lemma pred_filter :
  forall predicate a (lst: list t),
    predicate a = true -> filter predicate (a::lst) = a :: (filter predicate lst).
Proof.
  intros P a lst H.
  simpl. rewrite -> H. reflexivity.
Qed.

Lemma is_exist_not_cons_alt a h l  :
  is_less_exist a (h :: l) = false <->
  is_less_than h a = false /\ is_less_exist a l = false.
Proof.
  split.
  { intro H.
    simpl in H.
    destruct (is_less_than h a) eqn:E1.
    { destruct (is_less_exist a l) eqn:E2.
      unfold flip in H. rewrite E1 in H.
      discriminate H.
      unfold flip in H. rewrite E1 in H.
      discriminate H. }
    destruct (is_less_exist a l) eqn:E2.
    unfold flip in H. rewrite E1 in H.
    discriminate H. auto. }
  intro H.
  destruct H as [A B].
  simpl.
  unfold flip. rewrite A, B.
  auto.
Qed.

Lemma is_exist_not_cons_all a lst lst'  :
  is_less_exist a (lst ++ lst') = false <->
  is_less_exist a lst = false /\ is_less_exist a lst' = false.
Proof.
  split.
  { intro H.
    induction lst. auto.
    simpl in H.
    simpl.
    destruct (flip is_less_than a a0) eqn:E1.
    discriminate H. auto. }
  intro H.
  destruct H as [A B].
  induction lst. auto.
  simpl.
  rewrite is_exist_not_cons_alt in A.
  destruct A as [A1 A2].
  rewrite IHlst; auto.
  unfold flip. rewrite A1.
  auto.
Qed.

Lemma is_exist_cons_alt a h l  :
  is_less_exist a (h :: l) = true <->
  is_less_than h a = true \/ is_less_exist a l = true.
Proof.
  split.
  { intro H.
    destruct (is_less_than h a) eqn:E1; auto.
    destruct (is_less_exist a l) eqn:E2; auto.
    simpl in H. unfold flip in H.
    rewrite E1, E2 in H. discriminate H. }
  intro H. destruct H as [A|A].
  { simpl. unfold flip. rewrite A. auto. }
  simpl. rewrite A. rewrite orbT.
  reflexivity.
Qed.

Lemma is_exist_cons_all a lst lst'  :
  is_less_exist a (lst ++ lst') = true <->
  is_less_exist a lst = true \/ is_less_exist a lst' = true.
Proof.
  split.
  { intro H.
    induction lst. auto.
    simpl in H.
    simpl.
    destruct (flip is_less_than a a0) eqn:E1. auto.
    apply IHlst. simpl in H. apply H. }
  intro H.
  destruct H as [A|B].
  { induction lst. auto.
    simpl.
    unfold flip.
    rewrite is_exist_cons_alt in A.
    destruct (is_less_than a0 a) eqn:E1. auto.
    rewrite IHlst. auto.
    destruct A as [A1|A2]. discriminate A1.
    apply A2. }
  induction lst. auto.
  simpl.
  unfold flip.
  rewrite IHlst, orbT.
  reflexivity.
Qed.

Notation "lst ++ [ a ]" := (lst ++ (a::nil)) (at level 60).

Lemma is_less_than_bef_aft x b lst :
  is_less_exist x (lst ++ [b]) = is_less_exist x (b::lst).
Proof.
  destruct (is_less_exist x (b::lst)) eqn:E1.
  { rewrite is_exist_cons_alt in E1.
    destruct E1 as [A|A].
    { induction lst.
      { simpl. unfold flip.
        rewrite A. auto. }
      simpl. rewrite IHlst.
      apply orb_true_r. }
    induction lst.
    { simpl in A. discriminate A. }
    rewrite is_exist_cons_alt in A.
    rewrite <- app_comm_cons.
    rewrite is_exist_cons_alt.
    destruct A.
    all: auto. }
  rewrite is_exist_not_cons_alt in E1.
  destruct E1 as [A B].
  induction lst.
  { simpl. unfold flip.
    rewrite A. auto. }
  rewrite <- app_comm_cons.
  rewrite is_exist_not_cons_alt.
  auto.
  rewrite is_exist_not_cons_alt in B.
  destruct B as [B C].
  auto.
Qed.

Lemma nat_leb_trans a b c
      (AB : a <=? b = true)
      (BC : b <=? c = true) : a <=? c = true.
Proof.
  eapply elimT in AB; [|apply Nat.leb_spec0].
  eapply elimT in BC; [|apply Nat.leb_spec0].
  eapply introT.
  { apply Nat.leb_spec0. }
  etransitivity; eauto.
Qed.

Ltac andb_split :=
  repeat match goal with
         | H : _ && _ = true |- _ => apply andb_true_iff in H; destruct H
         end.

Lemma is_less_than_transitivity a b c
      (AB : is_less_than a b = true)
      (BC : is_less_than b c = true) :
    is_less_than a c = true.
Proof.
  unfold is_less_than in *.
  andb_split.
  repeat (apply andb_true_iff; split).
  all: eapply nat_leb_trans; eauto.
Qed.

Lemma is_less_than_reflexivity :
  forall a, is_less_than a a = true.
Proof.
  intros. unfold is_less_than.
  rewrite !PeanoNat.Nat.leb_refl. auto.
Qed.

Lemma is_less_exist_cont_true a b lst 
    (A: is_less_than a b = true)
    (B: is_less_exist a lst = true) : is_less_exist b lst = true.
Proof.
  rewrite <- B.
  induction lst; auto.
  rewrite is_exist_cons_alt in B.
  destruct B as [C|C].
  { simpl. unfold flip.
    rewrite C, (is_less_than_transitivity a0 a b); auto. }
  simpl. rewrite IHlst, C; auto.
  repeat rewrite orb_true_r.
  reflexivity.
Qed.

Definition func_correct (f: t -> t -> t) :=
  forall u v w, is_less_than u v = is_less_than (f u w) (f v w).

Lemma is_less_than_func f a b x w
      (F: func_correct f)
      (H: is_less_than a b = true)
      (P: (total_width (f b x) <=? w) = true) :
  (total_width (f a x) <=? w) = true.
Admitted.
  
      