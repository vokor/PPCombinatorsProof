From hahn Require Import Hahn.
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

Lemma is_less_than_get_false a b c
      (H1: is_less_than a b = true)
      (H2: is_less_than a c = false) :
  is_less_than b c = false.
Proof.
  destruct (is_less_than b c) eqn:E1; auto.
  rewrite (is_less_than_transitivity a b c) in H2; auto.
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

Lemma is_less_exist_cont_false a b lst
   (A: is_less_than a b = true)
   (B: is_less_exist b lst = false) : is_less_exist a lst = false.
Proof.
  induction lst. auto.
  rewrite is_exist_not_cons_alt in *.
  destruct B.
  destruct (is_less_than a0 a) eqn:E1; auto.
  rewrite (is_less_than_transitivity a0 a b) in H; auto.
Qed.

Require Import Lia.

Lemma is_less_width a b w
      (H: is_less_than a b = true)
      (A: total_width b <=? w = true) : total_width a <=? w = true.
Proof.
  apply leb_complete in A.
  apply Nat.leb_le.
  unfold is_less_than in H.
  andb_split.
  apply leb_complete in H0.
  apply leb_complete in H1.
  apply leb_complete in H2.
  apply leb_complete in H.
  unfold total_width in *.
  desf.
  simpls.
  lia.
Qed.
Lemma is_less_exist_destruct x lst lst' :
  is_less_exist x (lst ++ lst') = is_less_exist x lst || is_less_exist x lst'.
Proof.
  induction lst; auto.
  simpl.
  rewrite IHlst.
  apply orb_assoc.
Qed.  

Lemma is_exist_eq a lst :
  is_less_exist a lst = true <-> exists b, In b lst /\ is_less_than b a = true.
Proof.
  split.
  { ins.
    induction lst.
    { simpl in H.
      discriminate H. }
    apply is_exist_cons_alt in H.
    simpls.
    desf.
    { exists a0; auto. }
    assert (L: exists b : t, In b lst /\ is_less_than b a = true).
    { apply IHlst; auto. }
    desf.
    exists b; auto. }
  ins.
  desf.
  induction lst.
  { done. }
  apply is_exist_cons_alt.
  simpls.
  desf; auto.
Qed.

Fixpoint forallb_exist (lst: list t) (lst': list t) : bool :=
  match lst' with
  | nil       => true
  | x::xs   => (is_less_exist x lst) && forallb_exist lst xs
  end.

Fixpoint forallb_not_exist (lst: list t) (lst': list t) : bool :=
  match lst' with
  | nil     => true
  | x::xs   => negb (is_less_exist x lst) && forallb_not_exist lst xs
  end.

Lemma forallb_exist_nil :
  forall a lst, forallb_exist nil (lst ++ [a]) = false.
Proof.
  ins.
  induction lst; auto.
Qed.  

Lemma forallb_exist_correct a lst lst'
      (H: forallb_exist lst lst' = true) : forallb_exist (a::lst) lst' = true.
Proof.
  induction lst'; auto.
  simpl in H.
  simpl.
  unfold flip.
  apply andb_prop in H.
  destruct H.
  rewrite H, IHlst'; auto.
  rewrite andb_orb_distrib_l, andb_true_r, orb_true_r.
  reflexivity.
Qed.

Lemma forallb_exist_des_rev a lst lst' :
  forallb_exist lst (lst' ++ [a]) = true <-> is_less_exist a lst = true /\ forallb_exist lst lst' = true.
Proof.
  split.
  { ins.
    induction lst'.
    { simpl in H.
      rewrite andb_true_r in H.
      auto. }
    simpl in H.
    simpl.
    rewrite andb_true_iff in *.
    destruct H.
    rewrite H.
    rewrite and_comm, and_assoc.
    split; auto.
    apply and_comm.
    apply IHlst'; auto. }
  ins.
  desf.
  induction lst'.
  { simpl. rewrite H. auto. }
  simpl.
  simpl in H0.
  apply andb_true_iff in H0.
  desf.
  rewrite IHlst'; auto.
Qed.  

Lemma forallb_exist_rem_list_r l r lst :
  forallb_exist r lst = true -> forallb_exist (l ++ r) lst = true.
Proof.
  ins.
  induction lst using rev_ind; auto.
  rewrite forallb_exist_des_rev in *.
  desf.
  rewrite is_exist_cons_all.
  auto.
Qed.

Lemma forallb_exist_rem_list_l l r lst :
  forallb_exist l lst = true -> forallb_exist (l ++ r) lst = true.
Proof.
  ins.
  induction lst using rev_ind; auto.
  rewrite forallb_exist_des_rev in *.
  desf.
  rewrite is_exist_cons_all.
  auto.
Qed.  

Lemma forallb_not_exist_des a lst lst' :
  forallb_not_exist lst (a::lst') = true -> is_less_exist a lst = false /\ forallb_not_exist lst lst' = true.
Proof.
  ins.
  apply andb_prop in H.
  destruct H.
  apply negb_true_iff in H.
  auto.
Qed.

Lemma forallb_not_exist_des_rev a lst lst' :
  forallb_not_exist lst (lst' ++ [a]) = true <-> is_less_exist a lst = false /\ forallb_not_exist lst lst' = true.
Proof.
  split.
  { ins.
    induction lst'.
    { simpl.
      simpl in H.
      rewrite andb_true_r in H.
      apply negb_true_iff in H.
      rewrite H.
      auto. }
    rewrite <- app_comm_cons in H.
    apply forallb_not_exist_des in H.
    destruct H.
    simpl.
    rewrite andb_true_iff, negb_true_iff.
    apply and_comm, and_assoc.
    split; auto.
    apply and_comm, IHlst', H0. }
  ins.
  destruct H.
  induction lst'.
  { simpl.
    rewrite H.
    auto. }
  simpl.
  simpl in H0.
  apply andb_prop in H0.
  destruct H0.
  rewrite H0, IHlst'; auto.
Qed.

Lemma forallb_not_exist_des_lst l r lst :
  forallb_not_exist (l ++ r) lst = true <->
  forallb_not_exist l lst = true /\ forallb_not_exist r lst = true.
Proof.
  split.
  { ins.
    induction lst; auto.
    apply forallb_not_exist_des in H.
    destruct H.
    apply is_exist_not_cons_all in H.
    destruct H.
    simpl.
    rewrite H, H1.
    simpl.
    apply IHlst; auto. }
  ins.
  desf.
  induction lst; auto.
  simpl.
  apply forallb_not_exist_des in H.
  apply forallb_not_exist_des in H0.
  desf.
  rewrite andb_true_iff, negb_true_iff.
  rewrite is_exist_not_cons_all.
  auto.
Qed.

Lemma forallb_not_exist_des_lst' l r lst :
  forallb_not_exist lst (l ++ r) = true <->
  forallb_not_exist lst l = true /\ forallb_not_exist lst r = true.
Proof.
  split.
  { ins.
    induction r using rev_ind.
    { simpl.
      rewrite app_nil_r in H.
      auto. }
    rewrite app_assoc in H.
    apply forallb_not_exist_des_rev in H.
    destruct H.
    rewrite forallb_not_exist_des_rev.
    rewrite H.
    apply and_comm, and_assoc.
    rewrite and_comm in IHr.
    split; auto. }
  ins.
  destruct H.
  induction r using rev_ind.
  { rewrite app_nil_r.
    apply H. }
  rewrite app_assoc.
  rewrite forallb_not_exist_des_rev in *.
  destruct H0.
  auto.
Qed.
    
Lemma forallb_not_exist_elem a lst lst' :
     forallb_not_exist (lst ++ [a]) lst' = true -> forallb_not_exist lst lst' = true.
Proof.
  intro H.
  induction lst'; auto.
  apply forallb_not_exist_des in H.
  destruct H.
  simpl.
  rewrite IHlst'; auto.
  apply is_exist_not_cons_all in H.
  destruct H.
  rewrite H.
  auto.
Qed.

Definition format_correct1 a := height a = 2 -> first_line_width a = middle_width a.

Definition format_correct2 a := height a = 1 ->
                                first_line_width a = middle_width a /\
                                middle_width a = last_line_width a.

Definition format_correct3 a := height a > 0.

Definition format_correct a := << F1: format_correct1 a >> /\
                               << F2: format_correct2 a >> /\
                               << F3: format_correct3 a >>. 

Definition quad_correct a b c d := << T1: format_correct a >> /\
                                   << T2: format_correct b >> /\
                                   << T3: format_correct c >> /\
                                   << T4: format_correct d >>.

Definition fill_swap n := fun fs f : t => add_fill fs f n.

Definition fun_comb f n := f = add_beside \/ f = add_above \/ f = fill_swap n.

Lemma fun_correct b n m f g
      (H1: fun_comb f n)
      (H2: fun_comb g m) :
  forall a x y w, quad_correct a b x y /\
                  is_less_than a b = true /\
                  total_width (f x (g b y)) <= w ->
                  total_width (f x (g a y)) <= w.
Proof.
  ins.
  unfold fun_comb in *.
  desf.
  {
Admitted.
  
Require Import Lia.

Lemma leb_le_eq_true x y z :
  x <= z <-> (x + y <=? z + y) = true.
Proof.
  split.
    { intro T.
      eapply introT. apply Nat.leb_spec0.
      apply plus_le_compat_r; auto. }
    intro T.
    eapply elimT in T; [|apply Nat.leb_spec0].
    apply <- Nat.add_le_mono_r. eauto.
Qed.

Lemma leb_eq x y z : 
  x <=? y = (x + z <=? y + z).
Proof.
  symmetry.
  destruct (x <=? y) eqn:E1.
  { eapply elimT in E1; [|apply Nat.leb_spec0].
    apply leb_correct.
    apply Nat.add_le_mono_r; auto. }
  eapply elimF in E1; [|apply Nat.leb_spec0].
  apply leb_correct_conv.
  apply Nat.lt_nge in E1.
  apply plus_lt_compat_r; auto.
Qed.

Lemma indent'_linear a b sh :
  is_less_than a b = is_less_than (indent' sh a) (indent' sh b).
Proof.
  symmetry.
  destruct (is_less_than a b) eqn:E1.
  { unfold is_less_than in *.
    andb_split.
    repeat (apply andb_true_iff;
            unfold indent';
            destruct a; destruct b;
            simpl in *; split).
    repeat (apply andb_true_iff; split); auto.
    { eapply elimT in H2; [|apply Nat.leb_spec0].
      apply leb_le_eq_true; auto. }
    { eapply elimT in H1; [|apply Nat.leb_spec0].
      apply leb_le_eq_true; auto. }
    eapply elimT in H0; [|apply Nat.leb_spec0].
    apply leb_le_eq_true; auto.
  }
  unfold is_less_than in *.
  unfold indent'.
  destruct (height a <=? height b) eqn:E2.
  { destruct a; destruct b.
    simpl in *. rewrite E2. simpl.
    destruct (first_line_width + sh <=? first_line_width0 + sh) eqn:E3.
    { simpl.
      destruct (middle_width + sh <=? middle_width0 + sh) eqn:E4.
      { simpl.
        rewrite <- leb_le_eq_true in E3.
        rewrite <- leb_le_eq_true in E4.
        rewrite <- leb_eq.
        destruct (first_line_width <=? first_line_width0) eqn:E5.
        { destruct (middle_width <=? middle_width0) eqn:E6.
          { simpl in E1. apply E1. }
          apply leb_correct in E4. rewrite E4 in E6.
          discriminate E6. }
        apply leb_correct in E3. rewrite E3 in E5.
          discriminate E5. }
      auto. }
    auto. }
  destruct a; destruct b.
  simpl in *. rewrite E2.
  auto.
Qed.
