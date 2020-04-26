From hahn Require Import Hahn.
Require Import Format.
Require Import Doc.
Require Import PrettyPrinter.
Require Import FormatTrivial.
Require Import FormatList.
Require Import IsLess.
Require Import FuncCorrect.
Require Import MinHeight.

Require Import String.
Require Import ZArith Int.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.Bool.Bool.
Require Import Coq.ssr.ssrbool.
Require Import Lia.

Lemma par_elem2_not_less a b lst 
    (H: is_less_than a b = false) :
  pareto_by_elem a (b::lst) = b :: pareto_by_elem a lst.
Proof.
  unfold pareto_by_elem, filter.
  rewrite -> eq_conv_is_less.
  rewrite -> H. auto.
Qed.

Lemma par_elem2_not_less_rev a b lst 
    (H: is_less_than a b = false) :
  pareto_by_elem a (lst ++ [b]) = (pareto_by_elem a lst) ++ [b].
Proof.
  induction lst.
  { simpl.
    rewrite eq_conv_is_less, H.
    simpl. reflexivity. }
  simpl.
  rewrite -> eq_conv_is_less.
  destruct (is_less_than a a0) eqn:E1.
  { auto. }
  simpl. rewrite IHlst.
  reflexivity.
Qed.

Lemma par_elem2_less a b lst 
    (H: is_less_than a b = true) :
    pareto_by_elem a (b::lst) = pareto_by_elem a lst.
Proof.
  unfold pareto_by_elem, filter.
  rewrite -> eq_conv_is_less.
  rewrite -> H. auto.
Qed.

Lemma par_elem2_less_rev a b lst 
    (H: is_less_than a b = true) :
  pareto_by_elem a (lst ++ [b]) = pareto_by_elem a lst.
Proof.
  induction lst.
  { simpl.
    rewrite eq_conv_is_less, H.
    simpl. reflexivity. }
  simpl.
  rewrite -> eq_conv_is_less.
  destruct (is_less_than a a0) eqn:E1.
  { auto. }
  simpl. rewrite IHlst.
  reflexivity.
Qed.

Lemma pareto_by_elem_linear a lst lst' : 
    pareto_by_elem a (lst ++ lst') = 
    pareto_by_elem a lst ++ pareto_by_elem a lst'.
Proof.
  induction lst. auto.
  simpl. 
  rewrite eq_conv_is_less.
  destruct (is_less_than a a0) eqn:E1.
  simpl. apply IHlst.
  simpl. rewrite IHlst. reflexivity.
Qed.

Lemma pareto_by_elem_simpl a x xs lst 
    (H: is_less_than a x = true) : 
  pareto_by_elem a (lst ++ x :: xs) = pareto_by_elem a (lst ++ xs).
Proof.
  repeat rewrite pareto_by_elem_linear.
  rewrite par_elem2_less; auto.
Qed.

Lemma pareto_by_elem_remove a b lst
    (H: is_less_than a b = true) :
  pareto_by_elem a lst = pareto_by_elem a (pareto_by_elem b lst).
Proof.
  induction lst. auto.
  simpl.
  repeat rewrite eq_conv_is_less.
  destruct (is_less_than a a0) eqn:E3.
  { simpl.
    destruct (is_less_than b a0) eqn:E4.
    { simpl. auto. }
    simpl.
    rewrite eq_conv_is_less, E3. simpl.
    auto. }
  simpl.
  destruct (is_less_than b a0) eqn:E4.
  { simpl.
    assert (L: is_less_than a a0 = true).
    { apply (is_less_than_trans _ b); auto. }
    rewrite E3 in L. discriminate L. }
  simpl. rewrite eq_conv_is_less, E3.
  simpl. rewrite IHlst. reflexivity.
Qed.

Lemma pareto_by_elem_swap a b lst :
   pareto_by_elem b (pareto_by_elem a lst) = pareto_by_elem a (pareto_by_elem b lst).
Proof.
  induction lst. auto.
  simpl.
  repeat rewrite eq_conv_is_less.
  destruct (is_less_than a a0) eqn:E1.
  { simpl.
    destruct (is_less_than b a0) eqn:E2; auto.
    simpl.
    rewrite eq_conv_is_less, E1.
    auto. }
  simpl.
  destruct (is_less_than b a0) eqn:E2.
  { rewrite eq_conv_is_less, E2.
    auto. }
  rewrite eq_conv_is_less, E2.
  simpl.
  rewrite eq_conv_is_less, E1.
  simpl.
  rewrite IHlst.
  reflexivity.
Qed.
  
Lemma pareto_by_elem_not_nil :
  forall a b lst, is_less_exist a (pareto_by_elem b lst) = false ->
    is_less_than b a = true \/ is_less_exist a lst = false.
Proof.
  induction lst. auto.
  intro H.
  simpl in H.
  rewrite eq_conv_is_less in H.
  destruct (is_less_than b a0) eqn:E1.
  { simpl in H.
    rewrite is_exist_not_cons_alt.
    destruct IHlst; auto.
    rewrite H0.
    destruct (is_less_than a0 a) eqn:E2; auto.
    rewrite (is_less_than_trans b a0 a); auto. }
  simpl in H. simpl.
  unfold flip in *.
  destruct IHlst; auto.
  destruct (is_less_than a0 a) eqn:E2.
  simpl in H. discriminate H.
  simpl in H. apply H.
  rewrite H0.
  rewrite orb_false_r.
  destruct (is_less_than a0 a); auto.
Qed.

Lemma is_less_exist_with_elem :
  forall a b lst, is_less_exist a lst = false ->
    is_less_exist a (pareto_by_elem b lst) = false.
Proof.
  intros a b lst H.
  induction lst. auto.
  simpl.
  rewrite eq_conv_is_less.
  rewrite is_exist_not_cons_alt in H.
  destruct H.
  destruct (is_less_than b a0) eqn:E1; auto.
  simpl. unfold flip.
  rewrite H, IHlst; auto.
Qed.

Lemma is_less_exist_pareto_elem a b lst 
    (A: is_less_than a b = false)
    (C: is_less_exist b lst = true) : is_less_exist b (pareto_by_elem a lst) = true.
Proof.
  induction lst. auto.
  rewrite is_exist_cons_alt in C.
  destruct C.
  { destruct (is_less_than a a0) eqn:E1.
    { rewrite (is_less_than_trans a a0 b) in A; auto. }
    rewrite par_elem2_not_less; auto.
    rewrite is_exist_cons_alt; auto. }
  destruct (is_less_than a a0) eqn:E1.
  { rewrite par_elem2_less; auto. }
  rewrite par_elem2_not_less; auto.
  rewrite is_exist_cons_alt.
  auto.
Qed.

Lemma pareto_exec_exist a lst l r
    (H: is_less_exist a lst = true) :
  pareto_exec lst (l ++ a::r) = pareto_exec lst (l ++ r).
Proof. 
  generalize dependent lst.
  induction l.
  { intros lst H.
    simpl. rewrite H. reflexivity. }
  intros lst H.
  simpl.
  destruct (is_less_exist a0 lst) eqn:E1.
  { apply IHl; auto. }
  apply IHl.
  apply is_exist_cons_all.
  rewrite is_exist_cons_alt.
  destruct (is_less_exist a (pareto_by_elem a0 lst)) eqn:E2; auto.
  apply pareto_by_elem_not_nil in E2.
  destruct E2; auto.
  rewrite H0 in H.
  discriminate H.
Qed.

Lemma pareto_exec_same lst lst' :
   pareto_exec lst' (lst ++ lst') = pareto_exec lst' lst.
Proof.
  generalize dependent lst'.
  induction lst.
  { intro lst'.
    simpl.
    rewrite <- (app_nil_l lst') at 1 3.
    generalize dependent (nil: list t).
    induction lst'. auto.
    intro l.
    simpl.
    assert (L: is_less_exist a (l ++ a :: lst') = true).
    { apply is_exist_cons_all. 
      rewrite is_exist_cons_alt, is_less_than_refl.
      auto. }
    rewrite L.
    rewrite <- (app_nil_l lst') at 1 3.
    rewrite app_comm_cons.
    rewrite app_assoc.
    apply IHlst'. }
  intro lst'.
  rewrite <- app_comm_cons.
  simpl.
  destruct (is_less_exist a lst') eqn:E1. apply IHlst.
  rewrite <- IHlst.
  rewrite <- (app_nil_l (pareto_by_elem a lst')) at 1 2.
  rewrite <- app_assoc.
  generalize (nil : list t) at 1 3.
  induction lst'.
  { simpl. symmetry.
    apply pareto_exec_exist.
    rewrite is_exist_cons_all.
    simpl. unfold flip.
    rewrite is_less_than_refl. auto. }
  intro l.
  rewrite is_exist_not_cons_alt in E1.
  destruct E1 as [A B].
  destruct (is_less_than a a0) eqn:E2.
  { rewrite par_elem2_less; auto.
    rewrite pareto_exec_exist.
    apply IHlst'; auto.
    apply is_exist_cons_all.
    rewrite is_exist_cons_all.
    simpl. unfold flip.
    rewrite E2. auto. }
  rewrite par_elem2_not_less; auto.
  rewrite <- app_comm_cons.
  repeat rewrite pareto_exec_exist.
  2, 3: rewrite is_exist_cons_all; simpl; unfold flip;
    rewrite is_less_than_refl; auto.
  rewrite <- (app_nil_l (pareto_by_elem a lst')) at 1 2.
  rewrite <- app_assoc.
  assert (Rew: l ++ a0 :: nil ++ pareto_by_elem a lst' ++ a :: nil = 
               (l ++ a0 :: nil) ++ pareto_by_elem a lst' ++ a :: nil).
  { rewrite <- app_assoc. auto. }
  rewrite Rew.
  apply IHlst'; auto.
Qed.

Lemma linear_pareto_exist a lst 
    (H: is_less_exist a lst = true) :
  pareto (lst ++ [a]) = pareto lst.
Proof.
  unfold pareto.
  generalize (nil: list t) at 1 3.
  induction lst. discriminate H.
  intro lst'.
  rewrite is_exist_cons_alt in H.
  destruct H as [H|H].
  { simpl.
    destruct (is_less_exist a0 lst') eqn:E1.
    { rewrite pareto_exec_exist.
      rewrite app_nil_r.
      reflexivity.
      apply (is_less_exist_cont_true a0); auto. }
    rewrite pareto_exec_exist.
    { induction lst'.
      { simpl. rewrite app_nil_r.
        reflexivity. }
      rewrite is_exist_not_cons_alt in E1.
      destruct E1.
      simpl. rewrite eq_conv_is_less.
      rewrite app_nil_r.
      destruct (is_less_than a0 a1) eqn:E1; auto. }
    induction lst'.
    { simpl. unfold flip. rewrite H. auto. }
    simpl. rewrite eq_conv_is_less.
    rewrite is_exist_not_cons_alt in E1.
    destruct E1.
    destruct (is_less_than a0 a1) eqn:E2.
    { simpl. apply IHlst', H1. }
    simpl. rewrite IHlst'; auto.
    apply orb_true_r. }
  simpl.
  repeat rewrite IHlst; auto.
Qed.

Lemma linear_pareto_not_exist a lst (H : is_less_exist a lst = false) :
    pareto (lst ++ [a]) = pareto_by_elem a (pareto lst) ++ [a].
Proof.
  unfold pareto.
  assert (Gen: forall lst', is_less_exist a lst' = false ->
    pareto_exec lst' (lst ++ [a]) =
      pareto_by_elem a (pareto_exec lst' lst) ++ [a]).
  { induction lst.
    { intros lst' H1.
      simpl. rewrite H1. reflexivity. }
    intros lst' H1.
    rewrite is_exist_not_cons_alt in H.
    destruct H.
    simpl.
    repeat rewrite IHlst; auto.
    { destruct (is_less_exist a0 lst') eqn:E1; auto. }
    apply is_exist_not_cons_all.
    split.
    { apply is_less_exist_with_elem; auto. }
    apply is_exist_not_cons_alt. auto.
  }
  apply Gen. auto.
Qed.

Lemma pareto_ins_elem_exist a l r
      (H: is_less_exist a l = true) :
  pareto (l ++ a::r) = pareto (l ++ r).
Proof.
  unfold pareto.
  generalize dependent (nil:list t).
  induction l.
  { simpl in H.
    discriminate H. }
  intro lst.
  simpl.
  rewrite is_exist_cons_alt in H.
  destruct H.
  {  destruct (is_less_exist a0 lst) eqn:E1.
    { apply pareto_exec_exist.
      apply (is_less_exist_cont_true a0); auto. }
    apply pareto_exec_exist.
    rewrite is_exist_cons_all.
    simpl. unfold flip.
    rewrite H.
    auto. }
  destruct (is_less_exist a0 lst) eqn:E1; auto.
Qed.

Lemma pareto_nil : pareto nil = nil.
Proof.
  unfold pareto.
  auto.
Qed.

Lemma pareto_inside x lst :
   is_less_exist x (pareto lst) = is_less_exist x lst.
Proof.
  destruct (is_less_exist x lst) eqn:H.
  { generalize dependent x.
    induction lst using rev_ind; auto.
    ins.
    destruct (is_less_exist x lst) eqn:E1.
    { apply is_exist_cons_all in H.
      desf.
      { rewrite linear_pareto_exist; auto. }
      simpls.
      unfold flip in H.
      rewrite orb_false_r in H.
      rewrite linear_pareto_exist; auto.
      apply IHlst.
      apply (is_less_exist_cont_true x); auto. }
    rewrite linear_pareto_not_exist; auto.
    apply is_exist_cons_all in H.
    simpls.
    unfold flip in H.
    rewrite orb_false_r in H.
    apply is_exist_cons_all.
    desf.
    { simpls.
      unfold flip.
      destruct (is_less_than x x0) eqn:E2; auto.
      rewrite is_less_exist_pareto_elem; auto. }
    simpls.
    unfold flip.
    rewrite H; auto. }
  induction lst using rev_ind. auto.
  rewrite is_exist_not_cons_all in H.
  destruct H as [A B].
  rewrite is_exist_not_cons_alt in B.
  destruct B as [B C].
  destruct (is_less_exist x0 lst) eqn:E1.
  { rewrite linear_pareto_exist.
    all: auto. }
  rewrite linear_pareto_not_exist; auto.
  rewrite is_less_than_bef_aft, is_exist_not_cons_alt.
  rewrite is_less_exist_with_elem.
  all: auto.
Qed.

Lemma app_inv_all: forall (l:list t) l1 l2,
    l1 ++ l = l2 ++ l <-> l1 = l2.
Proof.
  split.
  { apply app_inv_tail. }
  ins.
  rewrite H.
  reflexivity.
Qed.

Lemma pareto_by_elem_pareto_swap lst x :
  pareto_by_elem x (pareto lst) = pareto (pareto_by_elem x lst).
Proof.
  induction lst using rev_ind. auto.
  destruct (is_less_exist x0 lst) eqn:E1.
  { rewrite linear_pareto_exist; auto.
    rewrite pareto_by_elem_linear.
    simpl. rewrite eq_conv_is_less.
    destruct (is_less_than x x0) eqn:E2.
    { simpl. rewrite app_nil_r.
      apply IHlst. }
    simpl.
    destruct (is_less_exist x0 (pareto_by_elem x lst)) eqn:E3.
    { rewrite linear_pareto_exist; auto. }
    apply pareto_by_elem_not_nil in E3.
    destruct E3.
    { rewrite linear_pareto_exist; auto.
      apply is_less_exist_pareto_elem; auto. }
    rewrite H in E1.
    discriminate E1. }
  rewrite linear_pareto_not_exist; auto.
  destruct (is_less_than x x0) eqn:E2.
  { repeat rewrite par_elem2_less_rev; auto.
    rewrite <- pareto_by_elem_remove; auto. }
  repeat rewrite par_elem2_not_less_rev; auto.
  rewrite linear_pareto_not_exist.
  { apply app_inv_all.
    rewrite pareto_by_elem_swap.
    rewrite IHlst.
    reflexivity. }
  apply is_less_exist_with_elem; auto.
Qed.

Lemma linear_pareto_exist_fst x y xs ys
      (H1: is_less_than x y = false)
      (H2: is_less_than y x = true) : pareto (x::xs ++ y::ys) = pareto (xs ++ y::ys).
Proof.
  induction ys using rev_ind.
  { rewrite app_comm_cons.
    destruct (is_less_exist y xs) eqn:E1.
    { repeat rewrite linear_pareto_exist; auto.
      { induction xs using rev_ind.
        { simpl in E1.
          discriminate E1. }
        apply is_exist_cons_all in E1.
        desf.
        { rewrite app_comm_cons.
          destruct (is_less_exist x0 xs) eqn:E2.
          { repeat rewrite linear_pareto_exist; auto.
            apply is_exist_cons_alt; auto. }
          repeat rewrite linear_pareto_not_exist; auto.
          { rewrite IHxs; auto. }
          apply is_exist_not_cons_alt.
          destruct (is_less_than x x0) eqn:E3; auto.
          rewrite (is_less_exist_cont_true y x0) in E2; auto.
          { discriminate E2. }
          apply (is_less_than_trans y x x0); auto. }
        simpl in E1.
        unfold flip in E1.
        rewrite orb_false_r in E1.
        rewrite app_comm_cons.
        destruct (is_less_exist x0 xs) eqn:E3.
        { repeat rewrite linear_pareto_exist; auto.
          { apply IHxs.
            apply (is_less_exist_cont_true x0 y); auto. }
          simpl.
          rewrite E3.
          apply orb_true_r. }
        repeat rewrite linear_pareto_not_exist; auto.
        { rewrite pareto_by_elem_pareto_swap.
          rewrite par_elem2_less.
          { rewrite pareto_by_elem_pareto_swap.
            reflexivity. }
          apply (is_less_than_trans x0 y x); auto. }
        apply is_exist_not_cons_alt.
        destruct (is_less_than x x0) eqn:E4; auto.
        rewrite (is_less_than_trans x x0 y) in H1; auto. }
      apply is_exist_cons_alt.
      rewrite E1.
      auto. }
    repeat rewrite linear_pareto_not_exist; auto.
    { rewrite pareto_by_elem_pareto_swap.
      rewrite par_elem2_less; auto.
      rewrite pareto_by_elem_pareto_swap.
      reflexivity. }
    apply is_exist_not_cons_alt.
    auto. }
  repeat rewrite app_comm_cons.
  repeat rewrite app_assoc.
  destruct (is_less_exist x0 (xs ++ y :: ys)) eqn:E1.
  { repeat rewrite linear_pareto_exist; auto.
    simpl.
    rewrite E1.
    apply orb_true_r. }
  repeat rewrite linear_pareto_not_exist; auto.
  { simpl.
    rewrite IHys.
    reflexivity. }
  simpl.
  rewrite E1.
  unfold flip.
  destruct (is_less_than x x0) eqn:E2.
  { apply is_exist_not_cons_all in E1.
    rewrite is_exist_not_cons_alt in E1.
    desf.
    rewrite (is_less_than_trans y x x0) in E0; auto. }
  simpl.
  reflexivity.
Qed.

Lemma pareto_ins_elem_not_exist a l r
      (H1: is_less_exist a r = true)
      (H2: forallb_not_exist (a::nil) r = true) :
  pareto (l ++ a::r) = pareto (l ++ r).
Proof.
  induction r using rev_ind.
  { simpl in H1.
    discriminate H1. }
  apply forallb_not_exist_des_rev in H2.
  destruct H2.
  simpl in H.
  apply is_exist_cons_all in H1.
  simpl in H1.
  unfold flip in *.
  rewrite orb_false_r in *.
  rewrite app_assoc.
  assert (Rew: l ++ a :: r ++ [x] = (l ++ a :: r) ++ [x]).
  { rewrite <- app_assoc.
    simpl.
    reflexivity. }
  rewrite Rew.
  clear Rew.
  destruct (is_less_exist a r) eqn:E1.
  { clear H1.
    destruct (is_less_exist x (l ++ a :: r)) eqn:E2.
    { repeat rewrite linear_pareto_exist; auto.
      apply is_exist_cons_all in E2.
      rewrite is_exist_cons_alt, H in E2.
      rewrite <- orb_true_iff in E2.
      simpl in E2.
      apply is_exist_cons_all.
      apply E2. }
    repeat rewrite linear_pareto_not_exist; auto.
    { rewrite <- IHr; auto. }
    apply is_exist_not_cons_all in E2.
    rewrite is_exist_not_cons_alt in E2.
    desf.
    apply is_exist_not_cons_all.
    auto. }
  clear IHr. 
  rewrite <- orb_true_iff in H1.
  simpl in H1.
  destruct (is_less_exist x (l ++ a :: r)) eqn:E2.
  { repeat rewrite linear_pareto_exist.
    { apply is_exist_cons_all in E2.
      rewrite is_exist_cons_alt in E2.
      destruct E2.
      { apply pareto_ins_elem_exist.
        apply (is_less_exist_cont_true x); auto. }
      destruct H2.
      { rewrite H2 in H.
        discriminate H. }
      rewrite (is_less_exist_cont_true x) in E1; auto.
      discriminate E1. }
    { apply is_exist_cons_all.
      apply is_exist_cons_all in E2.
      rewrite is_exist_cons_alt in E2.
      rewrite H in E2.
      rewrite <- orb_true_iff in E2.
      simpl in E2.
      apply E2. }
    apply E2. }
  repeat rewrite linear_pareto_not_exist; auto.
  { repeat rewrite pareto_by_elem_pareto_swap.
    rewrite pareto_by_elem_simpl; auto. }
  apply is_exist_not_cons_all in E2.
  rewrite is_exist_not_cons_alt in E2.
  destruct E2. destruct H3.
  apply is_exist_not_cons_all.
  auto.
Qed.

Lemma pareto_ins_list_exist l m r
      (H1: forallb_exist r m = true)
      (H2: forallb_not_exist m r = true) :
  pareto (l ++ m ++ r) = pareto (l ++ r).
Proof.
  generalize dependent r.
  induction m using rev_ind; auto.
  ins.
  rewrite <- app_assoc.
  simpl.
  apply forallb_exist_des_rev in H1.
  destruct H1.
  destruct r.
  { simpl in H.
    discriminate H. }
  rewrite app_assoc.
  apply forallb_not_exist_des_lst in H2.
  destruct H2.
  rewrite pareto_ins_elem_not_exist; auto.
  rewrite <- app_assoc.
  apply IHm; auto.
Qed.

Lemma pareto_by_elem_ins x lst
      (H: is_less_exist x lst = false) :
  pareto (pareto_by_elem x lst ++ [x]) =
  pareto_by_elem x (pareto lst) ++ [x].
Proof.
  rewrite linear_pareto_not_exist.
  { apply app_inv_all.
    generalize dependent x.
    induction lst using rev_ind. auto.
    ins.
    rewrite is_exist_not_cons_all, is_exist_not_cons_alt in H.
    destruct H as [A B].
    destruct B as [B C].
    destruct (is_less_than x0 x) eqn:E1.
    { rewrite par_elem2_less_rev; auto.
      destruct (is_less_exist x lst) eqn:E2.
      { rewrite linear_pareto_exist; auto. }
      rewrite linear_pareto_not_exist; auto.
      rewrite pareto_by_elem_linear.
      simpl. rewrite eq_conv_is_less, E1.
      simpl. rewrite <- pareto_by_elem_remove; auto.
      rewrite app_nil_r.
      apply IHlst.
      auto. }
    rewrite par_elem2_not_less_rev; auto.
    destruct (is_less_exist x lst) eqn:E2.
    { repeat rewrite linear_pareto_exist; auto.
      apply is_less_exist_pareto_elem; auto. }
    rewrite (linear_pareto_not_exist x lst); auto.
    rewrite linear_pareto_not_exist.
    { repeat rewrite par_elem2_not_less_rev; auto.
      repeat rewrite <- app_assoc.
      rewrite pareto_by_elem_swap, IHlst; auto.
      rewrite pareto_by_elem_swap.
      reflexivity. }
    apply is_less_exist_with_elem; auto. }
  induction lst. auto.
  rewrite is_exist_not_cons_alt in H.
  destruct H as [A B].
  destruct (is_less_than x a) eqn:E1.
  { rewrite par_elem2_less; auto. }
  rewrite par_elem2_not_less; auto.
  apply is_exist_not_cons_alt.
  auto.  
Qed.

Lemma pareto_rem_pareto_by_elem x lst' :
  forall lst, is_less_exist x lst = true ->
  pareto (lst ++ pareto_by_elem x lst') = pareto (lst ++ lst').
Proof.
  induction lst'; auto.
  intros.
  destruct (is_less_than x a) eqn:E1.
  { rewrite par_elem2_less; auto.
    rewrite pareto_ins_elem_exist; auto.
    apply (is_less_exist_cont_true x a); auto. }
  rewrite par_elem2_not_less; auto.
  assert (lem : lst ++ a::lst' = (lst ++ [a]) ++ lst').
  { rewrite <- app_assoc.
    auto. }
  rewrite lem.
  rewrite <- IHlst'.
  { rewrite <- app_assoc.
    auto. }
  apply is_exist_cons_all.
  auto.
Qed.  
 
Lemma pareto_linear_fst lst :
  forall lst', pareto (lst ++ lst') = pareto (pareto lst ++ lst').
Proof.
  induction lst using rev_ind; auto.
  ins.
  rewrite <- app_assoc.
  simpl.
  destruct (is_less_exist x lst) eqn:E1.
  { rewrite linear_pareto_exist.
    rewrite pareto_ins_elem_exist.
    all: auto. }
  rewrite linear_pareto_not_exist; auto.
  rewrite <- app_assoc.
  simpl.
  rewrite IHlst. 
  set (l := pareto lst).
  assert (lem : is_less_exist x l = false).
  { unfold l.
    rewrite pareto_inside; auto. }
  induction lst' using rev_ind.
  { repeat rewrite linear_pareto_not_exist; auto.
    { repeat rewrite pareto_by_elem_pareto_swap.
      rewrite <- pareto_by_elem_remove; auto.
      apply is_less_than_refl. }
    apply is_less_exist_with_elem; auto.
  }
  assert (rew: forall mas, mas ++ x::lst' ++ [x0] = (mas ++ x::lst') ++ [x0]).
  { ins.
    rewrite <- app_assoc.
    auto. }
  repeat rewrite rew.
  destruct (is_less_exist x0 (l ++ x::lst')) eqn:E2.
  { repeat rewrite linear_pareto_exist; auto.
    apply is_exist_cons_all.
    apply is_exist_cons_all in E2.
    destruct (is_less_exist x0 (x :: lst')) eqn:E3; auto.
    apply is_exist_not_cons_alt in E3.
    destruct E3.
    rewrite is_less_exist_pareto_elem; auto.
    destruct E2; auto. }
  repeat rewrite linear_pareto_not_exist; auto.
  { rewrite IHlst'.
    reflexivity. }
  apply is_exist_not_cons_all.
  apply is_exist_not_cons_all in E2.
  rewrite is_exist_not_cons_alt in *.
  destruct E2.
  rewrite is_less_exist_with_elem.
  all: auto.
Qed.
  
Lemma pareto_linear lst lst' :
  pareto (lst ++ lst') = pareto (pareto lst ++ pareto lst').
Proof.
  rewrite pareto_linear_fst.
  generalize (pareto lst) as mas.
  intro mas.
  induction lst' using rev_ind.
  { rewrite pareto_nil.
    reflexivity. }
  destruct (is_less_exist x lst') eqn:E1.
  { rewrite linear_pareto_exist; auto.
    rewrite app_assoc, pareto_ins_elem_exist.
    { rewrite app_nil_r.
      apply IHlst'. }
    apply is_exist_cons_all.
    auto. }
  rewrite linear_pareto_not_exist; auto.
  repeat rewrite app_assoc.
  destruct (is_less_exist x mas) eqn:E2.
  { repeat rewrite linear_pareto_exist.
    { rewrite pareto_rem_pareto_by_elem; auto. }
    { apply is_exist_cons_all.
      auto. }
    apply is_exist_cons_all.
    auto. }
  repeat rewrite linear_pareto_not_exist.
  { apply app_inv_all.
    rewrite IHlst'.
    rewrite pareto_by_elem_pareto_swap.
    rewrite pareto_by_elem_pareto_swap.
    repeat rewrite pareto_by_elem_linear.
    rewrite <- pareto_by_elem_remove; auto.
    apply is_less_than_refl. }
  { apply is_exist_not_cons_all.
    rewrite is_less_exist_with_elem; auto.
    rewrite pareto_inside; auto. }
  apply is_exist_not_cons_all.
  auto.
Qed.

Lemma pareto_less_elem a lst :
  In a lst -> is_less_exist a (pareto lst) = true.
Proof.
  induction lst using rev_ind; auto.
  ins.
  apply in_app_or in H.
  simpls.
  desf.
  { destruct (is_less_exist x lst) eqn:E1.
    { rewrite linear_pareto_exist; auto. }
    rewrite linear_pareto_not_exist; auto.
    apply is_exist_cons_all.
    rewrite is_exist_cons_alt.
    destruct (is_less_than x a) eqn:E2; auto.
    rewrite is_less_exist_pareto_elem; auto. }
  clear IHlst.
  destruct (is_less_exist a lst) eqn:E1.
  { rewrite linear_pareto_exist; auto.
    rewrite pareto_inside; auto. }
  rewrite linear_pareto_not_exist; auto.
  apply is_exist_cons_all.
  rewrite is_exist_cons_alt.
  rewrite is_less_than_refl.
  auto.
Qed.  

Lemma map_func_nil lst (f: t -> list t)
  (F: forall a, f a = nil) : concat (map f lst) = nil.
Proof.
  induction lst. auto.
  ins.
  rewrite F, IHlst.
  apply app_nil_l.
Qed.

Lemma pareto_list_remove lst lst' :
  forallb_exist lst lst' = true ->
      pareto (lst ++ lst') = pareto lst.
Proof.
  ins.
  induction lst'.
  { rewrite app_nil_r.
    reflexivity. }
  simpl in H.
  apply andb_prop in H.
  destruct H as [A B].
  rewrite pareto_ins_elem_exist; auto.
Qed.

Lemma add_general_rev f w lst a b:
  add_general f w (lst ++ [a]) b = add_general f w lst b ++ (if total_width (f a b) <=? w
                                                             then (f a b::nil) else nil).
Proof.  
  unfold add_general.
  induction lst; auto.
  simpl.
  desf.
  all: simpl; rewrite IHlst; reflexivity.
Qed.                               

Lemma add_general_not_exist_elem l a b c f w
      (H: is_less_exist b (add_general f w l a) = false) :
  is_less_exist b (add_general f w (pareto_by_elem c l) a) = false.
Proof.
  ins.
  induction l; auto.
  simpl in H.
  destruct (total_width (f a0 a) <=? w) eqn:E6.
  { apply is_exist_not_cons_alt in H.
    desf.
    destruct (is_less_than c a0) eqn:E3.
    { rewrite par_elem2_less; auto. }
    rewrite par_elem2_not_less; auto.
    simpl.
    rewrite E6.
    apply is_exist_not_cons_alt.
    auto. }
  destruct (is_less_than c a0) eqn:E3.
  { rewrite par_elem2_less; auto. }
  rewrite par_elem2_not_less; auto.
  simpl.
  rewrite E6.
  apply IHl; auto.
Qed.

Lemma cross_general_eq w f lst lst' :
  pareto (FormatTrivial.cross_general w f lst lst') =
  FormatList.cross_general f w lst lst'.
Proof.
  unfold cross_general.
  assert (H: FormatTrivial.cross_general w f lst lst' =
             concat (map (add_general f w lst) lst')).
  { induction lst'.
    { simpl.
      unfold FormatTrivial.cross_general.
      auto. }
    simpl.
    rewrite <- IHlst'.
    clear IHlst'.
    unfold FormatTrivial.cross_general.
    simpl.
    rewrite filter_app.
    apply app_inv_all.
    unfold add_general.
    generalize (fun f0 : t => total_width f0 <=? w) as g.
    generalize (fun f' : t => f f' a) as h.
    ins.
    induction lst; auto.
    simpl.
    destruct (g (h a0)); auto.
    rewrite IHlst.
    reflexivity.
  }
  rewrite H.
  reflexivity.
Qed.

Notation "a ⊆ b" := (incl a b)  (at level 60).

Lemma pareto_incl lst : pareto lst ⊆ lst.
Proof.
  induction lst using rev_ind; simpls.
  destruct (is_less_exist x lst) eqn:E1.
  { rewrite linear_pareto_exist; auto.
    apply incl_appl.
    apply IHlst. }
  rewrite linear_pareto_not_exist; auto.
  assert (L: forall l, pareto_by_elem x l ⊆ l).
  { ins.
    induction l.
    { done. }
    destruct (is_less_than x a) eqn:E2.
    { rewrite par_elem2_less; auto.
      apply incl_tl.
      apply IHl. }
    rewrite par_elem2_not_less; auto.
    apply incl_cons.
    { done. }
    apply incl_tl.
    apply IHl. }
  apply (incl_tran (m:= pareto lst ++ [x])).
  { apply incl_app.
    { apply incl_appl.
      apply L. }
    apply incl_appr.
    done. }
  apply incl_app.
  { apply incl_appl.
    apply IHlst. }
  apply incl_appr.
  done.
Qed.    
 
Lemma indent_eq sh lst w :
  FormatTrivial.indentDoc w sh lst = FormatList.indentDoc w sh lst.
Proof.
  unfold FormatTrivial.indentDoc, FormatTrivial.cross_general.
  generalize (empty).
  induction lst; auto.
  ins.
  destruct (total_width (indent' sh a) <=? w) eqn:E1.
  { rewrite IHlst.
    { reflexivity. }
    done. }
  apply IHlst.
  done.
Qed.    

Definition base_assumption lst lst' := list_correct lst /\
                                       list_correct lst' /\
                                       is_less_exist' lst lst'.  

Lemma pareto_inside' x lst
      (L: list_correct lst)
      (H: exists a, In a lst /\ is_less_than' a x = true) :
  exists b, In b (pareto lst) /\ is_less_than' b x = true.
Proof.
  desf.
  unfold is_less_than' in H0.
  unfold list_correct in L.
  unfold format_correct in L.
  unfold format_correct2 in L.
  desf. 
  { assert (format_correct1 a /\ height a > 0 /\ format_correct3 a).
    { apply L; auto. }   
    desf.
    lia. }
  { unfold is_less_than in H0.
    desf.
    assert (is_less_exist a (pareto lst) = true).
    { apply pareto_less_elem; auto. }
    apply is_exist_eq in H1.
    desf.
    exists b.
    split; auto.
    unfold is_less_than'.
    unfold is_less_than in *.
    unfold less_components in *.
    desf.
    andb_split.
    repeat (apply andb_true_iff; split).
    all: apply Nat.leb_le; auto.
    { apply leb_complete in H5.
      apply leb_complete in H8.
      lia. }
    { apply leb_complete in H4.
      apply leb_complete in H7.
      lia. }
    apply leb_complete in H3.
    apply leb_complete in H6.
    lia. }
  { assert (is_less_exist a (pareto lst) = true).
    { apply pareto_less_elem; auto. }
    apply is_exist_eq in H1.
    desf.
    exists b.
    split; auto.
    andb_split.
    apply leb_complete in H0.
    apply leb_complete in H3.
    apply leb_complete in H4.
    unfold is_less_than'.
    desf.
    { assert (height b > 0).
      { apply L.
        apply pareto_incl; auto. }
      lia. }
    { unfold is_less_than.
      desf.
      { lia. }
      { unfold is_less_than in H2.
        desf. }
      unfold is_less_than in H2.
      desf. }
    { unfold is_less_than in H2.
      unfold less_components in H2.
      repeat (apply andb_true_iff; split).
      all: apply Nat.leb_le.
      all: desf.
      { andb_split.
        apply leb_complete in H7.
        lia. }
      andb_split.
      apply leb_complete in H5.
      lia. }
    unfold is_less_than in H2.
    unfold less_components in H2.
    desf. }
  assert (is_less_exist a (pareto lst) = true).
  { apply pareto_less_elem; auto. }
  apply is_exist_eq in H1.
  desf.
  exists b.
  split; auto.
  unfold is_less_than'.
  rewrite (is_less_than_trans _ a); auto.
  desf.
  assert (is_less_than b x = true).
  { apply (is_less_than_trans _ a); auto. }
  unfold is_less_than in H3.
  unfold less_components in H3.
  desf.
  andb_split.
  repeat (apply andb_true_iff; split).
  all: apply Nat.leb_le.
  { lia. }
  { apply leb_complete in H6.
    apply H6. }
  apply leb_complete in H4.
  apply H4.
Qed.  
  
Lemma height_remove lst lst' w
      (E: base_assumption lst lst')
      (I: pick_best_list lst w ⊆ pick_best_list lst' w) :
  get_min_height lst w None = get_min_height lst' w None.
Proof.
  unfold base_assumption in E. 
  destruct E as [R1 R2].
  destruct R2 as [R2 E].
  unfold pick_best_list in I at 2.
  destruct (height_values lst' w).
  { assert (L: pick_best_list lst w ⊆ nil -> get_min_height lst w None = None).
    { clear.
      ins.
      unfold pick_best_list in H.
      desf.
      generalize Heq, H.
      clear.
      generalize (t::l) as lst.
      ins.
      induction lst; simpls.
      desf.
      { unfold incl in H.
        simpls.
        assert (False).
        { apply (H a); auto. }
        done. }
      { simpls.
        apply beq_nat_false in Heq0.
        apply height_not_eq in Heq; auto. }
      apply IHlst; auto. }
    desf.
    { simpls.
      apply L; auto. }
    apply L; auto. }
  desf.
  generalize E, I, H, Heq, H0, R1, R2.
  clear.
  generalize (t::l) as lst'.
  ins.
  destruct (height_values lst w).
  { unfold pick_best_list in I.
    desf.
    { assert (exists x, In x nil /\ is_less_than' x a = true).
      { apply E; auto. }
      desf. }
    assert (exists b, In b (t0 :: l0) /\ is_less_than' b a = true).
    { apply E; auto. }
    desf.
    assert (format_correct a /\ format_correct b).
    { split.
      { apply R2; auto. }
      apply R1; auto. }
    desf.
    assert (False).
    { unfold format_correct in *.
      unfold format_correct1 in *.
      unfold format_correct2 in *.
      unfold format_correct3 in *.
      apply (height_discr' b (t0::l0) w); auto.
      apply leb_complete in H0.
      unfold is_less_than' in H3.
      unfold is_less_than in H3.
      unfold less_components in H3.
      desf.
      all: andb_split.
      all: apply leb_complete in H4.
      all: apply leb_complete in H3.
      all: try apply leb_complete in H5.
      all: unfold total_width in *.
      all: desf; simpls.
      all: lia. }
    done. }
  desf.
  rewrite H3.  
  unfold pick_best_list in I.
  desf.
  generalize I, H1, H2.
  generalize (t0::l0) as lst.
  clear.
  ins.
  induction lst; simpls.
  desf.
  { generalize I.
    clear.
    ins.
    assert (In a0 (filter (fun f : t => (total_width f <=? w) && (height f =? height a)) lst')).
    { unfold incl in I.
      simpls.
      apply (I a0); auto. }
    clear I.
    induction lst'; simpls.
    desf.
    { rewrite in_cons_iff in H.
      desf.
      { apply andb_prop in Heq.
        desf.
        apply beq_nat_true in Heq0.
        auto. }
      apply IHlst'; auto. }
    apply IHlst'; auto. }
  { simpls.
    apply beq_nat_false in Heq.
    done. }
  { apply IHlst; auto.
    apply (incl_tran (m:= a1 :: filter (fun f : t => (total_width f <=? w) && (height f =? height a0)) lst)).
    { apply incl_tl.
      done. }
    apply I. }
  apply IHlst; auto.
Qed.

Lemma height_list_only a lst w
      (H: total_width a <=? w = true) :
   get_min_height (lst ++ [a]) w None = get_min_height lst w (Some (height a)).
Proof.
  generalize dependent a.
  induction lst.
  { ins.
    desf. }
  ins.
  desf.
  { clear IHlst.
    generalize H, Heq.
    clear.
    generalize a, a0.
    clear.
    induction lst.
    { ins.
      desf.
      rewrite NPeano.Nat.min_comm; auto. }
    ins.
    desf.
    { rewrite <- Nat.min_assoc.
      destruct (height a0 <=? height a) eqn:E1.
      { rewrite Min.min_l.
        { apply IHlst; auto. }
        apply leb_complete in E1; auto. }
      rewrite min_leb.
      { apply IHlst; auto. }
      apply Nat.leb_gt in E1; auto. }
    apply IHlst; auto. }
  apply IHlst; auto.
Qed.  

Lemma height_elem_big m n lst w
      (H: get_min_height lst w None = Some m)
      (I: n <= m) : get_min_height lst w (Some n) = Some n.
Proof.
  induction lst; simpls.
  desf.
  { clear IHlst.
    clear Heq.
    generalize dependent H.
    generalize I.
    generalize (height a) as p.
    clear I.
    generalize dependent n.
    induction lst; simpls.
    { ins.
      destruct (n <=? p) eqn:E1.
      { apply leb_complete in E1.
        rewrite Min.min_l; auto. }
      apply Nat.leb_gt in E1.
      inversion H.
      lia. }
    desf.
    ins.
    rewrite <- Nat.min_assoc.
    apply IHlst; auto. }
  apply IHlst; auto.
Qed. 

Lemma height_elem_res n lst w
      (H: get_min_height lst w None = None) : get_min_height lst w (Some n) = Some n.
Proof.
  induction lst; simpls.
  desf.
  { clear IHlst.
    clear Heq.
    generalize dependent H.
    generalize (height a) as m.
    generalize dependent n.
    induction lst; simpls.
    desf.
    ins.
    rewrite <- Nat.min_assoc.
    apply IHlst; auto. }
  apply IHlst; auto.
Qed.

Lemma height_elem_only lst lst' w n
      (H: get_min_height lst w None = get_min_height lst' w None) :
  get_min_height lst w (Some n) = get_min_height lst' w (Some n).
Proof.
  generalize dependent n.
  induction lst'.
  { ins.
    apply height_elem_res; auto. }
  ins.
  desf.
  { clear IHlst'.
    clear Heq.
    generalize H.
    clear.
    generalize (height a) as m.
    generalize dependent n.
    induction lst'.
    { ins.
      destruct (n <=? m) eqn:E1.
      { apply leb_complete in E1.
        rewrite Min.min_l; auto. 
        apply (height_elem_big m); auto. }
      apply Nat.leb_gt in E1.
      rewrite min_leb; auto.
      apply height_remove_val; auto. }
    ins.
    desf.
    { rewrite <- Nat.min_assoc.
      apply IHlst'; auto. }
    apply IHlst'; auto. }
  apply IHlst'; auto.
Qed.

Lemma pick_add_elems a lst lst' w
      (E: base_assumption lst lst')
      (I: lst ⊆ lst')
      (H: pick_best_list lst w ⊆ pick_best_list lst' w) :
  pick_best_list (lst ++ [a]) w ⊆ pick_best_list (lst' ++ [a]) w.
Proof.
  unfold base_assumption in E.
  destruct E as [R1 R2].
  destruct R2 as [R2 E].
  unfold pick_best_list at 1. 
  desf.
  apply best_remove_helper. 
  { rewrite <- Heq in Heq0.
    clear Heq.
    assert (T: get_min_height lst w None = get_min_height lst' w None).
    { apply height_remove; auto.
      simpls. }
    clear H.
    clear E.
    destruct (total_width a <=? w) eqn:E1.
    { rewrite height_list_only; auto.
      rewrite height_list_only in Heq0; auto.
      clear E1.
      rewrite <- Heq0.
      clear Heq0.
      symmetry.
      generalize (height a) as m.
      ins.
      apply height_elem_only; auto. }
    rewrite get_height_none; auto.
    rewrite get_height_none in Heq0; auto.
    rewrite <- T; auto. }
  unfold incl.
  clear Heq0.
  simpl.
  ins.
  desf.
  { assert (In a0 (lst ++ [a])).
    { rewrite Heq.
      done. }
    apply in_app_or in H0.
    desf.
    { apply in_app_l.
      generalize H0, I.
      clear.
      ins.
      induction lst.
      { done. }
      unfold incl in I.
      simpls.
      desf.
      all:apply (I a0); auto. }
    simpls.
    desf.
    apply in_app_r.
    simpls.
    auto. }
  assert (In a0 (lst ++ [a])).
  { rewrite Heq.
    apply in_cons.
    done. }
  apply in_app_or in H1.
  desf.
  { apply in_app_l.
    generalize H1, I.
    clear.
    ins.
    induction lst.
    { done. }
    unfold incl in I.
    simpls.
    desf.
    all:apply (I a0); auto. }
  simpls.
  desf.
  apply in_app_r.
  simpls.
  auto.
Qed.  

Lemma pareto_elem_height a lst w
      (C: list_correct lst)
      (F: format_correct a) :
      forall b, total_width b <= w ->
  get_min_height (lst ++ [a]) w (Some (height b)) =
  get_min_height (pareto_by_elem a lst ++ [a]) w (Some (height b)).
Proof.
  induction lst; auto.
  destruct (is_less_than a a0) eqn:E1.
  { intros.
    rewrite par_elem2_less; auto.
    assert (height a > 0 /\ height a0 > 0).
    { apply list_correct_add_b in C.
      desf.
      split.
      { apply F. }
      apply C0. }
    desf.
    unfold is_less_than in E1.
    unfold less_components in E1.
    desf.
    all: try lia.
    all: andb_split.
    all: apply leb_complete in H2.
    all: apply leb_complete in H3.
    all: apply leb_complete in H4.
    all: apply leb_complete in H5.
    all: simpls.
    { desf. 
      { destruct (height a0 <=? height b) eqn:E2.
        { apply leb_complete in E2.
          rewrite NPeano.Nat.min_r; auto.
          rewrite <- IHlst; auto.
          { clear IHlst.
            apply leb_complete in Heq1.
            repeat rewrite get_height_to_none; auto.
            { unfold total_width in *.
              desf.
              simpls.
              lia. }
            { lia. }
            { unfold total_width in *.
              desf.
              simpls.
              lia. }
            lia. }
          apply list_correct_add_b in C.
          desf. }
        apply Nat.leb_gt in E2.
        rewrite min_l.
        { apply IHlst; auto.
          apply list_correct_add_b in C.
          desf. }
        lia. }
      apply IHlst; auto.
      apply list_correct_add_b in C.
      desf. }
    desf.
    destruct (height a0 <=? height b) eqn:E2.
    { apply leb_complete in E2.
      rewrite NPeano.Nat.min_r; auto.
      rewrite <- IHlst; auto.
      { clear IHlst.
        apply leb_complete in Heq1.
        repeat rewrite get_height_to_none; auto.
        { unfold total_width in *.
          desf.
          simpls.
          lia. }
        { lia. }
        { unfold total_width in *.
          desf.
          simpls.
          lia. }
        lia. }
      apply list_correct_add_b in C.
      desf. }
    { apply Nat.leb_gt in E2.
      rewrite min_l.
      { apply IHlst; auto.
        apply list_correct_add_b in C.
        desf. }
      lia. }
      apply IHlst; auto.
      apply list_correct_add_b in C.
      desf. }
  intros.
  rewrite par_elem2_not_less; auto.
  simpls. 
  desf.
  { apply leb_complete in Heq.
    destruct (height b <=? height a0) eqn:E2.
    { apply leb_complete in E2.
      rewrite NPeano.Nat.min_l; auto.
      apply IHlst; auto.
      apply list_correct_add_b in C.
      desf. }
    apply Nat.leb_gt in E2.
    rewrite min_leb; auto.
    apply IHlst; auto.
    apply list_correct_add_b in C.
    desf. }
  apply IHlst; auto.
  apply list_correct_add_b in C.
  desf.
Qed. 

Lemma pick_height_none lst a w
      (C: list_correct lst)
      (F: format_correct a) :
  get_min_height (pareto_by_elem a lst ++ [a]) w None =
  get_min_height (lst ++ [a]) w None.
Proof.
  induction lst; auto.
  destruct (is_less_than a a0) eqn:E1.
  { rewrite par_elem2_less; auto.
    simpls. 
    assert (height a > 0 /\ height a0 > 0).
    { split.
      { apply F. }
      apply list_correct_add_b in C.
      desf.
      apply C0. }
    desf. 
    { unfold is_less_than in E1.
      unfold less_components in E1.
      desf.
      all: try lia.
      all: andb_split.
      all: apply leb_complete in H1.
      all: apply leb_complete in H2.
      all: apply leb_complete in H3.
      all: apply leb_complete in H4.
      all: apply leb_complete in Heq.
      { rewrite <- Heq0.
        rewrite get_height_to_none.
        { apply IHlst.
          apply list_correct_add_b in C.
          desf. }
        { unfold total_width in *.
          desf.
          simpls.
          lia. }
        lia. }
      rewrite <- Heq1.
      rewrite get_height_to_none.
      { apply IHlst.
        apply list_correct_add_b in C.
        desf. }
      { unfold total_width in *.
        desf.
        simpls.
        lia. }
      lia. }
    apply IHlst.
    apply list_correct_add_b in C.
    desf. }
  rewrite par_elem2_not_less; auto.
  simpls.
  desf.
  { apply leb_complete in Heq.
    rewrite <- pareto_elem_height; auto.
    apply list_correct_add_b in C.
    desf. }
  apply IHlst.
  apply list_correct_add_b in C.
  desf.
Qed.

Lemma pick_pareto_incl lst w
      (H: list_correct lst) :
  pick_best_list (pareto lst) w ⊆ pick_best_list lst w.
Proof.
  induction lst using rev_ind; simpls.
  destruct (is_less_exist x lst) eqn:E1.
  { rewrite linear_pareto_exist; auto.
    apply list_correct_add_e in H.
    desf.
    apply (incl_tran (m:= pick_best_list lst w)).
    { apply IHlst; auto. }
    clear IHlst.
    induction lst.
    { simpl in E1.
      discriminate E1. }
    apply is_exist_cons_alt in E1.
    desf.
    { apply pick_is_less'; auto.
      apply list_correct_add_b in H.
      desf. }
    simpls.
    destruct (total_width a <=? w) eqn:E2.
    { simpl.
      rewrite (get_height_exist _ x); auto.
      { desf.
        { rewrite filter_app.
          apply incl_cons.
          { done. }
          apply incl_tl.
          apply incl_appl.
          done. }
        rewrite filter_app.
        apply incl_appl.
        done. }
      apply list_correct_add_b in H.
      desf. }
    rewrite pick_height_link; auto.
    { desf.
      rewrite filter_app.
      apply incl_appl.
      done. }
    apply list_correct_add_b in H.
    desf. }
  apply list_correct_add_e in H.
  desf.
  rewrite linear_pareto_not_exist; auto. 
  apply (pick_add_elems x) in IHlst; auto.
  { apply (incl_tran (m:= pick_best_list (pareto lst ++ [x]) w)).
    { unfold pick_best_list.
      rewrite pick_height_none.
      { generalize (pareto lst).
        ins. 
        desf.
        rewrite <- Heq.
        rewrite <- Heq1.
        clear.
        induction l. 
        { done. }
        destruct (is_less_than x a) eqn:E1.
        { rewrite par_elem2_less; auto.
          simpls.
          desf.
          apply incl_tl.
          apply IHl. }
        rewrite par_elem2_not_less; auto.
        simpls.
        desf.
        apply incl_cons.
        { done. }
        apply incl_tl.
        apply IHl. }
      { apply (list_correct_incl _ lst); auto.
        apply pareto_incl. }
      apply H0. }
    apply IHlst. }
  { split.
    { apply (list_correct_incl _ lst); auto.
      apply pareto_incl. }
    split; auto.
    unfold is_less_exist'.
    ins.
    assert (is_less_exist b (pareto lst) = true).
    { apply pareto_less_elem; auto. }
    apply is_exist_eq in H2.
    desf.
    exists b0.
    split; auto.
    unfold is_less_than'.
    desf.
    unfold is_less_than in H3.
    unfold less_components in H3.
    desf.
    andb_split.
    rewrite H3, H6, H4.
    auto. }
  apply pareto_incl.
Qed.   

Lemma cross_general_cor lst1 lst2 lst1' lst2' f w
      (H1: lst1 ⊆ lst1')
      (H2: lst2 ⊆ lst2') :
  FormatTrivial.cross_general w f lst1 lst2 ⊆ FormatTrivial.cross_general w f lst1' lst2'.
Proof.
  induction lst2; simpls.
  unfold FormatTrivial.cross_general.
  simpl.
  rewrite filter_app.
  apply incl_app.
  { clear IHlst2.
    assert (L: In a lst2').
    { unfold incl in H2.
      simpl in H2.
      apply H2; auto. }
    clear H2.
    induction lst2'; simpls.
    rewrite filter_app.
    desf.
    { apply incl_appl.
      clear IHlst2'.
      induction lst1; simpls.
      desf.
      { apply incl_cons.
        { clear IHlst1.
          assert (L: In a0 lst1').
          { unfold incl in H1.
            simpl in H1.
            apply H1; auto. }
          clear H1.
          induction lst1'; simpls.
          desf.
          { simpl.
            auto. }
          apply IHlst1'.
          apply L. }
        apply IHlst1.
        apply (incl_tran (m:= a0 :: lst1)).
        { apply incl_tl.
          done. }
        apply H1. }
      apply IHlst1.
      apply (incl_tran (m:= a0 :: lst1)).
      { apply incl_tl.
        done. }
      apply H1. }
    apply incl_appr.
    apply IHlst2'.
    apply L.
  }
  unfold FormatTrivial.cross_general in IHlst2.
  apply IHlst2.
  apply (incl_tran (m:= a :: lst2)).
  { apply incl_tl.
    done. }
  apply H2.
Qed.

Lemma cross_general_elem a w f lst lst'
      (F: fun_correct f)
      (A: list_correct lst)
      (B: list_correct lst') :
  In a (FormatTrivial.cross_general w f lst lst') <->
  exists x y, a = (f x y) /\ In x lst /\ In y lst' /\ total_width (f x y) <= w. 
Proof.
  split.
  { ins.
    generalize dependent lst.
    induction lst'; simpls.
    ins.
    unfold FormatTrivial.cross_general in *.
    simpl in H.
    rewrite filter_app in H.
    apply in_app_or in H.
    apply list_correct_add_b in B.
    desf.
    { clear IHlst'.
      induction lst; simpls.
      apply list_correct_add_b in A.
      desf.
      { simpls.
        desf.
        { exists a1, a0.
          apply leb_complete in Heq.
          repeat split; auto. }
        assert (L: exists x y : t,
                   a = f x y /\ In x lst /\ (a0 = y \/ In y lst') /\ total_width (f x y) <= w).
        { apply IHlst; auto. }
        desf.
        all: exists x, y; desf; auto. }
      assert (L: exists x y : t,
                 a = f x y /\ In x lst /\ (a0 = y \/ In y lst') /\ total_width (f x y) <= w).
      { apply IHlst; auto. }
      desf.
      all: exists x, y; desf; auto. }
    assert (L: exists x y : t, a = f x y /\ In x lst /\ In y lst' /\ total_width (f x y) <= w).
    { apply IHlst'; auto. }
    desf.
    exists x,y.
    desf; auto. }
  ins.
  desf.
  assert (C: total_width x <= w /\ total_width y <= w).
  { unfold fun_correct in F.
    desf.
    apply F0; auto. }
  desf.
  generalize dependent lst.
  induction lst'; simpls.
  ins.
  unfold FormatTrivial.cross_general in *.
  simpls.
  rewrite filter_app.
  apply in_or_app.
  desf.
  { clear IHlst'.
    assert (In (f x y) (filter (fun f0 : t => total_width f0 <=? w) (map (fun a : t => f a y) lst))).
    { induction lst; simpls.
      apply list_correct_add_b in A.
      desf.
      { apply Nat.leb_gt in Heq.
        lia. }
      { simpls.
        assert (In (f x y) (filter (fun f0 : t => total_width f0 <=? w) (map (fun a0 : t => f a0 y) lst))).
        { apply IHlst; auto. }
        auto. }
      apply IHlst; auto. }
    auto. }
  assert (In (f x y)
    (filter (fun f0 : t => total_width f0 <=? w)
            (concat (map (fun b : t => map (fun a0 : t => f a0 b) lst) lst')))).
  { apply IHlst'; auto.
    apply list_correct_add_b in B.
    desf. }
  auto.
Qed.

Lemma cross_correct w lst lst' f
      (F: fun_correct f)
      (H1: list_correct lst)
      (H2: list_correct lst') : list_correct (FormatTrivial.cross_general w f lst lst').
Proof.
  unfold list_correct.
  ins.
  apply cross_general_elem in H; auto.
  desf.
  unfold fun_correct in F.
  desf.
  apply F.
  unfold list_correct in *.
  split.
  { apply H1; auto. }
  apply H2; auto.
Qed.  

Lemma elem_in lst1 lst2 lst1' lst2' f w
      (F: fun_correct f)
      (H1: base_assumption lst1' lst1)
      (H2: base_assumption lst2' lst2) :
  is_less_exist' (FormatTrivial.cross_general w f lst1' lst2')
                 (FormatTrivial.cross_general w f lst1 lst2).
Proof.
  unfold is_less_exist'. 
  ins.
  apply cross_general_elem in H; auto.
  { desf.
    assert (L1: exists a, In a lst1' /\ is_less_than' a x = true).
    { apply H1; auto. }
    assert (L2: exists b, In b lst2' /\ is_less_than' b y = true).
    { apply H2; auto. }
    desf.
    assert (L: quad_correct a x b y).
    { unfold quad_correct.
      unfold base_assumption in *.
      unfold list_correct in *.
      desf.
      split.
      { apply H1; auto. }
      split.
      { apply H7; auto. }
      split.
      { apply H2; auto. }
      apply H5; auto. }      
    clear H1.
    clear H2.
    clear H0.
    clear H3.
    assert (C: format_correct (f a b)).
    { unfold fun_correct in F.
      desf.
      apply F.
      unfold quad_correct in L.
      desf. }
    exists (f a b).
    split. 
    { assert (H: total_width (f a b) <=? w = true).
      { assert (R: is_less_than' (f a b) (f x y) = true).
        { apply F; auto. }
        unfold is_less_than' in R.      
        unfold is_less_than in R.
        unfold less_components in R.
        unfold format_correct in C.
        unfold format_correct1 in C.
        unfold format_correct2 in C.
        unfold format_correct3 in C.
        desf.
        all: andb_split.
        all: apply leb_complete in H0.
        all: apply leb_complete in H1.
        all: try apply leb_complete in H2.
        all: apply Nat.leb_le.
        all: unfold total_width in *.
        all: desf; simpls.
        all: desf.
        all: try lia. }
      generalize H, L1, L2.
      clear.
      ins.
      generalize dependent lst1'.
      induction lst2'.
      { done. }
      ins.
      desf.
      { clear IHlst2'.
        generalize dependent lst2'.
        unfold FormatTrivial.cross_general.
        ins.
        rewrite filter_app.
        apply in_app_l.
        induction lst1'.
        { done. }
        ins.
        desf.
        { apply in_cons.
          apply IHlst1'.
          apply L1. }
        apply IHlst1'.
        apply L1. }
      unfold FormatTrivial.cross_general in *.
      simpl.
      rewrite filter_app.
      apply in_app_r.
      apply IHlst2'; auto. }
    apply F; auto. }
  { unfold base_assumption in H1.
    desf. }
  unfold base_assumption in H2.
  desf.
Qed.
 
Lemma eval_cor w doc :
  evaluatorList w doc ⊆ evaluatorTrivial w doc.
Proof.
  induction doc.
  all: simpls.
  { rewrite <- indent_eq.
    unfold FormatTrivial.indentDoc.
    apply cross_general_cor.
    { done. }
    apply IHdoc. }
  { unfold besideDoc.
    rewrite <- cross_general_eq.
    apply (incl_tran (m := FormatTrivial.cross_general w add_beside (evaluatorList w doc1) (evaluatorList w doc2))).
    { apply pareto_incl. }
    apply cross_general_cor.
    all: done. }
  { unfold aboveDoc.
    rewrite <- cross_general_eq.
    apply (incl_tran (m := FormatTrivial.cross_general w add_above (evaluatorList w doc1) (evaluatorList w doc2))).
    { apply pareto_incl. }
    apply cross_general_cor.
    all: done. }
  { unfold choiceDoc.
    apply (incl_tran (m:= evaluatorList w doc1 ++ evaluatorList w doc2)).
    { apply pareto_incl. }
    apply incl_app.
    { apply incl_appl. 
      done. }
    apply incl_appr.
    done. }
  unfold fillDoc.
  rewrite <- cross_general_eq.
  apply (incl_tran (m := FormatTrivial.cross_general w (fun fs f : t => add_fill fs f s) 
       (evaluatorList w doc1) (evaluatorList w doc2))).
  { apply pareto_incl. }
  apply cross_general_cor; auto.
Qed.

Lemma indent_inside w a t l :
  In a (FormatTrivial.indentDoc w t l) <->
  exists b, In b l /\ a = indent' t b /\ total_width a <= w.
Proof.
  split.
  { induction l; simpls.
    unfold FormatTrivial.indentDoc in *.
    unfold FormatTrivial.cross_general in *.
    simpls. 
    desf.
    { ins.
      desf.
      { exists a0.
        apply leb_complete in Heq.
        auto. }
      assert (exists b : Format.t, In b l /\ a = indent' t b /\ total_width a <= w).
      { apply IHl; auto. }
      desf.      
      exists b; auto. }
    ins.
    assert (exists b : Format.t, In b l /\ a = indent' t b /\ total_width a <= w).
    { apply IHl; auto. }
    desf.
    exists b; auto. }
  ins.
  desf.
  induction l; simpls.
  unfold FormatTrivial.indentDoc in *.
  unfold FormatTrivial.cross_general in *.
  simpls. 
  desf.
  { apply leb_iff_conv in Heq.
    lia. }
  { apply in_cons.
    apply IHl; auto. }
  apply IHl; auto.
Qed.
  
Lemma e_trivial_correct w doc : list_correct (evaluatorTrivial w doc).
Proof.
  unfold list_correct.
  induction doc; ins.
  { desf.
    apply of_string_correct. }
  { assert (exists b, In b (evaluatorTrivial w doc) /\ a = indent' t b /\ total_width a <= w).
    { apply (indent_inside w); auto. }
    desf.
    apply IHdoc in H0.
    apply indent_format; auto. }
  all: try apply cross_general_elem in H; desf.
  { apply beside_format; auto. }
  { apply beside_correct. }
  { apply above_format; auto. }
  { apply above_correct. }
  { unfold FormatTrivial.choiceDoc in H.
    apply in_app_iff in H.
    desf.
    all: auto. }
  { apply fill_format; auto. }
  apply fill_correct.
Qed.

Lemma e_f_tr_correct w doc a : In a (evaluatorTrivial w doc) -> format_correct a.
Proof.
  ins.
  assert (list_correct (evaluatorTrivial w doc)).
  { apply e_trivial_correct. }
  apply H0; auto.
Qed.

Lemma e_list_correct w doc : list_correct (evaluatorList w doc).
Proof.
  apply (list_correct_incl _ (evaluatorTrivial w doc)).
  { apply eval_cor. }
  apply e_trivial_correct.
Qed.

Lemma e_f_lst_correct w doc a : In a (evaluatorList w doc) -> format_correct a.
Proof.
  ins.
  assert (list_correct (evaluatorList w doc)).
  { apply e_list_correct. }
  apply H0; auto.
Qed.

Lemma list_correct_linear lst lst' :
  list_correct (lst ++ lst') <-> list_correct lst /\ list_correct lst'.
Proof.
  split.
  { ins.
    unfold list_correct in *.    
    split.
    all: ins.
    all: apply H.
    { apply in_app_l; auto. }
    apply in_app_r; auto. }
  ins.
  desf.
  unfold list_correct in *.
  ins.
  apply in_app_or in H1.
  desf.
  { apply H; auto. }
  apply H0; auto.
Qed.      

Lemma indent_list w sh l
      (H: list_correct l) : list_correct (FormatTrivial.indentDoc w sh l).
Proof.
  unfold list_correct.
  ins.
  apply indent_inside in H0.
  desf.
  apply indent_format.
  apply H; auto.
Qed.  

Lemma elem_in_indent lst lst' w sh
      (H1: base_assumption lst lst') :
  is_less_exist' (FormatTrivial.indentDoc w sh lst) (FormatTrivial.indentDoc w sh lst').
Proof.
  unfold is_less_exist'.
  ins.
  unfold base_assumption in H1.
  apply indent_inside in H.
  desf.
  assert (exists c, In c lst /\ is_less_than' c b0 = true).
  { apply H4; auto. }
  desf.
  exists (indent' sh c).
  split.
  { apply indent_inside.
    exists c.
    repeat split; auto.
    apply (indent_width' b0); auto. }
  rewrite <- indent'_linear'; auto.
Qed.  

Lemma eval_in_elem w doc : is_less_exist' (evaluatorList w doc) (evaluatorTrivial w doc). 
Proof.
  unfold is_less_exist'. 
  induction doc; ins.
  { unfold is_less_than'. 
    exists b.
    destruct H as [H|H]; auto.
    rewrite is_less_than_refl.
    desf; auto.
    split; auto.
    all: repeat (apply andb_true_iff; split).
    all: apply Nat.leb_le.
    all: lia. }
  { rewrite <- indent_eq.
    apply indent_inside in H.
    desf.
    assert (format_correct b0).
    { apply (e_f_tr_correct w doc); auto. }
    apply IHdoc in H.
    desf.
    exists (indent' t a).
    split.
    { apply indent_inside.
      exists a.
      repeat split; auto.
      apply (indent_width' b0); auto.
      apply (e_f_lst_correct w doc); auto. }
    rewrite <- indent'_linear'; auto.
    apply (e_f_lst_correct w doc); auto. }
  { unfold besideDoc.
    rewrite <- cross_general_eq.
    apply pareto_inside'.
    { apply cross_correct.
      { apply beside_correct. }
      all: apply e_list_correct. }
    apply (elem_in (evaluatorTrivial w doc1) (evaluatorTrivial w doc2)); auto.
    { apply beside_correct. }
    { split.
      { apply e_list_correct. }
      split.
      { apply e_trivial_correct. }
      unfold is_less_exist'.
      apply IHdoc1. }
    split.
    { apply e_list_correct. }
    split.
    { apply e_trivial_correct. }
    unfold is_less_exist'.
    apply IHdoc2. }
  { unfold aboveDoc.
    rewrite <- cross_general_eq.
    apply pareto_inside'.
    { apply cross_correct.
      { apply above_correct. }
      all: apply e_list_correct. }
    apply (elem_in (evaluatorTrivial w doc1) (evaluatorTrivial w doc2)); auto.
    { apply above_correct. }
    { split.
      { apply e_list_correct. }
      split.
      { apply e_trivial_correct. }
      unfold is_less_exist'.
      apply IHdoc1. }
    split.
    { apply e_list_correct. } 
    split.
    { apply e_trivial_correct. }
    unfold is_less_exist'.
    apply IHdoc2. }
  { unfold choiceDoc.
    apply pareto_inside'.
    { apply list_correct_linear.
      split.
      all: apply e_list_correct. }
    unfold FormatTrivial.choiceDoc in H.
    apply in_app_or in H.
    desf.
    { assert (exists a : t, In a (evaluatorList w doc1) /\ is_less_than' a b = true).
      { apply IHdoc1; auto. }
      desf.
      exists a.
      split; auto.
      apply in_app_l; auto. }
    assert (exists a : t, In a (evaluatorList w doc2) /\ is_less_than' a b = true).
    { apply IHdoc2; auto. }
    desf.
    exists a.
    split; auto.
    apply in_app_r; auto. }
  unfold fillDoc.
  rewrite <- cross_general_eq.
  apply pareto_inside'.
  { apply cross_correct.
    { apply fill_correct. }
    all: apply e_list_correct. }
  apply (elem_in (evaluatorTrivial w doc1) (evaluatorTrivial w doc2)); auto.
  { apply fill_correct. }
  { split.
    { apply e_list_correct. }
    split.
    { apply e_trivial_correct. }
    unfold is_less_exist'.
    apply IHdoc1. }
  split.
  { apply e_list_correct. }
  split.
  { apply e_trivial_correct. }
  unfold is_less_exist'.
  apply IHdoc2.
Qed.

Lemma assumption_evals w a : base_assumption (evaluatorList w a) (evaluatorTrivial w a).
Proof.
  unfold base_assumption.
  split.
  { apply e_list_correct. }
  split.
  { apply e_trivial_correct. }
  apply eval_in_elem.
Qed.

Lemma pareto_beside a b w :
    pick_best_list (FormatList.besideDoc w (evaluatorList w a) (evaluatorList w b)) w ⊆
    pick_best_list (FormatTrivial.besideDoc w (evaluatorTrivial w a) (evaluatorTrivial w b)) w.
Proof.
  unfold besideDoc.
  rewrite <- cross_general_eq.
  apply (incl_tran (m := pick_best_list (FormatTrivial.cross_general w add_beside (evaluatorList w a) (evaluatorList w b)) w)).
  { apply pick_pareto_incl.
    apply cross_correct.
    { apply beside_correct. }
    all: apply e_list_correct. }
  apply best_remove.
  { apply height_less.
    { apply cross_correct.
      { apply beside_correct. }
      all: apply e_trivial_correct. }
    { apply cross_general_cor.
      all: apply eval_cor. }
    apply elem_in.
    { apply beside_correct. }
    all: apply assumption_evals. }
  apply cross_general_cor.
  all: apply eval_cor.
Qed.

Lemma pareto_above a b w :
    pick_best_list (FormatList.aboveDoc w (evaluatorList w a) (evaluatorList w b)) w ⊆
    pick_best_list (FormatTrivial.aboveDoc w (evaluatorTrivial w a) (evaluatorTrivial w b)) w.
Proof.
  unfold aboveDoc.
  rewrite <- cross_general_eq.
  apply (incl_tran (m := pick_best_list (FormatTrivial.cross_general w add_above (evaluatorList w a) (evaluatorList w b)) w)).
  { apply pick_pareto_incl.
    apply cross_correct.
    { apply above_correct. }
    all: apply e_list_correct. }
  apply best_remove.
  { apply height_less.
    { apply cross_correct.
      { apply above_correct. }
      all: apply e_trivial_correct. }
    { apply cross_general_cor.
      all: apply eval_cor. }
    apply elem_in.
    { apply above_correct. }
    all: apply assumption_evals. }  
  apply cross_general_cor.
  all: apply eval_cor.
Qed.  

Definition induction_cond (a: Doc) (b: Doc) (w: nat):=
  << A: pick_best_list (evaluatorList w a) w ⊆ pick_best_list (evaluatorTrivial w a) w >> /\
  << B: pick_best_list (evaluatorList w b) w ⊆ pick_best_list (evaluatorTrivial w b) w >>.

Lemma pareto_fill a b w n
       (H: induction_cond a b w) :
    pick_best_list (FormatList.fillDoc w (evaluatorList w a) (evaluatorList w b) n) w ⊆
    pick_best_list (FormatTrivial.fillDoc w (evaluatorTrivial w a) (evaluatorTrivial w b) n) w.
Proof.
  unfold fillDoc.
  rewrite <- cross_general_eq.
  apply (incl_tran (m := pick_best_list (FormatTrivial.cross_general w (fun fs f : t => add_fill fs f n) (evaluatorList w a) (evaluatorList w b)) w)).
  { apply pick_pareto_incl.
    apply cross_correct.
    { apply fill_correct. }
    all: apply e_list_correct. }
  apply best_remove. 
  { apply height_less.
    { apply cross_correct.
      { apply fill_correct. }
      all: apply e_trivial_correct. }
    { apply cross_general_cor.
      all: apply eval_cor. }
    apply elem_in.
    { apply fill_correct. }
    all: apply assumption_evals. }  
  apply cross_general_cor.
  all: apply eval_cor.
Qed.

Lemma pareto_choice a b w
       (H: induction_cond a b w) :
    pick_best_list (FormatList.choiceDoc (evaluatorList w a) (evaluatorList w b)) w ⊆
    pick_best_list (FormatTrivial.choiceDoc (evaluatorTrivial w a) (evaluatorTrivial w b)) w.
Proof.
  unfold choiceDoc, cross_general.
  apply (incl_tran (m := pick_best_list (evaluatorList w a ++ evaluatorList w b) w)).
  { apply pick_pareto_incl.
    unfold list_correct.
    ins.
    apply in_app_or in H0.
    desf.
    { assert (list_correct (evaluatorList w a)).
      { apply e_list_correct. }
      apply H1; auto. }
    assert (list_correct (evaluatorList w b)).
    { apply e_list_correct. }
    apply H1; auto. }
  unfold FormatTrivial.choiceDoc.
  apply best_remove. 
  { unfold induction_cond in H.
    desf.
    assert (A': get_min_height (evaluatorList w a) w None = get_min_height (evaluatorTrivial w a) w None).
    { apply height_remove; auto.
      apply assumption_evals. }
    clear A.
    assert (B': get_min_height (evaluatorList w b) w None = get_min_height (evaluatorTrivial w b) w None).
    { apply height_remove; auto.
      apply assumption_evals. }
    clear B.
    apply height_less.
    { apply list_correct_linear.
      split.
      all: apply e_trivial_correct. }
    { apply incl_app.
      { apply incl_appl.
        apply eval_cor. }
      apply incl_appr.
      apply eval_cor. }
    unfold is_less_exist'.
    ins.
    apply in_app_or in H.
    desf.
    { assert (exists a0 : t, In a0 (evaluatorList w a) /\ is_less_than' a0 b0 = true).
      { apply eval_in_elem; auto. }
      desf.
      exists a0.
      split; auto.
      apply in_or_app; auto. }
    assert (exists a0 : t, In a0 (evaluatorList w b) /\ is_less_than' a0 b0 = true).
    { apply eval_in_elem; auto. }
    desf.
    exists a0.
    split; auto.
    apply in_or_app; auto. }
  apply incl_app.
  { apply incl_appl. 
    apply eval_cor. }
  apply incl_appr.
  apply eval_cor.
Qed.

Lemma pareto_indent a w sh :
    pick_best_list (indentDoc w sh (evaluatorList w a)) w ⊆
    pick_best_list (FormatTrivial.indentDoc w sh (evaluatorTrivial w a)) w.
Proof.
  rewrite <- indent_eq.
  apply best_remove.
  { apply height_less.
    { apply indent_list.
      apply e_trivial_correct. }
    { unfold FormatTrivial.indentDoc.
      apply cross_general_cor.
      { done. }
      apply eval_cor. }
    apply elem_in_indent.
    apply assumption_evals. }
  unfold FormatTrivial.indentDoc.
  apply cross_general_cor.
  { done. }
  apply eval_cor.
Qed.
              
(*---------MAIN Theorem-----------*)
Theorem listEqTrivialProof :
  forall doc width,
    pretty_list evaluatorList width doc ⊆ pretty_list evaluatorTrivial width doc.
Proof.
  ins.
  unfold pretty_list.
  induction doc.
  all: simpls.
  { apply pareto_indent. }
  { by apply pareto_beside. }
  { by apply pareto_above. }
  { by apply pareto_choice. }
  by apply pareto_fill.
Qed.
