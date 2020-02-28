From hahn Require Import Hahn.
Require Import Format.
Require Import Doc.
Require Import PrettyPrinter.
Require Import FormatTrivial.
Require Import FormatList.
Require Import IsLess.
Require Import FuncCorrect.

Require Import String.
Require Import ZArith Int.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.Bool.Bool.
Require Import Coq.ssr.ssrbool.


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
    { apply (is_less_than_transitivity _ b); auto. }
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
    rewrite (is_less_than_transitivity b a0 a); auto. }
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
    { rewrite (is_less_than_transitivity a a0 b) in A; auto. }
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
      rewrite is_exist_cons_alt, is_less_than_reflexivity.
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
    rewrite is_less_than_reflexivity. auto. }
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
    rewrite is_less_than_reflexivity; auto.
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
          apply (is_less_than_transitivity y x x0); auto. }
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
          apply (is_less_than_transitivity x0 y x); auto. }
        apply is_exist_not_cons_alt.
        destruct (is_less_than x x0) eqn:E4; auto.
        rewrite (is_less_than_transitivity x x0 y) in H1; auto. }
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
    rewrite (is_less_than_transitivity y x x0) in E0; auto. }
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
      apply is_less_than_reflexivity. }
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
    apply is_less_than_reflexivity. }
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
  rewrite is_less_than_reflexivity.
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
      
Lemma min_leb a b
      (H: a < b) : min b a = a.
Proof.
  destruct a.
  { apply Nat.min_0_r. }
  apply NPeano.Nat.min_r_iff.
  apply Nat.lt_le_incl.
  apply H.
Qed.

Lemma get_height_less a x lst w
      (P: height a <= height x) :
  get_min_height (lst ++ [x]) w (Some (height a)) = get_min_height lst w (Some (height a)).
Proof.
  generalize dependent a.
  induction lst. 
  { ins.
    destruct (total_width x <=? w) eqn: E1.
    { rewrite NPeano.Nat.min_l; auto. }
    reflexivity. }
  ins.
  destruct (total_width a <=? w) eqn:E1.
  { destruct (height a0 <=? height a) eqn:E2.
    { apply leb_complete in E2.
      rewrite Nat.min_l; auto. }
    apply leb_iff_conv in E2.
    rewrite min_leb; auto.
    apply IHlst.
    apply Nat.lt_le_incl.
    apply (Nat.lt_le_trans _ (height a0)); auto. }
  apply IHlst; auto.
Qed.    

Require Import Lia.

Lemma get_height_to_none a b lst w
      (H: total_width a <= w)
      (P: height a <= height b) :
  get_min_height (lst ++ [a]) w (Some (height b)) = get_min_height (lst ++ [a]) w None.
Proof.
  generalize dependent b.
  generalize dependent a.
  induction lst.
  { ins.
    desf.
    { rewrite NPeano.Nat.min_r; auto. }
    apply Nat.leb_gt in Heq.
    lia. }
  ins.
  desf.
  { destruct (height b <=? height a) eqn:E1.
    { apply leb_complete in E1.
      rewrite NPeano.Nat.min_l; auto.
      repeat rewrite IHlst; auto.
      apply (NPeano.Nat.le_trans _ (height b)); auto. }
    apply leb_iff_conv in E1.
    rewrite min_leb; auto. }
  apply IHlst; auto.
Qed.      

Lemma get_height_none a lst w
      (H: (total_width a <=? w) = false) :
  forall (o: option nat),
  get_min_height (lst ++ [a]) w o = get_min_height lst w o.
Proof.
  induction lst.
  { simpls.
    desf. }
  ins.
  desf.
Qed.

Lemma get_height_exist a x w lst
      (H: is_less_exist x lst = true) :
  get_min_height lst w (Some (height a)) =
  get_min_height (lst ++ [x]) w (Some (height a)).
Proof.
  apply is_exist_eq in H.
  desf.
  generalize dependent b.
  generalize dependent a.
  induction lst.
  { done. }
  ins.
  unfold is_less_than in H0.
  andb_split.
  apply leb_complete in H0.
  apply leb_complete in H1.
  apply leb_complete in H2.
  apply leb_complete in H3.
  desf.
  { destruct (height a0 <=? height b) eqn:E1.
    { apply leb_complete in E1.
      rewrite Min.min_l; auto.
      rewrite get_height_less.
      { reflexivity. }
      lia. }
    apply Nat.leb_gt in E1.
    rewrite min_leb; auto.
    rewrite get_height_less; auto. }
  { rewrite get_height_none; auto.
    apply Nat.leb_gt.
    apply Nat.leb_gt in Heq.
    unfold total_width in *.
    desf.
    simpls.
    lia. }
  { destruct (height a0 <=? height a) eqn:E1.
    { apply leb_complete in E1.
      rewrite Min.min_l; auto.
      apply (IHlst _ b); auto.
      unfold is_less_than.
      apply andb_true_iff; split.
      apply andb_true_iff; split.
      apply andb_true_iff; split.
      all: apply NPeano.Nat.leb_le; auto. }
    apply Nat.leb_gt in E1.
    rewrite min_leb; auto.
    apply (IHlst _ b); auto.
    unfold is_less_than.
    apply andb_true_iff; split.
    apply andb_true_iff; split.
    apply andb_true_iff; split.
    all: apply NPeano.Nat.leb_le; auto. }
  apply (IHlst _ b); auto.
  unfold is_less_than.
  apply andb_true_iff; split.
  apply andb_true_iff; split.
  apply andb_true_iff; split.
  all: apply NPeano.Nat.leb_le; auto.
Qed.    

Lemma height_some_none a b lst w
      (H: total_width b <= w)
      (K: height b <= height a)
      (P: total_width a <= w) :
  get_min_height (lst ++ [b]) w (Some (height a)) =
  get_min_height (lst ++ [b]) w None.
Proof.
  induction lst.
  { simpl.    
    desf.
    { rewrite NPeano.Nat.min_r; auto. }
    apply Nat.leb_gt in Heq.
    unfold total_width in *.
    desf.
    simpls.
    lia. }
  simpl.
  desf.
  apply leb_complete in Heq.
  destruct (height a <=? height a0) eqn:E2.
  { apply leb_complete in E2.
    rewrite NPeano.Nat.min_l; auto.
    repeat rewrite get_height_to_none; auto.
    lia. }
  apply Nat.leb_gt in E2.
  rewrite min_leb; auto.
Qed. 

Lemma pick_is_less' a b lst w
      (H: is_less_than a b = true) :
  pick_best_list (a :: lst) w ⊆ pick_best_list ((a :: lst) ++ [b]) w.
Proof.
  simpls.
  destruct (total_width a <=? w) eqn:E2.
  { simpl.
    rewrite get_height_less.
    { desf.
      { apply incl_cons.
        { done. }
        apply incl_tl.
        rewrite filter_app.
        apply incl_appl.
        done. }
      rewrite filter_app.
      by apply incl_appl. }
    unfold is_less_than in H.
    andb_split.
    apply leb_complete in H.
    apply H. }
  rewrite get_height_none.
  { desf.
    rewrite filter_app.
    apply incl_appl.
    done. }
  unfold is_less_than in H.
  andb_split.
  apply leb_complete in H0.
  apply leb_complete in H1.
  apply leb_complete in H2.
  apply leb_complete in H.
  apply Nat.leb_gt.
  apply Nat.leb_gt in E2.
  unfold total_width in *.
  desf.
  simpls.
  lia.
Qed.

Lemma pick_is_less'' a b lst w
      (H: is_less_than b a = true) :
  pick_best_list (lst ++ [b]) w ⊆ pick_best_list ((a :: lst) ++ [b]) w.
Proof.
  unfold pick_best_list.
  simpls.
  destruct (total_width a <=? w) eqn:E1.
  { simpl.
    unfold is_less_than in H.
    andb_split.
    apply leb_complete in H0.
    apply leb_complete in H1.
    apply leb_complete in H2.
    apply leb_complete in H.
    apply leb_complete in E1.
    rewrite get_height_to_none; auto.
    { desf.
      apply incl_tl.
      done. }
    unfold total_width in *.
    desf.
    simpls.
    lia. }
  desf.
Qed.

Lemma pareto_elem_height a lst w :
      forall b, total_width b <= w ->
  get_min_height (lst ++ [a]) w (Some (height b)) =
  get_min_height (pareto_by_elem a lst ++ [a]) w (Some (height b)).
Proof.
  induction lst; auto.
  destruct (is_less_than a a0) eqn:E1.
  { intros.
    rewrite par_elem2_less; auto.
    unfold is_less_than in E1.
    andb_split.
    apply leb_complete in H0.
    apply leb_complete in H1.
    apply leb_complete in H2.
    apply leb_complete in H3.
    simpls.
    desf.
    destruct (height a0 <=? height b) eqn:E2.
    { apply leb_complete in E2.
      rewrite NPeano.Nat.min_r; auto.
      rewrite <- IHlst; auto.
      clear IHlst.
      apply leb_complete in Heq.
      repeat rewrite get_height_to_none; auto.
      { unfold total_width in *.
        desf.
        simpls.
        lia. }
      { lia. }
      unfold total_width in *.
      desf.
      simpls.
      lia. }
    apply Nat.leb_gt in E2.
    rewrite min_l.
    { apply IHlst; auto. }
    lia.
    apply IHlst; auto. }
  intros.
  rewrite par_elem2_not_less; auto.
  simpls.
  desf.
  { apply leb_complete in Heq.
    destruct (height b <=? height a0) eqn:E2.
    { apply leb_complete in E2.
      rewrite NPeano.Nat.min_l; auto. }
    apply Nat.leb_gt in E2.
    rewrite min_leb; auto. }
  apply IHlst; auto.
Qed.  

Lemma pick_height_none lst a w :
  get_min_height (pareto_by_elem a lst ++ [a]) w None =
  get_min_height (lst ++ [a]) w None.
Proof.
  induction lst; auto.
  destruct (is_less_than a a0) eqn:E1.
  { rewrite par_elem2_less; auto.
    simpls.
    desf.
    unfold is_less_than in E1.
    andb_split.
    apply leb_complete in H0.
    apply leb_complete in H1.
    apply leb_complete in H2.
    apply leb_complete in H.
    apply leb_complete in Heq.
    rewrite get_height_to_none.
    { apply IHlst. }
    { unfold total_width in *.
      desf.
      simpls.
      lia. }
    lia. }
  rewrite par_elem2_not_less; auto.
  simpls.
  desf.
  apply leb_complete in Heq.
  rewrite <- pareto_elem_height; auto.
Qed.    

Lemma elem_in_pick n a lst w
      (H: total_width a <= w)
      (H1: get_min_height lst w None = Some n)
      (H2: In a lst)
      (H3: height a = n) : In a (pick_best_list lst w).
Proof.
  unfold pick_best_list.
  rewrite H1.
  clear H1.
  induction lst; simpls.
  desf.
  { apply andb_false_iff in Heq.
    desf.
    { apply leb_complete_conv in Heq.
      lia. }
    apply Nat.eqb_neq in Heq.
    lia. }
    { apply andb_false_iff in Heq.
      desf.
    { apply leb_complete_conv in Heq.
      lia. }
    apply Nat.eqb_neq in Heq.
    lia. }
  { apply andb_prop in Heq.
    desf.
    apply leb_complete in Heq.
    apply Nat.eqb_eq in Heq0.
    apply in_cons.
    apply IHlst; auto. }
  apply IHlst; auto.
Qed.  

Lemma height_discr t l w
      (H: get_min_height l w (Some (height t)) = None) : False.
Proof.
  generalize dependent (height t).
  induction l; simpls.
  ins.
  desf.
  { apply (IHl (Init.Nat.min n (height a))).
    apply H. }
  apply (IHl n).
  apply H.
Qed.  

Lemma height_discr' t l w
      (P: In t l)
      (H: total_width t <= w)
      (D: get_min_height l w None = None) : False.
Proof.
  induction l.
  { done. }
  simpls.
  desf.
  { apply (height_discr t l w); auto. }
  { apply leb_complete_conv in Heq.
    lia. }
  { apply (height_discr a l w); auto. }
  apply IHl; auto.
Qed.    

Lemma best_remove_helper lst lst' w n
      (H: Some n = get_min_height lst' w None)
      (P: lst ⊆ lst') :
  filter (fun f : Format.t => (total_width f <=? w) && (height f =? n)) lst
         ⊆ pick_best_list lst' w.
Proof.
  generalize dependent n.
  induction lst.
  { ins.
    done. }
  ins.
  unfold incl in P.
  simpl in P.
  desf.
  { apply andb_prop in Heq.
    desf.
    apply beq_nat_true in Heq0.
    apply Nat.leb_le in Heq.
    apply incl_cons.
    { clear IHlst.
      apply (elem_in_pick n); auto. }
    apply IHlst; auto.
    generalize P.
    clear.
    ins.
    destruct lst.
    { done. }
    unfold incl.
    ins.
    apply P.
    auto. }
  apply IHlst; auto.
  generalize P.
  clear.
  ins.
  destruct lst.
  { done. }
  unfold incl.
  ins.
  apply P.
  auto.
Qed.
  
Lemma best_remove lst lst' w
      (H: get_min_height lst w None = get_min_height lst' w None) :
   lst ⊆ lst' -> pick_best_list lst w ⊆ pick_best_list lst' w.
Proof.
  ins.
  unfold pick_best_list at 1. 
  induction lst; simpls.
  desf.
  { apply incl_cons.
    {  unfold incl in H0.
      simpls.
      apply beq_nat_true in Heq0.
      apply leb_complete in Heq1.
      apply (elem_in_pick n); auto. }
    done. }
  { apply incl_cons.
    { apply leb_complete in Heq2.
      apply Nat.eqb_eq in Heq0.
      unfold incl in H0.
      simpl in H0.
      apply (elem_in_pick n); auto. }
    apply best_remove_helper; auto.
    unfold incl in H0.
    simpl in H0.
    generalize H0.
    clear.
    ins.
    unfold incl.
    simpl.
    ins.
    apply H0.
    auto. }
  { apply incl_cons. 
    { apply beq_nat_true in Heq0.
      apply leb_complete in Heq2.
      unfold incl in H0.
      simpl in H0.
      apply (elem_in_pick n); auto. }
    simpls.
    desf.
    { apply (height_discr t) in Heq1.
      done. }
    { apply (height_discr t) in Heq1.
      done. }
    generalize Heq1.
    clear.
    ins.
    induction l; simpls.
    desf.
    { apply (height_discr a) in Heq1.
      done. }
    { apply (height_discr a) in Heq1.
      done. }
    apply IHl; auto. }
  { apply best_remove_helper; auto.
    unfold incl in H0.
    simpl in H0.
    generalize H0.
    clear.
    ins.
    unfold incl.
    ins.
    apply H0.
    auto. }    
  { unfold incl in H0.
    simpl in H0.
    apply IHlst; auto.
    unfold incl.
    simpl.
    ins.
    apply H0; auto. }
  apply Nat.eqb_neq in Heq0.
  assert (height a = n).
  { generalize Heq1, Heq.
    clear.
    generalize dependent (t::l).
    ins.
    induction l0.
    { simpls.
      inversion Heq.
      auto. }
    simpls.
    desf.
    { apply (height_discr a0) in Heq1.
      done. }
    apply IHl0; auto. }
  lia.
Qed.

Lemma pick_height_link lst x w
      (N: is_less_exist x lst = true) :
  get_min_height (lst ++ [x]) w None = get_min_height lst w None.
Proof.
  induction lst.
  { simpls. }
  apply is_exist_cons_alt in N.
  desf.
  { clear IHlst.
    simpls.
    unfold is_less_than in N.
    andb_split.
    apply leb_complete in H0.
    apply leb_complete in H1.
    apply leb_complete in H2.
    apply leb_complete in H.
    desf.
    { rewrite get_height_less.
      { reflexivity. }
      apply H. }
    rewrite get_height_none.
    { reflexivity. }
    apply Nat.leb_gt in Heq.
    apply Nat.leb_gt.
    unfold total_width in *.
    desf.
    simpls.
    lia. }
  simpls.
  desf.
  { symmetry.
    apply get_height_exist; auto. }
  apply IHlst; auto.    
Qed.


Lemma cross_general_nil f w lst :
  FormatTrivial.cross_general w f nil lst = nil.
Proof.
  induction lst; auto.
Qed. 

Lemma height_values lst w :
  get_min_height lst w None = None \/
  exists a, In a lst /\ total_width a <=? w = true /\ get_min_height lst w None = Some (height a).
Proof.
  induction lst.
  { simpls.
    auto. }
  simpls.
  desf. 
  { assert (L: exists a0 : t,
     (a = a0 \/ In a0 lst) /\
     (total_width a0 <=? w) = true /\ get_min_height lst w (Some (height a)) = Some (height a0)).
    { exists a.
      repeat split; auto.
      generalize a.
      induction lst; auto.
      ins.
      desf.
      { apply height_discr in IHlst.
        done. }
      apply IHlst0; auto. }  
    auto. }
  { auto. }
  { clear IHlst.
    clear IHlst1.
    assert (L: exists a1 : t,
     (a = a1 \/ In a1 lst) /\
     (total_width a1 <=? w) = true /\ get_min_height lst w (Some (height a)) = Some (height a1)).
    { generalize dependent a.
      induction lst.
      { ins.
        exists a; auto. }
      ins.
      desf.
      { destruct ((height a1) <=? (height a)) eqn:E1.
        { apply leb_complete in E1.
          rewrite Min.min_l; auto.
          assert (L: exists a2 : t,
    (a1 = a2 \/ In a2 lst) /\
    (total_width a2 <=? w) = true /\ get_min_height lst w (Some (height a1)) = Some (height a2)).
          { apply IHlst; auto. }
          desf.
          all: exists a2; auto. }
        apply leb_iff_conv in E1.
        rewrite min_leb; auto.
        assert (L: exists a1 : t,
                   (a = a1 \/ In a1 lst) /\ (total_width a1 <=? w) = true /\ get_min_height lst w (Some (height a)) = Some (height a1)).
        { apply IHlst; auto. }
        desf.
        all: exists a2; auto. }
      assert (L: exists a2 : t,
                 (a1 = a2 \/ In a2 lst) /\ (total_width a2 <=? w) = true /\ get_min_height lst w (Some (height a1)) = Some (height a2)).
      { apply IHlst; auto. }
      desf.
      all: exists a2; auto. }
    auto. }
  assert (L: exists a1 : t, (a = a1 \/ In a1 lst) /\ (total_width a1 <=? w) = true /\ get_min_height lst w None = Some (height a1)).
  { exists a0.
    auto. }
  auto.
Qed.

Lemma height_eq lst w : get_min_height lst w None = None <->
                        forallb (fun f => negb (total_width f <=? w)) lst = true.
Proof.
  split.
  { ins.
    induction lst; auto.
    simpls.
    desf.
    { apply height_discr in H.
      done. }
    simpl.
    apply IHlst; auto. }
  ins.
  induction lst; auto.
  simpls.
  desf.
  simpl in H.
  apply IHlst; auto.
Qed.      

Lemma height_remove_val n m lst w
      (I: m < n) : get_min_height lst w (Some n) = Some m <-> get_min_height lst w None = Some m.
Proof.
  assert (L: forall n m lst w, m < n /\ get_min_height lst w (Some n) = Some m -> get_min_height lst w None = Some m).
  { clear.
    ins.
    destruct H as [H0 H].
    generalize dependent n.
    induction lst.
    { ins.
      inversion H.
      lia. }
    ins.
    desf.
    { destruct (n <=? height a) eqn:E1.
      { apply leb_complete in E1.
        rewrite Min.min_l in H; auto.
        clear IHlst.
        clear Heq.
        generalize dependent n.
        generalize dependent (height a).
        induction lst.
        { ins.
          inversion H.
          lia. }
        ins.
        desf.
        { destruct (n <=? height a0) eqn:E2.
          { apply leb_complete in E2.
            rewrite Min.min_l; auto.
            rewrite Min.min_l in H; auto.
            { apply (IHlst _ n0); auto. }
            lia. }
          apply Nat.leb_gt in E2.
          rewrite min_leb; auto.
          destruct (n0 <=? height a0) eqn:E3.
          { apply leb_complete in E3.
            rewrite Min.min_l in H; auto.
            apply (IHlst _ n0); auto. }
          apply Nat.leb_gt in E3.
          rewrite min_leb in H; auto. }
        apply (IHlst _ n0); auto. }
      apply Nat.leb_gt in E1.
      rewrite min_leb in H; auto. }
    apply (IHlst n); auto. }
  split.
  { ins.
    apply (L n); auto. }
  ins.
  generalize dependent n.
  induction lst; simpls.
  desf.
  { ins.
    destruct (n <=? height a) eqn:E1.
    { apply leb_complete in E1.
      rewrite Min.min_l; auto.
      apply IHlst; auto.
      apply (L (height a)).
      split; auto.
      lia. }
    apply leb_iff_conv in E1.
    rewrite min_leb; auto. }
  ins.
  apply IHlst; auto.
Qed.

Lemma height_discr5 lst w n m
      (P: m < n)
      (T: get_min_height lst w (Some m) = Some n) : False.
Proof.
  generalize dependent m.
  induction lst.
  { ins.
    inversion T.
    lia. }
  ins.
  desf.
  { destruct (m <=? height a) eqn:E2.
    { apply leb_complete in E2.
      rewrite Min.min_l in T; auto.
      apply (IHlst m); auto. }
    apply Nat.leb_gt in E2.
    rewrite min_leb in T; auto.
    apply (IHlst (height a)); auto.
    lia. }
  apply (IHlst m); auto.
Qed.

Lemma height_discr4 lst w a n
      (I: In a lst)
      (P: (total_width a <=? w) = true)
      (T: get_min_height lst w None = Some n)
      (H: height a < n) : False.
Proof.
  induction lst.
  { done. }
  simpls.
  desf.
  { clear IHlst.
    generalize dependent a.
    induction lst.
    { ins.
      inversion T.
      lia. }
    ins.
    desf.
    { destruct (height a0 <=? height a) eqn:E1.
      { apply leb_complete in E1.
        rewrite Min.min_l in T; auto.
        apply (IHlst a0); auto. }
      apply Nat.leb_gt in E1.
      rewrite min_leb in T; auto.
      apply (IHlst a); auto.
      lia. }
    apply (IHlst a0); auto. }
  { destruct (height a0 <=? n) eqn:E1.
    { apply leb_complete in E1.
      clear IHlst.
      apply le_lt_or_eq in E1.
      desf.
      { assert (D: False).
        { apply (height_discr5 lst w n (height a0)); auto. }
        done. }
      generalize T, H, I, P.
      generalize (height a0).
      clear.
      ins.
      generalize dependent I.
      generalize dependent n.
      induction lst; simpls.
      ins.
      desf.
      { rewrite min_leb in T; auto.
        apply (height_discr5 lst w n (height a)); auto. }
      { destruct (n <=? height a0) eqn:E1.
        { apply leb_complete in E1.
          rewrite Min.min_l in T; auto.
          apply (IHlst n); auto. }
        apply Nat.leb_gt in E1.
        rewrite min_leb in T; auto.
        apply (height_discr5 lst w n (height a0)); auto. }
      apply (IHlst n); auto. }
    apply Nat.leb_gt in E1.
    apply IHlst; auto.
    apply (height_remove_val (height a0)); auto. }
  apply IHlst; auto.
Qed.

Lemma height_eq1 lst lst' w a
      (I: lst ⊆ lst')
      (T: get_min_height lst' w None = Some (height a)) :
  get_min_height lst w (Some (height a)) = Some (height a).
Proof.
  induction lst; auto.
  simpls.
  desf.
  { destruct (height a <=? height a0) eqn:E1.
    { apply leb_complete in E1.
      rewrite Min.min_l; auto.
      apply IHlst.
      unfold incl in *.
      ins.
      apply (I a1); auto. }
    apply Nat.leb_gt in E1.
    assert (D: False).
    { unfold incl in I.
      simpls.
      apply (height_discr4 lst' w a0 (height a)); auto. }
    done. }
  apply IHlst.
  unfold incl in *.
  ins.
  apply (I a1); auto.
Qed.     

Lemma height_discr'' lst w a b
      (W: total_width a <=? w = true)
      (I: In a lst)
      (T: get_min_height lst w None = Some (height b))
      (E: height a <> height b)
      (H: is_less_than a b = true) : False.
Proof.
  unfold is_less_than in H.
  andb_split.
  apply leb_complete in H0.
  apply leb_complete in H1.
  apply leb_complete in H2.
  apply leb_complete in H.
  induction lst; simpls.
  desf.
  { apply (height_discr5 lst w (height b) (height a)); auto.
    lia. }
  { destruct (height a0 <? height b) eqn:E1.
    { apply Nat.ltb_lt in E1.
      apply (height_discr5 lst w (height b) (height a0)); auto. }
    apply Nat.ltb_ge in E1.
    clear IHlst.
    clear E1.
    generalize dependent a0.
    induction lst; simpls.
    ins.
    desf.
    { destruct (height a <=? height a1) eqn:E2.
      { apply leb_complete in E2.
        rewrite Min.min_r in T; auto.
        apply (height_discr5 lst w (height b) (height a)); auto.
        lia. }
      apply leb_iff_conv in E2.
      rewrite min_l in T.
      { apply (height_discr5 lst w (height b) (height a1)); auto.
        lia. }
      lia. }
    { destruct (height a1 <=? height a0) eqn:E2.
      { apply leb_complete in E2.
        rewrite Min.min_l in T; auto.
        apply (IHlst I a1); auto. }
      apply leb_iff_conv in E2.
      rewrite min_r in T.
      { apply (IHlst I a0); auto. }
      lia. }
    apply (IHlst I a1); auto. }
  apply IHlst; auto.
Qed.
    
Lemma height_incl_elem a lst lst' w
      (I: (a :: lst) ⊆ lst')
      (E: total_width a <=? w = true)
      (H: get_min_height lst w None = get_min_height lst' w None) :
  get_min_height lst w (Some (height a)) = get_min_height lst' w None.
Proof.
  generalize dependent a. 
  induction lst.
  { ins.
    assert (D: False).
    { apply leb_complete in E.
      unfold incl in I.
      simpls.
      apply (height_discr' a lst' w); auto. }
    done. }
  ins.
  desf.
  { destruct (height a0 <=? height a) eqn:E1.
    { apply leb_complete in E1.
      rewrite Min.min_l; auto.
      clear IHlst.
      generalize dependent a.
      generalize dependent a0.
      induction lst.  
      { ins.
        destruct (height a0 <? height a) eqn:E2.
        { apply Nat.ltb_lt in E2.
          assert (False).
          { apply (height_discr4 lst' w a0 (height a)); auto.
            unfold incl in I.
            simpls.
            apply (I a0); auto. }
          done. }
        apply Nat.ltb_ge in E2.
        assert (R: height a = height a0).
        { lia. }
        rewrite <- R.
        apply H. }
      ins.
      desf.
      { destruct (height a0 <=? height a) eqn:E2.
        { apply leb_complete in E2.
          rewrite Min.min_l; auto.
          destruct (height a1 <=? height a) eqn:E3.
          { apply leb_complete in E3.
            rewrite Min.min_l in H; auto.
            apply (IHlst a0 E a1); auto.
            unfold incl in *.
            ins.
            apply (I a2).
            desf; auto. }
          apply leb_iff_conv in E3.
          rewrite min_r in H.
          { apply (IHlst a0 E a); auto.
            unfold incl in *.
            ins.
            apply (I a2); auto.
            desf; auto. }
          lia. }
        apply Nat.leb_gt in E2.
        rewrite min_r.
        { destruct (height a1 <=? height a) eqn:E3.
          { apply leb_complete in E3.
            rewrite Min.min_l in H; auto.
            apply (IHlst a Heq0 a1); auto.
            { unfold incl in *.
              ins.
              apply (I a2).
              desf; auto. }
            lia. }
          apply leb_iff_conv in E3.
          rewrite min_r in H.
          { apply H. }
          lia. }
        lia. }
      apply (IHlst a0 E a1); auto.
      unfold incl in *.
      ins.
      apply (I a2).
      desf; auto. }
    apply leb_iff_conv in E1.
    rewrite Min.min_r; auto.
    lia. }
  apply IHlst; auto.
  unfold incl in *.
  ins.
  apply (I a1).
  desf; auto.
Qed.      

Lemma height_less lst lst' w
      (H: lst ⊆ lst') 
      (P: forall a, In a lst' -> is_less_exist a lst = true) :
            get_min_height lst w None = get_min_height lst' w None.
Proof.
  destruct (height_values lst' w) eqn:E1.
  { clear E1.
    rewrite e.
    apply height_eq.
    apply height_eq in e.
    clear P.
    induction lst; auto.
    simpl.
    apply andb_true_iff.
    split.
    { clear IHlst.
      assert (L: In a lst').
      { unfold incl in H.
        apply (H a); simpl.
        auto. }
      clear H.
      induction lst'.
      { done. }
      simpl in L.
      desf.
      { simpl in e.
        apply andb_prop in e.
        desf. }
      simpl in e.
      apply andb_prop in e.
      desf.
      apply IHlst'; auto. }
    apply IHlst.
    unfold incl in *.
    ins.
    apply (H a0); auto. }
  clear E1.
  desf.
  assert (L: is_less_exist a lst = true).
  { apply P; auto. }
  clear P.
  induction lst.
  { simpls. }
  simpl.
  apply is_exist_cons_alt in L.
  desf.
  { destruct (height a =? height a0) eqn:E1.
    { apply beq_nat_true in E1.
      rewrite <- E1.
      rewrite e1.
      apply (height_eq1 _ lst'); auto.
      unfold incl in *.
      ins.
      apply (H a1); auto. }
    apply beq_nat_false in E1.
    assert (D: False).
    { apply (height_discr'' lst' w a0 a); auto.
      unfold incl in H.
      simpls.
      apply (H a0); auto. }
    done. }
  { rewrite (is_less_width _ a) in Heq; auto.
    discriminate Heq. }
  { apply height_incl_elem; auto.
    apply IHlst; auto.
    unfold incl in *.
    ins.
    apply (H a1); auto. }
  apply IHlst; auto.
  unfold incl in *.
  simpl in H.
  ins.
  apply H; auto.
Qed.  

Lemma height_not_eq lst w n m
      (H: n <> m)
      (T: get_min_height lst w (Some m) = Some n) :
  get_min_height lst w None = Some n.
Proof.
  induction lst.
  { simpls.
    inversion T.
    lia. }
  simpls.
  desf.
  { destruct (m <=? height a) eqn:E1.
    { apply leb_complete in E1.
      rewrite Min.min_l in T; auto.
      assert (L: get_min_height lst w None = Some n).
      { apply IHlst; auto. }
      clear IHlst.
      apply height_remove_val; auto.
      assert (n < m).
      { assert (n < m <-> (m <= n -> False)).
        { clear.
          split.
          { ins.
            lia. }
          ins.
          lia. }
        apply H0.
        ins.
        apply (height_discr5 lst w n m); auto.
        lia. }
      lia. }
    apply leb_complete_conv in E1.
    rewrite min_leb in T; auto. }
  apply IHlst; auto.
Qed.  
 
Lemma height_remove lst lst' w
      (E: forall a, In a lst' -> is_less_exist a lst = true)
      (I: pick_best_list lst w ⊆ pick_best_list lst' w) :
  get_min_height lst w None = get_min_height lst' w None.
Proof.
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
  generalize E, I, H, Heq, H0.
  clear.
  generalize (t::l) as lst'.
  ins.
  destruct (height_values lst w).
  { unfold pick_best_list in I.
    desf.
    { assert (is_less_exist a nil = true).
      { apply E; auto. }
      simpls. }
    assert (is_less_exist a (t0 :: l0) = true).
    { apply E; auto. }
    apply is_exist_eq in H2.
    desf.
    assert (False).
    { apply (height_discr' b (t0::l0) w); auto.
      apply leb_complete in H0.
      unfold is_less_than in H3.
      andb_split.
      apply leb_complete in H5.
      apply leb_complete in H4.
      apply leb_complete in H3.
      unfold total_width in *.
      desf.
      simpls.
      lia. }
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
      (E: forall a, In a lst' -> is_less_exist a lst = true)
      (I: lst ⊆ lst')
      (H: pick_best_list lst w ⊆ pick_best_list lst' w) :
  pick_best_list (lst ++ [a]) w ⊆ pick_best_list (lst' ++ [a]) w.
Proof.
  unfold pick_best_list at 1.
  desf.
  apply best_remove_helper. 
  { rewrite <- Heq in Heq0.
    clear Heq.
    assert (T: get_min_height lst w None = get_min_height lst' w None).
    { apply height_remove; auto. }
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

Lemma pick_pareto_incl lst w :
  pick_best_list (pareto lst) w ⊆ pick_best_list lst w.
Proof.
  induction lst using rev_ind; simpls.
  destruct (is_less_exist x lst) eqn:E1.
  { rewrite linear_pareto_exist; auto.
    apply (incl_tran (m:= pick_best_list lst w)).
    { apply IHlst. }
    clear IHlst.
    induction lst.
    { simpl in E1.
      discriminate E1. }
    apply is_exist_cons_alt in E1.
    desf.
    { apply pick_is_less'.
      apply E1. }
    simpls.
    destruct (total_width a <=? w) eqn:E2.
    { simpl.
      rewrite (get_height_exist _ x); auto.
      desf.
      { rewrite filter_app.
        apply incl_cons.
        { done. }
        apply incl_tl.
        apply incl_appl.
        done. }
      rewrite filter_app.
      apply incl_appl.
      done. }
    rewrite pick_height_link; auto.
    desf.
    rewrite filter_app.
    apply incl_appl.
    done. }
  rewrite linear_pareto_not_exist; auto.
  apply (pick_add_elems x) in IHlst.
  { apply (incl_tran (m:= pick_best_list (pareto lst ++ [x]) w)).
    { clear. 
      generalize (pareto lst).
      ins.
      unfold pick_best_list.
      rewrite pick_height_none.
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
    apply IHlst. }
  { ins.
    apply pareto_less_elem; auto. }
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

Lemma cross_general_elem a w f lst lst' :
  In a (FormatTrivial.cross_general w f lst lst') ->
  exists x y, a = (f x y) /\ In x lst /\ In y lst' /\ total_width (f x y) <= w. 
Proof.
  ins.
  generalize dependent lst.
  induction lst'; simpls.
  ins.
  unfold FormatTrivial.cross_general in *.
  simpl in H.
  rewrite filter_app in H.
  apply in_app_or in H.
  desf.
  { clear IHlst'.
    induction lst; simpls.
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
  desf; auto.
Qed.  
 
Lemma elem_in lst1 lst2 lst1' lst2' f w
      (F: fun_correct f)
      (H1: forall a, In a lst1 -> is_less_exist a lst1' = true)
      (H2: forall a, In a lst2 -> is_less_exist a lst2' = true) :
  forall a, In a (FormatTrivial.cross_general w f lst1 lst2) ->
            is_less_exist a (FormatTrivial.cross_general w f lst1' lst2') = true.
Proof.
  ins.
  apply cross_general_elem in H.
  desf.
  assert (L1: is_less_exist x lst1' = true).
  { apply H1; auto. }
  assert (L2: is_less_exist y lst2' = true).
  { apply H2; auto. }
  clear H1.
  clear H2.
  clear H0.
  clear H3.
  apply is_exist_eq.
  apply is_exist_eq in L1.
  apply is_exist_eq in L2.
  desf.
  exists (f b0 b).
  split.
  { assert (H: total_width (f b0 b) <=? w = true).
    { assert (R: is_less_than (f b0 b) (f x y) = true).
      { apply F; auto. }
      unfold is_less_than in R.
      andb_split.
      apply leb_complete in H.
      apply leb_complete in H2.
      apply leb_complete in H1.
      apply leb_complete in H0.
      apply Nat.leb_le.
      unfold total_width in *.
      desf.
      simpls.
      lia. }
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
  apply F; auto.
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

Lemma eval_in_elem w doc :
  forall a, In a (evaluatorTrivial w doc) -> is_less_exist a (evaluatorList w doc) = true.
Proof.
  induction doc.
  all: simpls.
  { ins.
    unfold flip.
    desf; auto.
    rewrite is_less_than_reflexivity; auto. }
  { ins. 
    rewrite <- indent_eq.
    unfold FormatTrivial.indentDoc.
    apply (elem_in (empty :: nil) (evaluatorTrivial w doc)); auto.
    apply indent_correct. }
  { ins.
    unfold besideDoc.
    rewrite <- cross_general_eq.
    rewrite pareto_inside.
    apply (elem_in (evaluatorTrivial w doc1) (evaluatorTrivial w doc2)); auto.
    apply beside_correct. }
  { ins.
    unfold aboveDoc.
    rewrite <- cross_general_eq.
    rewrite pareto_inside.
    apply (elem_in (evaluatorTrivial w doc1) (evaluatorTrivial w doc2)); auto.
    apply above_correct. }
  { ins.
    unfold choiceDoc.
    rewrite pareto_inside.
    apply is_exist_cons_all.
    unfold FormatTrivial.choiceDoc in H.
    apply in_app_or in H.
    desf; auto. }
  ins.
  unfold fillDoc.
  rewrite <- cross_general_eq.
  rewrite pareto_inside.
  apply (elem_in (evaluatorTrivial w doc1) (evaluatorTrivial w doc2)); auto.
  apply fill_correct.
Qed.     

Definition induction_cond (a: Doc) (b: Doc) (w: nat):=
  << A: pick_best_list (evaluatorList w a) w ⊆ pick_best_list (evaluatorTrivial w a) w >> /\
  << B: pick_best_list (evaluatorList w b) w ⊆ pick_best_list (evaluatorTrivial w b) w >>.

Lemma pareto_beside a b w :
    pick_best_list (FormatList.besideDoc w (evaluatorList w a) (evaluatorList w b)) w ⊆
    pick_best_list (FormatTrivial.besideDoc w (evaluatorTrivial w a) (evaluatorTrivial w b)) w.
Proof.
  unfold besideDoc.
  rewrite <- cross_general_eq.
  apply (incl_tran (m := pick_best_list (FormatTrivial.cross_general w add_beside (evaluatorList w a) (evaluatorList w b)) w)).
  { apply pick_pareto_incl. }
  apply best_remove.
  { apply height_less.
    { apply cross_general_cor.
      all: apply eval_cor. }
    apply elem_in.
    { apply beside_correct. }
    all: apply eval_in_elem. }  
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
  { apply pick_pareto_incl. }
  apply best_remove.
  { apply height_less.
    { apply cross_general_cor.
      all: apply eval_cor. }
    apply elem_in.
    { apply above_correct. }
    all: apply eval_in_elem. }  
  apply cross_general_cor.
  all: apply eval_cor.
Qed.
  

Lemma pareto_fill a b w n
       (H: induction_cond a b w) :
    pick_best_list (FormatList.fillDoc w (evaluatorList w a) (evaluatorList w b) n) w ⊆
    pick_best_list (FormatTrivial.fillDoc w (evaluatorTrivial w a) (evaluatorTrivial w b) n) w.
Proof.
  unfold fillDoc.
  rewrite <- cross_general_eq.
  apply (incl_tran (m := pick_best_list (FormatTrivial.cross_general w (fun fs f : t => add_fill fs f n) (evaluatorList w a) (evaluatorList w b)) w)).
  { apply pick_pareto_incl. }
  apply best_remove. 
  { apply height_less.
    { apply cross_general_cor.
      all: apply eval_cor. }
    apply elem_in.
    { apply fill_correct. }
    all: apply eval_in_elem. }  
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
  { apply pick_pareto_incl. }
  unfold FormatTrivial.choiceDoc.
  apply best_remove. 
  { unfold induction_cond in H.
    desf.
    assert (A': get_min_height (evaluatorList w a) w None = get_min_height (evaluatorTrivial w a) w None).
    { apply height_remove; auto.
      apply eval_in_elem. }
    clear A.
    assert (B': get_min_height (evaluatorList w b) w None = get_min_height (evaluatorTrivial w b) w None).
    { apply height_remove; auto.
      apply eval_in_elem. }
    clear B.
    apply height_less.
    { apply incl_app.
      { apply incl_appl.
        apply eval_cor. }
      apply incl_appr.
      apply eval_cor. }
    ins.
    apply in_app_or in H.
    desf.
    { apply is_exist_cons_all.
      rewrite eval_in_elem; auto. }
    apply is_exist_cons_all.
    rewrite (eval_in_elem _ b); auto. }
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
    { unfold FormatTrivial.indentDoc.
      apply cross_general_cor.
      { done. }
      apply eval_cor. }
    apply elem_in; simpls.
    { apply indent_correct. }
    ins.
    apply eval_in_elem; auto. }
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
