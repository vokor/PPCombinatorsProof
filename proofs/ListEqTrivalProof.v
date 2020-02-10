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
    { apply (is_less_than_transitivity a b a0); auto. }
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

Lemma pareto_inside x lst
   (H:  is_less_exist x lst = false) :
  is_less_exist x (pareto lst) = false.
Proof.
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
    apply pareto_inside; auto. }
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
    apply pareto_inside; auto. }
  apply is_exist_not_cons_all.
  auto.
Qed.

Definition neighb_pareto (a: Doc) (b: Doc) (w: nat):=
  pareto (evaluatorTrivial w a) = (evaluatorList w a) /\
  pareto (evaluatorTrivial w b) = (evaluatorList w b).

Lemma cross_general_exist_helper w f x y ys lst lst'
      (H: is_less_exist x lst = true)
      (F: func_correct f)
      (T: (total_width (f x y) <=? w) = true) :
  
   is_less_exist (f x y)
     (filter (fun f0 : t => total_width f0 <=? w)
             (concat (map (fun f0 : t => map (f f0) (lst' ++ y :: ys)) lst))) = true.
Proof.
  induction lst. auto.
  simpl.
  rewrite map_app.
  repeat rewrite filter_app.
  repeat rewrite is_exist_cons_all.
  simpl.
  apply is_exist_cons_alt in H.
  destruct H.
  { destruct (total_width (f a y) <=? w) eqn:E1.
    { rewrite is_exist_cons_alt.
      red in F. desf.
      rewrite <- F1. auto. }
    rewrite (is_less_than_func_t_l _ _ x) in E1; auto. }
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

Lemma forallb_add_gener_true f a b w lst
      (H: is_less_than a b = true)
      (F: func_correct f) :
  forallb_exist (add_general f w lst a) (add_general f w lst b) = true.
Proof.
  unfold add_general, map_filter.
  set (l := nil) at 1.
  set (r := nil). 
  assert (Lem : forallb_exist l r = true); auto.
  generalize dependent r.
  generalize dependent l.
  induction lst; auto.
  simpl.
  ins.
  desf.
  { simpl.
    rewrite forallb_exist_correct. 
    { red in F.
      desf.
      unfold flip.
      rewrite <- F2.
      rewrite H.
      auto. }
    apply IHlst.
    apply Lem. }
  { rewrite forallb_exist_correct; auto. }
  { rewrite (is_less_than_func_t_r f a b) in Heq; auto. }
  apply IHlst.
  apply Lem.
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

Lemma add_general_not_exist lst x a f w
      (F: func_correct f)
      (H: is_less_exist x lst = false) :
  is_less_exist (f x a) (add_general f w lst a) = false.
Proof.
  induction lst; auto.
  red in F.
  apply is_exist_not_cons_alt in H.
  desf.
  simpl.
  destruct (total_width (f a0 a) <=? w) eqn:E3.
  { apply is_exist_not_cons_alt.
    rewrite <- F1.
    auto. }
  apply IHlst; auto.
Qed.

Lemma add_general_not_exist_elem l a b c f w
      (F: func_correct f)
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

Lemma pareto_add_general lst a f w
      (F: func_correct f) :
  pareto (add_general f w (pareto lst) a) =
  pareto (add_general f w lst a).
Proof.
  induction lst using rev_ind; auto.
  rewrite add_general_rev.
  destruct (is_less_exist x lst) eqn:E1.
  { rewrite linear_pareto_exist; auto.
    destruct (total_width (f x a) <=? w) eqn:E2.
    { rewrite linear_pareto_exist.
      { apply IHlst. }
      clear IHlst.
      induction lst; auto.
      simpl.
      apply is_exist_cons_alt in E1.
      destruct E1.
      { rewrite (is_less_than_func_t_l f a0 x); auto.
        simpl.
        unfold flip.
        red in F. desf.
        rewrite <- F1.
        rewrite H.
        auto. }
      desf.
      { simpl.
        rewrite IHlst; auto.
        apply orb_true_r. }
      apply IHlst.
      reflexivity. }
    rewrite app_nil_r.
    apply IHlst. }
  rewrite linear_pareto_not_exist; auto.
  rewrite add_general_rev.
  destruct (total_width (f x a) <=? w) eqn:E2.
  { repeat rewrite linear_pareto_not_exist; auto.
    { rewrite <- IHlst.
      apply app_inv_all.
      clear IHlst.
      apply pareto_inside in E1.
      generalize E1.
      clear E1.
      set (l := pareto lst).
      generalize dependent l.
      ins.
      induction l using rev_ind; auto. 
      apply is_exist_not_cons_all in E1.
      simpl in E1. unfold flip in E1.
      rewrite orb_false_r in E1.
      destruct E1 as [A B].
      destruct (is_less_than x x0) eqn:E1.
      { rewrite par_elem2_less_rev; auto.
        rewrite add_general_rev.
        destruct (total_width (f x0 a) <=? w) eqn:E4.
        { destruct (is_less_exist (f x0 a) (add_general f w l a)) eqn:E5.
          { rewrite linear_pareto_exist; auto. }
          rewrite linear_pareto_not_exist; auto.
          red in F. desf.
          rewrite par_elem2_less_rev.
          rewrite <- pareto_by_elem_remove.
          apply IHl; auto.
          all: rewrite <- F1; auto. }
        rewrite app_nil_r.
        apply IHl; auto. }
      rewrite par_elem2_not_less_rev; auto.
      repeat rewrite add_general_rev.
      destruct (total_width (f x0 a) <=? w) eqn:E4.
      + destruct (is_less_exist (f x0 a) (add_general f w l a)) eqn:E5.
        { repeat rewrite linear_pareto_exist; auto.
          clear IHl. clear A.
          induction l; auto.
          simpl in E5.
          destruct (is_less_than x a0) eqn:E3.
          { rewrite par_elem2_less; auto.
            destruct (total_width (f a0 a) <=? w) eqn:E6.
            { apply is_exist_cons_alt in E5.
              red in F.
              desf.
              { rewrite <- F1 in E5.
                rewrite (is_less_than_transitivity x a0 x0) in E1; auto. }
              apply IHl; auto. }
            apply IHl.
            apply E5. }
          rewrite par_elem2_not_less; auto.
          simpl.
          destruct (total_width (f a0 a) <=? w) eqn:E6.
          { apply is_exist_cons_alt in E5.
            desf.
            { apply is_exist_cons_alt.
              rewrite E5.
              auto. }
            apply is_exist_cons_alt.
            rewrite IHl; auto. }
          apply IHl.
          apply E5. }
        repeat rewrite linear_pareto_not_exist; auto.
        { red in F. desf.
          repeat rewrite par_elem2_not_less_rev.
          { rewrite pareto_by_elem_swap.
            rewrite IHl; auto.
            rewrite pareto_by_elem_swap.
            reflexivity. }
          all: rewrite <- F1; apply E1. }
        apply add_general_not_exist_elem; auto.
      + repeat rewrite app_nil_r.
        apply IHl.
        apply A. }
    { apply add_general_not_exist; auto. }
    apply add_general_not_exist_elem; auto.
    apply add_general_not_exist; auto.
    apply pareto_inside.
    apply E1. }
  repeat rewrite app_nil_r.
  rewrite <- IHlst.
  clear IHlst.
  generalize (pareto lst).
  intro.
  induction l using rev_ind; auto.
  rewrite add_general_rev.
  destruct (is_less_than x x0) eqn:E3.
  { rewrite par_elem2_less_rev; auto.
    simpl.
    rewrite (is_less_than_func_f_l f x x0); auto.
    rewrite app_nil_r.
    apply IHl. }
  clear E1.
  rewrite par_elem2_not_less_rev; auto.
  rewrite add_general_rev.
  red in F. desf.
  { destruct (is_less_exist (f x0 a) (add_general f w l a)) eqn:E5.
    + repeat rewrite linear_pareto_exist; auto.
      clear IHl.
      induction l; auto.
      simpl in E5.
      destruct (total_width (f a0 a) <=? w) eqn:E1.
      { apply is_exist_cons_alt in E5.
        destruct (is_less_than x a0) eqn:E4.
        { rewrite par_elem2_less; auto.
          desf.
          { rewrite <- F1 in E5.
            rewrite (is_less_than_transitivity x a0 x0) in E3; auto. }
          apply IHl; auto. }
        rewrite par_elem2_not_less; auto.
        simpl.
        rewrite E1.
        apply is_exist_cons_alt.
        destruct E5; auto. }
      destruct (is_less_than x a0) eqn:E4.
      { rewrite par_elem2_less; auto. }
      rewrite par_elem2_not_less; auto.
      simpl.
      rewrite E1.
      apply IHl; auto.
    + repeat rewrite linear_pareto_not_exist; auto.
      { rewrite IHl.
        reflexivity. }
      apply add_general_not_exist_elem; auto.
      red. auto. }
  repeat rewrite app_nil_r.
  apply IHl.
Qed.

Lemma remove_pareto_fst lst lst' f w
      (F: func_correct f) :
  cross_general f w (pareto lst) lst' =
  cross_general f w lst lst'.
Proof.
  unfold cross_general.
  induction lst'.
  { simpl. reflexivity. }
  simpl. 
  rewrite pareto_linear, IHlst', pareto_add_general.
  { rewrite <- pareto_linear.
    reflexivity. }
  auto.
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

Lemma remove_pareto lst lst' f w
      (F: func_correct f) :
  cross_general f w (pareto lst) (pareto lst') =
  cross_general f w lst lst'.
Proof. 
  rewrite remove_pareto_fst; auto.
  unfold cross_general.
  induction lst' using rev_ind; auto.
  destruct (is_less_exist x lst') eqn:E1.
  { rewrite linear_pareto_exist; auto.
    rewrite map_app.
    simpl.
    rewrite IHlst'. 
    induction lst' as [|x0 lst' _] using rev_ind.
    { simpl in E1.
      discriminate E1. }
    clear IHlst'.
    rewrite map_app. simpl.
    repeat rewrite concat_app.
    simpl.
    repeat rewrite app_nil_r.
    rewrite pareto_list_remove with
        (lst:= concat (map (add_general f w lst) lst') ++ add_general f w lst x0); auto.
    apply is_exist_cons_all in E1.
    destruct E1.
    { apply forallb_exist_rem_list_l.
      induction lst'; auto.
      simpl.
      apply is_exist_cons_alt in H.
      destruct H.
      { apply forallb_exist_rem_list_l.
        apply forallb_add_gener_true; auto. }
      apply forallb_exist_rem_list_r.
      apply IHlst'; auto. }
    simpl in H.
    unfold flip in H.
    rewrite orb_false_r in H.
    apply forallb_exist_rem_list_r.
    apply forallb_add_gener_true; auto. }
  rewrite linear_pareto_not_exist; auto.
  repeat rewrite map_app, concat_app.
  simpl.
  rewrite app_nil_r.
  symmetry.
  rewrite pareto_linear_fst.
  rewrite <- IHlst'.
  rewrite <- pareto_linear_fst.
  clear IHlst'.
  assert (P: is_less_exist x (pareto lst') = false).
  { apply pareto_inside in E1; auto. }
  clear E1.
  generalize P.
  generalize (pareto lst').
  clear P.
  ins.
  rewrite <- (app_nil_l (add_general f w lst x)).
  set (mas := nil).
  generalize dependent mas.
  induction l using rev_ind; auto.
  ins.
  apply is_exist_not_cons_all in P.
  simpl in P. unfold flip in P.
  rewrite orb_false_r in P.
  destruct P as [A B].
  rewrite map_app, concat_app.
  simpl. rewrite app_nil_r.
  rewrite <- app_assoc.
  destruct (is_less_than x x0) eqn:E1.
  { rewrite par_elem2_less_rev; auto.
    assert (Lem:  pareto (concat (map (add_general f w lst) l) ++
                                 add_general f w lst x0 ++ mas ++ add_general f w lst x) =
                  pareto (concat (map (add_general f w lst) l) ++ mas ++ add_general f w lst x)).
    { clear IHl.
      generalize (concat (map (add_general f w lst) l)).
      generalize dependent mas.
      induction lst; auto.
      ins.
      assert (Br: forall (a:list t) b c, a ++ b::c = (a ++ [b]) ++ c).
      { ins.
        rewrite <- app_assoc.
        simpl.
        reflexivity. }
      destruct (total_width (f a x0) <=? w) eqn:E2.
      { rewrite (is_less_than_func_t_r _ x x0); auto.
        simpl.
        rewrite pareto_linear.
        rewrite app_assoc.
        rewrite linear_pareto_exist_fst.
        { rewrite <- pareto_linear.
          rewrite <- app_assoc.
          rewrite Br.
          apply IHlst. }
        all: red in F; desf; rewrite <- F2; auto. }
      destruct (total_width (f a x) <=? w).
      { rewrite Br. apply IHlst. }
      apply IHlst. }
    rewrite Lem.
    apply IHl.
    apply A. }
  rewrite par_elem2_not_less_rev; auto.
  rewrite map_app, concat_app.
  simpl. rewrite app_nil_r.
  rewrite <- app_assoc.
  assert (Lem: forall (q: list t) s t h, q ++ s ++ t ++ h = q ++ (s ++ t) ++ h).
  { destruct q.
    { simpl. apply app_assoc. }
    simpl. ins. repeat rewrite app_assoc. reflexivity. }
  repeat rewrite Lem.
  apply IHl; auto.
Qed.

Lemma pareto_text :
  forall x,
    pareto (FormatTrivial.constructDoc x) = FormatList.constructDoc x.
Proof.
  intros x.
  unfold FormatTrivial.constructDoc.
  unfold FormatList.constructDoc.
  reflexivity.
Qed.

Definition indent_tuple sh := fun _ a : t => indent' sh a.

Lemma indent_eq_tuple a sh w :
  (total_width (indent' sh a) <=? w) = (total_width (indent_tuple sh a a) <=? w).
Proof.
  unfold indent_tuple.
  reflexivity.
Qed.

Lemma tuple_indent_correct :
  forall sh, func_correct (indent_tuple sh).
Proof.
  unfold indent_tuple.
  apply indent_correct.
Qed.
  
Lemma indent_exist x lst sh w
     (H1: is_less_exist x lst = true)
     (H2: (total_width (indent' sh x) <=? w) = true) :
  is_less_exist (indent' sh x) (indentDoc w sh lst) = true.
Proof.
  induction lst; auto.
  simpl.
  apply is_exist_cons_alt in H1.
  rewrite indent_eq_tuple in H2.
  desf.
  { apply is_exist_cons_alt.
    rewrite <- indent'_linear.
    rewrite H1; auto. }
  { rewrite indent_eq_tuple in Heq.
    rewrite (is_less_than_func_t_r _ a x) in Heq; auto.
    apply tuple_indent_correct. }
  { simpl.
    rewrite IHlst; auto.
    apply orb_true_r. }
  apply IHlst.
  reflexivity.
Qed.    

Lemma indent_pareto_by_elem lst w sh x:
  indentDoc w sh (pareto_by_elem x lst) = pareto_by_elem (indent' sh x) (indentDoc w sh lst).
Proof.
  induction lst; auto.
  destruct (is_less_than x a) eqn:E1.
  { rewrite par_elem2_less; auto.
    simpl.
    destruct (total_width (indent' sh a) <=? w).
    { rewrite par_elem2_less.
      { apply IHlst. }
      rewrite <- indent'_linear.
      apply E1. }
    apply IHlst. }
  rewrite par_elem2_not_less; auto.
  simpl.
  destruct (total_width (indent' sh a) <=? w).
  { rewrite par_elem2_not_less.
    { rewrite IHlst.
      reflexivity. }
    rewrite <- indent'_linear.
    apply E1. }
  apply IHlst.
Qed.  

Lemma indentDoc_pareto_by_elem lst w sh x
      (H: (total_width (indent' sh x) <=? w) = false) :
  pareto_by_elem (indent' sh x) (indentDoc w sh lst) = indentDoc w sh lst.
Proof.
  rewrite <- indent_pareto_by_elem.
  induction lst; auto.
  destruct (is_less_than x a) eqn:E1.
  { rewrite par_elem2_less; auto.
    rewrite indent_eq_tuple in H.
    simpl.
    rewrite indent_eq_tuple.
    rewrite (is_less_than_func_f_r _ x a); auto.
    apply tuple_indent_correct. }
  rewrite par_elem2_not_less; auto.
  simpl.
  desf.
  rewrite IHlst.
  reflexivity.
Qed.  

Lemma indent_with_pareto w sh lst :
  indentDoc w sh (pareto lst) = pareto (indentDoc w sh lst).
Proof.
  assert (Rev_destruct: forall a l, indentDoc w sh (l ++ [a]) =
                                    indentDoc w sh l ++ (if total_width (indent' sh a) <=? w then indent' sh a::nil else nil)).
  {
    ins.
    induction l; auto.
    simpl.
    destruct (total_width (indent' sh a0) <=? w).
    { simpl.
      rewrite IHl.
      reflexivity. }
    apply IHl. } 
  assert (F: func_correct (fun _ a : t => indent' w a)).
  { apply indent_correct. }
  red in F.
  desf.
  induction lst using rev_ind; auto.
  destruct (is_less_exist x lst) eqn:E1.
  { rewrite linear_pareto_exist; auto.
    rewrite Rev_destruct.
    destruct (total_width (indent' sh x) <=? w) eqn:E2.
    { destruct (is_less_exist (indent' sh x) (indentDoc w sh lst)) eqn:E3.
      { rewrite linear_pareto_exist; auto. }
      rewrite indent_exist in E3; auto.
      discriminate E3. }
    rewrite app_nil_r.
    apply IHlst. }
  rewrite linear_pareto_not_exist; auto.
  repeat rewrite Rev_destruct.
  destruct (total_width (indent' sh x) <=? w) eqn:E2.
  { rewrite indent_pareto_by_elem.
    rewrite linear_pareto_not_exist.
    { rewrite IHlst.
      reflexivity. }
    generalize E1.
    clear.
    ins.
    induction lst; auto.
    apply is_exist_not_cons_alt in E1.
    simpl.
    desf.
    { apply is_exist_not_cons_alt.
      rewrite <- indent'_linear.
      rewrite E1; auto. }
    apply IHlst.
    reflexivity. }
  repeat rewrite app_nil_r.
  rewrite indent_pareto_by_elem.
  rewrite <- IHlst.
  rewrite indentDoc_pareto_by_elem; auto.
Qed.
  
Lemma pareto_indent sh d w
    (H: pareto (evaluatorTrivial w d) = (evaluatorList w d)) :
    pareto (FormatTrivial.indentDoc w sh (evaluatorTrivial w d))
        = FormatList.indentDoc w sh (evaluatorList w d).
Proof.
  rewrite <- H. clear H.
  set (lst := evaluatorTrivial w d).
  rewrite indent_with_pareto.
  unfold FormatTrivial.indentDoc.
  rewrite cross_general_eq.
  unfold cross_general.
  assert (Lem: concat (map (add_general (fun _ a : t => indent' sh a) w (empty::nil)) lst) =
               indentDoc w sh lst).
  { unfold indentDoc.
    induction lst; auto.
    simpl.
    destruct (total_width (indent' sh a) <=? w).
    { simpl.
      rewrite IHlst.
      reflexivity. }
    simpl.
    apply IHlst.
  }
  rewrite Lem.
  reflexivity.
Qed.

Lemma pareto_beside a b w
      (H: neighb_pareto a b w) :
  pareto (FormatTrivial.besideDoc w (evaluatorTrivial w a) (evaluatorTrivial w b)) 
      = FormatList.besideDoc w (evaluatorList w a) (evaluatorList w b).
Proof.
  red in H. destruct H.
  rewrite <- H. rewrite <- H0.
  set (lst := evaluatorTrivial w a).
  set (arr := evaluatorTrivial w b).
  unfold besideDoc.
  rewrite remove_pareto.
  { unfold FormatTrivial.besideDoc.
    apply cross_general_eq. }
  apply beside_correct.
Qed.

Lemma pareto_above a b w
      (H: neighb_pareto a b w) :
  pareto (FormatTrivial.aboveDoc w (evaluatorTrivial w a) (evaluatorTrivial w b)) 
      = FormatList.aboveDoc w (evaluatorList w a) (evaluatorList w b).
Proof.
  red in H. destruct H.
  rewrite <- H. rewrite <- H0.
  set (lst := evaluatorTrivial w a).
  set (arr := evaluatorTrivial w b).
  unfold aboveDoc.
  rewrite remove_pareto.
  { unfold FormatTrivial.aboveDoc.
    apply cross_general_eq. }
  apply above_correct.
Qed.

Lemma pareto_fill a b w n
      (H: neighb_pareto a b w) :
  pareto (FormatTrivial.fillDoc w (evaluatorTrivial w a) (evaluatorTrivial w b) n) 
      = FormatList.fillDoc w (evaluatorList w a) (evaluatorList w b) n.
  red in H. destruct H.
  rewrite <- H. rewrite <- H0.
  set (lst := evaluatorTrivial w a).
  set (arr := evaluatorTrivial w b).
  unfold fillDoc.
  rewrite remove_pareto.
  { unfold FormatTrivial.fillDoc.
    apply cross_general_eq. }
  apply fill_correct.
Qed.

Lemma pareto_choice a b w
      (H: neighb_pareto a b w) :
  pareto (FormatTrivial.choiceDoc (evaluatorTrivial w a) (evaluatorTrivial w b)) =
  FormatList.choiceDoc (evaluatorList w a) (evaluatorList w b).
Proof.
  red in H. desf.
  rewrite <- H.
  rewrite <- H0.
  set (lst := evaluatorTrivial w a).
  set (arr := evaluatorTrivial w b).
  unfold choiceDoc.
  rewrite pareto_linear.
  reflexivity.
Qed.

Lemma pareto_common width doc :
  pareto (evaluatorTrivial width doc) = evaluatorList width doc.
Proof.
  induction doc; auto.
  all: simpl.
  { apply pareto_indent.
    apply IHdoc. }
  { apply pareto_beside.
    rels. }
  { apply pareto_above.
    rels. }
  { apply pareto_choice.
    rels. }
  apply pareto_fill.
  rels.
Qed.

Require Import Lia.

(*
Lemma height_less a b :
  is_less_than a b = true -> (a.(height) <=? b.(height)) = true.
Proof.
  ins.
  unfold is_less_than in H.
Admitted.

Lemma width_less a b :
  is_less_than a b = true -> (total_width a <=? total_width b) = true.
Proof.
Admitted.  
*)

Lemma is_better_true a b : is_less_than a b = true -> is_better_than a b = a.
Proof.
  ins.
  unfold is_better_than.
  unfold is_less_than in H.
  andb_split.
  apply leb_complete in H0.
  apply leb_complete in H1.
  apply leb_complete in H2.
  apply leb_complete in H.
  desf. (*
  { apply Nat.compare_eq in Heq.
    apply Nat.compare_eq in Heq0.
    unfold is_less_than in Heq1.
    desf.
    { apply leb_complete_conv in Heq1. lia. }
    { apply leb_complete_conv in Heq1. lia. }
    { apply leb_complete_conv in Heq1. lia. }
    apply leb_complete_conv in Heq1. lia. }
  { apply nat_compare_gt in Heq0.
    apply Nat.compare_eq in Heq.
    unfold total_width in Heq0.
    desf. ins. lia. } (*FIXME: instead of ins? *)
  apply nat_compare_gt in Heq.
  lia. *)
Admitted. 

Lemma better_destruct a b :
  is_better_than a b = a \/ is_better_than a b = b.
Proof.
  unfold is_better_than.
  desf; auto.
Qed.

Lemma is_better_less a b
      (H1: is_less_than a b = false)
      (H2: is_less_than b a = true) : is_better_than a b = b.
Admitted.

(*
Lemma is_better_tr1 a b c
      (H1: is_better_than a b = a)
      (H2: is_better_than b c = b) : is_better_than a c = a.
Proof.
  unfold is_better_than in *.
  desf.
  { apply hahn__nandb_split in Heq3.
    apply hahn__nandb_split in Heq1.
    rewrite negb_false_iff in Heq3.
    rewrite negb_false_iff in Heq1.
    apply NPeano.Nat.ltb_ge in Heq2.
    apply NPeano.Nat.ltb_ge in Heq0.
    apply NPeano.Nat.ltb_lt in Heq.
    desf.
    all: lia. }
  apply hahn__nandb_split in Heq4.
  apply hahn__nandb_split in Heq2.
  apply andb_prop in Heq0.
  apply Nat.ltb_ge in Heq3.
  apply Nat.ltb_ge in Heq1.
  apply Nat.ltb_ge in Heq.
  desf.
  { apply Nat.eqb_neq in Heq4.
    apply Nat.eqb_neq in Heq2.
    apply Nat.eqb_eq in Heq0.
    lia. }
  { apply negb_false_iff in Heq4.
    apply beq_nat_true in Heq0.
    apply Nat.eqb_neq in Heq2.
    lia. }
  { apply Nat.eqb_neq in Heq4.
    apply Nat.eqb_eq in Heq0.
    lia. }
  apply negb_true_iff in Heq5.
  apply negb_false_iff in Heq4.
  apply negb_false_iff in Heq2.
  rewrite (nat_leb_trans _ (total_width b)) in Heq5; auto.
  discriminate Heq5.
Qed.    *)

(*
Lemma is_better_tr2 a b c
      (H1: is_better_than a b = b)
      (H2: is_better_than b c = c) : is_better_than a c = c.
Proof. 
  unfold is_better_than in *.
  desf.
  { apply Nat.ltb_lt in Heq2.
    apply Nat.ltb_lt in Heq1.
    apply NPeano.Nat.ltb_ge in Heq.
    lia. }
  { apply andb_prop in Heq3.
    apply hahn__nandb_split in Heq0.
    apply Nat.ltb_lt in Heq1.
    apply Nat.ltb_ge in Heq2.
    apply Nat.ltb_ge in Heq.
    desf.
    { apply beq_nat_true in Heq3.
      apply beq_nat_false in Heq0.
      lia. }
    apply beq_nat_true in Heq3.
    lia. }
  { apply andb_prop in Heq2.
    apply hahn__nandb_split in Heq0.
    apply Nat.ltb_lt in Heq3.
    apply Nat.ltb_ge in Heq1.
    apply Nat.ltb_ge in Heq.
    desf.
    { apply beq_nat_true in Heq2.
      apply beq_nat_false in Heq0.
      lia. }
    apply Nat.eqb_eq in Heq2.
    lia. }
  apply Nat.ltb_ge in Heq3.
  apply Nat.ltb_ge in Heq1.
  apply Nat.ltb_ge in Heq.
  apply andb_prop in Heq4.
  apply andb_prop in Heq2.
  apply hahn__nandb_split in Heq0.
  desf.
  { apply Nat.eqb_eq in Heq4.
    apply Nat.eqb_neq in Heq0.
    apply Nat.eqb_eq in Heq2.
    lia. }
  apply negb_false_iff in Heq0.
  apply negb_true_iff in Heq6.
  apply negb_true_iff in Heq5.
  apply leb_iff_conv in Heq6.
  apply leb_iff_conv in Heq5.
  apply leb_complete in Heq0.
  lia. *)


Lemma is_better_tr3 a b c
      (H1: is_better_than a b = a)
      (H2: is_better_than a c = c) : is_better_than c b = c.
Proof. (*
  unfold is_better_than in *.
  desf.
  { apply Nat.ltb_lt in Heq1. lia. }
  { apply Nat.ltb_lt in Heq0.
    apply Nat.ltb_lt in Heq.
    lia. }
  { apply Nat.ltb_lt in Heq0.
    apply Nat.ltb_lt in Heq.
    apply Nat.ltb_ge in Heq1.
    lia. }
  { apply Nat.ltb_lt in Heq2. lia. }
  { apply andb_prop in Heq3.
    desf.
    apply negb_true_iff in Heq4.
    apply Nat.leb_gt in Heq4.
    lia. }
  { apply andb_prop in Heq1.
    desf.
    { apply Nat.ltb_lt in Heq.
      apply beq_nat_true in Heq1.
      apply NPeano.Nat.ltb_ge in Heq0.
      apply NPeano.Nat.ltb_ge in Heq2.
      lia. }
    apply beq_nat_true in Heq1.
    apply Nat.ltb_ge in Heq2.
    apply Nat.ltb_lt in Heq.
    lia. }
  { apply Nat.ltb_lt in Heq2. lia. }
  { apply andb_prop in Heq3.
    desf.
    apply negb_true_iff in Heq4.
    apply Nat.leb_gt in Heq4.
    lia. }
  { apply Nat.ltb_lt in Heq1.
    apply Nat.ltb_ge in Heq2.
    apply Nat.ltb_ge in Heq.
    apply andb_prop in Heq0.
    destruct Heq0.
    apply beq_nat_true in H. lia. }
  { apply Nat.ltb_lt in Heq3. lia. }
  { apply andb_prop in Heq4.
    desf.
    apply negb_true_iff in Heq5.
    apply Nat.leb_gt in Heq5.
    lia. }
  apply andb_prop in Heq2.
  apply andb_prop in Heq0.
  destruct Heq2.
  destruct Heq0.
  apply negb_true_iff in H0.
  apply negb_true_iff in H4.
  apply Nat.leb_gt in H0.
  apply Nat.leb_gt in H4.
  apply Nat.ltb_ge in Heq3.
  apply Nat.ltb_ge in Heq1.
  apply Nat.ltb_ge in Heq.
  apply Nat.eqb_eq in H3.
  apply Nat.eqb_eq in H.
  desf.
  { apply Nat.eqb_neq in Heq4.
    lia. }
  apply negb_false_iff in Heq4.
  apply leb_complete in Heq4.
  lia. *)
Admitted.

(*
Lemma is_better_assoc a b c :
  is_better_than a (is_better_than b c) = is_better_than (is_better_than a b) c.
Proof.
  destruct (better_destruct a (is_better_than b c)).
  { rewrite H.
    destruct (better_destruct (is_better_than a b) c).
    { rewrite H0.
      destruct (better_destruct a b).
      { rewrite H1.
        reflexivity. }
      rewrite H1 in H0.
      rewrite H0 in H.
      rewrite H.
      reflexivity. }
    destruct (better_destruct b c).
    { rewrite H1 in H.
      rewrite H in H0.
      assert (H2: is_better_than a c = a).
      { apply (is_better_tr1 a b c); auto. }
      rewrite <- H2 at 1.
      rewrite H.
      reflexivity. }
    rewrite H1 in H.
    destruct (better_destruct a b).
    { rewrite H2 in H0.
      rewrite H2.
      rewrite H.
      reflexivity. }
    rewrite H0.
    rewrite (is_better_tr2 _ b) in H; auto. }
  rewrite H.
  destruct (better_destruct (is_better_than a b) c).
  { rewrite H0.
    destruct (better_destruct a b).
    { rewrite H1 in H0.
      destruct (better_destruct b c).
      { rewrite H2 in H.
        rewrite H, H2.
        reflexivity. }
      rewrite H2 in H.
      rewrite H1, H2.
      rewrite <- H.
      rewrite <- H0 at 2.
      reflexivity. }
    rewrite H1 in H0.
    rewrite H0, H1.
    reflexivity. }
  rewrite H0.
  destruct (better_destruct a b).
  { rewrite H1 in H0.
    destruct (better_destruct b c).
    { rewrite H2 in H.
      assert (H3: is_better_than a c = a).
      { apply (is_better_tr1 _ b); auto. }
      rewrite H1 in H.
      rewrite H3 in H0.
      rewrite <- H0 at 2.
      rewrite H.
      apply H2. }
    apply H2. }
  rewrite H1 in H0.
  apply H0.
Qed. *)

Lemma is_better_out lst :
  forall a b,
  fold_left is_better_than (lst ++ [a]) b = is_better_than (fold_left is_better_than lst b) a.
Proof.
  induction lst; auto.
  ins.
Qed.

Lemma pick_best_des' b lst :
  forall a, pick_best (a::lst ++ [b]) = is_better_than (pick_best (a::lst)) b.
Proof.
  induction lst.
  { simpl.
    reflexivity. }
  ins.
Qed.
      
Lemma pick_best_des b lst : 
  lst <> nil -> pick_best (lst ++ [b]) = is_better_than (pick_best lst) b.
Proof.
  induction lst; rels.
  ins.
  apply is_better_out.
Qed.

Lemma pareto_not_nil :
  forall (lst: list t), lst <> nil -> pareto lst <> nil.
Proof.
  ins.
Admitted.
  

Lemma pareto_filter_eq :
  forall (lst:list t), pick_best lst = pick_best (pareto lst).
Proof.
  ins.
  induction lst using rev_ind; auto.
  destruct (is_less_exist x lst) eqn:E1.
  { rewrite linear_pareto_exist; auto.
    rewrite <- IHlst.
    clear IHlst.
    induction lst. 
    { simpl in E1.
      discriminate E1. }
    apply is_exist_cons_alt in E1.
    destruct E1.
    { simpl.
      clear IHlst.
      rewrite is_better_out.
      apply is_better_true in H.
      generalize dependent a.
      induction lst; auto.
      ins.
      destruct (better_destruct a0 a).
      { rewrite H0.
        rewrite <- IHlst at 2; auto. }
      rewrite H0.
      rewrite <-IHlst at 2; auto.
      apply (is_better_tr3 a0); auto. }
    admit. }
  rewrite linear_pareto_not_exist; auto. 
  destruct lst; auto.
  rewrite <- app_comm_cons.
  rewrite pick_best_des'.
  rewrite IHlst.
  apply pareto_inside in E1.
  generalize dependent E1.
  assert (pareto (t::lst) <> nil).
  { apply pareto_not_nil; rels. } (* What can be done instead of rels? *)
  generalize dependent H.
  generalize (pareto (t :: lst)).
  intros.
  rewrite <- pick_best_des; auto.
  generalize dependent E1.
  clear.
  ins.
  destruct l; auto.
  apply is_exist_not_cons_alt in E1.
  desf.
  destruct (is_less_than x t) eqn:E2.
  { rewrite par_elem2_less; auto.
    simpl.
    generalize dependent t.
    induction l.
    { ins.
      apply is_better_less; auto. }
    intros.
    apply is_exist_not_cons_alt in E0.
    destruct E0.
    destruct (is_less_than x a) eqn:E3.
    { rewrite par_elem2_less; auto.
      simpl.
      apply IHl; auto.
      { destruct (better_destruct t a).
        { rewrite H1. apply E1. }
        rewrite H1. apply H. }
      destruct (better_destruct t a).
      { rewrite H1. apply E2. }
      rewrite H1. apply E3. }
    rewrite par_elem2_not_less; auto.  
Admitted.    

Lemma pareto_nil_con lst :
  pareto lst = nil -> lst = nil.
Proof.
  ins.
  induction lst using rev_ind; auto.
  destruct (is_less_exist x lst) eqn:E1.
  { rewrite linear_pareto_exist in H; auto.
    rewrite IHlst in E1; auto.
    simpl in E1.
    discriminate E1. }
  rewrite linear_pareto_not_exist in H; auto.
  assert (pareto_by_elem x (pareto lst) ++ [x] <> nil).
  { generalize (pareto_by_elem x (pareto lst)).
    ins.
    clear.
    destruct l.
    all: simpl; rels. }
  rels.
Qed.
  
Lemma trivial_nil :
  forall doc w, evaluatorTrivial w doc = nil -> evaluatorList w doc = nil.
Proof.
  ins.
  assert (P: pareto (evaluatorTrivial w doc) = nil).
  { rewrite H. apply pareto_nil. }
  rewrite <- P.

Admitted.       

Lemma trivial_not_nil :
  forall w doc, evaluatorTrivial w doc <> nil -> evaluatorList w doc <> nil.
Admitted.

(*---------MAIN Theorem-----------*)
Theorem listEqTrivialProof :
  forall doc width,
    pretty evaluatorTrivial width doc = pretty evaluatorList width doc.
Proof.
  ins.
  unfold pretty, best_to_str.
  destruct (evaluatorTrivial width doc) eqn:E1.
  { rewrite trivial_nil.
    { reflexivity. }
    apply E1. }
  destruct (evaluatorList width doc) eqn:E2.
  { assert (L:  evaluatorList width doc <> nil).
    { apply trivial_not_nil.
      rewrite E1. (* What tactic I need instead of rels? *)
      rels. }
    rewrite E2 in L.
    rels. }
  rewrite <- E1.
  rewrite <- E2.
  clear.
  rewrite <- pareto_common.
  rewrite pareto_filter_eq.
  reflexivity.
Qed.
