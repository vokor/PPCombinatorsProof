Require Import Format.
Require Import Doc.
Require Import PrettyPrinter.
Require Import FormatTrivial.
Require Import FormatList.
Require Import String.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
(*Require Import Coq.Arith.PeanoNat.*)

Lemma listEqTrivialProof :
  forall x width,
    (pretty evaluatorTrival width x) = (pretty evaluatorList width x).
Proof.
  intros x.
Admitted.

Lemma is_less_than_Lt :
  forall a b, compare a b = Lt ->
    is_less_than a b = negb (is_less_than b a).
Proof.
  intros a b H.
  unfold compare in H.
  destruct (is_less_than a b) eqn:E1.
  { destruct (is_less_than b a) eqn:E2.
    discriminate H. auto.
  }
  destruct (is_less_than b a) eqn:E2.
  discriminate H. discriminate H.
Qed.

Lemma is_less_than_Gt :
  forall a b, compare a b = Gt ->
    is_less_than a b = false.
Proof.
  intros a b H.
  unfold compare in H.
  destruct (is_less_than a b) eqn:E1.
  destruct (is_less_than b a) eqn:E2.
  discriminate H. discriminate H.
  reflexivity.
Qed.

Lemma is_less_than_Eq :
  forall a b, compare a b = Eq ->
    is_less_than a b = is_less_than b a.
Proof.
  intros a b H.
  unfold compare in H.
  destruct (is_less_than a b) eqn:E1.
  { destruct (is_less_than b a) eqn:E2.
    reflexivity. discriminate H.
  }
  destruct (is_less_than b a) eqn:E2.
  discriminate H. reflexivity.
Qed.

Lemma Eq_uni :
  forall a b, compare a b = Eq -> compare b a = Eq.
Proof.
  intros a b.
  unfold compare.
  destruct (is_less_than a b).
  destruct (is_less_than b a).
  auto. discriminate.
  destruct (is_less_than b a).
  discriminate. auto.
Qed.

Lemma is_less_than_Same :
  forall a, is_less_than a a = true.
Proof.
  intro a.
  unfold is_less_than.
Admitted.

Lemma less_base :
  forall a b, negb (is_less_than a b) = true ->
    is_less_than a b = false.
Proof.
  intros a b H.
  destruct (is_less_than a b) eqn:E1.
  simpl in H. discriminate H.
  reflexivity.
Qed.

Lemma less_base' :
  forall a b, negb (is_less_than a b) = false ->
    is_less_than a b = true.
Proof.
  intros a b H.
  destruct (is_less_than a b) eqn:E1.
  simpl in H. reflexivity.
  discriminate H.
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

Lemma par_elem2_not_less :
  forall a b lst, is_less_than a b = false ->
    pareto_by_elem a (b::lst) = b :: pareto_by_elem a lst.
Proof.
  intros a b lst H.
  unfold pareto_by_elem, filter.
  rewrite -> eq_conv_is_less.
  rewrite -> H. auto.
Qed.

Lemma par_elem2_less :
  forall a b lst, is_less_than a b = true ->
    pareto_by_elem a (b::lst) = pareto_by_elem a lst.
Proof.
  intros a b lst H.
  unfold pareto_by_elem, filter.
  rewrite -> eq_conv_is_less.
  rewrite -> H. auto.
Qed.

Lemma as_pred :
  forall width sh a b, main_pred width sh a = false /\
    is_less_than a b = true -> main_pred width sh b = false.
Proof.
  intros w sh a b H.
  destruct H as [A B].
Admitted.

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
      discriminate H.
    }
    { destruct (is_less_exist a l) eqn:E2.
      unfold flip in H. rewrite E1 in H.
      discriminate H. auto.
    }
  }
  { intro H.
    destruct H as [A B].
    simpl.
    unfold flip. rewrite A, B.
    auto.
  }
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
    discriminate H. auto.
  }
  { intro H.
    destruct H as [A B].
    induction lst. auto.
    simpl.
    rewrite is_exist_not_cons_alt in A.
    destruct A as [A1 A2].
    rewrite IHlst; auto.
    unfold flip. rewrite A1.
    auto.
  }
Qed.

Require Import Coq.ssr.ssrbool.

Lemma is_exist_cons_alt a h l  :
  is_less_exist a (h :: l) = true <->
  is_less_than h a = true \/ is_less_exist a l = true.
Proof.
  split.
  { intro H.
    destruct (is_less_than h a) eqn:E1; auto.
    destruct (is_less_exist a l) eqn:E2; auto.
    simpl in H. unfold flip in H.
    rewrite E1, E2 in H. discriminate H.
  }
  { intro H. destruct H as [A|A].
    { simpl. unfold flip. rewrite A. auto.
    }
    { simpl. rewrite A. rewrite orbT.
      reflexivity.
    }
  }
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
    apply IHlst. simpl in H. apply H.
  }
  intro H.
  destruct H as [A|B].
  { induction lst. auto.
    simpl.
    unfold flip.
    rewrite is_exist_cons_alt in A.
    destruct (is_less_than a0 a) eqn:E1. auto.
    rewrite IHlst. auto.
    destruct A as [A1|A2]. discriminate A1.
    apply A2.
  }
  induction lst. auto.
  simpl.
  unfold flip.
  rewrite IHlst.
  rewrite orbT. reflexivity.
Qed.


Lemma is_less_than_transitivity :
  forall a b c, is_less_than a b = true /\ is_less_than b c = true ->
    is_less_than a c = true.
Proof.
  Admitted.

Lemma compare_Eq_transitivity :
  forall a b c, compare a b = Eq /\ is_less_than c b = true -> is_less_than c a = true.
Proof.
  intros a b c H.
  destruct H as [A B].
  unfold compare in A.
  destruct  (is_less_than a b) eqn:E1.
  { destruct (is_less_than b a) eqn:E2.
    all: apply (is_less_than_transitivity c b a); auto.
    discriminate A.
  }
  destruct (is_less_than b a) eqn:E2.
  discriminate A.
Admitted.

Lemma is_less_exist_transitivity :
  forall a b lst, is_less_than a b = true /\ is_less_exist a lst = true 
      -> is_less_exist b lst = true.
Proof.
  intros a b lst H.
  destruct H as [A B].
  rewrite <- B.
  induction lst; auto.
  rewrite is_exist_cons_alt in B.
  destruct B as [C|C].
  { simpl. unfold flip.
    rewrite C. rewrite (is_less_than_transitivity a0 a b); auto.
  }
  { simpl. rewrite IHlst, C; auto.
    unfold flip.
    destruct (is_less_than a0 b) eqn:E1.
    { destruct (is_less_than a0 a); auto.
    }
    { destruct (is_less_than a0 a); auto.
    }
  }
Qed.


Lemma is_less_exist_uni :
  forall a b lst, is_less_than a b = true /\ is_less_exist b lst = false-> 
    is_less_exist a (pareto_by_elem b lst) = is_less_exist a lst.
Proof.
  intros a b lst H.
  induction lst. auto.
  destruct H as [A B].
  rewrite is_exist_not_cons_alt in B.
  destruct B as [B C].
  simpl. rewrite eq_conv_is_less.
  destruct (is_less_than b a0) eqn:E1.
  { simpl. unfold flip.
    rewrite IHlst.
    destruct (is_less_exist a lst) eqn:E2.
    {
      destruct (compare a0 a) eqn:E3.
      rewrite orbT; auto.
      rewrite orbT; auto.
      rewrite orbT; auto.
    }
    destruct (compare a a0) eqn:E3.
    (* Here need discriminate B, because a = b = a0, but a0 <= b - false ??? *)
    admit.
    { assert (D : is_less_than a a0 = true).
      { apply (is_less_than_transitivity a b a0);auto.
      }
      rewrite is_less_than_Lt in D; auto.
      apply less_base in D. rewrite D. auto.
    }
    assert (D : is_less_than a a0 = true).
      { apply (is_less_than_transitivity a b a0);auto.
      }
    rewrite is_less_than_Gt in D. discriminate D. auto.
    auto.
  }
  simpl.
  rewrite IHlst.
  auto. auto.
Admitted.

Lemma pareto_by_elem_linear :
  forall a lst lst', pareto_by_elem a (lst ++ lst') = 
    (pareto_by_elem a lst) ++ (pareto_by_elem a lst').
Proof.
  intros a lst lst'.
  induction lst. auto.
  simpl. 
  rewrite eq_conv_is_less.
  destruct (is_less_than a a0) eqn:E1.
  simpl. apply IHlst.
  simpl. rewrite IHlst. reflexivity.
Qed.

Lemma pareto_by_elem_swap :
  forall a b lst, is_less_than a b = true ->
  pareto_by_elem a lst = pareto_by_elem a (pareto_by_elem b lst).
Proof.
  intros a b lst H.
  induction lst. auto.
  simpl.
  repeat rewrite eq_conv_is_less.
  destruct (is_less_than a a0) eqn:E3.
  { simpl.
    destruct (is_less_than b a0) eqn:E4.
    { simpl. auto.
    }
    simpl.
    rewrite eq_conv_is_less, E3. simpl.
    auto.
  }
  simpl.
  destruct (is_less_than b a0) eqn:E4.
  { simpl.
    assert (L: is_less_than a a0 = true).
    { apply (is_less_than_transitivity a b a0). auto.
    }
    rewrite E3 in L. discriminate L.
  }
  simpl. rewrite eq_conv_is_less, E3.
  simpl. rewrite IHlst. reflexivity.
Qed.

Lemma pareto_exec_elem :
  forall a b lst lst', is_less_than a b = true -> pareto_by_elem a (pareto_exec lst lst') =
      pareto_by_elem a (pareto_exec (pareto_by_elem b lst) lst').
Proof.
  intros a b lst lst' H.
  destruct lst. auto.
  generalize dependent t.
  generalize dependent lst.
  induction lst'.
  { intros lst t.
    simpl.
    repeat rewrite eq_conv_is_less.
    destruct (is_less_than a t) eqn:E1.
    { simpl.
      destruct (is_less_than b t) eqn:E2.
      { simpl. apply pareto_by_elem_swap. auto.
      }
     simpl. rewrite eq_conv_is_less, E1. simpl.
     apply pareto_by_elem_swap. auto.
    }
    simpl.
    destruct (is_less_than b t) eqn:E2.
    { assert (L1: is_less_than a t = true).
      { apply (is_less_than_transitivity a b t). auto.
      }
      rewrite L1 in E1. discriminate E1.
    }
    simpl.
    rewrite eq_conv_is_less, E1. simpl. 
    induction lst. auto.
    simpl.
    repeat rewrite eq_conv_is_less.
    destruct (is_less_than a a0) eqn:E3.
    { destruct (is_less_than b a0) eqn:E4.
      { simpl. auto.
      }
      simpl.
      rewrite eq_conv_is_less, E3.
      simpl. rewrite IHlst. reflexivity.
    }
    destruct (is_less_than b a0) eqn:E4.
    simpl.
    assert (L1: is_less_than a a0 = true).
    { apply (is_less_than_transitivity a b a0). auto.
    }
    rewrite L1 in E3. discriminate E3.
    simpl. rewrite eq_conv_is_less, E3.
    simpl. rewrite <- pareto_by_elem_swap.
    all: auto.
  }
  intros lst t. simpl.
  repeat rewrite eq_conv_is_less.
  unfold flip.
  destruct (is_less_than b t) eqn:E1.
  { simpl.
    destruct (compare t a0) eqn:cmp.
    { destruct (is_less_than a0 t) eqn:E2.
      { rewrite is_less_than_Eq; auto.
        rewrite E2. simpl.
        destruct (is_less_exist a0 (pareto_by_elem b lst)) eqn:E3.
        { rewrite IHlst'.
          simpl. rewrite eq_conv_is_less, E1. auto.
        }
        rewrite is_less_exist_uni in E3.
Admitted.

Lemma pareto_exec_elem_H :
  forall a x lst xs lst', is_less_than a x = true -> pareto_by_elem a (pareto_exec (lst ++ x :: xs) lst') 
  = pareto_by_elem a (pareto_exec (lst ++ xs) lst').
Proof.
  intros a x lst xs lst' H.
  generalize dependent lst.
  generalize dependent x.
  generalize dependent xs.
  induction lst'.
  { simpl.
    intros xs b H lst.
    repeat rewrite pareto_by_elem_linear.
    simpl. 
    rewrite eq_conv_is_less, H.
    auto.
  }
  intros xs b H lst.
  simpl.
  destruct (is_less_exist a0 (lst ++ b :: xs)) eqn:E1.
  { destruct (is_less_exist a0 (lst ++ xs)) eqn:E2. auto.
    assert (L1: is_less_than b a0 = true).
    { rewrite is_exist_cons_all in E1.
      destruct E1 as [AA|AA].
      { rewrite is_exist_not_cons_all in E2.
        destruct E2 as [A B]. rewrite A in AA.
        discriminate AA.
      }
      rewrite is_exist_not_cons_all in E2.
      destruct E2 as [A B].
      rewrite is_exist_cons_alt in AA.
      destruct AA as [BB|BB].
      apply BB. rewrite BB in B.
      discriminate B.
    }
    repeat rewrite IHlst'.
    admit. (* use pareto_exec_elem *)
    apply (is_less_than_transitivity a b a0).
    all: auto.
  }
Admitted.

Lemma pareto_exec_destruct :
  forall a b c lst, is_less_than a b = true  ->
  pareto_by_elem a (pareto_exec (b :: c :: nil) lst) =
    pareto_by_elem a (pareto_exec (c :: nil) lst).
Proof.
  intros a b c lst H.
  generalize dependent b.
  generalize dependent c.
  induction lst.
  { intros c b H.
    simpl.
    rewrite eq_conv_is_less, H.
    simpl. reflexivity.
  }
  intros c b H.
  simpl. unfold flip.
  destruct (is_less_than b a0) eqn:E1.
  { repeat rewrite eq_conv_is_less.
    simpl.
    destruct (is_less_than c a0) eqn:E2.
    { simpl. rewrite IHlst; auto.
    }
    simpl.
    destruct (is_less_than a0 c) eqn:E3.
    { simpl. rewrite IHlst; auto.
      rewrite (pareto_exec_elem a c (c::nil) lst).
      rewrite (pareto_exec_elem a a0 (a0::nil) lst).
      simpl. repeat rewrite eq_conv_is_less.
      repeat rewrite is_less_than_Same. auto.
      apply (is_less_than_transitivity a b a0); auto.
      apply (is_less_than_transitivity a b c).
      rewrite (is_less_than_transitivity b a0 c).
      auto. auto.
    }
    simpl.
    rewrite IHlst; auto.
    rewrite (pareto_exec_elem a a0 (c :: a0 :: nil) lst).
    simpl. repeat rewrite eq_conv_is_less.
    destruct (is_less_than a0 c) eqn:E4.
    discriminate.
    repeat rewrite is_less_than_Same. auto.
    apply (is_less_than_transitivity a b a0); auto.
  }
  destruct (is_less_than c a0) eqn:E2.
  { simpl. apply IHlst; auto.
  }
  simpl. repeat rewrite eq_conv_is_less.
  destruct (is_less_than a0 b) eqn:E3.
  { simpl. reflexivity.
  }
  simpl.
  set (v := (if ~~ is_less_than a0 c then c :: nil else nil) ++ a0 :: nil).
  apply (pareto_exec_elem_H a b nil). auto.
Qed.

Lemma simpl_elem_par_true :
  forall a b lst, is_less_than a b = true ->
    pareto_by_elem a (pareto (b :: lst)) = pareto_by_elem a (pareto lst).
Proof.
  intros a b lst H.
  generalize dependent b.
  induction lst.
  { intros b H.
    simpl.
    rewrite eq_conv_is_less, H.
    auto.
  }
  { intros b H.
    unfold pareto.
    simpl.
    rewrite eq_conv_is_less.
    destruct (is_less_than a0 b) eqn:E1.
    { unfold flip.
      destruct (compare a0 b) eqn:E2.
      { rewrite is_less_than_Eq in E1; auto.
        rewrite E1. simpl.
        assert (Lem : is_less_than a a0 = true).
        { rewrite (is_less_than_transitivity a b a0); auto.
        }
      unfold pareto in IHlst. simpl in IHlst.
      rewrite IHlst; auto. rewrite IHlst; auto.
      }
      { rewrite is_less_than_Lt in E1; auto.
        apply less_base in E1.
        rewrite E1. auto.
      }
      rewrite is_less_than_Gt in E1; auto.
      discriminate E1.
    }
    { unfold flip.
      assert (Lem: is_less_than b a0 = false -> pareto_by_elem a (pareto_exec (b :: a0 :: nil) lst) = 
      pareto_by_elem a (pareto_exec (a0 :: nil) lst)).
      { intro E2.
        rewrite pareto_exec_destruct; auto.
      }
      simpl.
      destruct (is_less_than b a0) eqn:E2.
      { simpl.
        rewrite (pareto_exec_elem_H a b nil nil); auto.
        rewrite (pareto_exec_elem_H a a0 nil nil).
        reflexivity.
        apply (is_less_than_transitivity a b a0); auto.
      }
      simpl. rewrite pareto_exec_destruct; auto.
    }
  }
Qed.

(* Need correction in proofs*)

(*
Lemma linear_pareto_not_exist :
  forall a lst, is_less_exist a lst = true -> pareto (a::lst) = pareto lst.
Proof.
  intros a lst H.
  unfold pareto. simpl.
  generalize dependent a.
  induction lst.
  {
    intros a H.
    simpl in H. discriminate H.
  }
  { intros b H.
    rewrite is_exist_cons_alt in H.
    destruct H as [A|A].
    { simpl. unfold flip.
      destruct (compare a b) eqn:E1.
      { rewrite is_less_than_Eq in A.
        rewrite A.
      simpl. rewrite eq_conv_is_less.
      rewrite A. simpl. reflexivity.
    }
    { destruct (is_less_than a b) eqn:E1.
      { simpl. unfold flip. rewrite is_less_than_base.
        rewrite eq_conv_is_less. rewrite E1; simpl.
        reflexivity.
      }
      { simpl. unfold flip. rewrite is_less_than_base.
        rewrite eq_conv_is_less. rewrite E1; simpl.
        rewrite IHlst; auto.
        rewrite IHlst. reflexivity.
        assert (Lem1 : is_less_than b a = true).
        { rewrite is_less_than_base, E1. auto.
        }
        rewrite (is_less_exist_transitivity b a lst); auto.
      }
    }
  }
Qed.

Lemma linear_pareto_exist :
  forall a lst (HH : is_less_exist a lst = false),
    pareto (a::lst) = a :: pareto_by_elem a (pareto lst).
Proof.
  intros a lst H.
  unfold pareto. simpl.
  generalize dependent a.
  induction lst.
  { intros a H. auto.
  }
  { intros b H.
    rewrite is_exist_not_cons_alt in H.
    destruct H as [A B].
    simpl. rewrite eq_conv_is_less, A.
    unfold flip. rewrite is_less_than_base, A.
    simpl. rewrite IHlst; auto.
    rewrite <- (simpl_elem_par_true b a).
    auto.
    rewrite is_less_than_base, A.
    auto.
  }
Qed.

Lemma par_elem_one:
  forall a b lst, 
    pareto_by_elem a (pareto_by_elem b lst) = 
    pareto_by_elem b (pareto_by_elem a lst).
Proof.
  intros a b lst.
  induction lst; auto.
  destruct (is_less_than b a0) eqn:E1.
  {
    rewrite -> par_elem2_less; auto.
    rewrite -> IHlst.
    destruct (is_less_than a a0) eqn:E2.
    rewrite -> par_elem2_less; auto.
    rewrite -> par_elem2_not_less; auto.
    rewrite -> par_elem2_less; auto.
  }
  {
    rewrite -> par_elem2_not_less; auto.
    destruct (is_less_than a a0) eqn:E2.
    {
      rewrite -> par_elem2_less; auto.
      rewrite -> IHlst.
      rewrite -> par_elem2_less; auto.
    }
    {
      rewrite -> par_elem2_not_less; auto.
      rewrite -> IHlst.
      rewrite -> par_elem2_not_less; auto.
      rewrite -> par_elem2_not_less; auto.
    }
  }
Qed.

Lemma indent'_linear :
  forall a b sh, is_less_than a b = is_less_than (indent' sh a) (indent' sh b).
Proof.
  intros a b sh.
Admitted.

Lemma main_pred_less :
  forall a b w sh, main_pred w sh a = true /\ main_pred w sh b = false
    -> is_less_than a b = true.
Proof.
  intros a b w sh H.
  unfold main_pred in H.
  destruct H as [A B].
  rewrite (indent'_linear a b sh).
Admitted.

Lemma linear_indent_true :
  forall width sh a b, main_pred width sh a = true ->
    indentDoc width sh (a::b) = (indent' sh a) :: indentDoc width sh b.
Proof.
  intros w sh a lst P.
  unfold indentDoc. unfold filter_map.
  simpl. unfold filter_map_pred.
  rewrite P. reflexivity.
Qed.

Lemma linear_indent_false :
  forall width sh x xs, main_pred width sh x = false ->
    indentDoc width sh (x::xs) = indentDoc width sh xs.
Proof.
  intros w sh x xs P.
  unfold indentDoc, filter_map.
  simpl. unfold filter_map_pred.
  rewrite P. reflexivity.
Qed.

Lemma linear_indent_op :
  forall w sh x xs, main_pred w sh x = true ->
     is_less_exist (indent' sh x) (indentDoc w sh xs) = is_less_exist x xs.
Proof.
  intros w sh x xs H.
  induction xs; auto.
  destruct (main_pred w sh a) eqn:E1.
  { rewrite linear_indent_true; auto.
    destruct (is_less_exist x (a :: xs)) eqn:E2.
    { rewrite is_exist_cons_alt, IHxs.
      rewrite is_exist_cons_alt in E2.
      destruct E2 as [A|A].
      { rewrite <- (indent'_linear a x sh). auto.
      }
      rewrite A. auto.
    }
    rewrite is_exist_not_cons_alt, IHxs.
    rewrite is_exist_not_cons_alt in E2.
    destruct E2 as [A B].
    rewrite <- indent'_linear.
    auto.
  }
  rewrite linear_indent_false; auto.
  rewrite IHxs.
  destruct (is_less_exist x (a :: xs)) eqn:E2.
  {
  rewrite is_exist_cons_alt in E2.
  destruct E2 as [E2'|E2']; auto.
  assert (L : is_less_than x a = true).
  { rewrite (main_pred_less x a w sh).
    reflexivity.
    auto.
  }
  rewrite is_less_than_base in L.
  rewrite E2' in L.
  discriminate L.
  }
  rewrite is_exist_not_cons_alt in E2.
  destruct E2 as [A B].
  auto.
Qed.

Lemma pareto_indent_elem:
  forall a w sh lst, pareto_by_elem (indent' sh a) (indentDoc w sh lst) = 
    indentDoc w sh (pareto_by_elem a lst).
Proof.
  intros a w sh lst.
  induction lst; auto.
  destruct (is_less_than a a0) eqn:E1.
  { rewrite par_elem2_less; auto.
    destruct (main_pred w sh a0) eqn:E2.
    { rewrite linear_indent_true; auto.
      rewrite par_elem2_less, IHlst.
      reflexivity.
      rewrite (indent'_linear a a0 sh) in E1.
      auto.
    }
    rewrite linear_indent_false; auto.
  }
  rewrite par_elem2_not_less; auto.
  destruct (main_pred w sh a0) eqn:E2.
  { rewrite linear_indent_true; auto.
    rewrite par_elem2_not_less, IHlst.
    rewrite linear_indent_true; auto.
    rewrite (indent'_linear a a0 sh) in E1.
    auto.
  }
  rewrite linear_indent_false.
  rewrite linear_indent_false.
  all: auto.
Qed.

Lemma pareto_indent_common : 
  forall sh x w, pareto (indentDoc w sh x) = indentDoc w sh (pareto x).
Proof.
  intros sh lst w.
  induction lst.
  + auto.
  + destruct (main_pred w sh a) eqn:E1.
     rewrite -> linear_indent_true.
     - destruct (is_less_exist a lst) eqn:E2.
       * rewrite ->  linear_pareto_not_exist.
        { rewrite -> IHlst.
          rewrite -> linear_pareto_not_exist.
          reflexivity. apply E2.
        }
        { rewrite linear_indent_op; auto.
        }
       * rewrite ->  linear_pareto_exist.
         { rewrite -> IHlst.
           rewrite ->  linear_pareto_exist.
           rewrite -> linear_indent_true.
           rewrite -> pareto_indent_elem.
           auto. auto. auto. }
         { rewrite -> linear_indent_op; auto.
         }
     - auto.
     - rewrite -> linear_indent_false; auto.
       *  rewrite -> IHlst.
          destruct (is_less_exist a lst) eqn:E2.
          { rewrite ->  linear_pareto_not_exist; auto. }
          { rewrite linear_pareto_exist, linear_indent_false; auto.
            set (lst' := pareto lst).
            induction lst'; auto.
            destruct (is_less_than a a0) eqn:E3.
            { rewrite par_elem2_less; auto.
              rewrite <- IHlst'.
              rewrite linear_indent_false; auto.
              rewrite (as_pred w sh a a0); auto.
            }
            { rewrite par_elem2_not_less; auto.
              destruct (main_pred w sh a0) eqn:E4.
              { rewrite -> linear_indent_true; auto.
                rewrite -> linear_indent_true; auto.
                rewrite IHlst'; auto.
              }
              { rewrite -> linear_indent_false; auto.
                rewrite -> linear_indent_false; auto.
              }
            }
         }
Qed.

Lemma pareto_indent : 
  forall n d width,
    pareto (evaluatorTrival width d) = (evaluatorList width d) -> 
    pareto (indentDoc width n (evaluatorTrival width d)) 
        = indentDoc width n (evaluatorList width d).
Proof.
  intros n d w H1.
  rewrite <- H1.
  apply pareto_indent_common.
Qed.

Definition neighb_pareto (a: Doc) (b: Doc) (w: nat):=
  pareto (evaluatorTrival w a) = (evaluatorList w a) /\
  pareto (evaluatorTrival w b) = (evaluatorList w b).

Lemma pareto_beside :
  forall a b w,
    neighb_pareto a b w ->
    pareto (FormatTrivial.besideDoc w (evaluatorTrival w a) (evaluatorTrival w b)) 
      = FormatList.besideDoc w (evaluatorList w a) (evaluatorList w b).
Proof.
  intros a b w H.
  red in H.
  (* destruct H as [AA BB]. unnw. *)
  unfold neighb_pareto in H.
Admitted.