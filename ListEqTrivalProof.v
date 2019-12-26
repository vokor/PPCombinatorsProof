Require Import Format.
Require Import Doc.
Require Import PrettyPrinter.
Require Import FormatTrivial.
Require Import FormatList.
Require Import String.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.Bool.Bool.

Lemma listEqTrivialProof :
  forall x width,
    (pretty evaluatorTrival width x) = (pretty evaluatorList width x).
Proof.
  intros x.
Admitted.

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
  rewrite IHlst, orbT.
  reflexivity.
Qed.


Lemma is_less_than_transitivity :
  forall a b c, is_less_than a b = true /\ is_less_than b c = true ->
    is_less_than a c = true.
Proof.
  Admitted.

Lemma is_less_than_reflexivity :
  forall a, is_less_than a a = true.
Proof.
  Admitted.
  
Lemma is_less_exist_transitivity_1 :
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
    rewrite C, (is_less_than_transitivity a0 a b); auto.
  }
  simpl. rewrite IHlst, C; auto.
  repeat rewrite orb_true_r.
  reflexivity.
Qed.

Lemma is_less_exist_transitivity_2 :
  forall a b lst, is_less_exist a lst = false /\ is_less_exist b lst = true 
      -> is_less_than a b = true.
Proof.
  intros a b lst H.
  destruct H as [A B].
  rewrite <- B.
  symmetry.
  induction lst. discriminate B.
  destruct (is_less_than a b). auto.
  apply is_exist_not_cons_alt.
  apply is_exist_not_cons_alt in A.
  destruct A as [A1 A2].
  (* discriminate IHlst *)
Admitted.

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

Lemma pareto_by_elem_linear :
  forall a lst lst', pareto_by_elem a (lst ++ lst') = 
    pareto_by_elem a lst ++ pareto_by_elem a lst'.
Proof.
  intros a lst lst'.
  induction lst. auto.
  simpl. 
  rewrite eq_conv_is_less.
  destruct (is_less_than a a0) eqn:E1.
  simpl. apply IHlst.
  simpl. rewrite IHlst. reflexivity.
Qed.

Lemma pareto_by_elem_simpl :
  forall a x xs lst, is_less_than a x = true -> pareto_by_elem a (lst ++ x :: xs) =
    pareto_by_elem a (lst ++ xs).
Proof.
  intros a x xs lst H.
  repeat rewrite pareto_by_elem_linear.
  rewrite par_elem2_less; auto.
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
    assert (L1': is_less_than b a0 = true).
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
    { set (mas:= lst ++ xs). 
      rewrite app_nil_r.
      rewrite <- (app_nil_l mas) at 1.
      rewrite <- (app_nil_l (pareto_by_elem a0 mas)).
      generalize (nil : list t) as mas'.
      induction mas. auto.
      destruct (is_less_than a0 a1) eqn:E3.
      { intro mas'.
        rewrite IHlst', par_elem2_less; auto.
        apply (is_less_than_transitivity a a0 a1).
        rewrite (is_less_than_transitivity a b a0).
        all: auto.
      }
      intro mas'.
      rewrite par_elem2_not_less; auto.
      assert (Rew: forall l, mas' ++ a1::l = (mas' ++ a1::nil) ++ l).
      { intro l. induction mas'. auto.
        simpl. rewrite IHmas'. reflexivity.
      }
      rewrite Rew. rewrite (Rew (pareto_by_elem a0 mas)).
      auto.
    }
    apply (is_less_than_transitivity a b a0).
    all: auto.
  }
  rewrite is_exist_not_cons_all, is_exist_not_cons_alt in E1.
  destruct E1, H1.
  destruct (is_less_exist a0 (lst ++ xs)) eqn:E2.
  { rewrite is_exist_cons_all in E2.
    destruct E2.
    rewrite H0 in H3. discriminate H3.
    rewrite H2 in H3. discriminate H3.
  }
  destruct (is_less_than a0 b) eqn:E3.
  { rewrite pareto_by_elem_simpl; auto.
  }
  repeat rewrite pareto_by_elem_linear.
  rewrite par_elem2_not_less; auto.
  repeat rewrite <- app_assoc.
  rewrite <- app_comm_cons, IHlst'; auto.
Qed.

Lemma pareto_exec_elem_simpl :
  forall a x xs lst', is_less_than a x = true -> pareto_by_elem a (pareto_exec (x :: xs) lst') 
  = pareto_by_elem a (pareto_exec xs lst').
Proof.
  intros a x xs.
  rewrite <- (app_nil_l (x::xs)).
  rewrite <- (app_nil_l xs).
  apply pareto_exec_elem.
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
  intros b H.
  unfold pareto.
  simpl.
  rewrite eq_conv_is_less.
  unfold flip.
  unfold pareto in IHlst. simpl in IHlst.
  destruct (is_less_than a0 b) eqn:E1.
  { simpl.
    destruct (is_less_than b a0) eqn:E2; auto.
    simpl.
    repeat rewrite IHlst.
    all: auto. apply (is_less_than_transitivity a b a0); auto.
  }
  destruct (is_less_than b a0) eqn:E2.
  { simpl.
    repeat rewrite IHlst; auto.
    apply (is_less_than_transitivity a b a0); auto.
  }
  simpl.
  apply pareto_exec_elem_simpl; auto.
Qed.

Notation "lst += a" := (lst ++ (a::nil)) (at level 0).

Lemma pareto_exec_exist :
  forall a lst l r, is_less_exist a lst = true -> pareto_exec lst (l ++ a::r) =
    pareto_exec lst (l ++ r).
Proof.
  intros a lst l r H.
  generalize dependent lst.
  induction l.
  { intros lst H.
    simpl. rewrite H. reflexivity.
  }
  intros lst H.
  simpl.
  destruct (is_less_exist a0 lst) eqn:E1.
  { apply IHl; auto.
  }
  apply IHl.
  apply is_exist_cons_all.
  rewrite is_exist_cons_alt.
  rewrite (is_less_exist_transitivity_2 a0 a lst); auto.
Qed.

Lemma pareto_exec_same : 
  forall lst lst', pareto_exec lst' (lst ++ lst') = pareto_exec lst' lst.
Proof.
  intros lst lst'.
  induction lst.
  { simpl.
    induction lst' using rev_ind. auto.
    simpl. destruct lst'.
    { simpl. unfold flip.
      rewrite is_less_than_reflexivity. simpl.
      reflexivity.
    }
    simpl. unfold flip.
    rewrite is_less_than_reflexivity. simpl.
Admitted.

Lemma linear_pareto_exist :
  forall a lst, is_less_exist a lst = true -> pareto (lst += a) = pareto lst.
Proof.
  intros a lst H.
  unfold pareto.
  generalize dependent (nil: list t).
  induction lst. discriminate H.
  intro lst'.
  rewrite is_exist_cons_alt in H.
  destruct H as [H|H].
  { simpl.
    destruct (is_less_exist a0 lst') eqn:E1.
    { rewrite pareto_exec_exist.
Admitted.
  (*
  assert (link : forall x mas, pareto_by_elem x mas = mas ->
    pareto_exec nil mas = pareto_by_elem x (pareto_exec nil mas)).
  { intros x mas.
    induction mas. auto.
    simpl. rewrite eq_conv_is_less.
    destruct (is_less_than x a0) eqn:E1.
    { simpl.
      
    }
  }
  assert (exist_bigger: forall (mas: list t), exists x, pareto_by_elem x mas = mas).
  { intro mas.
    induction mas.
    simpl. exists empty. reflexivity.
    simpl. 
    
    
  generalize dependent a.
  generalize dependent (nil: list t).
  induction lst.
  {
    intros lst a H.
    simpl in H. discriminate H.
  }
  { intros l b H.
    rewrite is_exist_cons_alt in H.
    simpl. unfold flip.
    destruct H as [A|A].
    { destruct (is_less_than b a) eqn:E1.
      { simpl. admit. (* Here a and b are equals in our context *)
      }
      simpl. rewrite eq_conv_is_less, A. simpl.
      auto.
    }
    destruct (is_less_than b a) eqn:E1.
    { simpl. repeat rewrite IHlst.
      reflexivity.
      apply (is_less_exist_transitivity b a).
      all: auto.
    }
    simpl. rewrite eq_conv_is_less.
    destruct (is_less_than a b) eqn:E2; auto.
    simpl. 
    
        rewrite is_less_than_base.
      
      
      
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
*)

Lemma linear_pareto_not_exist :
  forall a lst (HH : is_less_exist a lst = false),
    pareto (lst += a) = (pareto lst) += a.
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
    simpl.
    Admitted.
   (* rewrite is_less_than_base, A.
    simpl. rewrite IHlst; auto.
    rewrite <- (simpl_elem_par_true b a).
    auto.
    rewrite is_less_than_base, A.
    auto.
  }
Qed. *)

Lemma as_pred :
  forall width sh a b, main_pred width sh a = false /\
    is_less_than a b = true -> main_pred width sh b = false.
Proof.
  intros w sh a b H.
  destruct H as [A B].
Admitted.

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

Lemma linear_indent_true_f :
  forall width sh a b, main_pred width sh a = true ->
    indentDoc width sh (a::b) = (indent' sh a) :: indentDoc width sh b.
Proof.
  intros w sh a lst P.
  unfold indentDoc. unfold filter_map.
  simpl. unfold filter_map_pred.
  rewrite P. reflexivity.
Qed.

Lemma linear_indent_false_f :
  forall width sh x xs, main_pred width sh x = false ->
    indentDoc width sh (x::xs) = indentDoc width sh xs.
Proof.
  intros w sh x xs P.
  unfold indentDoc, filter_map.
  simpl. unfold filter_map_pred.
  rewrite P. reflexivity.
Qed.

Lemma linear_indent_true_e :
  forall w sh a lst, main_pred w sh a = true ->
    indentDoc w sh (lst += a) = (indentDoc w sh lst) += (indent' sh a).
Proof.
  intros w sh a lst P.
  induction lst.
  { simpl. unfold filter_map_pred.
    rewrite P. reflexivity.
  }
  simpl. unfold filter_map_pred.
  destruct (main_pred w sh a0) eqn:E1.
  { simpl. rewrite IHlst. reflexivity.
  }
  apply IHlst.
Qed.

Lemma linear_indent_false_e :
  forall w sh a lst, main_pred w sh a = false ->
    indentDoc w sh (lst += a) = indentDoc w sh lst.
Proof.
  intros w sh a lst P.
  induction lst.
  { simpl. unfold filter_map_pred.
    rewrite P. reflexivity.
  }
  simpl. unfold filter_map_pred.
  destruct (main_pred w sh a0) eqn:E1.
  { simpl. rewrite IHlst. reflexivity.
  }
  apply IHlst.
Qed.

Lemma linear_indent_op :
  forall w sh x xs, main_pred w sh x = true ->
     is_less_exist (indent' sh x) (indentDoc w sh xs) = is_less_exist x xs.
Proof.
  intros w sh x xs H.
  induction xs; auto.
  destruct (main_pred w sh a) eqn:E1.
  { rewrite linear_indent_true_f; auto.
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
  rewrite linear_indent_false_f; auto.
  rewrite IHxs.
  destruct (is_less_exist x (a :: xs)) eqn:E2.
  { rewrite is_exist_cons_alt in E2.
    destruct E2 as [E2|E2]; auto.
    assert (L : is_less_than x a = true).
    { rewrite (main_pred_less x a w sh).
      reflexivity.
      auto.
    }
    assert (D : main_pred w sh x = false).
    { apply (as_pred w sh a x). auto.
    }
    rewrite D in H. discriminate H.
  }
  rewrite is_exist_not_cons_alt in E2.
  destruct E2. apply H1.
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
    { rewrite linear_indent_true_f; auto.
      rewrite par_elem2_less, IHlst.
      reflexivity.
      rewrite (indent'_linear a a0 sh) in E1.
      auto.
    }
    rewrite linear_indent_false_f; auto.
  }
  rewrite par_elem2_not_less; auto.
  destruct (main_pred w sh a0) eqn:E2.
  { rewrite linear_indent_true_f; auto.
    rewrite par_elem2_not_less, IHlst.
    rewrite linear_indent_true_f; auto.
    rewrite (indent'_linear a a0 sh) in E1.
    auto.
  }
  repeat rewrite linear_indent_false_f.
  all: auto.
Qed.

Lemma pareto_indent_common : 
  forall sh lst w, pareto (indentDoc w sh lst) = indentDoc w sh (pareto lst).
Proof.
  intros sh lst w.
  induction lst using rev_ind. auto.
  destruct (main_pred w sh x) eqn:E1.
  { rewrite linear_indent_true_e; auto.
    { destruct (is_less_exist x lst) eqn:E2.
      { rewrite linear_pareto_exist, IHlst, linear_pareto_exist; auto.
        rewrite linear_indent_op; auto.
      }
      repeat rewrite linear_pareto_not_exist.
      rewrite IHlst, linear_indent_true_e.
      all: auto.
      rewrite linear_indent_op.
      all: auto.
    }
  }
  rewrite linear_indent_false_e; auto.
  rewrite IHlst.
  destruct (is_less_exist x lst) eqn:E2.
  { rewrite linear_pareto_exist; auto.
  }
  rewrite linear_pareto_not_exist, linear_indent_false_e; auto.
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