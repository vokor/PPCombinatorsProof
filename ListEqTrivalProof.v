Require Import Format.
Require Import Doc.
Require Import PrettyPrinter.
Require Import FormatTrivial.
Require Import FormatList.
Require Import String.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.

Lemma listEqTrivialProof :
  forall x width,
    (pretty evaluatorTrival width x) = (pretty evaluatorList width x).
Proof.
  intros x.
Admitted.

Lemma is_less_than_base :
  forall a b, is_less_than a b = negb (is_less_than b a).
Proof.
  intros a b.
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

Lemma linear_indent_true :
  forall width sh a b, main_pred width sh a = true ->
    indentDoc width sh (a::b) = (indent' sh a) :: indentDoc width sh b.
Proof.
Admitted.

Lemma as_pred :
  forall width sh a b, main_pred width sh a = false /\
    is_less_than a b = true -> main_pred width sh b = false.
Proof.
  intros w sh a b H.
  destruct H as [A B].
Admitted.

Lemma linear_indent_false :
  forall width sh a b, main_pred width sh a = false ->
    indentDoc width sh (a::b) = indentDoc width sh b.
Proof.
intros w a x xs P.
unfold indentDoc.
unfold filter_map.
Admitted.

Lemma pareto_indent_elem:
  forall a w sh lst, pareto_by_elem (indent' sh a) (indentDoc w sh lst) = 
    indentDoc w sh (pareto_by_elem a lst).
Proof.
Admitted.

Lemma linear_indent_op_t :
  forall w sh x xs, (is_less_exist x xs) = true /\ (main_pred w sh x) = true ->
     is_less_exist (indent' sh x) (indentDoc w sh xs) = true.
Admitted.

Lemma linear_indent_op_f :
  forall w sh x xs, is_less_exist x xs = false /\ (main_pred w sh x) = true ->
     is_less_exist (indent' sh x) (indentDoc w sh xs) = false.
Proof.
  intros w sh x xs H.
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

Lemma is_less_than_transitivity :
  forall a b c, is_less_than a b = true /\ is_less_than b c = true ->
    is_less_than a c = true.
Proof.
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
    { unfold flip. rewrite is_less_than_base, E1.
      auto.
    }
    { unfold flip. rewrite is_less_than_base, E1.
      simpl.
      unfold pareto in IHlst. simpl in IHlst.
      rewrite IHlst; auto.
      rewrite IHlst. reflexivity.
      rewrite (is_less_than_transitivity a b a0). reflexivity.
      rewrite H, is_less_than_base, E1; auto.
    }
  }
Qed.

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
      rewrite is_less_than_base. rewrite A.
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
        { apply linear_indent_op_t.
          rewrite -> E1. rewrite -> E2. auto.
        }
       * rewrite ->  linear_pareto_exist.
         { rewrite -> IHlst.
           rewrite ->  linear_pareto_exist.
           rewrite -> linear_indent_true.
           rewrite -> pareto_indent_elem.
           auto. auto. auto. }
         { rewrite -> linear_indent_op_f.
           auto. rewrite -> E1. rewrite E2. auto.
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