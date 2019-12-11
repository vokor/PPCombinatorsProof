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

Lemma pareto_text :
  forall x,
    pareto (FormatTrivial.constructDoc x) = FormatList.constructDoc x.
Proof.
  intros x.
  unfold FormatTrivial.constructDoc.
  unfold FormatList.constructDoc.
  reflexivity.
Qed.

Lemma leb_correct :
  forall a, PeanoNat.Nat.leb a a = true.
Proof.
  intro a.
  (* apply leb_le. *)
Admitted.

Lemma symmetry_is_less_than :
  forall a, is_less_than a a = true.
Proof.
  intro a.
  unfold is_less_than.
  rewrite -> leb_correct.
  rewrite -> leb_correct.
  rewrite -> leb_correct.
  rewrite -> leb_correct.
  auto.
Qed.

Lemma linear_indent_true :
  forall width sh a b, main_pred width sh a = true ->
    indentDoc width sh (a::b) = (indent' sh a) :: indentDoc width sh b.
Proof.
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
  forall w sh x xs, andb (is_less_exist x xs) (main_pred w sh x) = true ->
     is_less_exist (indent' sh x) (indentDoc w sh xs) = true.
Admitted.

Lemma linear_indent_op_f :
  forall w sh x xs, andb (negb (is_less_exist x xs)) (main_pred w sh x) = true ->
     is_less_exist (indent' sh x) (indentDoc w sh xs) = false.
Admitted.

Lemma linear_pareto_not_exist :
  forall a lst, is_less_exist a lst = true -> pareto (a::lst) = pareto lst.
Admitted.

  (* is_exist a (h :: l) <-> *)
  (* is_less_than a h \/ is_exist a l. *)
Lemma is_exist_not_cons_alt a h l  :
  is_less_exist a (h :: l) = false <->
  is_less_than a h = false /\ is_less_exist a l = false.
Proof.
Admitted.

Lemma eq_conv_is_less :
  forall a b,
    (compose negb (is_less_than a)) b = negb (is_less_than a b).
Proof.
  intros a b.
  unfold compose.
  reflexivity.
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

Lemma linear_pareto_exist :
  forall a lst (HH : is_less_exist a lst = false),
    pareto (a::lst) = a :: pareto_by_elem a (pareto lst).
Proof.
  intros a lst HH.
  induction lst; auto.
  rewrite is_exist_not_cons_alt in HH.
  destruct HH as [A B].
  destruct (is_less_exist a lst) eqn:E1.
  discriminate B.
Admitted.
  
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

Lemma par_elem_less :
  forall a lst, is_less_exist a lst = false ->
    pareto_by_elem a (pareto lst) = pareto lst.
Proof.
  intros a lst H.
  induction lst.
  auto.
  rewrite is_exist_not_cons_alt in H.
  destruct H as [A B].
  destruct (is_less_exist a0 lst) eqn:E1.
  rewrite -> linear_pareto_not_exist; auto.
  rewrite -> linear_pareto_exist; auto.
  rewrite -> par_elem2_not_less; auto.
  rewrite -> par_elem_one.
  rewrite -> IHlst; auto.
Qed.

Lemma par_less :
  forall a lst, is_less_exist a lst = false ->
   is_less_exist a (pareto lst) = false.
Proof.
  intros a lst H.
  induction lst.
  auto.
  destruct (is_less_exist a0 lst) eqn:E1.
  {
    rewrite -> linear_pareto_not_exist.
    rewrite is_exist_not_cons_alt in H.
    destruct H as [A B].
    apply IHlst. auto. auto.
  }
  {
    rewrite -> linear_pareto_exist; auto.
    rewrite -> is_exist_not_cons_alt.
    rewrite is_exist_not_cons_alt in H.
    destruct H as [A B].
    rewrite -> par_elem_less; auto.
  }
Qed.

Lemma pred_filter :
  forall predicate a (lst: list t),
    predicate a = true -> filter predicate (a::lst) = a :: (filter predicate lst).
Proof.
  intros P a lst H.
  simpl. rewrite -> H. reflexivity.
Qed.

Lemma relat_less_compose :
  forall a lst,
    is_less_exist a lst = false -> lst = pareto_by_elem a lst.
Proof.
  intros a lst H.
  unfold pareto_by_elem.
  induction lst.
  auto.
  apply is_exist_not_cons_alt in H.
  destruct H as [A B].
  destruct (compose negb (is_less_than a) a0) eqn:E2.
  {
    rewrite pred_filter.
    rewrite <- IHlst.
    auto. auto. auto.
  }
  {
    rewrite eq_conv_is_less in E2.
    rewrite A in E2.
    discriminate E2.
  }
Qed.

Lemma relat_lst_and_elem : 
  forall a lst, is_less_exist a lst = false ->
    pareto lst = pareto_by_elem a (pareto lst).
Proof.
  intros a lst H.
  apply par_less in H.
  apply relat_less_compose.
  apply H.
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
          rewrite -> E1. rewrite -> E2. reflexivity.
        }
       * rewrite ->  linear_pareto_exist.
         { rewrite -> IHlst.
           rewrite ->  linear_pareto_exist.
           rewrite -> linear_indent_true.
           rewrite -> pareto_indent_elem.
           auto. auto. auto.
         }
         {  rewrite -> linear_indent_op_f.
            auto. rewrite -> E1. rewrite E2. auto.
         }
     - auto.
     - rewrite -> linear_indent_false.
       * destruct (is_less_exist a lst) eqn:E2.
         { rewrite ->  linear_pareto_not_exist.
           rewrite -> IHlst.
           auto. auto.
         }
         { rewrite -> linear_pareto_exist.
           rewrite -> IHlst.
           rewrite -> linear_indent_false.
           rewrite <- relat_lst_and_elem.
           auto.
           apply E2. apply E1. apply E2.
         }
       * auto.
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
