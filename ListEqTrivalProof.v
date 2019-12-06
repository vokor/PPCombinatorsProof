Require Import format.
Require Import doc.
Require Import PrettyPrinter.
Require Import formatTrivial.
Require Import formatList.
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
    pareto (formatTrivial.constructDoc x) = formatList.constructDoc x.
Proof.
  intros x.
  unfold formatTrivial.constructDoc.
  unfold formatList.constructDoc.
  reflexivity.
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

Lemma linear_indent_op_t :
  forall w sh x xs, andb (is_exist x xs) (main_pred w sh x) = true ->
     is_exist (indent' sh x) (indentDoc w sh xs) = true.
Admitted.

Lemma linear_indent_op_f :
  forall w sh x xs, andb (negb (is_exist x xs)) (main_pred w sh x) = true ->
     is_exist (indent' sh x) (indentDoc w sh xs) = false.
Admitted.

Lemma linear_pareto_not_exist :
  forall a lst, is_exist a lst = true -> pareto (a::lst) = pareto lst.
Admitted.

Lemma linear_pareto_exist :
  forall a lst, is_exist a lst = false -> pareto (a::lst) = a :: (pareto lst).
Proof.
  intros a lst H.
  induction lst.
  + unfold pareto.
    unfold pareto_exec. rewrite -> H.
    simpl. reflexivity.
  +
Admitted.

Lemma pareto_indent_common : 
  forall sh x w, pareto (indentDoc w sh x) = indentDoc w sh (pareto x).
Proof.
  intros sh lst w.
  induction lst.
  + auto.
  + destruct (main_pred w sh a) eqn:E1.
     rewrite -> linear_indent_true.
     - destruct (is_exist a lst) eqn:E2.
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
           auto. auto. auto.
         }
         {  rewrite -> linear_indent_op_f.
            auto. rewrite -> E1. rewrite E2. auto.
         }
     - auto.
     - rewrite -> linear_indent_false.
       * destruct (is_exist a lst) eqn:E2.
         { rewrite ->  linear_pareto_not_exist.
           rewrite -> IHlst.
           auto. auto.
         }
         { rewrite -> linear_pareto_exist.
           rewrite -> IHlst.
           rewrite -> linear_indent_false.
           auto. auto. auto.
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
