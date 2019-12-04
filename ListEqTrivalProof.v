Require Import format.
Require Import doc.
Require Import PrettyPrinter.
Require Import formatTrivial.
Require Import formatList.
Require Import String.

Lemma listEqTrivialProof :
  forall x width,
    (pretty evaluatorTrival width x) = (pretty evaluatorList width x).
Proof.
  intros x.
  Abort.


Lemma pareto_text :
  forall x,  
    pareto (formatTrivial.constructDoc x) = formatList.constructDoc x.
Proof.
  intros x.
  unfold formatTrivial.constructDoc.
  unfold formatList.constructDoc.
  reflexivity.
Qed.


Lemma pareto_indent : 
  forall n d width,
    pareto (evaluatorTrival width d) = (evaluatorList width d) -> 
    pareto (indentDoc width n (evaluatorTrival width d)) 
        = indentDoc width n (evaluatorList width d).
Proof.
  intros n d w H1.
  rewrite <- H1.

  