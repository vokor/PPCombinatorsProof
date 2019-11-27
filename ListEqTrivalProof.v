Require Import format.
Require Import doc.
Require Import PrettyPrinter.
Require Import formatTrivial.
Require Import formatList.

Definition default_width := 100.

Lemma ListEqTrivialProof :
  forall x: Doc,
    (pretty EvaluatorTrival default_width x) = (pretty EvaluatorList default_width x).
Proof.
  intros x.
  Abort.