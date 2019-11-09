Require Import format.
Open Scope list_scope.
Load Doc.

Module formatTrival.
Export Format Doc.

Definition cross_general (width: nat) (op: t -> t -> t) (fl1: list t) (fl2: list t) :=
  List.filter 
    (fun f => total_width f <=? width)
    (List.concat (map (fun f => map (op f) fl2) fl1)).

Definition blank_line := (line "")::nil.

(* Shift each block to 'shift' positions right *)
Definition indentDoc (shift: nat) (fs: list t) :=
  map (indent' shift) fs.

(* Construct document from 'string' using 'above' rule *)
Definition constructDoc (s: string) := (of_string s)::nil.

(* Use 'beside' rule for 2 documents. New document ~ n x m *)
Definition besideDoc (width: nat) (fs1: list t) (fs2: list t) := 
  cross_general width add_beside fs1 fs2.

(* Use 'above' rule for 2 documents. New document ~ n x m *)
Definition aboveDoc (width: nat) (fs1: list t) (fs2: list t) := 
   cross_general width add_above fs1 fs2.

(* 'Fill' rule *)
Definition fillDoc (width: nat) (fs1: list t) (fs2: list t) (shift: nat) :=
   cross_general width (fun fs f => add_fill fs f shift) fs1 fs2.

(* Choice operation *)
Definition choiceDoc (fs1: list t) (fs2: list t) := 
    fs1 ++ fs2.

Fixpoint EvaluatorTrival (width: nat) (doc: Doc): list t:=
  match doc with
  | Text s     => constructDoc s
  | Indent n d => indentDoc n (EvaluatorTrival width d)
  | Beside a b => besideDoc width (EvaluatorTrival width a) (EvaluatorTrival width b)
  | Above a b  => aboveDoc width (EvaluatorTrival width a) (EvaluatorTrival width b)
  | Choice a b => choiceDoc (EvaluatorTrival width a) (EvaluatorTrival width b)
  | Fill a b n => fillDoc width (EvaluatorTrival width a) (EvaluatorTrival width b) n
  end.

End formatTrival.