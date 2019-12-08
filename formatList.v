Require Import Format.
Require Import Doc.

Open Scope list_scope.
Require Import ZArith Int.
Require Import Coq.Lists.List.
Require Import String.

Definition map_filter (mapf: t -> t) (filterf: t -> bool) (l: list t): list t := 
  fold_left
    (fun lst a => let b := mapf a in
                  if (filterf b)
                  then cons b lst
                  else lst
    )
    l nil.

Require Import Coq.Program.Basics.

(* I mean does exist B from lst : B < A *)
Definition is_less_exist (a: t) (lst: list t) : bool :=
  existsb ((flip is_less_than) a) lst.

(* Remove all elements > a *)
Definition pareto_by_elem (a: t) (lst: list t) :=
  filter (compose negb (is_less_than a)) lst.

Fixpoint pareto_exec (acc: list t) (mas: list t): list t :=
      match mas with
      | x::xs => if (is_less_exist x acc) then
            pareto_exec acc xs
         else pareto_exec (x :: pareto_by_elem x acc) xs 
      | nil   => acc
      end.

(* Remove the worst performing Docs *)
Definition pareto (lst: list t): list t:= pareto_exec nil lst. 

(*Сonstruct a list of elements satisfying the predicate*)
Definition add_general (op: t -> t -> t) (width: nat) (fl: list t) (f: t): list t :=
  map_filter (fun f' => op f' f)
             (fun f => total_width f <=? width)
              fl.

(* Apply operator each with each, check predicate, construct new list, O(n^2) *)
Definition cross_general (op: t -> t -> t) (width: nat) (fl1: list t) (fl2: list t) :=
  let cross_lst := List.concat (map (add_general op width fl1) fl2) in
  pareto cross_lst.

(* Construct document from 'string' using 'above' rule *)
Definition constructDoc (s: string) := (of_string s)::nil.

(* Use 'beside' rule for 2 documents. New document ~ n x m *)
Definition besideDoc (width: nat) (fs1: list t) (fs2: list t) := 
  cross_general add_beside width fs1 fs2.

(* Use 'above' rule for 2 documents. New document ~ n x m *)
Definition aboveDoc (width: nat) (fs1: list t) (fs2: list t) := 
   cross_general add_above width fs1 fs2.

(* 'Fill' rule *)
Definition fillDoc (width: nat)(fs1: list t) (fs2: list t) (shift: nat) :=
   cross_general (fun fs f => add_fill fs f shift)
                  width fs1 fs2.

(* Choice operation *)
Definition choiceDoc (fs1: list t) (fs2: list t) := 
    (pareto (fs1 ++ fs2)).

Fixpoint evaluatorList (width: nat) (doc: Doc): list t:=
  match doc with
  | Text s     => constructDoc s
  | Indent n d => indentDoc width n (evaluatorList width d)
  | Beside a b => besideDoc width (evaluatorList width a) (evaluatorList width b)
  | Above a b  => aboveDoc width (evaluatorList width a) (evaluatorList width b)
  | Choice a b => choiceDoc (evaluatorList width a) (evaluatorList width b)
  | Fill a b n => fillDoc width (evaluatorList width a) (evaluatorList width b) n
  end.
