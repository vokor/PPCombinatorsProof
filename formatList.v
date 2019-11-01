Load format.
Open Scope list_scope.

Definition map_filter (mapf: t -> t) (filterf: t -> bool) (l: list t): list t := 
  fold_left
    (fun lst a => let b := mapf a in
                  if (filterf b)
                  then cons b lst
                  else lst
    )
    l nil.

Definition filter_map (filterf: t -> bool) (mapf: t -> t) (l: list t): list t :=
  fold_left
    (fun lst a => if filterf a
                  then cons (mapf a) lst
                  else lst
    )
    l nil.

Record pair : Type := Pair {
  fst : nat;
  snd: list t
}.

(*Сonstructs a list of elements if their number satisfying the predicate*)
Definition filteri (filterf: nat -> bool) (lst: list t): list t := 
  let (_, result) := 
    fold_left
      (fun p a => match p with
         | Pair n lst => Pair (n + 1) (if filterf n then cons a lst else lst)
         end )
      lst (Pair 0 nil) in
  result.

Fixpoint makeList (len:nat) (a: bool): list bool :=
    match len with
      | 0 => nil
      | S len => a :: (makeList len a)
    end.

Fixpoint updateHelper (cur: nat) (lst: list bool) (val: bool) (pos: nat): list bool:=
    match lst with
    | a::b => if pos =? cur then 
          val::b else
          a:: updateHelper pos b val (cur + 1)
    | nil => nil
    end.

Definition update := updateHelper 0.

Fixpoint inner_iteri (lstt: list t) (lstb: list bool) (pos1: nat) (pos2: nat) (val: t): list bool :=
  match lstt with
    | (a::b) => let inner_lst :=
        if (andb (pos1 <? pos2) (nth pos2 lstb false)) then
            match compare val a with
              | Lt => update lstb false pos2
              | Gt => update lstb false pos1
              | Eq => lstb
            end
        else lstb
      in inner_iteri b inner_lst pos1 (pos2 + 1) val
    | nil => lstb
  end.

Fixpoint outer_iteri (lst: list t) (allLst: list t) (listb: list bool) (pos: nat): list bool :=
  match lst with
    | (a::b) => let newList := if (nth pos listb false) then
            (inner_iteri allLst listb pos 0 a) else listb
        in outer_iteri b allLst newList (pos + 1)
    | nil => listb
  end.

(* Remove the worst performing Docs *)
Definition factorize (lst: list t): list t:=
  let flags := makeList (length lst) true in
  let modifyFlags := outer_iteri lst lst flags 0 in
  filteri (fun i => (nth i modifyFlags false)) lst.

(*Сonstruct a list of elements satisfying the predicate*)
Definition add_general (op: t -> t -> t) (width: nat) (fl: list t) (f: t): list t :=
  map_filter (fun f' => op f' f)
             (fun f => total_width f <=? width)
              fl.

(* Apply operator each with each, check predicate, construct new list, O(n^2) *)
Definition cross_general (op: t -> t -> t) (width: nat) (fl1: list t) (fl2: list t) :=
  let cross_lst := concat (map (add_general op width fl1) fl2) in
  factorize cross_lst.

Record t' : Type := T' {
  width   : nat;
  lst     : list t
}.


(* Shift each block to 'shift' positions right *)
Definition indentDoc (shift: nat) (fs: t') :=
    T'
    fs.(width)
   (filter_map (fun f => total_width f + shift <=? fs.(width))
                       (indent' shift)
                       fs.(lst)).

Definition default_width := 100.

Definition initial: t':=
   T'
   default_width
   (empty::nil).

Definition blank_line :=
   T'
   default_width
   ((line "")::nil).

(* Construct document from 'string' using 'above' rule *)
Definition constructDoc (s: string) := 
    T'
    default_width
    ((of_string s)::nil).

(* Remove blocks with height < n *)
Definition removeDoc (fs: t') (n: nat) := 
    T'
    fs.(width)
    (filter (fun f => f.(height) <? n) fs.(lst)).

(* Use 'beside' rule for 2 documents. New document ~ n x m *)
Definition besideDoc (fs1: t') (fs2: t') := 
    T'
    fs1.(width)
    (cross_general add_beside fs1.(width) fs1.(lst) fs2.(lst)).

(* Add one space at the end of each block in first Doc. Union 2 Docs*)
Definition unionDoc (fs1: t') (fs2: t') := 
  besideDoc fs1 (besideDoc (constructDoc " "%string) fs2).

(* Use 'above' rule for 2 documents. New document ~ n x m *)
Definition aboveDoc (fs1: t') (fs2: t') := 
    T'
    fs1.(width)
    (cross_general add_above fs1.(width) fs1.(lst) fs2.(lst)).

(* 'Fill' rule *)
Definition fillDoc (fs1: t') (fs2: t') (shift: nat) :=
    T'
    fs1.(width)
   (cross_general (fun fs f => add_fill fs f shift)
                  fs1.(width) fs1.(lst) fs2.(lst)).

(* Choice operation *)
Definition choiceDoc (fs1: t') (fs2: t') := 
    T'
    (max fs1.(width) fs2.(width))
    (factorize (fs1.(lst) ++ fs2.(lst))).

(* Pick with minimum height *)
Definition pick_best (t : {t : t' | nil <> lst t}) :=
  match t with
  | exist _ x _ =>
    match x.(lst) with
    | nil => empty
    | hd :: tl => fold_left (fun best f =>
        if f.(height) <? best.(height)
        then f
        else best)
      tl hd
    end
  end.

Program Definition to_string' (t:t') :=
  match t.(lst) with
  | nil => "Empty set of strings to choose from."%string
  | _ => to_string (pick_best t)
  end.