Load format.

Definition cons (a:t) (lst: list t):= a :: lst.

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

Definition add_general (op: t -> t -> t) (width: nat) (fl: list t) (f: t): list t :=
  map_filter (fun f' => op f' f)
             (fun f => total_width f <=? width)
              fl.

Record pair : Type := Pair {
  fst : nat;
  snd: list t
}.

Definition filteri (filterf: nat -> bool) (lst: list t) := 
  let (_, result) := 
    fold_left
      (fun p a => match p with
         | Pair n lst => Pair (n + 1) (if (filterf n) then cons a lst else lst)
         end )
      lst (Pair 0 nil) in
  result.


Fixpoint makeList (len:nat) (a: bool): list bool :=
    match len with
      | 0 => nil
      | S len => a :: (makeList len a)
    end.

Fixpoint update (lst: list bool) (val: bool) (cur: nat) (pos:nat): list bool:=
  match lst with
  | (a::b) => if (pos =? cur) then 
        (val::(update b val (cur + 1) pos)) else
        (a::(update b val (cur + 1) pos))
  | nil => nil
  end.

(*My realisation of interi*)
Fixpoint inner_iteri (lstt: list t) (lstb: list bool) (pos1: nat) (pos2: nat) (val: t): list bool := 
  match lstt with
    | (a::b) => let inner_lst :=
        if (andb (pos1 <? pos2) (nth pos2 lstb false)) then
            match compare val a with
              | Lt => update lstb false 0 pos2
              | Gt => update lstb false 0 pos1
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

Definition factorize (lst: list t) :=
  let flags := makeList (length lst) true in
  let modifyFlags := outer_iteri lst lst flags 0 in
  filteri (fun i => (nth i modifyFlags false)) lst.

Definition cross_general (op: t -> t -> t) (width: nat) (fl1: list t) (fl2: list t) :=
  let cross_lst := concat (map (add_general op width fl1) fl2) in
  factorize cross_lst.

Record t' : Type := T' {
  width   : nat;
  lst     : list t
}.

Notation ">>" := (fun shift fs => 
    T'
    fs.(width)
   (filter_map (fun f => total_width f <=? fs.(width) - shift)
                       (indent shift)
                       fs.(lst))).

(*Why in original code was let default_width = ref 100? What means ref?*)
Definition default_width := 100.

Definition initial :=
   T'
   default_width
   (empty::nil).

Definition blank_line :=
   T'
   default_width
   ((line "")::nil).

Notation "!" := (fun s => 
    T'
    default_width
    ((of_string s)::nil)).

Notation "^" := (fun fs n => 
    T'
    fs.(width)
    (filter (fun f => f.(height) <? n) fs.(lst))).

Notation ">|<" := (fun fs1 fs2 => 
    T'
    fs1.(width)
    (cross_general add_beside fs1.(width) fs1.(lst) fs2.(lst))).

Notation ">||<" := (fun fs1 fs2 => fs1 >|< !(" "%string) >|< fs2).

Notation ">-<" := (fun fs1 fs2 => 
    T'
    fs1.(width)
    (cross_general add_above fs1.(width) fs1.(lst) fs2.(lst))).

Notation ">--<" := (fun fs1 fs2 => fs1 >-< blank_line >-< fs2).

Notation ">/<" := (fun fs1 fs2 shift => 
    T'
    fs1.(width)
   (cross_general (fun fs f => add_fill fs f shift)
                  fs1.(width) fs1.(lst) fs2.(lst))).

Notation ">?<" := (fun fs1 fs2 => 
    T'
    max fs1.(width) fs2.(width)
    (factorize (fs1.(lst)::fs2.(lst)))).

(*Remove Exception: Empty set of strings to choose from.*)
(*hd and tl in OCaml means hd::tl ?*)
Definition pick_best (t: t') :=
  match t.(lst) with
  | (hd::tl) => fold_left (fun best f =>
        if f.(height) <? best.(height)
        then f
        else best)
      tl hd
  | nil => empty
  end.

(*
In process. Will be something like this if need

Definition pick_best' (t : {t : t' | nil <> t.(lst)}) :=
  match t.(lst) with
  | exist _ x _ =>
    match x with
    | nil => empty
    | hd :: tl => fold_left (fun best f =>
        if f.(height) <? best.(height)
        then f
        else best)
      tl hd
    end
  end.
*)
Definition to_string' (t:t') := to_string (pick_best t).





























