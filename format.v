Require Import ZArith Int.
Require Import String.
Require Import Coq.Lists.List.

Record t : Type := T {
  height           : nat;
  first_line_width : nat;
  middle_width     : nat;
  last_line_width  : nat;
  to_text          : nat -> string -> string
}.

Definition is_less_than  (a:t) (b:t): bool := 
  match a, b with
  | T h1 fw1 m1 lw1 t1, T h2 fw2 m2 lw2 t2 => 
      andb (h1 <=? h2) (andb (fw1 <=? fw2) (andb (m1 <=? m2) (lw1 <=? lw2)))
  end.

Definition compare (f1:t) (f2:t): Z :=
  match is_less_than f1 f2, is_less_than f2 f1 with
  | true, _ => -1 
  | _, true =>  1 
  | _,_     =>  0
  end.

Definition empty: t := T 0 0 0 0 (fun s t => t).

Definition line (nt:string): t := T 1 (String.length nt) (String.length nt) (String.length nt) (fun s t => append nt t).

Definition sp :=
  fix sp_helper n :=
    match n with
    | O    => EmptyString
    | S n' => append " " (sp_helper n')
    end.

(*The return value of this function should be option nat, but I can't use this type in other functions, because they have return value: nat*)
Definition list_max_long (in_list : {in_list : list nat | in_list <> nil}) : nat :=
  match in_list with
  | exist _ x PX =>
    match x with
    | nil => 0 
    | hd :: tl => 1 + fold_left max tl hd
    end
  end. 

Lemma list_max_long_not_0 : forall x, list_max_long x <> 0.
Proof.
  intros [x HH]. unfold list_max_long.
  destruct x.
  { (* intros AA. red in HH. apply HH. reflexivity. *)
    auto. }
  simpl. intros AA. inversion AA.
Qed.

Program Definition list_max (in_list : {in_list : list nat | nil <> in_list}) : nat :=
  match in_list with
  | nil => _
  | hd :: tl => fold_left max tl hd
  end.

(* Analog of list_max. Maybe it will be better? *)
Fixpoint maximum (l:list nat) : nat :=
    match l with
    | nil => O
    | (x::xs) => max x (maximum xs)
    end.

Definition add_above (f1:t) (f2:t): t :=
  match f1, f2 with
  | T h1 fw1 m1 lw1 t1, T h2 fw2 m2 lw2 t2 => 
      match h1, h2 with
       | O, _ => f2
       | _, O => f1
       | _, _ => 
        let middle_with_new :=
           match h1, h2 with
           | 1,1 => fw1
           | 1,2 => fw2
           | 1,_ =>
            (* I can't found analog of 'x when x > 2' (line 59 in format.ml).
               But according to pattern matching 'x' is always > 2. *)
             max fw2 m2
           | 2,1 => lw1
           | _,1 => max m1 lw1
           | _,_ => list_max (exist _ (m1::lw1::fw2::m2::nil)
                                    (@nil_cons _ _ _))
           end
        in T
           (h1 + h2)
           fw1
           middle_with_new
           lw2
           (fun s t => t1 s (append "\n" (append (sp s) (t2 s t))))
           (*The question is how to use operator ++ instead of append?*)
        end
  end.

Definition add_beside (f1:t) (f2:t):t :=
  match f1, f2 with
  | T h1 fw1 m1 lw1 t1, T h2 fw2 m2 lw2 t2 => 
      match h1, h2 with
       | O, _ => f2
       | _, O => f1
       | _, _ => 
        let middle_width_new :=
           match h1, h2 with
           | 1,(1|2) => fw1 + fw2
           | 1,_ => fw1 + m2
           | 2,1 => fw1
           | _,_ => match (andb (3 <=? h1) (h2 =? 1)) with
              | true  => m1
              | false => list_max (m1::(lw1 + fw2)::(lw1 + m2)::nil)
              end
           end
        in
          let first_line_width_new :=
            if (h1 =? 1) then fw1 + fw2 else fw1
          in
            T
            (h1 + h2 - 1)
            first_line_width_new
            middle_width_new 
            (lw1 + lw2)
            (fun s t => t1 s (t2 (s + lw1) t))
        end
  end.

Definition add_fill (f1:t) (f2:t) (shift:nat) :t :=
  match f1, f2 with
  | T h1 fw1 m1 lw1 t1, T h2 fw2 m2 lw2 t2 => 
      match h1, h2 with
       | O, _ => f2
       | _, O => f1
       | _, _ => 
        let middle_width_new :=
           match h1, h2 with
           | 1,(1|2) => fw1 + fw2
           | 1,_ => shift + m2
           | 2,1 => fw1
           | 2,2 => list_max (m1::(lw1 + fw2)::(shift + m2)::nil)
           | 2,_ => max (lw1 + fw2) (shift + m2)
           | _,1 => m1
           | _,2 => max m1 (lw1 + fw2)
           | _,_ => list_max (m1::(lw1 + fw2)::(shift + m2)::nil)
           end
        in
          let first_line_width_new :=
            if (h1 =? 1) then fw1 + fw2 else fw1
          in
            let last_line_width_new := 
              if (h2 =? 1) then lw2 + lw1 else lw2 + shift
            in 
              T
              (h1 + h2 - 1)
              first_line_width_new
              middle_width_new
              last_line_width_new
              (fun s t => t1 s (t2 (s + shift) t))
        end
  end.


Definition to_string (f:t) := 
  match f with
  | T _ _ _ _ to_text => to_text 0 EmptyString
  end.

Definition total_width (f:t) := 
  match f with
  | T h fw m lw f => list_max (fw::m::lw::nil)
  end.

(*This is my realisation of split in Coq. I can't found it in Standart Library*)
Definition split regexp :=
  let
   fix sp_helper pos s:=
     match s with
     | EmptyString => nil
     | String _ s' =>
         match pos with
         | 0 =>
            match index 0 regexp s with
            | Some n => 
               substring 0 n s::
                sp_helper (n + 1) s'
            | None   => s::nil
            end
         | _ => sp_helper (pos - 1) s'
         end
     end
  in sp_helper 0.

Definition of_string s :=
  let 
    lines := split "\n" s
  in
    let
      lineFormats := map line lines
    in fold_left add_above lineFormats empty.

Definition ident shift f :=
  match f with
  | T h fw m lw to_text => T
    h
    (shift + fw)
    (shift + m)
    (shift + lw)
    (fun s t => append (sp shift) (to_text (shift + s) t))
  end.

(* What's level is correct? *)
Notation "a >|< b" := (add_beside a b) (at level 70).
Notation "a >-< b" := (add_above a b) (at level 70).
Notation "a >/< b" := (add_fill a b) (at level 70).
