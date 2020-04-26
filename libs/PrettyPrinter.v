Require Import Format.
Require Import Doc.

Require Import ZArith Int.
Require Import Coq.Lists.List.
Require Import String.

Fixpoint get_min_height (lst : list t) (w: nat) (res: option nat) :=
  match lst with
  | nil => res
  | hd :: tl => if total_width hd <=? w
                then match res with
                     | Some n => get_min_height tl w (Some (min n hd.(height)))
                     | None => get_min_height tl w (Some hd.(height))
                     end
                else get_min_height tl w res
  end.
                    
Definition pick_best_list (lst : list t) (w: nat) :=
  match lst with
  | nil => nil
  | _   =>  match get_min_height lst w None with
            | None   => nil
            | Some n => filter
                          (fun f => andb (total_width f <=? w) (f.(height) =? n))
                          lst
            end
  end.

Definition pretty_list (docToVar: nat -> Doc -> list t) (width: nat) (doc: Doc) :=
  pick_best_list (docToVar width doc) width.
