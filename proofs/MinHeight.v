From hahn Require Import Hahn.
Require Import Format.
Require Import IsLess.
Require Import FuncCorrect.
Require Import PrettyPrinter.
Require Import FormatList.

Require Import String.
Require Import ZArith Int.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.Bool.Bool.
Require Import Coq.ssr.ssrbool.

Lemma min_leb a b
      (H: a < b) : min b a = a.
Proof.
  destruct a.
  { apply Nat.min_0_r. }
  apply NPeano.Nat.min_r_iff.
  apply Nat.lt_le_incl.
  apply H.
Qed.

Lemma get_height_less a x lst w
      (P: height a <= height x) :
  get_min_height (lst ++ [x]) w (Some (height a)) = get_min_height lst w (Some (height a)).
Proof.
  generalize dependent a.
  induction lst. 
  { ins.
    destruct (total_width x <=? w) eqn: E1.
    { rewrite NPeano.Nat.min_l; auto. }
    reflexivity. }
  ins.
  destruct (total_width a <=? w) eqn:E1.
  { destruct (height a0 <=? height a) eqn:E2.
    { apply leb_complete in E2.
      rewrite Nat.min_l; auto. }
    apply leb_iff_conv in E2.
    rewrite min_leb; auto.
    apply IHlst.
    apply Nat.lt_le_incl.
    apply (Nat.lt_le_trans _ (height a0)); auto. }
  apply IHlst; auto.
Qed.    

Require Import Lia.

Lemma get_height_to_none a b lst w
      (H: total_width a <= w)
      (P: height a <= height b) :
  get_min_height (lst ++ [a]) w (Some (height b)) = get_min_height (lst ++ [a]) w None.
Proof.
  generalize dependent b.
  generalize dependent a.
  induction lst.
  { ins.
    desf.
    { rewrite NPeano.Nat.min_r; auto. }
    apply Nat.leb_gt in Heq.
    lia. }
  ins.
  desf.
  { destruct (height b <=? height a) eqn:E1.
    { apply leb_complete in E1.
      rewrite NPeano.Nat.min_l; auto.
      repeat rewrite IHlst; auto.
      apply (NPeano.Nat.le_trans _ (height b)); auto. }
    apply leb_iff_conv in E1.
    rewrite min_leb; auto. }
  apply IHlst; auto.
Qed.      

Lemma get_height_none a lst w
      (H: (total_width a <=? w) = false) :
  forall (o: option nat),
  get_min_height (lst ++ [a]) w o = get_min_height lst w o.
Proof.
  induction lst.
  { simpls.
    desf. }
  ins.
  desf.
Qed.

Lemma get_height_exist a x w lst
      (C: list_correct lst)
      (F: format_correct x)
      (H: is_less_exist x lst = true) :
  get_min_height lst w (Some (height a)) =
  get_min_height (lst ++ [x]) w (Some (height a)).
Proof.
  apply is_exist_eq in H.
  desf.
  assert (height b > 0).
  { apply C; auto. }
  generalize dependent b.
  generalize dependent a.
  induction lst.
  { done. }
  ins.
  assert (height a > 0 /\ height x > 0).
  { split.
    { apply C.
      done. }
    apply F. }
  unfold is_less_than in H0.
  unfold less_components in H0. 
  desf.
  all: try lia.
  all: andb_split.
  all: apply leb_complete in H0.
  all: apply leb_complete in H4.
  all: apply leb_complete in H5.
  all: try apply leb_complete in H.
  { destruct (height a0 <=? height b) eqn:E1.
    { apply leb_complete in E1.
      rewrite Min.min_l; auto.
      { rewrite get_height_less.
        { reflexivity. }
        lia. }
      lia. }
    apply Nat.leb_gt in E1.
    rewrite min_leb.
    { rewrite <- Heq1.
      rewrite get_height_less; auto. }
    lia. }
  { destruct (height a0 <=? height b) eqn:E1.
    { apply leb_complete in E1.
      rewrite Min.min_l; auto.
      { rewrite get_height_less.
        { reflexivity. }
        lia. }
      lia. }
    apply Nat.leb_gt in E1.
    rewrite min_leb.
    { rewrite <- Heq0.
      rewrite get_height_less; auto.
      lia. }
    lia. }
  { rewrite get_height_none; auto.
    apply Nat.leb_gt.
    apply Nat.leb_gt in Heq.
    unfold total_width in *.
    desf.
    simpls.
    lia. }
  { rewrite get_height_none; auto.
    apply Nat.leb_gt.
    apply Nat.leb_gt in Heq.
    unfold total_width in *.
    desf.
    simpls.
    lia. }
  { apply list_correct_add_b in C.
    desf.
    destruct (height a0 <=? height a) eqn:E1.
    { apply leb_complete in E1.
      rewrite Min.min_l; auto.
      apply (IHlst C _ b); auto.
      { unfold is_less_than.
        desf.
        unfold less_components.
        apply leb_complete in H6.
        repeat (apply andb_true_iff; split).
        all: apply NPeano.Nat.leb_le; auto.
        lia. }
      lia. }
    apply Nat.leb_gt in E1.
    rewrite min_leb; auto.
    apply (IHlst C _ b); auto.
    unfold is_less_than.
    desf.
    unfold less_components.
    apply leb_complete in H6.
    repeat (apply andb_true_iff; split).
    all: apply NPeano.Nat.leb_le; auto.
    { lia. }
    apply NPeano.Nat.leb_le.
    lia. }
  { apply list_correct_add_b in C.
    desf.
    destruct (height a0 <=? height a) eqn:E1.
    { apply leb_complete in E1.
      rewrite Min.min_l; auto.
      apply (IHlst C _ b); auto.
      { unfold is_less_than.
        desf.
        unfold less_components.
        apply leb_complete in H6.
        repeat (apply andb_true_iff; split).
        all: apply NPeano.Nat.leb_le; auto.
        lia. }
      lia. }
    apply Nat.leb_gt in E1.
    rewrite min_leb; auto.
    apply (IHlst C _ b); auto.
    unfold is_less_than.
    desf.
    unfold less_components.
    apply leb_complete in H6.
    repeat (apply andb_true_iff; split).
    all: apply NPeano.Nat.leb_le; auto.
    { lia. }
    apply NPeano.Nat.leb_le.
    lia. }
  { apply list_correct_add_b in C.
    desf.
    apply (IHlst C _ b); auto.
    { unfold is_less_than.
      desf.
      unfold less_components.
      apply leb_complete in H6.
      repeat (apply andb_true_iff; split).
      all: apply NPeano.Nat.leb_le; auto.
      lia. }
    lia. }
  apply list_correct_add_b in C.
  desf.
  apply (IHlst C _ b); auto.
  { unfold is_less_than.
    desf.
    unfold less_components.
    apply leb_complete in H6.
    repeat (apply andb_true_iff; split).
    all: apply NPeano.Nat.leb_le; auto.
    lia. }
  lia. 
Qed.

Lemma height_some_none a b lst w
      (H: total_width b <= w)
      (K: height b <= height a)
      (P: total_width a <= w) :
  get_min_height (lst ++ [b]) w (Some (height a)) =
  get_min_height (lst ++ [b]) w None.
Proof.
  induction lst.
  { simpl.    
    desf.
    { rewrite NPeano.Nat.min_r; auto. }
    apply Nat.leb_gt in Heq.
    unfold total_width in *.
    desf.
    simpls.
    lia. }
  simpl.
  desf.
  apply leb_complete in Heq.
  destruct (height a <=? height a0) eqn:E2.
  { apply leb_complete in E2.  
    rewrite NPeano.Nat.min_l; auto.    
    repeat rewrite get_height_to_none; auto.
    lia. }
  apply Nat.leb_gt in E2.
  rewrite min_leb; auto.
Qed. 

Notation "a ⊆ b" := (incl a b)  (at level 60).

Lemma pick_is_less' a b lst w
      (A: format_correct a)
      (B: format_correct b)
      (H: is_less_than a b = true) :
  pick_best_list (a :: lst) w ⊆ pick_best_list ((a :: lst) ++ [b]) w.
Proof.
  simpls.
  destruct (total_width a <=? w) eqn:E2.
  { simpl.
    rewrite get_height_less.
    { desf.
      { apply incl_cons.
        { done. }
        apply incl_tl.
        rewrite filter_app.
        apply incl_appl.
        done. }
      rewrite filter_app.
      by apply incl_appl. }
    unfold is_less_than in H.
    unfold less_components in H.
    desf.
    all: andb_split.
    all: apply leb_complete in H.
    all: apply H. }
  rewrite get_height_none.
  { desf.
    rewrite filter_app.
    apply incl_appl.
    done. }
  assert (height a > 0 /\ height b > 0).
  { split.
    { apply A. }
    apply B. }
  unfold is_less_than in H.
  unfold less_components in H.
  desf.
  all: try lia.
  all: andb_split.
  all: apply leb_complete in H2.
  all: apply leb_complete in H3.
  all: apply leb_complete in H4.
  all: apply Nat.leb_gt in E2.
  all: apply Nat.leb_gt.
  all: unfold total_width in *.
  { desf.
    simpls.
    lia. }
  desf.
  simpls.
  lia.
Qed.

Lemma elem_in_pick n a lst w
      (H: total_width a <= w)
      (H1: get_min_height lst w None = Some n)
      (H2: In a lst)
      (H3: height a = n) : In a (pick_best_list lst w).
Proof.
  unfold pick_best_list.
  rewrite H1.
  clear H1.
  induction lst; simpls.
  desf.
  { apply andb_false_iff in Heq.
    desf.
    { apply leb_complete_conv in Heq.
      lia. }
    apply Nat.eqb_neq in Heq.
    lia. }
    { apply andb_false_iff in Heq.
      desf.
    { apply leb_complete_conv in Heq.
      lia. }
    apply Nat.eqb_neq in Heq.
    lia. }
  { apply andb_prop in Heq.
    desf.
    apply leb_complete in Heq.
    apply Nat.eqb_eq in Heq0.
    apply in_cons.
    apply IHlst; auto. }
  apply IHlst; auto.
Qed.

Lemma height_discr t l w
      (H: get_min_height l w (Some (height t)) = None) : False.
Proof.
  generalize dependent (height t).
  induction l; simpls.
  ins.
  desf.
  { apply (IHl (Init.Nat.min n (height a))).
    apply H. }
  apply (IHl n).
  apply H.
Qed.  

Lemma height_discr' t l w
      (P: In t l)
      (H: total_width t <= w)
      (D: get_min_height l w None = None) : False.
Proof.
  induction l.
  { done. }
  simpls.
  desf.
  { apply (height_discr t l w); auto. }
  { apply leb_complete_conv in Heq.
    lia. }
  { apply (height_discr a l w); auto. }
  apply IHl; auto.
Qed.    

Lemma best_remove_helper lst lst' w n
      (H: Some n = get_min_height lst' w None)
      (P: lst ⊆ lst') :
  filter (fun f : Format.t => (total_width f <=? w) && (height f =? n)) lst
         ⊆ pick_best_list lst' w.
Proof.
  generalize dependent n.
  induction lst.
  { ins.
    done. }
  ins.
  unfold incl in P.
  simpl in P.
  desf.
  { apply andb_prop in Heq.
    desf.
    apply beq_nat_true in Heq0.
    apply Nat.leb_le in Heq.
    apply incl_cons.
    { clear IHlst.
      apply (elem_in_pick n); auto. }
    apply IHlst; auto.
    generalize P.
    clear.
    ins.
    destruct lst.
    { done. }
    unfold incl.
    ins.
    apply P.
    auto. }
  apply IHlst; auto.
  generalize P.
  clear.
  ins.
  destruct lst.
  { done. }
  unfold incl.
  ins.
  apply P.
  auto.
Qed.
  
Lemma best_remove lst lst' w
      (H: get_min_height lst w None = get_min_height lst' w None) :
   lst ⊆ lst' -> pick_best_list lst w ⊆ pick_best_list lst' w.
Proof.
  ins.
  unfold pick_best_list at 1. 
  induction lst; simpls.
  desf.
  { apply incl_cons.
    {  unfold incl in H0.
      simpls.
      apply beq_nat_true in Heq0.
      apply leb_complete in Heq1.
      apply (elem_in_pick n); auto. }
    done. }
  { apply incl_cons.
    { apply leb_complete in Heq2.
      apply Nat.eqb_eq in Heq0.
      unfold incl in H0.
      simpl in H0.
      apply (elem_in_pick n); auto. }
    apply best_remove_helper; auto.
    unfold incl in H0.
    simpl in H0.
    generalize H0.
    clear.
    ins.
    unfold incl.
    simpl.
    ins.
    apply H0.
    auto. }
  { apply incl_cons. 
    { apply beq_nat_true in Heq0.
      apply leb_complete in Heq2.
      unfold incl in H0.
      simpl in H0.
      apply (elem_in_pick n); auto. }
    simpls.
    desf.
    { apply (height_discr t) in Heq1.
      done. }
    { apply (height_discr t) in Heq1.
      done. }
    generalize Heq1.
    clear.
    ins.
    induction l; simpls.
    desf.
    { apply (height_discr a) in Heq1.
      done. }
    { apply (height_discr a) in Heq1.
      done. }
    apply IHl; auto. }
  { apply best_remove_helper; auto.
    unfold incl in H0.
    simpl in H0.
    generalize H0.
    clear.
    ins.
    unfold incl.
    ins.
    apply H0.
    auto. }    
  { unfold incl in H0.
    simpl in H0.
    apply IHlst; auto.
    unfold incl.
    simpl.
    ins.
    apply H0; auto. }
  apply Nat.eqb_neq in Heq0.
  assert (height a = n).
  { generalize Heq1, Heq.
    clear.
    generalize dependent (t::l).
    ins.
    induction l0.
    { simpls.
      inversion Heq.
      auto. }
    simpls.
    desf.
    { apply (height_discr a0) in Heq1.
      done. }
    apply IHl0; auto. }
  lia.
Qed.

Lemma pick_height_link lst x w
      (C: list_correct lst)
      (F: format_correct x)
      (N: is_less_exist x lst = true) :
  get_min_height (lst ++ [x]) w None = get_min_height lst w None.
Proof.
  induction lst.
  { simpls. }
  apply is_exist_cons_alt in N.
  desf.
  { clear IHlst.
    simpls.
    assert (height x > 0 /\ height a > 0).
    { split.
      { apply F. }
      apply list_correct_add_b in C.
      desf.
      apply C0. }
    unfold is_less_than in N.
    unfold less_components in N.
    desf.
    all: try lia.
    all: andb_split.
    all: apply leb_complete in H1.
    all: apply leb_complete in H2.
    all: apply leb_complete in H4.
    all: apply leb_complete in H3.
    { rewrite <- Heq0.
      rewrite get_height_less.
      { reflexivity. }
      lia. }
    { rewrite <- Heq0.
      rewrite get_height_less.
      { reflexivity. }
      lia. }
    { rewrite get_height_none.
      { reflexivity. }
      apply Nat.leb_gt in Heq.
      apply Nat.leb_gt.
      unfold total_width in *.
      desf.
      simpls.
      lia. }
    rewrite get_height_none.
    { reflexivity. }
    apply Nat.leb_gt in Heq.
    apply Nat.leb_gt.
    unfold total_width in *.
    desf.
    simpls.
    lia. }
  simpls.
  desf.
  { symmetry.
    apply get_height_exist; auto.
    apply list_correct_add_b in C.
    desf. }
  apply IHlst; auto.
  apply list_correct_add_b in C.
  desf.
Qed.

Lemma cross_general_nil f w lst :
  FormatTrivial.cross_general w f nil lst = nil.
Proof.
  induction lst; auto.
Qed. 

Lemma height_values lst w :
  get_min_height lst w None = None \/
  exists a, In a lst /\ total_width a <=? w = true /\ get_min_height lst w None = Some (height a).
Proof.
  induction lst.
  { simpls.
    auto. }
  simpls.
  desf. 
  { assert (L: exists a0 : t,
     (a = a0 \/ In a0 lst) /\
     (total_width a0 <=? w) = true /\ get_min_height lst w (Some (height a)) = Some (height a0)).
    { exists a.
      repeat split; auto.
      generalize a.
      induction lst; auto.
      ins.
      desf.
      { apply height_discr in IHlst.
        done. }
      apply IHlst0; auto. }  
    auto. }
  { auto. }
  { clear IHlst.
    clear IHlst1.
    assert (L: exists a1 : t,
     (a = a1 \/ In a1 lst) /\
     (total_width a1 <=? w) = true /\ get_min_height lst w (Some (height a)) = Some (height a1)).
    { generalize dependent a.
      induction lst.
      { ins.
        exists a; auto. }
      ins.
      desf.
      { destruct ((height a1) <=? (height a)) eqn:E1.
        { apply leb_complete in E1.
          rewrite Min.min_l; auto.
          assert (L: exists a2 : t,
    (a1 = a2 \/ In a2 lst) /\
    (total_width a2 <=? w) = true /\ get_min_height lst w (Some (height a1)) = Some (height a2)).
          { apply IHlst; auto. }
          desf.
          all: exists a2; auto. }
        apply leb_iff_conv in E1.
        rewrite min_leb; auto.
        assert (L: exists a1 : t,
                   (a = a1 \/ In a1 lst) /\ (total_width a1 <=? w) = true /\ get_min_height lst w (Some (height a)) = Some (height a1)).
        { apply IHlst; auto. }
        desf.
        all: exists a2; auto. }
      assert (L: exists a2 : t,
                 (a1 = a2 \/ In a2 lst) /\ (total_width a2 <=? w) = true /\ get_min_height lst w (Some (height a1)) = Some (height a2)).
      { apply IHlst; auto. }
      desf.
      all: exists a2; auto. }
    auto. }
  assert (L: exists a1 : t, (a = a1 \/ In a1 lst) /\ (total_width a1 <=? w) = true /\ get_min_height lst w None = Some (height a1)).
  { exists a0.
    auto. }
  auto.
Qed.

Lemma height_eq lst w : get_min_height lst w None = None <->
                        forallb (fun f => negb (total_width f <=? w)) lst = true.
Proof.
  split.
  { ins.
    induction lst; auto.
    simpls.
    desf.
    { apply height_discr in H.
      done. }
    simpl.
    apply IHlst; auto. }
  ins.
  induction lst; auto.
  simpls.
  desf.
  simpl in H.
  apply IHlst; auto.
Qed.      

Lemma height_remove_val n m lst w
      (I: m < n) : get_min_height lst w (Some n) = Some m <-> get_min_height lst w None = Some m.
Proof.
  assert (L: forall n m lst w, m < n /\ get_min_height lst w (Some n) = Some m -> get_min_height lst w None = Some m).
  { clear.
    ins.
    destruct H as [H0 H].
    generalize dependent n.
    induction lst.
    { ins.
      inversion H.
      lia. }
    ins.
    desf.
    { destruct (n <=? height a) eqn:E1.
      { apply leb_complete in E1.
        rewrite Min.min_l in H; auto.
        clear IHlst.
        clear Heq.
        generalize dependent n.
        generalize dependent (height a).
        induction lst.
        { ins.
          inversion H.
          lia. }
        ins.
        desf.
        { destruct (n <=? height a0) eqn:E2.
          { apply leb_complete in E2.
            rewrite Min.min_l; auto.
            rewrite Min.min_l in H; auto.
            { apply (IHlst _ n0); auto. }
            lia. }
          apply Nat.leb_gt in E2.
          rewrite min_leb; auto.
          destruct (n0 <=? height a0) eqn:E3.
          { apply leb_complete in E3.
            rewrite Min.min_l in H; auto.
            apply (IHlst _ n0); auto. }
          apply Nat.leb_gt in E3.
          rewrite min_leb in H; auto. }
        apply (IHlst _ n0); auto. }
      apply Nat.leb_gt in E1.
      rewrite min_leb in H; auto. }
    apply (IHlst n); auto. }
  split.
  { ins.
    apply (L n); auto. }
  ins.
  generalize dependent n.
  induction lst; simpls.
  desf.
  { ins.
    destruct (n <=? height a) eqn:E1.
    { apply leb_complete in E1.
      rewrite Min.min_l; auto.
      apply IHlst; auto.
      apply (L (height a)).
      split; auto.
      lia. }
    apply leb_iff_conv in E1.
    rewrite min_leb; auto. }
  ins.
  apply IHlst; auto.
Qed.

Lemma height_discr5 lst w n m
      (P: m < n)
      (T: get_min_height lst w (Some m) = Some n) : False.
Proof.
  generalize dependent m.
  induction lst.
  { ins.
    inversion T.
    lia. }
  ins.
  desf.
  { destruct (m <=? height a) eqn:E2.
    { apply leb_complete in E2.
      rewrite Min.min_l in T; auto.
      apply (IHlst m); auto. }
    apply Nat.leb_gt in E2.
    rewrite min_leb in T; auto.
    apply (IHlst (height a)); auto.
    lia. }
  apply (IHlst m); auto.
Qed.

Lemma height_discr4 lst w a n
      (I: In a lst)
      (P: (total_width a <=? w) = true)
      (T: get_min_height lst w None = Some n)
      (H: height a < n) : False.
Proof.
  induction lst.
  { done. }
  simpls.
  desf.
  { clear IHlst.
    generalize dependent a.
    induction lst.
    { ins.
      inversion T.
      lia. }
    ins.
    desf.
    { destruct (height a0 <=? height a) eqn:E1.
      { apply leb_complete in E1.
        rewrite Min.min_l in T; auto.
        apply (IHlst a0); auto. }
      apply Nat.leb_gt in E1.
      rewrite min_leb in T; auto.
      apply (IHlst a); auto.
      lia. }
    apply (IHlst a0); auto. }
  { destruct (height a0 <=? n) eqn:E1.
    { apply leb_complete in E1.
      clear IHlst.
      apply le_lt_or_eq in E1.
      desf.
      { assert (D: False).
        { apply (height_discr5 lst w n (height a0)); auto. }
        done. }
      generalize T, H, I, P.
      generalize (height a0).
      clear.
      ins.
      generalize dependent I.
      generalize dependent n.
      induction lst; simpls.
      ins.
      desf.
      { rewrite min_leb in T; auto.
        apply (height_discr5 lst w n (height a)); auto. }
      { destruct (n <=? height a0) eqn:E1.
        { apply leb_complete in E1.
          rewrite Min.min_l in T; auto.
          apply (IHlst n); auto. }
        apply Nat.leb_gt in E1.
        rewrite min_leb in T; auto.
        apply (height_discr5 lst w n (height a0)); auto. }
      apply (IHlst n); auto. }
    apply Nat.leb_gt in E1.
    apply IHlst; auto.
    apply (height_remove_val (height a0)); auto. }
  apply IHlst; auto.
Qed.

Lemma height_eq1 lst lst' w a
      (I: lst ⊆ lst')
      (T: get_min_height lst' w None = Some (height a)) :
  get_min_height lst w (Some (height a)) = Some (height a).
Proof.
  induction lst; auto.
  simpls.
  desf.
  { destruct (height a <=? height a0) eqn:E1.
    { apply leb_complete in E1.
      rewrite Min.min_l; auto.
      apply IHlst.
      unfold incl in *.
      ins.
      apply (I a1); auto. }
    apply Nat.leb_gt in E1.
    assert (D: False).
    { unfold incl in I.
      simpls.
      apply (height_discr4 lst' w a0 (height a)); auto. }
    done. }
  apply IHlst.
  unfold incl in *.
  ins.
  apply (I a1); auto.
Qed.     

Lemma height_discr'' lst w a b
      (W: total_width a <=? w = true)
      (I: In a lst)
      (L: format_correct a)
      (T: get_min_height lst w None = Some (height b))
      (E: height a <> height b)
      (H: is_less_than' a b = true) : False.
Proof.
  unfold is_less_than' in H.
  unfold is_less_than in H.
  unfold less_components in H.
  desf.
  { unfold format_correct in L.
    desf.
    unfold format_correct2 in F2.
    lia. } 
  { andb_split.
    apply leb_complete in H0.
    apply leb_complete in H1.
    apply leb_complete in H.
    induction lst; simpls.
    desf.
    { apply (height_discr5 lst w (height b) (height a)); auto.
      lia. }
    { destruct (height a0 <? height b) eqn:E1.
      { apply Nat.ltb_lt in E1.
        apply (height_discr5 lst w (height b) (height a0)); auto. }
      apply Nat.ltb_ge in E1.
      clear IHlst.
      clear E1.
      generalize dependent a0.
      induction lst; simpls.
      ins.
      desf.
      { destruct (height a <=? height a1) eqn:E2.
        { apply leb_complete in E2.
          rewrite Min.min_r in T; auto.
          apply (height_discr5 lst w (height b) (height a)); auto.
          lia. }
        apply leb_iff_conv in E2.
        rewrite min_l in T.
        { apply (height_discr5 lst w (height b) (height a1)); auto.
          lia. }
        lia. }
      { destruct (height a1 <=? height a0) eqn:E2.
        { apply leb_complete in E2.
          rewrite Min.min_l in T; auto.
          apply (IHlst I a1); auto. }
        apply leb_iff_conv in E2.
        rewrite min_r in T.
        { apply (IHlst I a0); auto. }
        lia. }
      apply (IHlst I a1); auto. }
    apply IHlst; auto. }
  andb_split.
  apply leb_complete in H0.
  apply leb_complete in H1.
  apply leb_complete in H.
  apply leb_complete in H2.
  induction lst; simpls.
  desf.
  all: rewrite <- Heq0 in T. 
  { apply (height_discr5 lst w (height b) (height a)); auto.
    lia. }
  { destruct (height a0 <? height b) eqn:E1.
    { apply Nat.ltb_lt in E1.
      apply (height_discr5 lst w (height b) (height a0)); auto. }
    apply Nat.ltb_ge in E1.
    clear IHlst.
    clear E1.
    generalize dependent a0.
    induction lst; simpls.
    ins.
    desf.
    { destruct (height a <=? height a1) eqn:E2.
      { apply leb_complete in E2.
        rewrite Min.min_r in T; auto.
        apply (height_discr5 lst w (height b) (height a)); auto.
        lia. }
      apply leb_iff_conv in E2.
      rewrite min_l in T.
      { apply (height_discr5 lst w (height b) (height a1)); auto.
        lia. }
      lia. }
    { destruct (height a1 <=? height a0) eqn:E2.
      { apply leb_complete in E2.
        rewrite Min.min_l in T; auto.
        apply (IHlst I a1); auto. }
      apply leb_iff_conv in E2.
      rewrite min_r in T.
      { apply (IHlst I a0); auto. }
      lia. }
    apply (IHlst I a1); auto. }
  apply IHlst; auto.
  rewrite <- Heq0.
  apply T.
Qed.
    
Lemma height_incl_elem a lst lst' w
      (I: (a :: lst) ⊆ lst')
      (E: total_width a <=? w = true)
      (H: get_min_height lst w None = get_min_height lst' w None) :
  get_min_height lst w (Some (height a)) = get_min_height lst' w None.
Proof.
  generalize dependent a. 
  induction lst.
  { ins.
    assert (D: False).
    { apply leb_complete in E.
      unfold incl in I.
      simpls.
      apply (height_discr' a lst' w); auto. }
    done. }
  ins.
  desf.
  { destruct (height a0 <=? height a) eqn:E1.
    { apply leb_complete in E1.
      rewrite Min.min_l; auto.
      clear IHlst.
      generalize dependent a.
      generalize dependent a0.
      induction lst.  
      { ins.
        destruct (height a0 <? height a) eqn:E2.
        { apply Nat.ltb_lt in E2.
          assert (False).
          { apply (height_discr4 lst' w a0 (height a)); auto.
            unfold incl in I.
            simpls.
            apply (I a0); auto. }
          done. }
        apply Nat.ltb_ge in E2.
        assert (R: height a = height a0).
        { lia. }
        rewrite <- R.
        apply H. }
      ins.
      desf.
      { destruct (height a0 <=? height a) eqn:E2.
        { apply leb_complete in E2.
          rewrite Min.min_l; auto.
          destruct (height a1 <=? height a) eqn:E3.
          { apply leb_complete in E3.
            rewrite Min.min_l in H; auto.
            apply (IHlst a0 E a1); auto.
            unfold incl in *.
            ins.
            apply (I a2).
            desf; auto. }
          apply leb_iff_conv in E3.
          rewrite min_r in H.
          { apply (IHlst a0 E a); auto.
            unfold incl in *.
            ins.
            apply (I a2); auto.
            desf; auto. }
          lia. }
        apply Nat.leb_gt in E2.
        rewrite min_r.
        { destruct (height a1 <=? height a) eqn:E3.
          { apply leb_complete in E3.
            rewrite Min.min_l in H; auto.
            apply (IHlst a Heq0 a1); auto.
            { unfold incl in *.
              ins.
              apply (I a2).
              desf; auto. }
            lia. }
          apply leb_iff_conv in E3.
          rewrite min_r in H.
          { apply H. }
          lia. }
        lia. }
      apply (IHlst a0 E a1); auto.
      unfold incl in *.
      ins.
      apply (I a2).
      desf; auto. }
    apply leb_iff_conv in E1.
    rewrite Min.min_r; auto.
    lia. }
  apply IHlst; auto.
  unfold incl in *.
  ins.
  apply (I a1).
  desf; auto.
Qed.  

Definition is_less_exist' lst lst' :=
  forall b, In b lst' -> exists a, In a lst /\ is_less_than' a b = true.

Lemma is_less_width a b w
      (C: format_correct a)
      (H: is_less_than' a b = true)
      (A: total_width b <=? w = true) : total_width a <=? w = true.
Proof.
  apply leb_complete in A.
  apply Nat.leb_le.
  unfold is_less_than' in H.
  unfold is_less_than in H.
  unfold less_components in H.
  desf.
  all: andb_split.
  all: apply leb_complete in H.
  all: apply leb_complete in H0.
  all: apply leb_complete in H1.
  all: try apply leb_complete in H2.
  all: unfold total_width in *; desf; simpls.
  all: try lia.
  assert (first_line_width = middle_width).
  { apply C; auto. }
  lia.  
Qed.

Lemma height_less lst lst' w
      (C: list_correct lst')
      (H: lst ⊆ lst') 
      (P: is_less_exist' lst lst') :
            get_min_height lst w None = get_min_height lst' w None.
Proof.
  assert (list_correct lst).
  { apply (list_correct_incl _ lst'); auto. }
  destruct (height_values lst' w) eqn:E1.
  { clear E1.
    rewrite e.
    apply height_eq.
    apply height_eq in e.
    clear P.
    induction lst; auto.
    simpl.
    apply andb_true_iff.
    split.
    { clear IHlst.
      assert (L: In a lst').
      { unfold incl in H.
        apply (H a); simpl.
        auto. }
      clear H.
      induction lst'.
      { done. }
      simpl in L.
      desf.
      { simpl in e.
        apply andb_prop in e.
        desf. }
      simpl in e.
      apply andb_prop in e.
      desf.
      apply IHlst'; auto.
      apply list_correct_add_b in C.
      desf. }
    apply IHlst.
    unfold incl in *.
    ins.
    apply (H a0); auto.
    apply list_correct_add_b in H0.
    desf. }
  clear E1.
  desf.
  assert (L: exists t, In t lst /\ is_less_than' t a = true).
  { apply P; auto. }
  clear P.
  induction lst; desf.
  simpls.
  desf.
  { destruct (height a =? height t) eqn:E1.
    { apply beq_nat_true in E1.
      rewrite <- E1.
      rewrite e1.
      apply (height_eq1 _ lst'); auto.
      unfold incl in *.
      ins.
      apply (H a0); auto. }
    apply beq_nat_false in E1.
    assert (D: False).
    { apply (height_discr'' lst' w t a); auto.
      unfold incl in H.
      simpls.
      apply (H t); auto.
      apply list_correct_add_b in H0.
      desf. }
    done. }
  { rewrite (is_less_width _ a) in Heq; auto.
    { discriminate Heq. }
    apply list_correct_add_b in H0.
    desf. }
  { apply height_incl_elem; auto.
    apply IHlst; auto.
    { unfold incl in *.
      ins.
      apply (H a1); auto. }
    { apply list_correct_add_b in H0.
      desf. }
    exists t.
    auto. }
  apply IHlst.
  { unfold incl in *.
    simpl in H.
    ins.
    apply H; auto. }
  { apply list_correct_add_b in H0.
    desf. }
  exists t.
  auto.
Qed.  

Lemma height_not_eq lst w n m
      (H: n <> m)
      (T: get_min_height lst w (Some m) = Some n) :
  get_min_height lst w None = Some n.
Proof.
  induction lst.
  { simpls.
    inversion T.
    lia. }
  simpls.
  desf.
  { destruct (m <=? height a) eqn:E1.
    { apply leb_complete in E1.
      rewrite Min.min_l in T; auto.
      assert (L: get_min_height lst w None = Some n).
      { apply IHlst; auto. }
      clear IHlst.
      apply height_remove_val; auto.
      assert (n < m).
      { assert (n < m <-> (m <= n -> False)).
        { clear.
          split.
          { ins.
            lia. }
          ins.
          lia. }
        apply H0.
        ins.
        apply (height_discr5 lst w n m); auto.
        lia. }
      lia. }
    apply leb_complete_conv in E1.
    rewrite min_leb in T; auto. }
  apply IHlst; auto.
Qed.  
