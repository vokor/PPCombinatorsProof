Require Import Hahn.
Require Import Format.
Require Import Doc.
Require Import PrettyPrinter.
Require Import FormatTrivial.
Require Import FormatList.
Require Import IsLess.
Require Import FuncCorrect.

Require Import String.
Require Import ZArith Int.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.Bool.Bool.
Require Import Coq.ssr.ssrbool.


Lemma listEqTrivialProof :
  forall x width,
    (pretty evaluatorTrivial width x) = (pretty evaluatorList width x).
Proof.
  intros x.
Admitted.

Lemma pareto_text :
  forall x,
    pareto (FormatTrivial.constructDoc x) = FormatList.constructDoc x.
Proof.
  intros x.
  unfold FormatTrivial.constructDoc.
  unfold FormatList.constructDoc.
  reflexivity.
Qed.

Lemma par_elem2_not_less a b lst 
    (H: is_less_than a b = false) :
  pareto_by_elem a (b::lst) = b :: pareto_by_elem a lst.
Proof.
  unfold pareto_by_elem, filter.
  rewrite -> eq_conv_is_less.
  rewrite -> H. auto.
Qed.

Lemma par_elem2_less a b lst 
    (H: is_less_than a b = true) :
    pareto_by_elem a (b::lst) = pareto_by_elem a lst.
Proof.
  unfold pareto_by_elem, filter.
  rewrite -> eq_conv_is_less.
  rewrite -> H. auto.
Qed.

Lemma pareto_by_elem_linear a lst lst' : 
    pareto_by_elem a (lst ++ lst') = 
    pareto_by_elem a lst ++ pareto_by_elem a lst'.
Proof.
  induction lst. auto.
  simpl. 
  rewrite eq_conv_is_less.
  destruct (is_less_than a a0) eqn:E1.
  simpl. apply IHlst.
  simpl. rewrite IHlst. reflexivity.
Qed.

Lemma pareto_by_elem_simpl a x xs lst 
    (H: is_less_than a x = true) : 
  pareto_by_elem a (lst ++ x :: xs) = pareto_by_elem a (lst ++ xs).
Proof.
  repeat rewrite pareto_by_elem_linear.
  rewrite par_elem2_less; auto.
Qed.

Lemma pareto_by_elem_swap a b lst
    (H: is_less_than a b = true) :
  pareto_by_elem a lst = pareto_by_elem a (pareto_by_elem b lst).
Proof.
  induction lst. auto.
  simpl.
  repeat rewrite eq_conv_is_less.
  destruct (is_less_than a a0) eqn:E3.
  { simpl.
    destruct (is_less_than b a0) eqn:E4.
    { simpl. auto. }
    simpl.
    rewrite eq_conv_is_less, E3. simpl.
    auto. }
  simpl.
  destruct (is_less_than b a0) eqn:E4.
  { simpl.
    assert (L: is_less_than a a0 = true).
    { apply (is_less_than_transitivity a b a0); auto. }
    rewrite E3 in L. discriminate L. }
  simpl. rewrite eq_conv_is_less, E3.
  simpl. rewrite IHlst. reflexivity.
Qed.

Lemma pareto_by_elem_not_nil :
  forall a b lst, is_less_exist a (pareto_by_elem b lst) = false ->
    is_less_than b a = true \/ is_less_exist a lst = false.
Proof.
  induction lst. auto.
  intro H.
  simpl in H.
  rewrite eq_conv_is_less in H.
  destruct (is_less_than b a0) eqn:E1.
  { simpl in H.
    rewrite is_exist_not_cons_alt.
    destruct IHlst; auto.
    rewrite H0.
    destruct (is_less_than a0 a) eqn:E2; auto.
    rewrite (is_less_than_transitivity b a0 a); auto. }
  simpl in H. simpl.
  unfold flip in *.
  destruct IHlst; auto.
  destruct (is_less_than a0 a) eqn:E2.
  simpl in H. discriminate H.
  simpl in H. apply H.
  rewrite H0.
  rewrite orb_false_r.
  destruct (is_less_than a0 a); auto.
Qed.

Notation "lst ++ [ a ]" := (lst ++ (a::nil)) (at level 60).

Lemma pareto_exec_exist a lst l r
    (H: is_less_exist a lst = true) :
  pareto_exec lst (l ++ a::r) = pareto_exec lst (l ++ r).
Proof. 
  generalize dependent lst.
  induction l.
  { intros lst H.
    simpl. rewrite H. reflexivity. }
  intros lst H.
  simpl.
  destruct (is_less_exist a0 lst) eqn:E1.
  { apply IHl; auto. }
  apply IHl.
  apply is_exist_cons_all.
  rewrite is_exist_cons_alt.
  destruct (is_less_exist a (pareto_by_elem a0 lst)) eqn:E2; auto.
  apply pareto_by_elem_not_nil in E2.
  destruct E2; auto.
  rewrite H0 in H.
  discriminate H.
Qed.

Lemma pareto_exec_same lst lst' :
   pareto_exec lst' (lst ++ lst') = pareto_exec lst' lst.
Proof.
  generalize dependent lst'.
  induction lst.
  { intro lst'.
    simpl.
    rewrite <- (app_nil_l lst') at 1 3.
    generalize dependent (nil: list t).
    induction lst'. auto.
    intro l.
    simpl.
    assert (L: is_less_exist a (l ++ a :: lst') = true).
    { apply is_exist_cons_all. 
      rewrite is_exist_cons_alt, is_less_than_reflexivity.
      auto. }
    rewrite L.
    rewrite <- (app_nil_l lst') at 1 3.
    rewrite app_comm_cons.
    rewrite app_assoc.
    apply IHlst'. }
  intro lst'.
  rewrite <- app_comm_cons.
  simpl.
  destruct (is_less_exist a lst') eqn:E1. apply IHlst.
  rewrite <- IHlst.
  rewrite <- (app_nil_l (pareto_by_elem a lst')) at 1 2.
  rewrite <- app_assoc.
  generalize (nil : list t) at 1 3.
  induction lst'.
  { simpl. symmetry.
    apply pareto_exec_exist.
    rewrite is_exist_cons_all.
    simpl. unfold flip.
    rewrite is_less_than_reflexivity. auto. }
  intro l.
  rewrite is_exist_not_cons_alt in E1.
  destruct E1 as [A B].
  destruct (is_less_than a a0) eqn:E2.
  { rewrite par_elem2_less; auto.
    rewrite pareto_exec_exist.
    apply IHlst'; auto.
    apply is_exist_cons_all.
    rewrite is_exist_cons_all.
    simpl. unfold flip.
    rewrite E2. auto. }
  rewrite par_elem2_not_less; auto.
  rewrite <- app_comm_cons.
  repeat rewrite pareto_exec_exist.
  2, 3: rewrite is_exist_cons_all; simpl; unfold flip;
    rewrite is_less_than_reflexivity; auto.
  rewrite <- (app_nil_l (pareto_by_elem a lst')) at 1 2.
  rewrite <- app_assoc.
  assert (Rew: l ++ a0 :: nil ++ pareto_by_elem a lst' ++ a :: nil = 
               (l ++ a0 :: nil) ++ pareto_by_elem a lst' ++ a :: nil).
  { rewrite <- app_assoc. auto. }
  rewrite Rew.
  apply IHlst'; auto.
Qed.

Lemma linear_pareto_exist a lst 
    (H: is_less_exist a lst = true) :
  pareto (lst ++ [a]) = pareto lst.
Proof.
  unfold pareto.
  generalize (nil: list t) at 1 3.
  induction lst. discriminate H.
  intro lst'.
  rewrite is_exist_cons_alt in H.
  destruct H as [H|H].
  { simpl.
    destruct (is_less_exist a0 lst') eqn:E1.
    { rewrite pareto_exec_exist.
      rewrite app_nil_r.
      reflexivity.
      apply (is_less_exist_transitivity a0); auto. }
    rewrite pareto_exec_exist.
    { induction lst'.
      { simpl. rewrite app_nil_r.
        reflexivity. }
      rewrite is_exist_not_cons_alt in E1.
      destruct E1.
      simpl. rewrite eq_conv_is_less.
      rewrite app_nil_r.
      destruct (is_less_than a0 a1) eqn:E1; auto. }
    induction lst'.
    { simpl. unfold flip. rewrite H. auto. }
    simpl. rewrite eq_conv_is_less.
    rewrite is_exist_not_cons_alt in E1.
    destruct E1.
    destruct (is_less_than a0 a1) eqn:E2.
    { simpl. apply IHlst', H1. }
    simpl. rewrite IHlst'; auto.
    apply orb_true_r. }
  simpl.
  repeat rewrite IHlst; auto.
Qed.

Lemma linear_pareto_not_exist a lst (H : is_less_exist a lst = false) :
    pareto (lst ++ [a]) = pareto_by_elem a (pareto lst) ++ [a].
Proof.
  unfold pareto.
  assert (Gen: forall lst', is_less_exist a lst' = false ->
    pareto_exec lst' (lst ++ [a]) =
      pareto_by_elem a (pareto_exec lst' lst) ++ [a]).
  { induction lst.
    { intros lst' H1.
      simpl. rewrite H1. reflexivity. }
    intros lst' H1.
    rewrite is_exist_not_cons_alt in H.
    destruct H.
    simpl.
    repeat rewrite IHlst; auto.
    { destruct (is_less_exist a0 lst') eqn:E1; auto. }
    apply is_exist_not_cons_all.
    split.
    { apply is_less_exist_with_elem; auto. }
    apply is_exist_not_cons_alt. auto.
  }
  apply Gen. auto.
Qed.

Lemma leb_le_eq_true x y z :
  x <= z <-> (x + y <=? z + y) = true.
Proof.
  split.
    { intro T.
      eapply introT. apply Nat.leb_spec0.
      apply plus_le_compat_r; auto. }
    intro T.
    eapply elimT in T; [|apply Nat.leb_spec0].
    apply <- Nat.add_le_mono_r. eauto.
Qed.

Lemma leb_eq x y z : 
  x <=? y = (x + z <=? y + z).
Proof.
  symmetry.
  destruct (x <=? y) eqn:E1.
  { eapply elimT in E1; [|apply Nat.leb_spec0].
    apply leb_correct.
    apply Nat.add_le_mono_r; auto. }
  eapply elimF in E1; [|apply Nat.leb_spec0].
  apply leb_correct_conv.
  apply Nat.lt_nge in E1.
  apply plus_lt_compat_r; auto.
Qed.

Lemma indent'_linear a b sh :
  is_less_than a b = is_less_than (indent' sh a) (indent' sh b).
Proof.
  symmetry.
  destruct (is_less_than a b) eqn:E1.
  { unfold is_less_than in *.
    andb_split.
    repeat (apply andb_true_iff;
            unfold indent';
            destruct a; destruct b;
            simpl in *; split).
    repeat (apply andb_true_iff; split); auto.
    { eapply elimT in H2; [|apply Nat.leb_spec0].
      apply leb_le_eq_true; auto. }
    { eapply elimT in H1; [|apply Nat.leb_spec0].
      apply leb_le_eq_true; auto. }
    eapply elimT in H0; [|apply Nat.leb_spec0].
    apply leb_le_eq_true; auto.
  }
  unfold is_less_than in *.
  unfold indent'.
  destruct (height a <=? height b) eqn:E2.
  { destruct a; destruct b.
    simpl in *. rewrite E2. simpl.
    destruct (first_line_width + sh <=? first_line_width0 + sh) eqn:E3.
    { simpl.
      destruct (middle_width + sh <=? middle_width0 + sh) eqn:E4.
      { simpl.
        rewrite <- leb_le_eq_true in E3.
        rewrite <- leb_le_eq_true in E4.
        rewrite <- leb_eq.
        destruct (first_line_width <=? first_line_width0) eqn:E5.
        { destruct (middle_width <=? middle_width0) eqn:E6.
          { simpl in E1. apply E1. }
          apply leb_correct in E4. rewrite E4 in E6.
          discriminate E6. }
        apply leb_correct in E3. rewrite E3 in E5.
          discriminate E5. }
      auto. }
    auto. }
  destruct a; destruct b.
  simpl in *. rewrite E2.
  auto.
Qed.

Lemma linear_indent_true_f width sh a b 
    (P: main_pred width sh a = true) :
  indentDoc width sh (a::b) = (indent' sh a) :: indentDoc width sh b.
Proof.
  unfold indentDoc. unfold filter_map.
  simpl. unfold filter_map_pred.
  rewrite P. reflexivity.
Qed.

Lemma linear_indent_false_f width sh x xs 
    (P: main_pred width sh x = false) :
  indentDoc width sh (x::xs) = indentDoc width sh xs.
Proof.
  unfold indentDoc, filter_map.
  simpl. unfold filter_map_pred.
  rewrite P. reflexivity.
Qed.

Lemma main_pred_transitivity w sh a b 
    (A: is_less_than a b = true)
    (B: main_pred w sh a = false) :
  main_pred w sh b = false.
Proof.
  unfold main_pred in *.
  unfold total_width in *.
  simpl in *.
  destruct b. destruct a.
  unfold is_less_than in A.
  simpl in *.
  apply Nat.leb_gt.
  andb_split.
  apply Nat.leb_gt in B.
  apply leb_complete in H.
  apply leb_complete in H1.
  apply leb_complete in H2.
  apply leb_complete in H0.
  eapply Nat.lt_le_trans; eauto.
  apply Nat.add_le_mono_r, Nat.max_le_compat; auto.
  apply Nat.max_le_compat; auto.
Qed.

Lemma linear_indent_true_e w sh a lst
    (P: main_pred w sh a = true) :
  indentDoc w sh (lst ++ [a]) = indentDoc w sh lst ++ [indent' sh a].
Proof.
  induction lst.
  { simpl. unfold filter_map_pred.
    rewrite P. reflexivity. }
  simpl. unfold filter_map_pred.
  destruct (main_pred w sh a0) eqn:E1.
  { simpl. rewrite IHlst. reflexivity. }
  apply IHlst.
Qed.

Lemma linear_indent_false_e w sh a lst 
    (P: main_pred w sh a = false) :
  indentDoc w sh (lst ++ [a]) = indentDoc w sh lst.
Proof.
  induction lst.
  { simpl. unfold filter_map_pred.
    rewrite P. reflexivity. }
  simpl. unfold filter_map_pred.
  destruct (main_pred w sh a0) eqn:E1.
  { simpl. rewrite IHlst. reflexivity. }
  apply IHlst.
Qed.

Lemma linear_indent_op w sh x xs
    (H: main_pred w sh x = true) :
  is_less_exist (indent' sh x) (indentDoc w sh xs) = is_less_exist x xs.
Proof.
  induction xs; auto.
  destruct (main_pred w sh a) eqn:E1.
  { rewrite linear_indent_true_f; auto.
    destruct (is_less_exist x (a :: xs)) eqn:E2.
    { rewrite is_exist_cons_alt, IHxs.
      rewrite is_exist_cons_alt in E2.
      destruct E2 as [A|A].
      { rewrite <- (indent'_linear a x sh). auto. }
      rewrite A. auto. }
    rewrite is_exist_not_cons_alt, IHxs.
    rewrite is_exist_not_cons_alt in E2.
    destruct E2 as [A B].
    rewrite <- indent'_linear.
    auto. }
  rewrite linear_indent_false_f; auto.
  rewrite IHxs.
  destruct (is_less_exist x (a :: xs)) eqn:E2.
  { rewrite is_exist_cons_alt in E2.
    destruct E2 as [E2|E2]; auto.
    rewrite (main_pred_transitivity _ _ a x) in H; auto. }
  rewrite is_exist_not_cons_alt in E2.
  destruct E2. apply H1.
Qed.

Lemma pareto_indent_elem a w sh lst :
  pareto_by_elem (indent' sh a) (indentDoc w sh lst) = 
    indentDoc w sh (pareto_by_elem a lst).
Proof.
  induction lst; auto.
  destruct (is_less_than a a0) eqn:E1.
  { rewrite par_elem2_less; auto.
    destruct (main_pred w sh a0) eqn:E2.
    { rewrite linear_indent_true_f; auto.
      rewrite par_elem2_less, IHlst.
      reflexivity.
      rewrite (indent'_linear a a0 sh) in E1.
      auto. }
    rewrite linear_indent_false_f; auto. }
  rewrite par_elem2_not_less; auto.
  destruct (main_pred w sh a0) eqn:E2.
  { rewrite linear_indent_true_f; auto.
    rewrite par_elem2_not_less, IHlst.
    rewrite linear_indent_true_f; auto.
    rewrite (indent'_linear a a0 sh) in E1.
    auto. }
  repeat rewrite linear_indent_false_f.
  all: auto.
Qed.

Lemma pareto_indent sh d w
    (H: pareto (evaluatorTrivial w d) = (evaluatorList w d)) :
    pareto (indentDoc w sh (evaluatorTrivial w d))
        = indentDoc w sh (evaluatorList w d).
Proof.
  rewrite <- H.
  set (lst := evaluatorTrivial w d).
  induction lst using rev_ind. auto.
  destruct (main_pred w sh x) eqn:E1.
  { rewrite linear_indent_true_e; auto.
    { destruct (is_less_exist x lst) eqn:E2.
      { rewrite linear_pareto_exist, IHlst, linear_pareto_exist; auto.
        rewrite linear_indent_op; auto. }
      repeat rewrite linear_pareto_not_exist; auto.
      rewrite IHlst, pareto_indent_elem, linear_indent_true_e; auto.
      rewrite linear_indent_op; auto. } }
  rewrite linear_indent_false_e; auto.
  rewrite IHlst.
  destruct (is_less_exist x lst) eqn:E2.
  { rewrite linear_pareto_exist; auto. }
  rewrite linear_pareto_not_exist; auto.
  rewrite linear_indent_false_e; auto.
  set (mas := pareto lst).
  induction mas. auto.
  destruct (main_pred w sh a) eqn:E3.
  { rewrite linear_indent_true_f; auto.
    simpl. rewrite eq_conv_is_less.
    destruct (is_less_than x a) eqn:E4.
    { rewrite (main_pred_transitivity w sh x a) in E3; auto.
      discriminate E3. }
    simpl (if ~~ false then a :: pareto_by_elem x mas else pareto_by_elem x mas).
    rewrite linear_indent_true_f; auto.
    rewrite IHmas. reflexivity. }
  rewrite linear_indent_false_f; auto.
  simpl. rewrite eq_conv_is_less.
  destruct (is_less_than x a) eqn:E4; auto.
  simpl (if ~~ false then a :: pareto_by_elem x mas else pareto_by_elem x mas).
  rewrite linear_indent_false_f; auto.
Qed.

Definition neighb_pareto (a: Doc) (b: Doc) (w: nat):=
  pareto (evaluatorTrivial w a) = (evaluatorList w a) /\
  pareto (evaluatorTrivial w b) = (evaluatorList w b).

Lemma cross_general_exist_helper w f x y ys lst lst'
      (H: is_less_exist x lst = true)
      (F: func_correct f)
      (T: (total_width (f x y) <=? w) = true) :
  
   is_less_exist (f x y)
     (filter (fun f0 : t => total_width f0 <=? w)
             (concat (map (fun f0 : t => map (f f0) (lst' ++ y :: ys)) lst))) = true.
Proof.
  induction lst. auto.
  simpl.
  rewrite map_app.
  repeat rewrite filter_app.
  repeat rewrite is_exist_cons_all.
  simpl.
  apply is_exist_cons_alt in H.
  destruct H.
  { destruct (total_width (f a y) <=? w) eqn:E1.
    { rewrite is_exist_cons_alt.
      rewrite <- F. auto. }    
    rewrite (is_less_than_func _ _ x) in E1; auto. }
  auto.
Qed.

Lemma trivial_cross_general_not_exist lst lst' x w f
      (H: is_less_exist x lst = false)
      (F: func_correct f) :
 pareto (FormatTrivial.cross_general w f (lst ++ [x]) lst') =
 pareto (FormatTrivial.cross_general w f lst lst') ++ [x].
Proof.
 
Admitted.

Lemma trivial_cross_general_exist lst lst' x w f
      (H: is_less_exist x lst = true)
      (F: func_correct f) :
 pareto (FormatTrivial.cross_general w f (lst ++ [x]) lst') =
  pareto (FormatTrivial.cross_general w f lst lst').
Proof.
  unfold FormatTrivial.cross_general.
  destruct lst as [| a lst].
  { simpl in H. discriminate. }
  assert (Lem: forall (q: list t) s t h, q ++ s ++ t ++ h = (q ++ s ++ t) ++ h).
  { destruct q.
    { simpl. apply app_assoc. }
    simpl. ins. repeat rewrite app_assoc. reflexivity. }
  apply is_exist_cons_alt in H.
  simpl.
  destruct H.
  { rewrite map_app, concat_app.
    generalize (concat (map (fun f0 : t => map (f f0) lst') lst)).
    simpl.
    generalize lst' as mas.
    induction mas using rev_ind.
    { simpl. ins. rewrite app_nil_r. reflexivity. }
    rewrite app_nil_r.
    repeat rewrite map_app.
    simpl.
    ins. rewrite Lem.
    rewrite filter_app. simpl.
    destruct (total_width (f x x0) <=? w) eqn:E1.
    { rewrite linear_pareto_exist.
      { repeat rewrite <- app_assoc.
        generalize (f a x0 :: nil).
        ins.
        assert (R : map (f a) mas ++ l0 ++ l ++ map (f x) mas =
                    map (f a) mas ++ (l0 ++ l) ++ map (f x) mas).
        { generalize (map (f a) mas).
          ins. destruct l1.
          { simpl. apply app_assoc. }
          simpl. repeat rewrite app_assoc. reflexivity. }
        rewrite R.
        generalize (l0 ++ l).
        rewrite app_nil_r in IHmas.
        apply IHmas. }
      generalize (map (f x) mas).
      generalize mas.
      ins.
      induction mas0.
      { simpl.
        rewrite (is_less_than_func f a x x0 w); auto.
        apply  is_exist_cons_alt.
        unfold func_correct in F.
        rewrite <- F.
        auto. }
      simpl.
      destruct (total_width (f a a0) <=? w) eqn:E2.
      { apply is_exist_cons_alt.
        rewrite IHmas0.
        auto. }
      apply IHmas0. }
    rewrite app_nil_r.
    repeat rewrite filter_app.
    generalize mas.
    generalize (filter (fun f0 : t => total_width f0 <=? w) (f a x0 :: nil)).
    generalize (filter (fun f0 : t => total_width f0 <=? w) l).
    ins.
    rewrite <- (app_nil_r (map (f a) mas0)).
    generalize (nil: list t).
    induction mas0 using rev_ind.
    { simpl. rewrite app_nil_r. reflexivity. }
    repeat rewrite map_app. simpl.
    rewrite (filter_app _  (map (f x) mas0)).
    simpl.
    ins.
    rewrite <- (app_assoc _ _ l2).
    destruct (total_width (f x x1) <=? w) eqn:E2.
    { rewrite Lem, linear_pareto_exist.
      { apply IHmas0. }
      repeat rewrite filter_app.
      repeat rewrite is_exist_cons_all.
      simpl.
      rewrite (is_less_than_func f a x x1 w); auto.
      rewrite is_exist_cons_alt.
      rewrite <- F. rewrite H. simpl.
      repeat rewrite or_assoc. auto. }
    rewrite app_nil_r.
    apply IHmas0. }
  rewrite map_app, concat_app. simpl.
  rewrite app_nil_r.
  generalize (map (f a) lst').
  ins. (* TODO: check this, it (Rew) can be done simplier *)
  assert (Rew: forall lst1 lst2, concat (map (fun f0 : t => map (f f0) lst1) lst2) =
         concat (map (fun f0 : t => map (f f0) (lst1 ++ (nil: list t))) lst2)).
  { ins. rewrite app_nil_r. reflexivity. }
  rewrite Rew.
  generalize (nil: list t).
  induction lst' using rev_ind.
  { ins. rewrite app_nil_r.
    reflexivity. }
  ins.
  repeat rewrite map_app.
  simpl.
  repeat rewrite app_assoc.
  rewrite filter_app. simpl.
  assert (Rew2 : concat (map (fun f0 : t => map (f f0) ((lst' ++ [x0]) ++ l0)) lst) =
                   concat (map (fun f0 : t => map (f f0) (lst' ++ ((x0::nil) ++ l0))) lst)).
    { simpl.
      generalize lst as mas.        
      destruct mas; auto. simpl.
      rewrite <- app_assoc. simpl. reflexivity. }
  rewrite Rew2. simpl.  
  destruct (total_width (f x x0) <=? w) eqn:E1.
  { rewrite linear_pareto_exist.
    { rewrite <- app_assoc.
      apply IHlst'. }
    repeat rewrite filter_app.
    repeat rewrite is_exist_cons_all.
    rewrite  cross_general_exist_helper; auto. }
  rewrite <- app_assoc.
  rewrite app_nil_r.
  apply IHlst'.
Qed.

Lemma remove_pareto lst lst' f w
      (F: func_correct f) :
  cross_general f w (pareto lst) (pareto lst') =
  cross_general f w lst lst'.
Proof.
Admitted.

Lemma cross_general_eq w f lst1 lst2 :
  pareto (FormatTrivial.cross_general w f lst1 lst2) =
  FormatList.cross_general f w lst1 lst2.
Proof.
Admitted.
  
Lemma pareto_beside a b w
      (H: neighb_pareto a b w) :
  pareto (FormatTrivial.besideDoc w (evaluatorTrivial w a) (evaluatorTrivial w b)) 
      = FormatList.besideDoc w (evaluatorList w a) (evaluatorList w b).
Proof.
  red in H. destruct H.
  rewrite <- H. rewrite <- H0.
  set (lst := evaluatorTrivial w a).
  set (arr := evaluatorTrivial w b).
  unfold besideDoc.
  rewrite remove_pareto.
  { unfold FormatTrivial.besideDoc.
    apply cross_general_eq. }
  apply beside_correct.
Qed.

Lemma pareto_above a b w
      (H: neighb_pareto a b w) :
  pareto (FormatTrivial.aboveDoc w (evaluatorTrivial w a) (evaluatorTrivial w b)) 
      = FormatList.aboveDoc w (evaluatorList w a) (evaluatorList w b).
Proof.
  red in H. destruct H.
  rewrite <- H. rewrite <- H0.
  set (lst := evaluatorTrivial w a).
  set (arr := evaluatorTrivial w b).
  unfold aboveDoc.
  rewrite remove_pareto.
  { unfold FormatTrivial.aboveDoc.
    apply cross_general_eq. }
  apply above_correct.
Qed.

Lemma pareto_fill a b w n
      (H: neighb_pareto a b w) :
  pareto (FormatTrivial.fillDoc w (evaluatorTrivial w a) (evaluatorTrivial w b) n) 
      = FormatList.fillDoc w (evaluatorList w a) (evaluatorList w b) n.
  red in H. destruct H.
  rewrite <- H. rewrite <- H0.
  set (lst := evaluatorTrivial w a).
  set (arr := evaluatorTrivial w b).
  unfold fillDoc.
  rewrite remove_pareto.
  { unfold FormatTrivial.fillDoc.
    apply cross_general_eq. }
  apply fill_correct.
Qed.

  (*
  unfold FormatTrivial.besideDoc. unfold FormatTrivial.cross_general.
  unfold add_general.
  
  generalize arr.
  induction lst using rev_ind.
  { intro lst'.
    unfold pareto at 1.  unfold FormatTrivial.besideDoc. simpl.
    unfold pareto at 1. simpl.
    unfold besideDoc, cross_general, add_general. unfold map_filter. simpl.
    generalize (pareto lst'). ins.
    induction l. auto.
    simpl. apply IHl. }
  intro lst'.
  unfold FormatTrivial.besideDoc.
  destruct (is_less_exist x lst) eqn:E1.
  { rewrite linear_pareto_exist, trivial_cross_general_exist; auto. apply IHlst.
    apply beside_correct. }
  rewrite linear_pareto_not_exist; auto.
  generalize E1.
  generalize lst as mas.
  generalize lst' as mas'.
  intro mas'.
  induction mas'.
  { ins.
    unfold besideDoc, cross_general. simpl.
    unfold FormatTrivial.cross_general. simpl.
    assert (IsNil: concat (map (fun _ : t => nil) (mas ++ [x])) = (nil: list t)).
    { generalize mas. ins.
      induction mas0. auto.
      simpl. auto. }
    rewrite IsNil. auto. }
  intros mas E.
  
  
   pareto (FormatTrivial.cross_general w add_beside (lst ++ [x]) lst') =
  besideDoc w (pareto (lst ++ [x])) (pareto lst')
Admitted.
  *)