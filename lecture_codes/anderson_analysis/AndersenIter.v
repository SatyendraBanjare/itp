Require Import Arith List TheoryList.

Require Import ListUtil Tactics Maps.
Require Import Pointer Machine AndersenModel AndersenSound.

Lemma incl_add : forall s a,
  AllocSet.incl s (AllocSet.add s a) = true.
  intros.
  generalize (AllocSet.In_add s a).
  generalize (AllocSet.incl_ok s (AllocSet.add s a)).
  intuition.
  apply H2; intros.
  generalize (H0 x); intuition.
Qed.

Lemma incl_add2 : forall s1 s2 a,
  AllocSet.incl s1 s2 = true
  -> AllocSet.incl (AllocSet.add s1 a) (AllocSet.add s2 a) = true.
  intros.
  generalize (AllocSet.incl_ok s1 s2).
  generalize (AllocSet.incl_ok (AllocSet.add s1 a) (AllocSet.add s2 a)).
  intuition.

  apply H3; intros.
  generalize (AllocSet.In_add s1 a x); intuition; subst.
  eauto.
  generalize (AllocSet.In_add s2 a x); intuition.
Qed.

Hint Resolve incl_add2.

Lemma incl_union2 : forall s1 s2 s3 s4,
  AllocSet.incl s1 s3 = true
  -> AllocSet.incl s2 s4 = true
  -> AllocSet.incl (AllocSet.union s1 s2)
  (AllocSet.union s3 s4) = true.
  intros.
  generalize (AllocSet.incl_ok s1 s3).
  generalize (AllocSet.incl_ok s2 s4).
  generalize (AllocSet.incl_ok (AllocSet.union s1 s2) (AllocSet.union s3 s4)).
  intuition.

  apply H5; intros.
  generalize (AllocSet.In_union H6); intuition eauto.
Qed.

Hint Resolve incl_union2.

Lemma incl_fold1 : forall (f : allocation_site -> AllocSet.set) x ls s,
  AllocSet.In x (fold_left
    (fun known site =>
      AllocSet.union known (f site))
    ls s) = true
  -> (AllocSet.In x s = true
    \/ exists y, In y ls /\ AllocSet.In x (f y) = true).
  induction ls; simpl; intuition.

  generalize (IHls (AllocSet.union s (f a))); intuition.
  destruct (AllocSet.In_union H0); intuition.
  right; eauto.

  destruct H0; intuition.
  right; eauto.
Qed.

Lemma incl_fold2 : forall (f : allocation_site -> AllocSet.set) x ls s,
  (AllocSet.In x s = true
    \/ exists y, In y ls /\ AllocSet.In x (f y) = true)
  -> AllocSet.In x (fold_left
    (fun known site =>
      AllocSet.union known (f site))
    ls s) = true.
  induction ls; simpl; intuition.

  firstorder.

  generalize (IHls (AllocSet.union s (f a))); intuition eauto.

  generalize (IHls (AllocSet.union s (f a))); intuition.
  destruct H0; intuition; subst.
  eauto.
  apply H2.
  eauto.
Qed.

Lemma incl_elems : forall t1 t2 y,
  AllocSet.incl t1 t2 = true
  -> In y (AllocSet.elems t1)
  -> In y (AllocSet.elems t2).
  intros.
  generalize (AllocSet.incl_ok t1 t2).
  generalize (AllocSet.elems_ok t1).
  generalize (AllocSet.elems_ok t2).
  intuition.

  generalize (H1 y).
  generalize (H2 y).
  intuition.
Qed.

Lemma incl_fold_read : forall (f1 f2 : allocation_site -> AllocSet.set) s1 s2 t1 t2,
  (forall a, AllocSet.incl (f1 a) (f2 a) = true)
  -> AllocSet.incl s1 s2 = true
  -> AllocSet.incl t1 t2 = true
  -> AllocSet.incl
  (fold_left
    (fun known site =>
      AllocSet.union known (f1 site))
    (AllocSet.elems t1) s1)
  (fold_left
    (fun known site =>
      AllocSet.union known (f2 site))
    (AllocSet.elems t2) s2) = true.
  intros.

  generalize (AllocSet.incl_ok
    (fold_left
      (fun (known : AllocSet.set) (site : allocation_site) =>
        AllocSet.union known (f1 site)) (AllocSet.elems t1) s1)
    (fold_left
      (fun (known : AllocSet.set) (site : allocation_site) =>
        AllocSet.union known (f2 site)) (AllocSet.elems t2) s2)); intuition.

  apply H4; intros.

  apply incl_fold2.
  destruct (incl_fold1 _ _ _ _ H2) as [Hcase | Hcase].

  eauto.

  destruct Hcase as [y [Helems Hin]].
  right; exists y; intuition.

  eapply incl_elems; eauto.

  eauto.
Qed.

Hint Resolve incl_fold_read.

Lemma incl_fold3' : forall a (f : allocation_site -> AllocSet.set) s ls h,
  AllocMap.sel h a = AllocSet.union (f a) s
  -> AllocMap.sel
  (fold_left (fun known site =>
    AllocMap.upd known site (AllocSet.union (f site) s))
  ls h) a = AllocSet.union (f a) s.
  induction ls; simpl; intuition.
  apply IHls.
  AllocMap_split.
Qed.

Lemma incl_fold3 : forall f s a ls h,
  if In_eq_dec eq_nat_dec a ls
    then AllocMap.sel (fold_left (fun known site =>
      AllocMap.upd known site (AllocSet.union (f site) s))
    ls h) a = AllocSet.union (f a) s
    else AllocMap.sel (fold_left (fun known site =>
      AllocMap.upd known site (AllocSet.union (f site) s))
    ls h) a = AllocMap.sel h a.
  induction ls; simpl; intuition.

  destruct (In_eq_dec eq_nat_dec a nil); trivial.
  inversion i.
  
  destruct (In_eq_dec eq_nat_dec a (a0 :: ls)).
  simpl in i; intuition; subst.

  apply incl_fold3'; auto.
  apply AllocMap.sel_upd_eq.

  destruct (In_eq_dec eq_nat_dec a ls); intuition.

  destruct (In_eq_dec eq_nat_dec a ls); intuition.
  
  wrong; intuition.

  rewrite IHls.
  apply AllocMap.sel_upd_neq.
  simpl in n.
  intuition.
Qed.

Lemma incl_fold_write : forall a s1 s2 t1 t2 h1 h2,
  AllocSet.incl (AllocMap.sel h1 a) (AllocMap.sel h2 a) = true
  -> AllocSet.incl s1 s2 = true
  -> AllocSet.incl t1 t2 = true
  -> AllocSet.incl
  (AllocMap.sel (fold_left (fun known site =>
    AllocMap.upd known site (AllocSet.union (AllocMap.sel h1 site) s1))
  (AllocSet.elems t1) h1) a)
  (AllocMap.sel (fold_left (fun known site =>
    AllocMap.upd known site (AllocSet.union (AllocMap.sel h2 site) s2))
  (AllocSet.elems t2) h2) a) = true.
  intros.

  generalize (incl_fold3 (AllocMap.sel h1) s1 a (AllocSet.elems t1) h1).
  generalize (incl_fold3 (AllocMap.sel h2) s2 a (AllocSet.elems t2) h2).
  destruct (In_eq_dec eq_nat_dec a (AllocSet.elems t1));
    destruct (In_eq_dec eq_nat_dec a (AllocSet.elems t2));
      intuition; rewrite H2; rewrite H3; auto.

  wrong.
  generalize (AllocSet.elems_ok t1 a).
  generalize (AllocSet.elems_ok t2 a).
  generalize (AllocSet.incl_ok t1 t2).
  intuition.
  
  apply AllocSet.incl_trans with (AllocMap.sel h2 a); auto.
Qed.

Hint Resolve incl_fold_write.

Definition ins_sites i :=
  match i with
    | AbsAllocate _ site => AllocSet.add AllocSet.empty site
    | _ => AllocSet.empty
  end.

Module VarSet : SET with Definition dom := var := AllocSet.

Definition ins_vars i :=
  match i with
    | AbsAllocate v _ => VarSet.add VarSet.empty v
    | AbsCopy v1 v2 => VarSet.add (VarSet.add VarSet.empty v1) v2
    | AbsRead v1 v2 => VarSet.add (VarSet.add VarSet.empty v1) v2
    | AbsWrite v1 v2 => VarSet.add (VarSet.add VarSet.empty v1) v2
  end.

Section prog.
  Variable program : list abstract_instruction.

  Definition pSites := fold_left AllocSet.union (map ins_sites program).
  Definition pVars := fold_left VarSet.union (map ins_vars program).
End prog.

Section fixed_point.
  Variable program : list abstract_instruction.

  Definition progSites := pSites program AllocSet.empty.
  Definition progVars := pVars program VarSet.empty.

  Record approx' (abs1 abs2 : abstract_state) : Prop := {
    approxVars : forall v, AllocSet.incl
      (VarMap.sel (avars abs1) v) (VarMap.sel (avars abs2) v) = true;
    approxHeap : forall a, AllocSet.incl
      (AllocMap.sel (aheap abs1) a) (AllocMap.sel (aheap abs2) a) = true
  }.

  Lemma increasing' : forall abs ins,
    approx' abs (abstract_exec ins abs).
    destruct ins; intuition; simpl.
    
    VarMap_split; apply incl_add.
    
    VarMap_split.
    
    VarMap_split; apply incl_fold_union.
    
    apply incl_write_bonanza.
  Qed.

  Lemma monotonic' : forall abs abs' ins,
    approx' abs abs'
    -> approx' (abstract_exec ins abs) (abstract_exec ins abs').
    destruct ins; intuition; simpl.

    destruct (eq_nat_dec v v0); subst.
    repeat rewrite VarMap.sel_upd_eq; eauto.
    repeat rewrite VarMap.sel_upd_neq; eauto.

    destruct (eq_nat_dec v v1); subst.
    repeat rewrite VarMap.sel_upd_eq; eauto.
    repeat rewrite VarMap.sel_upd_neq; eauto.

    destruct (eq_nat_dec v v1); subst.
    repeat rewrite VarMap.sel_upd_eq; eauto.
    repeat rewrite VarMap.sel_upd_neq; eauto.

    eauto.
  Qed.

  Lemma approx_refl' : forall s, approx' s s.
    intuition.
  Qed.

  Lemma approx_trans' : forall s1 s2 s3,
    approx' s1 s2 -> approx' s2 s3 -> approx' s1 s3.
    intuition.
    eapply AllocSet.incl_trans; eauto.
    eapply AllocSet.incl_trans; eauto.
  Qed.

  Lemma approx_init' : forall s, approx' abstract_initState s.
    unfold abstract_initState; intuition; simpl; intuition.
    rewrite VarMap.sel_init; apply AllocSet.incl_empty.
    rewrite AllocMap.sel_init; apply AllocSet.incl_empty.
  Qed.

  Record valid (abs : abstract_state) : Prop := {
    validVarsDom : forall v, VarSet.In v progVars = false
      -> AllocSet.incl (VarMap.sel (avars abs) v) AllocSet.empty = true;
    validHeapDom : forall a, AllocSet.In a progSites = false
      -> AllocSet.incl (AllocMap.sel (aheap abs) a) AllocSet.empty = true;
    validVars : forall v, AllocSet.incl (VarMap.sel (avars abs) v) progSites = true;
    validHeap : forall a, AllocSet.incl (AllocMap.sel (aheap abs) a) progSites = true
  }.

  Definition astate := sig valid.

  Definition approx (abs1 abs2 : astate) := approx' (proj1_sig abs1) (proj1_sig abs2).

  Record approxStrict (abs1 abs2 : astate) : Prop := {
    strictApprox : approx abs2 abs1;
    strictNe : (exists v, VarSet.In v progVars = true
      /\ AllocSet.incl (VarMap.sel (avars (proj1_sig abs1)) v)
      (VarMap.sel (avars (proj1_sig abs2)) v) = false)
    \/ exists a, AllocSet.In a progSites = true
      /\ AllocSet.incl (AllocMap.sel (aheap (proj1_sig abs1)) a)
      (AllocMap.sel (aheap (proj1_sig abs2)) a) = false
  }.

  Definition ainstruction := sig (fun ins => In ins program).

  Lemma fold_In_union : forall a ls s,
    AllocSet.In a s = true
    -> AllocSet.In a (fold_left AllocSet.union ls s) = true.
    induction ls; simpl; intuition eauto.
  Qed.

  Hint Resolve VarSet.incl_In VarSet.incl_union_left.

  Lemma fold_In_unionv : forall a ls s,
    VarSet.In a s = true
    -> VarSet.In a (fold_left VarSet.union ls s) = true.
    induction ls; simpl; intuition eauto.
  Qed.

  Lemma allocate_site : forall v a prog s,
    In (AbsAllocate v a) prog
      -> AllocSet.In a (pSites prog s) = true.
    unfold pSites.

    induction prog; simpl; intuition; subst.

    unfold pSites; simpl.
    apply fold_In_union; eauto.
  Qed.

  Lemma incl_add3 : forall x s1 s2,
    AllocSet.In x s2 = true
    -> AllocSet.incl s1 s2 = true
    -> AllocSet.incl (AllocSet.add s1 x) s2 = true.
    intros.
    generalize (AllocSet.incl_ok (AllocSet.add s1 x) s2); intuition.
    apply H3; intros.
    generalize (AllocSet.In_add s1 x x0);
      generalize (AllocSet.incl_ok s1 s2);
	intuition; subst; intuition.
  Qed.

  Lemma incl_union : forall s1 s2 s3,
    AllocSet.incl s1 s3 = true
    -> AllocSet.incl s2 s3 = true
    -> AllocSet.incl (AllocSet.union s1 s2) s3 = true.
    intros.
    generalize (AllocSet.incl_ok (AllocSet.union s1 s2) s3); intuition.
    apply H3; intros.
    generalize (AllocSet.incl_ok s1 s3);
      generalize (AllocSet.incl_ok s2 s3);
	generalize (AllocSet.In_union H1);
	  intuition.
  Qed.

  Lemma incl_valid_read : forall (f : allocation_site -> AllocSet.set) s2 ls s1,
    AllocSet.incl s1 s2 = true
    -> (forall site, AllocSet.incl (f site) s2 = true)
    -> AllocSet.incl
    (fold_left
      (fun known site => AllocSet.union known (f site))
      ls s1) s2 = true.
    induction ls; simpl; intuition.
    apply IHls; auto.
    apply incl_union; auto.
  Qed.

  Lemma incl_valid_write : forall a s1 s2 f ls h,
    AllocSet.incl s1 s2 = true
    -> (forall a, AllocSet.incl (f a) s2 = true)
    -> (forall a, AllocSet.incl (AllocMap.sel h a) s2 = true)
    -> AllocSet.incl
    (AllocMap.sel
      (fold_left
	(fun known site => AllocMap.upd known site
          (AllocSet.union (f site) s1))
	ls h) a)
    s2 = true.
    induction ls; simpl; intuition.

    apply IHls; intuition.
    AllocMap_split.
    apply incl_union; auto.
  Qed.
  
  Hint Resolve VarSet.In_add_eq VarSet.In_add_neq VarSet.incl_union_right.

  Lemma allocate_var : forall v a prog s,
    In (AbsAllocate v a) prog
      -> VarSet.In v (pVars prog s) = true.
    unfold pVars.

    induction prog; simpl; intuition; subst.

    unfold pVars; simpl.
    apply fold_In_unionv; eauto.
  Qed.

  Lemma copy_var : forall v a prog s,
    In (AbsCopy v a) prog
      -> VarSet.In v (pVars prog s) = true.
    unfold pVars.

    induction prog; simpl; intuition; subst.

    unfold pVars; simpl.
    apply fold_In_unionv.
    apply VarSet.incl_In with (VarSet.add (VarSet.add VarSet.empty v) a).
    eauto.
    destruct (eq_nat_dec v a); subst; eauto.
    rewrite VarSet.In_add_neq; auto.
  Qed.

  Lemma read_var : forall v a prog s,
    In (AbsRead v a) prog
      -> VarSet.In v (pVars prog s) = true.
    unfold pVars.

    induction prog; simpl; intuition; subst.

    unfold pVars; simpl.
    apply fold_In_unionv.
    apply VarSet.incl_In with (VarSet.add (VarSet.add VarSet.empty v) a).
    eauto.
    destruct (eq_nat_dec v a); subst; eauto.
    rewrite VarSet.In_add_neq; auto.
  Qed.

  Lemma write_var : forall v a prog s,
    In (AbsWrite v a) prog
      -> VarSet.In v (pVars prog s) = true.
    unfold pVars.

    induction prog; simpl; intuition; subst.

    unfold pVars; simpl.
    apply fold_In_unionv.
    apply VarSet.incl_In with (VarSet.add (VarSet.add VarSet.empty v) a).
    eauto.
    destruct (eq_nat_dec v a); subst; eauto.
    rewrite VarSet.In_add_neq; auto.
  Qed.

  Lemma sel_write_valid : forall f s a ls h,
    AllocMap.sel
    (fold_left (fun known site => AllocMap.upd known site
      (AllocSet.union (f site) s))
    ls h) a
    = if In_eq_dec eq_nat_dec a ls
      then AllocSet.union (f a) s
      else AllocMap.sel h a.
    induction ls; simpl; intuition;
      match goal with
	| [ |- context[if ?X then _ else _] ] => destruct X
      end; simpl in *; intuition; subst; intuition.

    apply incl_fold3'; apply AllocMap.sel_upd_eq.

    destruct (In_eq_dec eq_nat_dec a ls); intuition.

    destruct (In_eq_dec eq_nat_dec a ls); intuition.
    rewrite IHls.
    rewrite AllocMap.sel_upd_neq; auto.
  Qed.

  Lemma aexec' : forall ins abs, In ins program -> valid abs -> valid (abstract_exec ins abs).
    intros ins abs Hins Habs.
    destruct Habs.
    destruct ins; split; simpl; intuition.

    VarMap_split.
    wrong.
    unfold progVars in H; rewrite allocate_var with v0 a program VarSet.empty in H;
      auto; discriminate.

    VarMap_split.
    apply incl_add3; auto.
    unfold progSites; eapply allocate_site; eauto.

    VarMap_split.
    wrong.
    unfold progVars in H; rewrite copy_var with v1 v0 program VarSet.empty in H;
      auto; discriminate.

    VarMap_split.
    apply incl_union; auto.

    VarMap_split.
    unfold progVars in H; rewrite read_var with v1 v0 program VarSet.empty in H;
      auto; discriminate.

    VarMap_split.
    apply incl_valid_read; auto.

    rewrite sel_write_valid.
    match goal with
      | [ |- context[if ?X then _ else _] ] => destruct X
    end; auto.
    caseEq (VarSet.In v progVars); intro Hin.
    assert (false = true); [idtac | discriminate].
    rewrite <- H.
    apply AllocSet.incl_In with (VarMap.sel (avars abs) v); auto.
    generalize (AllocSet.elems_ok (VarMap.sel (avars abs) v)); intuition.
    generalize (H0 a); intuition.
    unfold progVars in Hin; rewrite write_var with v v0 program VarSet.empty in Hin;
      auto; discriminate.
    
    apply incl_valid_write; auto.
  Qed.

  Definition aexec : ainstruction -> astate -> astate.
    intros ins abs.
    destruct ins as [ins Hins].
    destruct abs as [abs Habs].
    exists (abstract_exec ins abs).
    apply aexec'; trivial.
  Defined.

  Definition ainitState : astate.
    exists abstract_initState.
    unfold abstract_initState.
    split; simpl; intuition.

    rewrite VarMap.sel_init; apply AllocSet.incl_empty.
    rewrite AllocMap.sel_init; apply AllocSet.incl_empty.
    rewrite VarMap.sel_init; apply AllocSet.incl_empty.
    rewrite AllocMap.sel_init; apply AllocSet.incl_empty.
  Defined.

  Lemma ainstr_widen : forall h t,
    {ins : abstract_instruction | In ins t}
    -> {ins : abstract_instruction | In ins (h :: t)}.
    intros.
    destruct H as [ins Hins].
    exists ins.
    intuition.
  Defined.

  Definition aprogram' : forall (prog : list abstract_instruction),
    list (sig (fun ins => In ins prog)).
    refine (fix aprogram' (prog : list abstract_instruction)
      : list (sig (fun ins => In ins prog)) :=
      match prog return list (sig (fun ins => In ins prog)) with
	| nil => nil
	| h :: t => exist _ h _ :: map (ainstr_widen _ _) (aprogram' t)
      end); intuition.
  Defined.

  Definition aprogram := aprogram' program.
    
  Theorem increasing : forall abs ins,
    approx abs (aexec ins abs).
    destruct abs as [abs Habs].
    destruct ins as [ins Hins].
    unfold approx.
    simpl.
    apply increasing'.
  Qed.

  Hint Resolve increasing.

  Theorem monotonic : forall abs abs' ins,
    approx abs abs'
    -> approx (aexec ins abs) (aexec ins abs').
    destruct abs as [abs Habs].
    destruct abs' as [abs' Habs'].
    destruct ins as [ins Hins].
    unfold approx.
    simpl.
    apply monotonic'.
  Qed.

  Hint Resolve monotonic.

  Theorem approx_refl : forall s, approx s s.
    destruct s as [s Hs].
    unfold approx.
    simpl.
    apply approx_refl'.
  Qed.

  Hint Resolve approx_refl.

  Theorem approx_trans : forall s1 s2 s3,
    approx s1 s2 -> approx s2 s3 -> approx s1 s3.
    destruct s1.
    destruct s2.
    destruct s3.
    unfold approx.
    simpl.
    apply approx_trans'.
  Qed.

  Hint Resolve approx_trans.

  Theorem approx_init : forall s, approx ainitState s.
    destruct s.
    unfold approx, ainitState.
    simpl.
    apply approx_init'.
  Qed.

  Hint Resolve approx_init.

  Hint Resolve AllocSet.incl_empty.

  Theorem approxStrict_approx : forall s1 s2,
    approx s2 s1
    -> ~approxStrict s1 s2
    -> approx s1 s2.
    destruct s1.
    destruct s2.
    intuition.
    destruct H.
    split; simpl in *; intuition.

    caseEq (AllocSet.incl (VarMap.sel (avars x) v1) (VarMap.sel (avars x0) v1)); intro Heq; trivial.
    wrong.
    apply H0.
    intuition.
    unfold approx; simpl; intuition.
    left.
    exists v1.
    intuition.

    inversion v.
    caseEq (VarSet.In v1 progVars); intro Heq'; trivial.
    rewrite <- Heq.
    apply AllocSet.incl_trans with AllocSet.empty; eauto.
    
    caseEq (AllocSet.incl (AllocMap.sel (aheap x) a) (AllocMap.sel (aheap x0) a));
    intro Heq; trivial.
    wrong.
    apply H0.
    intuition.
    unfold approx; simpl; intuition.
    right.
    exists a.
    intuition.

    inversion v.
    caseEq (AllocSet.In a progSites); intro Heq'; trivial.
    rewrite <- Heq.
    apply AllocSet.incl_trans with AllocSet.empty; eauto.
  Qed.

  Hint Resolve approxStrict_approx.

  Theorem approxStrict_trans : forall s1 s2 s3,
    approx s2 s1 -> approxStrict s2 s3 -> approxStrict s1 s3.
    destruct s1.
    destruct s2.
    destruct s3.
    unfold approx; simpl.
    intuition; unfold approx in *; simpl in *; intuition.

    eapply AllocSet.incl_trans; eauto.

    eapply AllocSet.incl_trans; eauto.

    left.
    destruct H as [v' [Hin Hincl]].
    exists v'; intuition.
    caseEq (AllocSet.incl (VarMap.sel (avars x) v') (VarMap.sel (avars x1) v')); trivial; intro Heq.
    rewrite <- Hincl.
    symmetry.
    eapply AllocSet.incl_trans; eauto.

    eapply AllocSet.incl_trans; eauto.
    eapply AllocSet.incl_trans; eauto.

    right.
    destruct H as [a [Hin Hincl]].
    exists a; intuition.
    caseEq (AllocSet.incl (AllocMap.sel (aheap x) a) (AllocMap.sel (aheap x1) a)); trivial; intro Heq.
    rewrite <- Hincl.
    symmetry.
    eapply AllocSet.incl_trans; eauto.
  Qed.

  Hint Resolve approxStrict_trans.

  Definition approx_dec : forall abs1 abs2, {approx abs1 abs2} + {~approx abs1 abs2}.
    destruct abs1 as [abs1 Habs1].
    destruct abs2 as [abs2 Habs2].
      
    assert (checkVar : forall v,
      {AllocSet.incl
	(VarMap.sel (avars abs1) v)
	(VarMap.sel (avars abs2) v) = true}
      + {~AllocSet.incl
	(VarMap.sel (avars abs1) v)
	(VarMap.sel (avars abs2) v) = true}).
    intro.
    destruct (AllocSet.incl (VarMap.sel (avars abs1) v)
      (VarMap.sel (avars abs2) v)); auto.

    assert (checkHeap : forall v,
      {AllocSet.incl
	(AllocMap.sel (aheap abs1) v)
	(AllocMap.sel (aheap abs2) v) = true}
      + {~AllocSet.incl
	(AllocMap.sel (aheap abs1) v)
	(AllocMap.sel (aheap abs2) v) = true}).
    intro.
    destruct (AllocSet.incl (AllocMap.sel (aheap abs1) v)
      (AllocMap.sel (aheap abs2) v)); auto.

    refine (match AllS_dec (fun v => AllocSet.incl
      (VarMap.sel (avars abs1) v)
      (VarMap.sel (avars abs2) v) = true)
    checkVar (VarSet.elems progVars) with
	      | left Hvars =>
		match AllS_dec (fun v => AllocSet.incl
		  (AllocMap.sel (aheap abs1) v)
		  (AllocMap.sel (aheap abs2) v) = true)
		checkHeap (AllocSet.elems progSites) with
		  | left Hheap => left _ _
		  | right Hheap => right _ _
		end
	      | right Hvars => right _ _
	    end); intuition.

    unfold approx in *; simpl in *; intuition.

    caseEq (VarSet.In v progVars); intro Heq.
    pattern v; eapply AllS_In; eauto.
    generalize (VarSet.elems_ok progVars); intuition.
    generalize (H v); intuition.
    
    inversion Habs1.
    apply AllocSet.incl_trans with AllocSet.empty; eauto.

    caseEq (AllocSet.In a progSites); intro Heq.
    pattern a; eapply AllS_In; eauto.
    generalize (AllocSet.elems_ok progSites); intuition.
    generalize (H a); intuition.
    
    inversion Habs1.
    apply AllocSet.incl_trans with AllocSet.empty; eauto.

    unfold approx in H; simpl in H; intuition.
    apply Hheap.
    apply AllS_deduce; auto.
    
    unfold approx in H; simpl in H; intuition.
    apply Hvars.
    apply AllS_deduce; auto.
  Qed.

  Definition approxStrict_dec : forall abs1 abs2, {approxStrict abs1 abs2} + {~approxStrict abs1 abs2}.
    destruct abs1 as [abs1 Habs1].
    destruct abs2 as [abs2 Habs2].

    assert (checkVar : forall v,
      {AllocSet.incl (VarMap.sel (avars abs1) v)
	(VarMap.sel (avars abs2) v) = true}
      + {~AllocSet.incl (VarMap.sel (avars abs1) v)
	(VarMap.sel (avars abs2) v) = true}).
    intros.
    match goal with
      [ |- {?X = true} + {_} ] => destruct X
    end; intuition.

    assert (checkHeap : forall v,
      {AllocSet.incl (AllocMap.sel (aheap abs1) v)
	(AllocMap.sel (aheap abs2) v) = true}
      + {~AllocSet.incl (AllocMap.sel (aheap abs1) v)
	(AllocMap.sel (aheap abs2) v) = true}).
    intros.
    match goal with
      [ |- {?X = true} + {_} ] => destruct X
    end; intuition.

    refine (match approx_dec (exist _ abs2 Habs2) (exist _ abs1 Habs1) with
	      | left Happrox =>
		match AllS_dec_some (fun v => AllocSet.incl (VarMap.sel (avars abs1) v)
		  (VarMap.sel (avars abs2) v) = true)
		checkVar (VarSet.elems progVars) with
		  | left Hvars =>
		    match AllS_dec_some (fun v => AllocSet.incl (AllocMap.sel (aheap abs1) v)
		      (AllocMap.sel (aheap abs2) v) = true)
		    checkHeap (AllocSet.elems progSites) with
		      | left Hheap => right _ _
		      | right Hheap => left _ _
		    end
		  | right Hvars => left _ _
		end
	      | right Happrox => right _ _
	    end); intuition; try (injection Heq; intros; subst; intuition).

    destruct H as [v [Hin Hincl]].
    simpl in *; idtac.
    rewrite (AllS_In Hvars) in Hincl; try discriminate.
    generalize (VarSet.elems_ok progVars); intuition.
    generalize (H v); intuition.

    destruct H as [a [Hin Hincl]].
    simpl in *; idtac.
    rewrite (AllS_In Hheap) in Hincl; try discriminate.
    generalize (AllocSet.elems_ok progSites); intuition.
    generalize (H a); intuition.

    right.
    destruct (AllS_not (f := fun v : AllocMap.dom =>
      AllocSet.incl (AllocMap.sel (aheap abs1) v)
      (AllocMap.sel (aheap abs2) v) = true) checkHeap H); intuition.
    destruct H1 as [x [Hin Hincl]].
    exists x; simpl; intuition.
    generalize (AllocSet.elems_ok progSites); intuition.
    generalize (H1 x); intuition.
    match goal with
      | [ |- ?X = _ ] => destruct X
    end; intuition.

    left.
    destruct (AllS_not (f := fun v : VarMap.dom =>
      AllocSet.incl (VarMap.sel (avars abs1) v)
      (VarMap.sel (avars abs2) v) = true) checkVar H); intuition.
    destruct H1 as [x [Hin Hincl]].
    exists x; simpl; intuition.
    generalize (VarSet.elems_ok progVars); intuition.
    generalize (H1 x); intuition.
    match goal with
      | [ |- ?X = _ ] => destruct X
    end; intuition.
  Qed.

  Hint Resolve approxStrict_dec.

  Fixpoint distinct (ls : list nat) : Prop :=
    match ls with
      | nil => True
      | h::t => AllS (fun x => x <> h) t
	/\ distinct t
    end.

  Definition cardinality_atLeast s n :=
    exists ls, distinct ls
      /\ length ls = n
      /\ AllS (fun x => AllocSet.In x s = true) ls.
  
  Definition cardinality s n :=
    cardinality_atLeast s n
    /\ forall n', cardinality_atLeast s n' -> n' <= n.

  Definition bound := length (AllocSet.elems progSites).

  Definition neq_nat_dec : forall (x y : nat), {x <> y} + {~x <> y}.
    intros.
    destruct (eq_nat_dec x y); auto.
  Defined.

  Definition distinctify : forall (ls : list allocation_site),
    {ls' : list allocation_site | distinct ls'
      /\ forall x, In x ls <-> In x ls'}.
    induction ls.

    exists (@nil allocation_site); simpl; intuition.

    destruct IHls as [ls' [Hdist Hin]].
    destruct (AllS_dec (fun x => x <> a) (fun x => neq_nat_dec x a) ls').
    exists (a :: ls'); simpl; firstorder.

    destruct (AllS_not_dec (f := fun x : allocation_site => x <> a)
      (fun x => neq_nat_dec x a) n) as [[x [Hin' Hnot]] | Heq].
    exists ls'; intuition.
    generalize (Hin x0); intuition.
    simpl in H; intuition; subst.
    replace x0 with x; auto.
    destruct (eq_nat_dec x x0); intuition.

    simpl; right.
    generalize (Hin x0); intuition.

    rewrite Heq in n.
    wrong.
    intuition.
  Qed.

  Lemma incl_S : forall (ls : list allocation_site) a,
    In a ls
    -> exists ls', length ls = S (length ls')
      /\ incl ls (a :: ls').
    induction ls; simpl; intuition; subst.
    firstorder.
    
    destruct (eq_nat_dec a0 a); subst.
    exists ls; intuition.

    destruct (IHls _ H0) as [ls' [Hlen Hincl]].
    rewrite Hlen.
    exists (a :: ls'); intuition.
    red; intros.
    red in Hincl.
    simpl in *; intuition.
    destruct (Hincl a1); intuition.
  Qed.

  Lemma incl_trans' : forall (a : allocation_site) ls1 ls2,
    distinct (a :: ls1)
    -> incl (a :: ls1) (a :: ls2)
    -> incl ls1 ls2.
    unfold incl; intuition.
    destruct (eq_nat_dec a0 a); subst.
    simpl in H; intuition.
    wrong.

    generalize H1 H2; clear_all.
    induction ls1; simpl; intuition; subst.
    generalize (AllS_In H2 a); intuition.
    apply H0.
    inversion H2; intuition.

    assert (In a0 (a :: ls2)).
    intuition.
    inversion H2; intuition.
    wrong; intuition.
  Qed.

  Lemma incl_length : forall (ls1 ls2 : list allocation_site),
    incl ls1 ls2
    -> distinct ls1
    -> length ls1 <= length ls2.
    induction ls1.

    destruct ls2; intuition.
    
    simpl; intuition.
    assert (exists ls', length ls2 = S (length ls')
      /\ incl ls2 (a :: ls')).
    apply incl_S; intuition.
    destruct H0 as [ls' [Hlen Hincl]].
    rewrite Hlen.
    generalize (IHls1 ls'); intuition.
    assert (incl ls1 ls').
    apply incl_trans' with a; simpl; intuition.
    red; intros.
    inversion H3; subst; intuition.
    
    intuition.
  Qed.

  Lemma card : forall s,
    AllocSet.incl s progSites = true
    -> {n : nat
      | n <= bound
	/\ cardinality s n}.
    intros.
    destruct (distinctify (AllocSet.elems s)) as [ls [Hdis Hin]].
    exists (length ls); intuition.

    unfold bound.
    generalize (AllocSet.elems_ok progSites).
    generalize (AllocSet.elems_ok s).
    generalize (AllocSet.incl_ok s progSites).
    intuition.
    apply incl_length; auto.
    red; intros.
    generalize (Hin a); intuition.
    generalize (H1 a).
    generalize (H0 a).
    generalize (H2 a).
    intuition.

    split.
    unfold cardinality_atLeast.
    exists ls; intuition.
    apply AllS_deduce; intuition.
    generalize (AllocSet.elems_ok s); intuition.
    generalize (H1 x); intuition.
    apply H3.
    generalize (Hin x); intuition.

    intros.
    destruct H0 as [ls' Hls']; intuition.
    rewrite <- H2.
    apply incl_length; auto.
    red; intros.
    generalize (AllS_In H3 _ H1); intro Hin'.
    generalize (AllocSet.elems_ok s).
    generalize (Hin a); intuition.
    apply H6.
    generalize (H5 a); intuition.
  Qed.

  Definition var_bounded : forall (abs : astate) (v : var),
    AllocSet.incl (VarMap.sel (avars (proj1_sig abs)) v) progSites = true.
    destruct abs as [abs Habs]; simpl.
    inversion Habs.
    eauto.
  Qed.

  Definition site_bounded : forall (abs : astate) (s : allocation_site),
    AllocSet.incl (AllocMap.sel (aheap (proj1_sig abs)) s) progSites = true.
    destruct abs as [abs Habs]; simpl.
    inversion Habs.
    eauto.
  Qed.

  Definition size (abs : astate) :=
    fold_right plus 0 (map (fun x => proj1_sig (card _ (var_bounded abs x)))
      (VarSet.elems progVars))
    + fold_right plus 0 (map (fun x => proj1_sig (card _ (site_bounded abs x)))
      (AllocSet.elems progSites)).
  
  Lemma mult_le : forall n x m y,
    x <= n * m
    -> y <= n
    -> y + x <= n * S m.
    intros.
    replace (n * S m) with (n + n * m).
    omega.

    clear_all.
    induction n; simpl; intuition.
  Qed.

  Lemma size_bounded : forall abs,
    size abs <= bound * (length (VarSet.elems progVars) + length (AllocSet.elems progSites)).
    unfold size.
    intros.
    induction (VarSet.elems progVars); simpl.

    induction (AllocSet.elems progSites); simpl; intuition.

    destruct (card (AllocMap.sel (aheap (proj1_sig abs)) a) (site_bounded abs a)); simpl; intuition.
    apply mult_le; trivial.

    destruct (card (VarMap.sel (avars (proj1_sig abs)) a) (var_bounded abs a)); simpl; intuition.
    generalize (mult_le _ _ _ _ IHl H).
    omega.
  Qed.

  Lemma fold_plus_ge : forall (A : Set) f1 f2 (ls : list A),
    AllS (fun x => f1 x >= f2 x) ls
    -> fold_right plus 0 (map f1 ls) >= fold_right plus 0 (map f2 ls).
    induction ls; simpl; intuition.
    inversion H; subst.
    intuition.
  Qed.

  Lemma fold_plus_gt : forall (A : Set) f1 f2 x,
    f1 x > f2 x
    -> forall (ls : list A), AllS (fun x => f1 x >= f2 x) ls
    -> In x ls
    -> fold_right plus 0 (map f1 ls) > fold_right plus 0 (map f2 ls).
    induction ls; simpl; intuition; subst.
    
    inversion H0; subst.
    generalize (fold_plus_ge _ _ _ _ H4).
    omega.

    inversion H0; subst.
    intuition.
  Qed.
  
  Lemma sum_plus1 : forall x1 y1 x2 y2,
    x1 > x2
    -> y1 >= y2
    -> x1 + y1 > x2 + y2.
    intros; omega.
  Qed.

  Lemma sum_plus2 : forall x1 y1 x2 y2,
    x1 >= x2
    -> y1 > y2
    -> x1 + y1 > x2 + y2.
    intros; omega.
  Qed.

  Lemma incl_cardinality' : forall s1 s2 c,
    AllocSet.incl s1 s2 = true
    -> cardinality_atLeast s1 c
    -> cardinality_atLeast s2 c.
    intros.
    destruct H0 as [ls]; intuition.
    exists ls; intuition.
    apply AllS_deduce; intros.
    apply AllocSet.incl_In with s1; auto.
    apply (AllS_In H3); auto.
  Qed.

  Lemma incl_cardinality : forall s1 s2 c1 c2,
    AllocSet.incl s1 s2 = true
    -> cardinality s1 c1
    -> cardinality s2 c2
    -> c1 <= c2.
    intros.
    destruct H0.
    destruct H1.
    destruct H1 as [ls2 Hls2].
    intuition.
    
    apply H3.
    eapply incl_cardinality'; eauto.
  Qed.

  Lemma incl_gt : forall (x : allocation_site) ls2 ls1,
    distinct ls1
    -> incl ls1 ls2
    -> ~In x ls1
    -> In x ls2
    -> length ls2 > length ls1.
    intros.

    assert (incl (x :: ls1) ls2).
    red; simpl; intuition; subst; trivial.

    assert (length (x :: ls1) <= length ls2).
    apply incl_length; trivial.
    split; intuition.
    apply AllS_deduce.
    intros; subst; auto.

    simpl in H4.
    unfold allocation_site in H4.
    omega.
  Qed.

  Lemma set_grew : forall s1 s2 c1 c2,
    AllocSet.incl s2 s1 = true
    -> AllocSet.incl s1 s2 = false
    -> cardinality s1 c1
    -> cardinality s2 c2
    -> c1 > c2.
    intros.

    destruct (AllocSet.incl_false H0) as [x [Hyes Hno]].

    destruct H1.
    destruct H2.
    destruct H1 as [ls1 Hls1].
    destruct H2 as [ls2 Hls2]; intuition.

    subst.
    apply incl_gt with x; eauto.
    
    red; intros.
    destruct (In_dec eq_nat_dec a ls1); trivial.
    wrong.
    assert (S (length ls1) <= length ls1).
    apply H3.
    exists (a :: ls1); simpl; intuition.
    apply AllS_deduce.
    intros; subst; auto.
    constructor; intuition.
    apply AllocSet.incl_In with s2; auto.
    apply (AllS_In H9); auto.
    omega.

    intro.
    assert (AllocSet.In x s2 = true).
    apply (AllS_In H9); auto.
    congruence.

    destruct (In_dec eq_nat_dec x ls1); trivial.
    wrong.
    assert (S (length ls1) <= length ls1).
    apply H3.
    exists (x :: ls1); simpl; intuition.
    apply AllS_deduce.
    intros; subst; auto.
    omega.
  Qed.

  Lemma size_approxStrict : forall abs abs',
    approxStrict abs abs'
    -> size abs > size abs'.
    destruct abs as [abs Habs].
    destruct abs' as [abs' Habs'].
    intros.
    destruct H; simpl in *; idtac.
    destruct strictNe0 as [[v [Hin Hincl]] | [a [Hin Hincl]]].

    unfold size; simpl.
    apply sum_plus1.

    apply fold_plus_gt with v.
    destruct (card (VarMap.sel (avars abs) v)
      (var_bounded (exist valid abs Habs) v)) as [c1 [Hlt1 Hc1]]; simpl.
    destruct (card (VarMap.sel (avars abs') v)
      (var_bounded (exist valid abs' Habs') v)) as [c2 [Hlt2 Hc2]]; simpl.
    apply set_grew with (VarMap.sel (avars abs) v) (VarMap.sel (avars abs') v); intuition.
    destruct strictApprox0.
    simpl in *; auto.

    apply AllS_deduce; intros.
    destruct (card (VarMap.sel (avars abs) x)
      (var_bounded (exist valid abs Habs) x)) as [c1 [Hlt1 Hc1]]; simpl.
    destruct (card (VarMap.sel (avars abs') x)
      (var_bounded (exist valid abs' Habs') x)) as [c2 [Hlt2 Hc2]]; simpl.
    assert (c2 <= c1); try omega.
    apply incl_cardinality with (VarMap.sel (avars abs') x) (VarMap.sel (avars abs) x); auto.
    destruct strictApprox0.
    simpl in *; auto.

    generalize (VarSet.elems_ok progVars); intuition.
    generalize (H v); intuition.
    
    apply fold_plus_ge.
    apply AllS_deduce; intros.
    destruct (card (AllocMap.sel (aheap abs) x)
      (site_bounded (exist valid abs Habs) x)) as [c1 [Hlt1 Hc1]]; simpl.
    destruct (card (AllocMap.sel (aheap abs') x)
        (site_bounded (exist valid abs' Habs') x)) as [c2 [Hlt2 Hc2]]; simpl.
    assert (c2 <= c1); try omega.
    apply incl_cardinality with (AllocMap.sel (aheap abs') x) (AllocMap.sel (aheap abs) x); auto.
    destruct strictApprox0.
    simpl in *; auto.

    unfold size; simpl.
    apply sum_plus2.

    apply fold_plus_ge.
    apply AllS_deduce; intros.
    destruct (card (VarMap.sel (avars abs) x)
      (var_bounded (exist valid abs Habs) x)) as [c1 [Hlt1 Hc1]]; simpl.
    destruct (card (VarMap.sel (avars abs') x)
        (var_bounded (exist valid abs' Habs') x)) as [c2 [Hlt2 Hc2]]; simpl.
    assert (c2 <= c1); try omega.
    apply incl_cardinality with (VarMap.sel (avars abs') x) (VarMap.sel (avars abs) x); auto.
    destruct strictApprox0.
    simpl in *; auto.

    apply fold_plus_gt with a.
    destruct (card (AllocMap.sel (aheap abs) a)
        (site_bounded (exist valid abs Habs) a)) as [c1 [Hlt1 Hc1]]; simpl.
    destruct (card (AllocMap.sel (aheap abs') a)
        (site_bounded (exist valid abs' Habs') a)) as [c2 [Hlt2 Hc2]]; simpl.
    apply set_grew with (AllocMap.sel (aheap abs) a) (AllocMap.sel (aheap abs') a); intuition.
    destruct strictApprox0.
    simpl in *; auto.

    apply AllS_deduce; intros.
    destruct (card (AllocMap.sel (aheap abs) x)
      (site_bounded (exist valid abs Habs) x)) as [c1 [Hlt1 Hc1]]; simpl.
    destruct (card (AllocMap.sel (aheap abs') x)
      (site_bounded (exist valid abs' Habs') x)) as [c2 [Hlt2 Hc2]]; simpl.
    assert (c2 <= c1); try omega.
    apply incl_cardinality with (AllocMap.sel (aheap abs') x) (AllocMap.sel (aheap abs) x); auto.
    destruct strictApprox0.
    simpl in *; auto.

    generalize (AllocSet.elems_ok progSites); intuition.
    generalize (H a); intuition.
  Qed.

  Lemma approxStrict_wf' : forall n a,
    bound * (length (VarSet.elems progVars) + length (AllocSet.elems progSites)) - size a <= n
    -> Acc approxStrict a.
    induction n; simpl; intuition.

    constructor; intros.
    wrong.
    generalize (size_approxStrict _ _ H0).
    generalize (size_bounded y).
    omega.

    constructor; intros.
    apply IHn.
    generalize (size_approxStrict _ _ H0).
    omega.
  Qed.

  Theorem approxStrict_wf : well_founded approxStrict.
    intro.
    eapply approxStrict_wf'; eauto.
  Qed.

  Hint Resolve approxStrict_wf.

  Definition fixed_point' : {fp : astate
    | forall s, reachable_flowInsensitive aprogram aexec ainitState s
      -> approx s fp}.
    apply fixed_point with (approxStrict := approxStrict)
      (1 := fun (_ : astate) => 0); eauto.
  Qed.

  Lemma In_map : forall (A B : Set) x (f : A -> B) ls,
    In x ls
    -> In (f x) (map f ls).
    induction ls; simpl; intuition.
    subst; auto.
  Qed.

  Lemma in_aprogram' : forall i prog,
    In i prog ->
    exists H : In i prog,
      In (exist (fun i0 => In i0 prog) i H)
      (aprogram' prog).
    induction prog; intros.

    inversion H.

    destruct H; subst.
    simpl.
    eauto.

    simpl.
    destruct (IHprog H) as [h Hh].
    caseEq (ainstr_widen a prog (exist (fun i => In i prog) _ h)); intros.
    simpl in H0.
    injection H0; intros; subst.
    exists (in_cons a x prog h); right.
    apply (In_map _ _ (exist (fun i0 : abstract_instruction => In i0 prog) x h)
      (ainstr_widen a prog)).
    trivial.
  Qed.

  Lemma in_aprogram : forall i,
    In i program
      -> exists H, In (exist (fun i => In i program) i H) aprogram.
    unfold aprogram; intros.
    apply in_aprogram'; trivial.
  Qed.

  Axiom valid_irrel : forall s (H1 H2 : valid s), H1 = H2.

  Lemma reachable_a : forall s1 (Hv1 : valid s1) s2,
    reachable_flowInsensitive program abstract_exec s1 s2
      -> exists Hv2 : valid s2,
	reachable_flowInsensitive aprogram aexec (exist _ _ Hv1) (exist _ _ Hv2).
    induction 1; intuition eauto.

    assert (valid (abstract_exec i s)).
    apply aexec'; trivial.
    destruct (IHreachable_flowInsensitive H1) as [Hv2 Hreach].
    exists Hv2.

    destruct (in_aprogram _ H) as [Hin HHin].

    apply Rfi_Step with (exist (fun i => In i program) i Hin); auto.

    unfold aexec at 2; simpl.
    rewrite (valid_irrel _ (aexec' i s Hin Hv1) H1).
    trivial.
  Qed.

  Definition fixed_point : {fp : abstract_state
    | forall s, reachable_flowInsensitive program abstract_exec abstract_initState s
      -> approx' s fp}.
    destruct fixed_point' as [[fp Hvalid] Hfp].
    exists fp; intros.

    assert (valid abstract_initState).
    unfold abstract_initState; intuition.
    split; simpl; intuition.
    rewrite VarMap.sel_init; eauto.
    rewrite AllocMap.sel_init; eauto.
    rewrite VarMap.sel_init; eauto.
    rewrite AllocMap.sel_init; eauto.

    destruct (reachable_a _ (proj2_sig ainitState) _ H).
    generalize (Hfp _ H1); intros.
    trivial.
  Qed.
End fixed_point.

