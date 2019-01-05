Require Import Arith List Omega TheoryList.
Require Import ListUtil Maps Tactics.
Require Import Machine AndersenModel Pointer.

Set Implicit Arguments.

Inductive followPath : var -> nat -> state -> nat -> Prop :=
  | Path_Done : forall v s,
    followPath v 0 s (VarMap.sel (vars s) v)
  | Path_Step : forall v n s v',
    followPath v n s v'
    -> v' <> 0
    -> followPath v (S n) s (NatMap.sel (heap s) v').

Inductive abstract_followPath
  : var -> nat -> abstract_state -> allocation_site -> Prop :=
  | APath_Done : forall v s a,
    AllocSet.In a (VarMap.sel (avars s) v) = true
    -> abstract_followPath v 0 s a
  | APath_Step : forall v n s v' a,
    abstract_followPath v n s v'
    -> AllocSet.In a (AllocMap.sel (aheap s) v') = true
    -> abstract_followPath v (S n) s a.

Hint Constructors followPath abstract_followPath.

Definition pathCompatible (conc : state) (abs : abstract_state)
  v1 n1 v2 n2 :=
  forall r, followPath v1 n1 conc r
    -> r <> 0
    -> followPath v2 n2 conc r
    -> exists r',
      abstract_followPath v1 n1 abs r'
      /\ abstract_followPath v2 n2 abs r'.

Definition allPaths conc abs :=
  forall v1 n1 v2 n2, pathCompatible conc abs v1 n1 v2 n2.

Record compatible (conc : state) (abs : abstract_state) : Prop := {
  compatInitial : NatMap.sel (heap conc) 0 = 0;
  compatInBounds : forall v n v', followPath v n conc v' -> v' <= limit conc;
  compatZeroed : forall a, a > limit conc -> NatMap.sel (heap conc) a = 0;
  compatPaths : allPaths conc abs
}.

Hint Constructors reachable_flowInsensitive.

Lemma abstractAllocate' : forall v program next,
  In (Allocate v) program
    -> exists site, In (AbsAllocate v site) (abstractProgram' next program).
  induction program; simplify;
    destruct a; firstorder.
Qed.

Lemma abstractAllocate : forall v program,
  In (Allocate v) program
    -> exists site, In (AbsAllocate v site) (abstractProgram program).
  intros; unfold abstractProgram; apply abstractAllocate'; trivial.
Qed.

Ltac VarMap_split :=
  match goal with
    | [ |- context[VarMap.sel (VarMap.upd ?M ?A ?V) ?A'] ] =>
      let Haddr := fresh "Haddr" with Heq := fresh "Heq" in
	(destruct (VarMap.sel_upd M A V A') as [[Haddr Heq] | [Haddr Heq]];
	  rewrite Heq; simplify)
  end.

Ltac nat_split :=
  match goal with
    | [ |- context[match ?N with O => _ | S _ => _ end] ] => destruct N; simplify
  end.

Hint Rewrite VarMap.sel_upd_eq : Maps.
Hint Rewrite VarMap.sel_upd_neq using (intuition; fail) : Maps.

Ltac mySimplify := repeat progress (simplify;
  autorewrite with Maps;
    try match goal with
	  | [ H : _ |- _ ] =>
	    rewrite VarMap.sel_upd_eq in H
	      || (rewrite VarMap.sel_upd_eq in H; [idtac | intuition; fail])
	end).

Hint Resolve AllocSet.In_add_eq.

Lemma pathCompatible_symm : forall conc abs v1 n1 v2 n2,
  pathCompatible conc abs v1 n1 v2 n2
  -> pathCompatible conc abs v2 n2 v1 n1.
  unfold pathCompatible; firstorder.
Qed.

Hint Resolve pathCompatible_symm.

Lemma followPath_write_var : forall v v' conc' n r,
  v <> v'
  -> followPath v' n conc' r
  -> forall conc pc addr lim, conc' = Build_state pc (VarMap.upd (vars conc) v addr) (heap conc) lim
    -> followPath v' n conc r.
  induction 2; mySimplify.
Qed.

Hint Resolve followPath_write_var.

Lemma abstract_followPath_write_var : forall v v' n abs r,
  v <> v'
  -> abstract_followPath v' n abs r
  -> forall site, abstract_followPath v' n
    (Build_abstract_state (VarMap.upd (avars abs) v site) (aheap abs)) r.
  induction 2; mySimplify.
  constructor; mySimplify.
Qed.

Hint Resolve abstract_followPath_write_var.

Lemma compatible_write_var : forall conc abs v addr site pc lim,
  let conc' := Build_state
    pc
    (VarMap.upd (vars conc) v addr)
    (heap conc)
    lim in
    let abs' := Build_abstract_state
      (VarMap.upd (avars abs) v site)
      (aheap abs) in
      allPaths conc abs
      -> (forall n1 n2, pathCompatible conc' abs' v n1 v n2)
      -> (forall v' n n', v <> v' -> pathCompatible conc' abs' v n v' n')
      -> allPaths conc' abs'.
  unfold allPaths; mySimplify.
  
  destruct (VarMap.sel_upd (vars conc) v (limit conc) v1);
    destruct (VarMap.sel_upd (vars conc) v (limit conc) v2);
      mySimplify.

  generalize (H v1 n1 v2 n2); unfold pathCompatible; mySimplify.
  assert (followPath v1 n1 conc r); eauto.
  assert (followPath v2 n2 conc r); eauto.
  destruct (H3 _ H10 H8 H11) as [r' Hr'].
  mySimplify.
Qed.

Lemma followPath_SO : forall s v n r,
  NatMap.sel (heap s) (VarMap.sel (vars s) v) = 0
  -> followPath v n s r
  -> r = VarMap.sel (vars s) v \/ r = 0.
  induction 2; mySimplify.
Qed.

Hint Resolve followPath_SO.

Lemma followPath_SO' : forall s v n r,
  NatMap.sel (heap s) (VarMap.sel (vars s) v) = 0
  -> followPath v n s r
  -> (n = 0 /\ r = VarMap.sel (vars s) v)
  \/ (n = 1 /\ r = 0).
  induction 2; mySimplify.
Qed.

Lemma followPath_S : forall s v n r,
  NatMap.sel (heap s) (VarMap.sel (vars s) v) = 0
  -> followPath v (S n) s r
  -> r = 0.
  intros.
  generalize (followPath_SO' H H0); mySimplify.
Qed.

Lemma step_Allocate : forall v program conc abs,
  In (Allocate v) program
    -> compatible conc abs
    -> exists ins', In ins' (abstractProgram program)
      /\ compatible (exec (Allocate v) conc) (abstract_exec ins' abs).
  intros.
  destruct (abstractAllocate _ _ H) as [site Hsite].
  exists (AbsAllocate v site); mySimplify.

  destruct (eq_nat_dec v0 v); subst.

  assert (Hcase : v' = VarMap.sel (vars (Build_state (S (pc conc))
    (VarMap.upd (vars conc) v (S (limit conc))) 
    (heap conc) (S (limit conc)))) v \/ v' = 0).
  apply followPath_SO with n; mySimplify.
  mySimplify.

  assert (v' <= limit conc); eauto; omega.

  apply compatible_write_var; mySimplify.

  red; intros.
  destruct n1; destruct n2; mySimplify.

  inversion H0; mySimplify.
  exists site.
  split; constructor; mySimplify.

  wrong.
  inversion H0; mySimplify.
  assert (S (limit conc) = 0); try omega.
  eapply followPath_S; eauto; mySimplify.

  wrong.
  inversion H2; mySimplify.
  assert (S (limit conc) = 0); try omega.
  eapply followPath_S; eauto; mySimplify.

  assert (r = 0).
  eapply followPath_S; eauto; mySimplify.
  mySimplify.

  red; intros.
  
  assert (Hcases : (n = 0 /\ r = VarMap.sel
    (vars (Build_state (S (pc conc))
      (VarMap.upd (vars conc) v (S (limit conc))) 
      (heap conc) (S (limit conc)))) v)
  \/ (n = 1 /\ r = 0)).
  apply followPath_SO'; mySimplify.
  mySimplify.
  wrong.
  assert (S (limit conc) <= limit conc); eauto; omega.
Qed.

Lemma abstractCopy' : forall src dst program next,
  In (Copy src dst) program
    -> In (AbsCopy src dst) (abstractProgram' next program).
  induction program; simplify;
    destruct a; intuition.
Qed.

Lemma abstractCopy : forall src dst program,
  In (Copy src dst) program
    -> In (AbsCopy src dst) (abstractProgram program).
  intros; unfold abstractProgram; apply abstractCopy'; trivial.
Qed.

Hint Resolve abstractCopy.

Lemma followPath_swap_var : forall v1 n conc1 r,
  followPath v1 n conc1 r
  -> forall conc2 v2, VarMap.sel (vars conc1) v1 = VarMap.sel (vars conc2) v2
    -> heap conc2 = heap conc1
    -> followPath v2 n conc2 r.
  induction 1; mySimplify.
  rewrite H; trivial.
  rewrite <- H2.
  eauto.
Qed.

Hint Resolve AllocSet.incl_In.

Lemma abstract_followPath_incl : forall v1 abs1 abs2 v2 n r,
  AllocSet.incl (VarMap.sel (avars abs1) v1) (VarMap.sel (avars abs2) v2) = true
  -> aheap abs1 = aheap abs2
  -> abstract_followPath v1 n abs1 r
  -> abstract_followPath v2 n abs2 r.
  induction 3; mySimplify.
  apply APath_Step with v'; eauto; congruence.
Qed.

Hint Resolve AllocSet.incl_union_right AllocSet.incl_refl.

Lemma step_Copy : forall dst src program conc abs,
  In (Copy dst src) program
    -> compatible conc abs
    -> exists ins', In ins' (abstractProgram program)
      /\ compatible (exec (Copy dst src) conc) (abstract_exec ins' abs).
  intros.
  exists (AbsCopy dst src); mySimplify.

  destruct (eq_nat_dec v dst); subst.

  apply compatInBounds0 with src n.
  
  apply followPath_swap_var with dst
    (Build_state (S (pc conc))
      (VarMap.upd (vars conc) dst (VarMap.sel (vars conc) src))
      (heap conc) (limit conc)); auto; mySimplify.

  apply compatInBounds0 with v n.

  apply followPath_swap_var with v
    (Build_state (S (pc conc))
      (VarMap.upd (vars conc) dst (VarMap.sel (vars conc) src))
      (heap conc) (limit conc)); auto; mySimplify.

  destruct (eq_nat_dec dst src); subst.

  apply compatible_write_var; auto.

  rewrite AllocSet.union_idempotent.
  repeat rewrite VarMap.upd_self.
  red; intros.
  assert (Hpath1 : followPath src n1 conc r).
  eapply followPath_swap_var; eauto; mySimplify.
  assert (Hpath2 : followPath src n2 conc r).
  eapply followPath_swap_var; eauto; mySimplify.
  destruct (compatPaths0 _ _ _ _ _ Hpath1 H1 Hpath2) as [r' [Hpath1' Hpath2']].
  destruct abs; mySimplify.

  rewrite AllocSet.union_idempotent.
  repeat rewrite VarMap.upd_self.
  red; intros.
  assert (Hpath1 : followPath src n conc r).
  eapply followPath_swap_var; eauto; mySimplify.
  assert (Hpath2 : followPath v' n' conc r).
  eapply followPath_swap_var; eauto; mySimplify.
  destruct (compatPaths0 _ _ _ _ _ Hpath1 H2 Hpath2) as [r' [Hpath1' Hpath2']].
  destruct abs; mySimplify.

  apply compatible_write_var; intuition.

  red; intros.
  assert (Hpath1 : followPath src n1 conc r).
  eapply followPath_swap_var; eauto; mySimplify.
  assert (Hpath2 : followPath src n2 conc r).
  eapply followPath_swap_var; eauto; mySimplify.
  destruct (compatPaths0 _ _ _ _ _ Hpath1 H1 Hpath2) as [r' [Hpath1' Hpath2']].
  exists r'.
  split;
    eapply (abstract_followPath_incl (v1 := src)); eauto; mySimplify.

  red; intros.
  assert (Hpath1 : followPath src n0 conc r).
  eapply followPath_swap_var; eauto; mySimplify.
  assert (Hpath2 : followPath v' n' conc r).
  eapply followPath_swap_var; eauto; mySimplify.
  unfold allPaths in compatPaths0.
  destruct (compatPaths0 _ _ _ _ _ Hpath1 H2 Hpath2) as [r' [Hpath1' Hpath2']].
  exists r'.
  split.
  eapply (abstract_followPath_incl (v1 := src)); eauto; mySimplify.
  eauto.
Qed.

Lemma abstractRead' : forall src dst program next,
  In (Read src dst) program
    -> In (AbsRead src dst) (abstractProgram' next program).
  induction program; simplify;
    destruct a; intuition.
Qed.

Lemma abstractRead : forall src dst program,
  In (Read src dst) program
    -> In (AbsRead src dst) (abstractProgram program).
  intros; unfold abstractProgram; apply abstractRead'; trivial.
Qed.

Hint Resolve abstractRead.

Lemma followPath_read : forall v1 n conc1 r,
  followPath v1 n conc1 r
  -> forall conc2, heap conc1 = heap conc2
    -> forall v2, VarMap.sel (vars conc2) v2 <> 0
      -> VarMap.sel (vars conc1) v1
      = NatMap.sel (heap conc2) (VarMap.sel (vars conc2) v2)
      -> followPath v2 (S n) conc2 r.
  induction 1; mySimplify.
  rewrite H1.
  constructor; auto.

  rewrite H1.
  auto.
Qed.

Lemma abstract_followPath_expand : forall v n abs r,
  abstract_followPath v n abs r
  -> forall abs', aheap abs = aheap abs'
    -> (forall v', AllocSet.incl (VarMap.sel (avars abs) v')
      (VarMap.sel (avars abs') v') = true)
    -> abstract_followPath v n abs' r.
  induction 1; intuition.
  injection H0; intros; subst.
  eauto.

  apply APath_Step with v'.
  eauto.
  congruence.
Qed.

Lemma incl_fold_union' : forall ls s s' f,
  AllocSet.incl s s' = true
  -> AllocSet.incl s
  (fold_left
    (fun known (site : allocation_site) => AllocSet.union known (f site))
    ls
    s') = true.
  induction ls; mySimplify.
  apply IHls.
  apply AllocSet.incl_trans with s'; auto.
  apply AllocSet.incl_union_left.
Qed.

Lemma incl_fold_union : forall ls s f,
  AllocSet.incl s
  (fold_left
    (fun known (site : allocation_site) => AllocSet.union known (f site))
    ls
    s) = true.
  intros.
  apply incl_fold_union'; auto.
Qed.

Lemma abstract_followPath_read : forall v1 abs1 n' r,
  abstract_followPath v1 n' abs1 r
  -> forall n, n' = S n
    -> forall abs2, aheap abs1 = aheap abs2
      -> forall v2, (forall a, AllocSet.In a (VarMap.sel (avars abs1) v1) = true
	-> AllocSet.incl (AllocMap.sel (aheap abs1) a)
	(VarMap.sel (avars abs2) v2) = true)
      -> abstract_followPath v2 n abs2 r.
  induction n'; mySimplify.
  injection H0; mySimplify.
  inversion H; mySimplify.

  destruct n.

  inversion H3; subst.
  eauto.

  apply APath_Step with v'; try congruence; eauto.
Qed.

Lemma incl_fold_union_read : forall a f ls s i,
  ls = AllocSet.elems s
  -> AllocSet.In a s = true
  -> AllocSet.incl (f a)
  (fold_left
    (fun known (site : allocation_site) =>
      AllocSet.union known (f site))
    ls
    i)
  = true.
  induction ls; mySimplify;
    generalize (AllocSet.elems_ok s a); rewrite <- H.

  intuition.

  mySimplify.
  apply incl_fold_union'; auto.

  destruct (eq_nat_dec a0 a); subst.
  apply incl_fold_union'; auto.

  apply IHls with (AllocSet.remove s a0).
  symmetry; apply AllocSet.elems_remove; auto.
  apply AllocSet.In_remove; auto.
Qed.

Lemma step_Read : forall dst src program conc abs,
  In (Read dst src) program
    -> compatible conc abs
    -> exists ins', In ins' (abstractProgram program)
      /\ compatible (exec (Read dst src) conc) (abstract_exec ins' abs).
  intros.
  exists (AbsRead dst src).

  caseEq (VarMap.sel (vars conc) src); mySimplify.
  rewrite H1; rewrite compatInitial0; mySimplify.
  rewrite H1; rewrite compatInitial0;
    rewrite H1 in H0; rewrite compatInitial0 in H0;
      mySimplify.
  rewrite H1; rewrite compatInitial0;
    rewrite H1 in H0; rewrite compatInitial0 in H0;
      mySimplify.
  rewrite H1; rewrite compatInitial0;
    mySimplify.

  red; intros.
  red; intros.
  destruct (compatPaths0 v1 n1 v2 n2 r) as [r' [Hpath1 Hpath2]]; auto.
  exists r'.
  split; apply abstract_followPath_expand with abs; mySimplify;
    VarMap_split; apply incl_fold_union.

  destruct (NatMap.sel (heap conc) (VarMap.sel (vars conc) src)); mySimplify.
  caseEq (NatMap.sel (heap conc) (VarMap.sel (vars conc) src)); mySimplify;
  rewrite H2 in H1; mySimplify.

  destruct (eq_nat_dec dst v); mySimplify.
  apply compatInBounds0 with src (S n0).
  eapply followPath_read; eauto; mySimplify.
  
  rewrite H0.
  rewrite H0 in H1.
  destruct (NatMap.sel (heap conc) (S n)); auto.

  caseEq (NatMap.sel (heap conc) (VarMap.sel (vars conc) src)); mySimplify.

  red; intros.
  red; intros.
  destruct (compatPaths0 v1 n1 v2 n2 r) as [r' [Hpath1 Hpath2]]; auto.
  exists r'.
  split; apply abstract_followPath_expand with abs; mySimplify;
    VarMap_split; apply incl_fold_union.

  apply compatible_write_var; mySimplify.
  
  red; intros.
  destruct (compatPaths0 src (S n1) src (S n2) r) as [r' [Hpath1 Hpath2]]; auto.
  eapply followPath_read; eauto; mySimplify.
  eapply followPath_read; eauto; mySimplify.
  exists r'.
  split;
    [apply abstract_followPath_read with src abs (S n1)
      | apply abstract_followPath_read with src abs (S n2)];
    mySimplify; eapply incl_fold_union_read; eauto.

  red; intros.
  destruct (compatPaths0 src (S n1) v' n' r) as [r' [Hpath1 Hpath2]]; auto.
  eapply followPath_read; eauto; mySimplify.
  eapply followPath_swap_var; eauto; mySimplify.
  exists r'.
  split.
  apply abstract_followPath_read with src abs (S n1);
    mySimplify; eapply incl_fold_union_read; eauto.
  eapply abstract_followPath_incl; eauto.
Qed.

Lemma abstractWrite' : forall src dst program next,
  In (Write src dst) program
    -> In (AbsWrite src dst) (abstractProgram' next program).
  induction program; simplify;
    destruct a; intuition.
Qed.

Lemma abstractWrite : forall src dst program,
  In (Write src dst) program
    -> In (AbsWrite src dst) (abstractProgram program).
  intros; unfold abstractProgram; apply abstractWrite'; trivial.
Qed.

Hint Resolve abstractWrite.

Lemma abstract_followPath_write_preserve : forall v n abs1 r,
  abstract_followPath v n abs1 r
  -> forall abs2, avars abs1 = avars abs2
    -> (forall addr, AllocSet.incl
      (AllocMap.sel (aheap abs1) addr)
      (AllocMap.sel (aheap abs2) addr) = true)
    -> abstract_followPath v n abs2 r.
  induction 1; intuition.

  injection H0; intros; subst.
  constructor; congruence.

  eauto.
Qed.

Ltac AllocMap_split :=
  match goal with
    | [ |- context[AllocMap.sel (AllocMap.upd ?M ?A ?V) ?A'] ] =>
      let Haddr := fresh "Haddr" with Heq := fresh "Heq" in
	(destruct (AllocMap.sel_upd M A V A') as [[Haddr Heq] | [Haddr Heq]];
	  rewrite Heq; simplify)
  end.

Hint Resolve AllocSet.incl_union_left.

Lemma incl_write_bonanza' : forall addr h s ls i,
  (forall addr', AllocSet.incl (AllocMap.sel h addr') (AllocMap.sel i addr') = true)
  -> AllocSet.incl (AllocMap.sel h addr)
  (AllocMap.sel
    (fold_left
      (fun known (site : allocation_site) =>
        AllocMap.upd known site (AllocSet.union (AllocMap.sel h site) s))
      ls
      i) addr) = true.
  induction ls; mySimplify.
  apply IHls; mySimplify.
  match goal with
    | [ |- AllocSet.incl ?X ?Y = true ] => generalize (AllocSet.incl_ok X Y)
  end; intuition.
  clear H1.
  apply H2; clear H2; intuition.
  destruct (AllocMap.sel_upd i a (AllocSet.union (AllocMap.sel h a) s) addr'); intuition; subst;
    rewrite H3; eauto.
Qed.

Lemma incl_write_bonanza : forall addr h s ls,
  AllocSet.incl (AllocMap.sel h addr)
  (AllocMap.sel
    (fold_left
      (fun known (site : allocation_site) =>
        AllocMap.upd known site (AllocSet.union (AllocMap.sel h site) s))
      ls
      h) addr) = true.
  intros.
  apply incl_write_bonanza'; auto.
Qed.

Ltac NatMap_split :=
  match goal with
    | [ |- context[NatMap.sel (NatMap.upd ?M ?A ?V) ?A'] ] =>
      let Haddr := fresh "Haddr" with Heq := fresh "Heq" in
	(destruct (NatMap.sel_upd M A V A') as [[Haddr Heq] | [Haddr Heq]];
	  rewrite Heq; simplify)
  end.

Lemma fold_left_sum : forall ns n1 n2,
  fold_left (fun x y => S (x + y)) ns (n1 + n2)
  = n1 + fold_left (fun x y => S (x + y)) ns n2.
  induction ns; simplify.
  replace (S (n1 + n2 + a)) with ((n1 + a) + S n2); try omega.
  replace (S (n2 + a)) with (a + S n2); try omega.
  repeat rewrite IHns.
  omega.
Qed.

Lemma followPath_case : forall v n conc' r conc a src,
  vars conc' = vars conc
  -> heap conc' = NatMap.upd (heap conc) a (VarMap.sel (vars conc) src)
  -> followPath v n conc' r
  -> followPath v n conc r
  \/ exists n', followPath src n' conc r.
  induction 3; mySimplify.

  rewrite H; eauto.

  rewrite H0; NatMap_split.

  destruct H3 as [n' Hpath].
  rewrite H0; NatMap_split.
Qed.

Lemma followPath_nothing_new : forall v n conc' r conc a src,
  vars conc' = vars conc
  -> heap conc' = NatMap.upd (heap conc) a (VarMap.sel (vars conc) src)
  -> followPath v n conc' r
  -> exists v', exists n', followPath v' n' conc r.
  intros.
  destruct (followPath_case _ H H0 H1); eauto.
Qed.

Lemma allPaths_step : forall conc' conc a src v n r,
  vars conc' = vars conc
  -> heap conc' = NatMap.upd (heap conc) a (VarMap.sel (vars conc) src)
  -> followPath v n conc' r
  -> followPath v n conc r
  \/ exists n1, exists n2,
    n = S (n1 + n2)
    /\ followPath v n1 conc a
    /\ followPath src n2 conc' r.
  induction 3; mySimplify.

  rewrite H; eauto.

  rewrite H0; NatMap_split.
  right.
  exists n.
  exists 0.
  mySimplify.
  rewrite <- H; trivial.

  destruct H3 as [n1 [n2 [Hsum [Hpath1 Hpath2]]]].
  right.
  exists n1.
  exists (S n2).
  mySimplify.
Qed.
  
Lemma follow_conjoin : forall v1 n1 conc v2 n2 r,
  followPath v1 n1 conc (VarMap.sel (vars conc) v2)
  -> followPath v2 n2 conc r
  -> followPath v1 (n1 + n2) conc r.
  induction 2; mySimplify.

  replace (n1 + 0) with n1; eauto.

  replace (n1 + S n) with (S (n1 + n)); eauto.
Qed.

Lemma abstract_follow_conjoin : forall conc abs abs' v n1 a dst src n2 r',
  allPaths conc abs
  -> avars abs' = avars abs
  -> (forall addr,
    AllocSet.incl (AllocMap.sel (aheap abs) addr)
    (AllocMap.sel (aheap abs') addr) = true)
  -> (forall r, AllocSet.In r (VarMap.sel (avars abs) dst) = true
    -> AllocSet.incl (VarMap.sel (avars abs) src) (AllocMap.sel (aheap abs') r) = true)
  -> a = VarMap.sel (vars conc) dst
  -> a <> 0
  -> followPath v n1 conc a
  -> abstract_followPath src n2 abs' r'
  -> abstract_followPath v (S (n1 + n2)) abs' r'.
  induction 8; intuition; subst.

  replace (n1 + 0) with n1; try omega.
  destruct (H v n1 dst 0 (VarMap.sel (vars conc) dst)) as [r' [Hpath1 Hpath2]]; auto.
  inversion Hpath2; subst.
  apply APath_Step with r'.
  apply abstract_followPath_write_preserve with abs; auto.
  apply AllocSet.incl_In with (VarMap.sel (avars abs) v0); auto.
  rewrite <- H0; trivial.
  
  replace (n1 + S n) with (S (n1 + n)); eauto.
Qed.

Lemma allPaths_write : forall conc' conc src abs abs' dst,
  vars conc' = vars conc
  -> heap conc' = NatMap.upd (heap conc) (VarMap.sel (vars conc) dst) (VarMap.sel (vars conc) src)
  -> VarMap.sel (vars conc) dst <> 0
  -> avars abs' = avars abs
  -> (forall addr,
    AllocSet.incl (AllocMap.sel (aheap abs) addr)
    (AllocMap.sel (aheap abs') addr) = true)
  -> (forall r, AllocSet.In r (VarMap.sel (avars abs) dst) = true
    -> AllocSet.incl (VarMap.sel (avars abs) src) (AllocMap.sel (aheap abs') r) = true)
  -> allPaths conc abs
  -> forall n v1 n1 r, r <> 0
    -> followPath v1 n1 conc' r
    -> forall v2 n2, followPath v2 n2 conc' r
      -> n1 + n2 <= n
      -> exists r',
	abstract_followPath v1 n1 abs' r'
	/\ abstract_followPath v2 n2 abs' r'.
  induction n; mySimplify.

  destruct n1; mySimplify.
  destruct n2; mySimplify.
  inversion H7; subst.
  inversion H8; subst.
  destruct (H5 v1 0 v2 0 (VarMap.sel (vars conc') v1)) as [r' [Hpath1 Hpath2]]; auto.
  rewrite H; auto.
  rewrite <- H11; rewrite H; auto.
  inversion Hpath1; subst.
  inversion Hpath2; subst.
  rewrite <- H2 in H10.
  rewrite <- H2 in H12.
  eauto.

  destruct (allPaths_step _ H H0 H7).
  
  destruct (allPaths_step _ H H0 H8).

  destruct (H5 v1 n1 v2 n2 r) as [r' [Hpath1 Hpath2]]; auto.
  exists r'; split;
    destruct abs'; mySimplify;
      apply abstract_followPath_write_preserve with abs; auto.

  destruct H11 as [n1' [n2' [Hsum [Hpath1 Hpath2]]]].
  assert (Hih : exists r',
    abstract_followPath v1 n1 abs' r' /\ abstract_followPath src n2' abs' r').
  apply IHn with r; mySimplify.
  destruct Hih as [r' [Hapath1 Hapath2]].
  exists r'.
  mySimplify.
  eapply abstract_follow_conjoin; eauto.
  
  destruct H10 as [n1' [n2' [Hsum [Hpath1 Hpath2]]]].
  assert (Hih : exists r',
    abstract_followPath src n2' abs' r' /\ abstract_followPath v2 n2 abs' r').
  apply IHn with r; mySimplify.
  destruct Hih as [r' [Hapath1 Hapath2]].
  exists r'.
  mySimplify.
  eapply abstract_follow_conjoin; eauto.
Qed.

Lemma sel_bonanza' : forall addr (f : allocation_site -> AllocSet.set) ls h,
  AllocMap.sel h addr = f addr
  -> AllocMap.sel
  (fold_left
    (fun known site =>
      AllocMap.upd known site (f site))
    ls h)
  addr = f addr.
  induction ls; mySimplify.
  apply IHls.
  AllocMap_split.
Qed.

Lemma sel_bonanza : forall addr (f : allocation_site -> AllocSet.set) ls h,
  In addr ls
  -> AllocMap.sel
  (fold_left
    (fun known site =>
      AllocMap.upd known site (f site))
    ls h)
  addr = f addr.
  induction ls; mySimplify.

  apply sel_bonanza'.
  apply AllocMap.sel_upd_eq.
Qed.

Lemma sel_updated' : forall r (f : allocation_site -> AllocSet.set) ls h,
  AllocMap.sel h r = f r
  -> AllocMap.sel
  (fold_left
    (fun known site => AllocMap.upd known site (f site)) ls h) r = f r.
  induction ls; mySimplify.

  rewrite IHls; auto.
  AllocMap_split.
Qed.

Lemma sel_updated : forall r src f ls dst h,
  ls = AllocSet.elems dst
  -> AllocSet.In r dst = true
  -> AllocSet.incl src
  (AllocMap.sel
    (fold_left
      (fun known (site : allocation_site) =>
        AllocMap.upd known site
        (AllocSet.union (f site) src))
      ls h) r) = true.
  induction ls; mySimplify.
  
  destruct (AllocSet.elems_ok dst r); intuition.
  rewrite <- H0 in H4.
  inversion H4.

  destruct (eq_nat_dec a r); subst.
  generalize (sel_updated' (r := r) (fun site => AllocSet.union (f site) src)
    ls (h := AllocMap.upd h r (AllocSet.union (f r) src))); intro.
  unfold AllocMap.dom in H1.
  rewrite H1; auto.
  apply AllocMap.sel_upd_eq.

  apply IHls with (AllocSet.remove dst a).
  symmetry; apply AllocSet.elems_remove; auto.
  apply AllocSet.In_remove; auto.
Qed.

Lemma step_Write : forall dst src program conc abs,
  In (Write dst src) program
    -> compatible conc abs
    -> exists ins', In ins' (abstractProgram program)
      /\ compatible (exec (Write dst src) conc) (abstract_exec ins' abs).
  intros.
  exists (AbsWrite dst src).

  caseEq (VarMap.sel (vars conc) dst); mySimplify.

  rewrite H1; auto.
  rewrite H1; rewrite H1 in H0; eauto.
  rewrite H1; rewrite H1 in H0; auto.
  rewrite H1.

  red; intros.
  red; intros.
  destruct (compatPaths0 v1 n1 v2 n2 r) as [r' [Hvar Hheap]]; auto.
  exists r'.
  split;
    apply abstract_followPath_write_preserve with abs; simpl; intuition;
      apply incl_write_bonanza.

  rewrite H0; simpl.
  rewrite NatMap.sel_upd_neq; auto.

  rewrite H0; rewrite H0 in H1.
  simpl.

  assert (exists v'', exists n'', followPath v'' n'' conc v').

  apply followPath_nothing_new with v n0
    (Build_state (S (pc conc)) (vars conc)
      (NatMap.upd (heap conc) (S n) (VarMap.sel (vars conc) src))
      (limit conc))
    (S n) src; auto.
  destruct H2 as [v'' [n'' Hn'']]; eauto.

  rewrite H0; rewrite H0 in H1; mySimplify.
  rewrite NatMap.sel_upd_neq; auto.
  assert (S n <= limit conc).
  apply compatInBounds0 with dst 0.
  rewrite <- H0; trivial.
  omega.

  rewrite H0.
  red; intros.
  red; intros.
  apply allPaths_write with
    (Build_state (S (pc conc)) (vars conc)
      (NatMap.upd (heap conc) (S n) (VarMap.sel (vars conc) src))
      (limit conc))
    conc src abs dst (n1 + n2) r; simpl; intuition.

  apply incl_write_bonanza.
  eapply sel_updated; eauto.
Qed.

Lemma followPath_goto : forall conc conc' v n r,
  vars conc' = vars conc
  -> heap conc' = heap conc
  -> followPath v n conc r
  -> followPath v n conc' r.
  induction 3; mySimplify.
  rewrite <- H; auto.
  rewrite <- H0; auto.
Qed.

Lemma step_Goto : forall n conc abs,
  compatible conc abs
  -> compatible (exec (Goto n) conc) abs.
  mySimplify.

  apply compatInBounds0 with v n0.
  apply followPath_goto with (Build_state n (vars conc) (heap conc) (limit conc)); simpl; auto.

  red; intros; red; intros.
  destruct (compatPaths0 v1 n1 v2 n2 r) as [r' [Hpath1 Hpath2]]; auto.
  apply followPath_goto with (Build_state n (vars conc) (heap conc) (limit conc)); simpl; auto.
  apply followPath_goto with (Build_state n (vars conc) (heap conc) (limit conc)); simpl; auto.
  eauto.
Qed.

Section allocation_site_model_is_conservative.
  Variable program : list instruction.

  Lemma allocation_site_step :
    forall conc abs, compatible conc abs
      -> forall program ins, In ins program
	-> compatible (exec ins conc) abs
	\/ exists ins', In ins' (abstractProgram program)
	  /\ compatible (exec ins conc) (abstract_exec ins' abs).
    destruct ins; intuition.
    
    right; apply step_Allocate; intuition.
    right; apply step_Copy; intuition.
    right; apply step_Read; intuition.
    right; apply step_Write; intuition.
    left; apply step_Goto; intuition.
  Qed.

  Theorem allocation_site_model_is_conservative :
    forall conc conc', reachable_flowInsensitive program exec conc conc'
      -> forall abs, compatible conc abs
	-> exists abs', reachable_flowInsensitive (abstractProgram program)
	  abstract_exec abs abs'
	  /\ compatible conc' abs'.
    induction 1; intuition.

    exists abs; intuition.

    assert (compatible (exec i s) abs
      \/ exists ins', In ins' (abstractProgram program)
	/\ compatible (exec i s) (abstract_exec ins' abs)).
    apply allocation_site_step; intuition.
    destruct H1 as [Hcompat | [ins' [Hin Hcompat]]]; auto.

    destruct (IHreachable_flowInsensitive _ Hcompat) as [abs' [Hreach Hcompat']].
    eauto.
  Qed.

  Definition abstract_initState :=
    Build_abstract_state
    (VarMap.init AllocSet.empty)
    (AllocMap.init AllocSet.empty).

  Lemma andersen_start :
    forall conc, reachable_flowInsensitive program exec initState conc
      -> exists abs, reachable_flowInsensitive (abstractProgram program)
	abstract_exec abstract_initState abs
	  /\ compatible conc abs.
    intros.
    eapply allocation_site_model_is_conservative; eauto.

    intuition.

    unfold initState; simpl.
    apply NatMap.sel_init.

    assert (forall s, followPath v n s v'
      -> s = initState
      -> v' <= limit initState); eauto.
    induction 1; mySimplify.
    rewrite VarMap.sel_init; auto.

    unfold initState; simpl.
    apply NatMap.sel_init.

    red; intros; red; intros.
    wrong.
    assert (forall s, followPath v1 n1 s r
      -> s = initState
      -> False); eauto.
    induction 1; mySimplify;
      apply H1.

    apply VarMap.sel_init. 
    apply NatMap.sel_init.
  Qed.

  Theorem andersen_sound : forall v1 v2,
    (forall abs, reachable_flowInsensitive (abstractProgram program)
      abstract_exec abstract_initState abs
      -> forall site, AllocSet.In site
	(AllocSet.intersect (VarMap.sel (avars abs) v1) (VarMap.sel (avars abs) v2))
	= false)
    -> mustNotAlias program v1 v2.
    unfold mustNotAlias; intuition.
    generalize (flowInsensitive_is_conservative H0); intro Hfi.
    destruct (andersen_start Hfi) as [abs [Hexec Hcompat]].
    destruct (eq_nat_dec (VarMap.sel (vars s) v1) 0); trivial.

    intuition.
    destruct (compatPaths0 v1 0 v2 0 (VarMap.sel (vars s) v1))
      as [r' [Hpath1 Hpath2]]; auto.
    rewrite H1; trivial.

    inversion Hpath1; subst.
    inversion Hpath2; subst.
    wrong.
    generalize (H _ Hexec r'); intro Hfalse.
    destruct (AllocSet.In_intersect' Hfalse); congruence.
  Qed.

End allocation_site_model_is_conservative.
