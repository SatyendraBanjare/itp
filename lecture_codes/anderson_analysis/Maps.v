Require Import List TheoryList.
Require Import ListUtil Tactics.

Set Implicit Arguments.

Axiom ext_eq : forall (S T : Set) (f g : S -> T),
  (forall x, f x = g x) -> f = g.

Module Type EQ.
  Parameter dom : Set.
  Parameter dom_eq_dec : forall (x y : dom), {x = y} + {x <> y}.
End EQ.

Module Type MAP.
  Variable dom : Set.

  Parameter map : Set -> Set.

  Parameter init : forall (ran : Set), ran -> map ran.
  Parameter sel : forall (ran : Set), map ran -> dom -> ran.
  Parameter upd : forall (ran : Set), map ran -> dom -> ran -> map ran.

  Axiom sel_init : forall (ran : Set) (v : ran) a,
    sel (init v) a = v.

  Axiom sel_upd : forall (ran : Set) (m : map ran) a v a',
    (a = a' /\ sel (upd m a v) a' = v)
    \/ (a <> a' /\ sel (upd m a v) a' = sel m a').

  Axiom sel_upd_eq : forall (ran : Set) (m : map ran) a v,
    sel (upd m a v) a = v.

  Axiom sel_upd_neq : forall (ran : Set) (m : map ran) a v a',
    a <> a'
    -> sel (upd m a v) a' = sel m a'.

  Axiom upd_self : forall (ran : Set) (m : map ran) a,
    upd m a (sel m a) = m.
End MAP.

Module FuncMap (Param : EQ) : MAP with Definition dom := Param.dom.
  Import Param.

  Section Map.
    Variable ran : Set.

    Definition map := dom -> ran.

    Definition init (r : ran) : map :=
      fun _ => r.
    Definition sel (m : map) (d : dom) : ran :=
      m d.
    Definition upd (m : map) (d : dom) (r : ran) : map :=
      fun d' =>
	if dom_eq_dec d d'
	  then r
	  else m d'.

    Theorem sel_init : forall v a,
      sel (init v) a = v.
      trivial.
    Qed.

    Theorem sel_upd : forall m a v a',
      (a = a' /\ sel (upd m a v) a' = v)
      \/ (a <> a' /\ sel (upd m a v) a' = sel m a').
      intros.
      unfold upd, sel.
      destruct (dom_eq_dec a a'); simplify.
    Qed.

    Theorem sel_upd_eq : forall m a v,
      sel (upd m a v) a = v.
      intros.
      unfold upd, sel.
      destruct (dom_eq_dec a a); simplify.
    Qed.

    Theorem sel_upd_neq : forall m a v a',
      a <> a'
      -> sel (upd m a v) a' = sel m a'.
      intros.
      unfold upd, sel.
      destruct (dom_eq_dec a a'); simplify.
    Qed.

    Theorem upd_self : forall m a,
      upd m a (sel m a) = m.
      intros.
      unfold map.
      apply ext_eq.
      intro.
      unfold upd, sel.
      destruct (dom_eq_dec a x); congruence.
    Qed.
  End Map.

  Definition dom := dom.
End FuncMap.

Module Type SET.
  Variable dom : Set.

  Parameter set : Set.

  Parameter empty : set.
  Parameter In : dom -> set -> bool.
  Parameter add : set -> dom -> set.
  Parameter remove : set -> dom -> set.
  Parameter union : set -> set -> set.
  Parameter intersect : set -> set -> set.

  Parameter incl : set -> set -> bool.
  Parameter elems : set -> list dom.
  
  Axiom In_add : forall s v v',
    In v' (add s v) = true
    <-> v = v' \/ In v' s = true.

  Axiom In_add_eq : forall s v,
    In v (add s v) = true.

  Axiom In_add_neq : forall s v v',
    v <> v'
    -> In v' (add s v) = In v' s.

  Axiom In_union : forall s s' v,
    In v (union s s') = true
    -> In v s = true \/ In v s' = true.

  Axiom In_union' : forall s s' v,
    In v s = true
    -> In v s' = true
    -> In v (union s s') = true.

  Axiom union_idempotent : forall s,
    union s s = s.

  Axiom In_intersect : forall v s' s,
    In v (intersect s s') = true
    -> In v s = true /\ In v s' = true.

  Axiom In_intersect' : forall v s' s,
    In v (intersect s s') = false
    -> In v s = false \/ In v s' = false.

  Axiom incl_ok : forall s1 s2,
    incl s1 s2 = true <-> (forall x, In x s1 = true -> In x s2 = true).

  Axiom incl_empty : forall s,
    incl empty s = true.

  Axiom In_empty : forall x,
    In x empty = false.

  Axiom incl_refl : forall s,
    incl s s = true.
  
  Axiom incl_false : forall s1 s2,
    incl s1 s2 = false
    -> exists x, In x s1 = true /\ In x s2 = false.

  Axiom incl_trans : forall s1 s2,
    incl s1 s2 = true
    -> forall s3, incl s2 s3 = true
      -> incl s1 s3 = true.

  Axiom incl_In : forall s1 s2,
    incl s1 s2 = true
    -> forall x, In x s1 = true
      -> In x s2 = true.

  Axiom incl_union_left : forall s1 s2,
    incl s1 (union s1 s2) = true.

  Axiom incl_union_right : forall s1 s2,
    incl s2 (union s1 s2) = true.

  Axiom elems_ok : forall s x,
    List.In x (elems s) <-> In x s = true.

  Axiom elems_remove : forall s x ls,
    elems s = x :: ls
    -> elems (remove s x) = ls.

  Axiom In_remove : forall x x' s,
    In x s = true
    -> x <> x'
    -> In x (remove s x') = true.
End SET.

Module ListSet (Param : EQ) : SET with Definition dom := Param.dom.
  Import Param.

  Section Map.
    Definition set := list dom.

    Definition empty : set := nil.

    Definition In (v : dom) (s : set) : bool :=
      if In_eq_dec dom_eq_dec v s
	then true
	else false.

    Definition add (s : set) (v : dom) : set :=
      if In_eq_dec dom_eq_dec v s
	then s
	else v :: s.

    Fixpoint remove (s : set) (v : dom) {struct s} : set :=
      match s with
	| nil => nil
	| v' :: s' =>
	  if dom_eq_dec v v'
	    then s'
	    else v' :: remove s' v
      end.

    Fixpoint union (s1 s2 : set) {struct s1} : set :=
      match s1 with
	| nil => s2
	| v :: s1' => add (union s1' s2) v
      end.

    Fixpoint intersect (s1 s2 : set) {struct s1} : set :=
      match s1 with
	| nil => nil
	| v :: s1' =>
	  if In_eq_dec dom_eq_dec v s2
	    then v :: intersect s1' s2
	    else intersect s1' s2
      end.

    Definition incl (s1 s2 : set) : bool :=
      if incl_eq_dec dom_eq_dec s1 s2
	then true
	else false.
    Definition elems (s : set) : list dom := s.

    Theorem In_add : forall s v v',
      In v' (add s v) = true
      <-> v = v' \/ In v' s = true.
      unfold In, add; intros.
      destruct (In_eq_dec dom_eq_dec v s).
      destruct (In_eq_dec dom_eq_dec v' s); simplify.
      destruct (In_eq_dec dom_eq_dec v' (v :: s)); simplify.
      destruct (In_eq_dec dom_eq_dec v' s); simplify.
      destruct (In_eq_dec dom_eq_dec v' s); simplify.
    Qed.

    Theorem In_add_eq : forall s v,
      In v (add s v) = true.
      unfold In, add; intros.
      destruct (In_eq_dec dom_eq_dec v s); simplify.
      destruct (In_eq_dec dom_eq_dec v s); simplify.
      destruct (In_eq_dec dom_eq_dec v (v :: s)); simplify.
    Qed.

    Theorem In_add_neq : forall s v v',
      v <> v'
      -> In v' (add s v) = In v' s.
      unfold In, add; intros.
      destruct (In_eq_dec dom_eq_dec v s); simplify.
      destruct (In_eq_dec dom_eq_dec v' (v :: s)); simplify;
	destruct (In_eq_dec dom_eq_dec v' s); simplify.
    Qed.

    Theorem In_union : forall s s' v,
      In v (union s s') = true
      -> In v s = true \/ In v s' = true.
      unfold In; induction s; simplify.
      generalize (IHs s' v).
      destruct (In_eq_dec dom_eq_dec v (add (union s s') a)); simplify.
      destruct (In_eq_dec dom_eq_dec v (union s s')); simplify;
	destruct (In_eq_dec dom_eq_dec v (a :: s)); simplify;
	  destruct (In_eq_dec dom_eq_dec v s'); simplify;
	    destruct (In_eq_dec dom_eq_dec v s); simplify.
    
      wrong.
      generalize (In_add (union s s') a v); simplify.
      apply n.
      unfold In at 1 in H3.
      destruct (In_eq_dec dom_eq_dec v (add (union s s') a)); simplify.
      unfold In in H3.
      destruct (In_eq_dec dom_eq_dec v (union s s')); simplify.
    Qed.

    Theorem In_union' : forall s s' v,
      In v s = true
      -> In v s' = true
      -> In v (union s s') = true.
      unfold In; induction s; simplify.
      generalize (IHs s' v).
      
      destruct (In_eq_dec dom_eq_dec v (add (union s s') a)); simplify.
      destruct (In_eq_dec dom_eq_dec v s'); simplify.
      destruct (In_eq_dec dom_eq_dec v (a :: s)); simplify.

      wrong.
      apply n.
      generalize (In_add (union s s') v v); unfold In; simplify;
	destruct (In_eq_dec dom_eq_dec v (add (union s s') v)); simplify.

      wrong.
      apply n.
      generalize (In_add (union s s') a v); simplify.
      assert (In v (add (union s s') a) = true).
      apply H4.

      unfold In.
      destruct (In_eq_dec dom_eq_dec v (union s s')); trivial.
      wrong.
      apply n0.
      generalize i.
      clear_all.
      induction s; simplify.
      unfold add.
      destruct (In_eq_dec dom_eq_dec a (union s s')); simplify.

      unfold add.
      destruct (In_eq_dec dom_eq_dec a (union s s')).
      generalize i.
      clear_all.
      induction s; simplify.
      unfold add.
      destruct (In_eq_dec dom_eq_dec a (union s s')); simplify.
      
      right.
      generalize i.
      clear_all.
      induction s; simplify.
      unfold add.
      destruct (In_eq_dec dom_eq_dec a (union s s')); simplify.
    Qed.

    Theorem incl_ok : forall s1 s2,
      incl s1 s2 = true <-> (forall x, In x s1 = true -> In x s2 = true).
      unfold incl, In.
      intros.
      destruct (incl_eq_dec dom_eq_dec s1 s2); simplify.
      destruct (In_eq_dec dom_eq_dec x s1); simplify.
      destruct (In_eq_dec dom_eq_dec x s2); simplify.
      wrong; eauto.
      wrong.
      apply n.
      do 2 intro.
      generalize (H a).
      destruct (In_eq_dec dom_eq_dec a s1); simplify.
      destruct (In_eq_dec dom_eq_dec a s2); simplify.
    Qed.

    Lemma union_idempotent' : forall s s',
      List.incl s s'
      -> union s s' = s'.
      induction s; simplify.
      rewrite IHs.
      unfold add.
      destruct (In_eq_dec dom_eq_dec a s'); simplify.
      wrong; intuition.
      do 2 intro.
      intuition.
    Qed.

    Theorem  In_intersect : forall v s' s,
      In v (intersect s s') = true
      -> In v s = true /\ In v s' = true.
      induction s; simpl; intuition.

      unfold In in H.
      destruct (In_eq_dec dom_eq_dec v nil); try discriminate.
      inversion i.

      destruct (In_eq_dec dom_eq_dec a s').
      unfold In in *; idtac.
      destruct (In_eq_dec dom_eq_dec v (a :: intersect s s')); try discriminate.
      destruct (In_eq_dec dom_eq_dec v (a :: s)); trivial.
      wrong.
      apply n.
      destruct i0; subst; intuition.
      destruct (In_eq_dec dom_eq_dec v (intersect s s')); try tauto.
      destruct (In_eq_dec dom_eq_dec v s); intuition; try discriminate.

      destruct (dom_eq_dec a v); subst.
      wrong.
      intuition.
      unfold In in H2.
      destruct (In_eq_dec dom_eq_dec v s'); intuition; discriminate.

      unfold In.
      destruct (In_eq_dec dom_eq_dec v (a :: s)); trivial.
      intuition.
      wrong; apply n1.
      unfold In in H1.
      destruct (In_eq_dec dom_eq_dec v s); try discriminate.
      intuition.

      destruct (In_eq_dec dom_eq_dec a s').
      unfold In in *; idtac.
      destruct (In_eq_dec dom_eq_dec v (a :: intersect s s')); try discriminate.
      destruct (In_eq_dec dom_eq_dec v s'); trivial.
      wrong.
      destruct (In_eq_dec dom_eq_dec v (intersect s s')); try tauto.
      destruct (In_eq_dec dom_eq_dec v s); intuition; try discriminate.

      destruct i0; subst; intuition.

      intuition.
    Qed.

    Theorem In_intersect' : forall v s' s,
      In v (intersect s s') = false
      -> In v s = false \/ In v s' = false.
      induction s; simpl; intuition.

      destruct (In_eq_dec dom_eq_dec a s').
      unfold In in H.
      destruct (In_eq_dec dom_eq_dec v (a :: intersect s s')); try discriminate.
      destruct (dom_eq_dec a v); subst.
      wrong; intuition.

      unfold In in IHs.
      destruct (In_eq_dec dom_eq_dec v (intersect s s')); intuition.
      wrong; intuition.

      destruct (In_eq_dec dom_eq_dec v s); try discriminate.
      unfold In.
      destruct (In_eq_dec dom_eq_dec v s'); auto.
      destruct (In_eq_dec dom_eq_dec v (a :: s)); auto.
      destruct i1; subst; intuition.

      intuition.
      destruct (dom_eq_dec a v); subst.

      unfold In at 2.
      destruct (In_eq_dec dom_eq_dec v s'); intuition.

      unfold In at 1.
      destruct (In_eq_dec dom_eq_dec v (a :: s)); auto.
      destruct i; subst; intuition.
      unfold In in H1.
      destruct (In_eq_dec dom_eq_dec v s); try discriminate.
      intuition.
    Qed.

    Theorem union_idempotent : forall s,
      union s s = s.
      intros.
      apply union_idempotent'; intuition.
    Qed.

    Theorem incl_empty : forall s,
      incl empty s = true.
      unfold incl, empty.
      intro.
      destruct (incl_eq_dec dom_eq_dec nil s); trivial.
      wrong; apply n.
      red; intuition.
      inversion H.
    Qed.

    Theorem In_empty : forall x,
      In x empty = false.
      unfold In, empty.
      intro.
      destruct (In_eq_dec dom_eq_dec x nil); trivial.
      inversion i.
    Qed.

    Theorem incl_refl : forall s,
      incl s s = true.
      intros.
      unfold incl.
      destruct (incl_eq_dec dom_eq_dec s s); simplify.
      wrong; intuition.
    Qed.

    Theorem incl_false : forall s1 s2,
      incl s1 s2 = false
      -> exists x, In x s1 = true /\ In x s2 = false.
      intros.
      unfold incl in H.
      destruct (incl_eq_dec dom_eq_dec s1 s2); try discriminate.
      clear H.
      induction s1.

      wrong.
      apply n.
      red; intuition.
      inversion H.

      destruct (In_dec dom_eq_dec a s2).

      assert (exists x : dom, In x s1 = true /\ In x s2 = false).
      apply IHs1.
      intro.
      apply n.
      red; simpl; intuition; subst; trivial.
      
      destruct H as [x Hx].
      exists x; intuition.
      unfold In in *; idtac.
      destruct (In_eq_dec dom_eq_dec x (a :: s1)); trivial.
      destruct (In_eq_dec dom_eq_dec x s1); try discriminate.
      wrong; intuition.
      
      exists a; intuition.
      unfold In.
      destruct (In_eq_dec dom_eq_dec a (a :: s1)); intuition.
      wrong; intuition.

      unfold In.
      destruct (In_eq_dec dom_eq_dec a s2); intuition.
    Qed.

    Theorem incl_trans : forall s1 s2,
      incl s1 s2 = true
      -> forall s3, incl s2 s3 = true
	-> incl s1 s3 = true.
      unfold incl.
      intros.
      destruct (incl_eq_dec dom_eq_dec s1 s3); simplify.
      destruct (incl_eq_dec dom_eq_dec s1 s2); simplify.
      destruct (incl_eq_dec dom_eq_dec s2 s3); simplify.
      wrong; apply n.
      do 2 intro.
      auto.
    Qed.

    Theorem incl_In : forall s1 s2,
      incl s1 s2 = true
      -> forall x, In x s1 = true
	-> In x s2 = true.
      intros.
      generalize (incl_ok s1 s2).
      intuition.
    Qed.

    Theorem incl_union_left : forall s1 s2,
      incl s1 (union s1 s2) = true.
      intros.
      generalize (incl_ok s1 (union s1 s2)).
      simplify.
      unfold incl.
      destruct (incl_eq_dec dom_eq_dec s1 (union s1 s2)); simplify.
      wrong; apply n.
      clear_all.
      induction s1; simplify.
      do 2 intro.
      inversion H.
      unfold add.
      destruct (In_eq_dec dom_eq_dec a (union s1 s2)); simplify.
    Qed.

    Theorem incl_union_right : forall s1 s2,
      incl s2 (union s1 s2) = true.
      intros.
      generalize (incl_ok s2 (union s1 s2)).
      simplify.
      unfold incl.
      destruct (incl_eq_dec dom_eq_dec s2 (union s1 s2)); simplify.
      wrong; apply n.
      clear_all.
      induction s1; simplify.
      unfold add.
      destruct (In_eq_dec dom_eq_dec a (union s1 s2)); simplify.
    Qed.

    Theorem elems_ok : forall s x,
      List.In x (elems s) <-> In x s = true.
      unfold In, elems; simplify.
      destruct (In_eq_dec dom_eq_dec x s); simplify.
      destruct (In_eq_dec dom_eq_dec x s); simplify.
    Qed.

    Theorem elems_remove : forall s x ls,
      elems s = x :: ls
      -> elems (remove s x) = ls.
      unfold elems, remove.
      simplify.
      destruct (dom_eq_dec x x); simplify.
    Qed.

    Theorem In_remove : forall x x' s,
      In x s = true
      -> x <> x'
      -> In x (remove s x') = true.
      unfold In.
      induction s; simplify.
      destruct (dom_eq_dec x' a); simplify.
      destruct (In_eq_dec dom_eq_dec x s); simplify.
      wrong.
      destruct (In_eq_dec dom_eq_dec x (a :: s)); simplify.
      destruct (In_eq_dec dom_eq_dec x (a :: remove s x')); simplify.
      wrong.
      destruct (In_eq_dec dom_eq_dec x s); simplify;
	destruct (In_eq_dec dom_eq_dec x (a :: s)); simplify.
      destruct (In_eq_dec dom_eq_dec x (remove s x')); simplify.
    Qed.

  End Map.

  Definition dom := dom.
End ListSet.
