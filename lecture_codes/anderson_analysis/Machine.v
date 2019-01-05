Require Import List TheoryList Wf.

Require Import ListUtil.

Set Implicit Arguments.

Section reachable.

  Variables instruction state : Set.
  Variable program : list instruction.
  Variable pc : state -> nat.
  Variable exec : instruction -> state -> state.

  Inductive reachable : state -> state -> Prop :=
    | R_Done : forall s, reachable s s
    | R_Step : forall s s' i,
      nth_spec program (pc s) i
	-> reachable (exec i s) s'
	-> reachable s s'.

  Inductive reachable_flowInsensitive : state -> state -> Prop :=
    | Rfi_Done : forall s, reachable_flowInsensitive s s
    | Rfi_Step : forall s s' i,
      In i program
	-> reachable_flowInsensitive (exec i s) s'
	-> reachable_flowInsensitive s s'.

  Hint Constructors reachable_flowInsensitive.

  Theorem flowInsensitive_is_conservative :
    forall s s', reachable s s'
      -> reachable_flowInsensitive s s'.
    induction 1; eauto.
  Qed.

  Section approx.
    Variable approx : state -> state -> Prop.
    Variable approxStrict : state -> state -> Prop.

    Hypothesis approx_refl : forall s,
      approx s s.

    Hypothesis approx_trans : forall s1 s2 s3,
      approx s1 s2
      -> approx s2 s3
      -> approx s1 s3.

    Hypothesis increasing : forall s ins,
      approx s (exec ins s).

    Hypothesis monotonic : forall s1 s2 ins,
      approx s1 s2
      -> approx (exec ins s1) (exec ins s2).

    Section fixed_point.
      Variable fp : state.

      Hypothesis fp_ok : forall ins,
	In ins program
	  -> approx (exec ins fp) fp.
      
      Theorem fixed_point_ok : forall s,
	approx s fp
	-> forall s', reachable_flowInsensitive s s'
	  -> approx s' fp.
	induction 2; intuition eauto.
      Qed.
    End fixed_point.

    Hypothesis approxStrict_approx : forall s1 s2,
      approx s2 s1
      -> ~approxStrict s1 s2
      -> approx s1 s2.

    Hypothesis approxStrict_trans : forall s1 s2 s3,
      approx s2 s1
      -> approxStrict s2 s3
      -> approxStrict s1 s3.

    Variable approxStrict_dec : forall x y, {approxStrict x y} + {~approxStrict x y}.

    Hypothesis approxStrict_wf : well_founded approxStrict.

    Variable init : state.

    Hypothesis init_low : forall s, approx init s.

    Lemma iterate_approx : forall prog s,
      approx s (fold_left (fun s ins => exec ins s) prog s).
      induction prog; simpl; intuition eauto.
    Qed.

    Hint Resolve iterate_approx.

    Lemma iterate_pick' : forall ins prog s s',
      In ins prog
      -> approx s s'
      -> approxStrict (exec ins s) s
      -> approxStrict
      (fold_left (fun st ins => exec ins st)
        prog s') s.
      induction prog; simpl; intuition; subst.
      
      apply approxStrict_trans with (exec ins s); trivial.
      apply approx_trans with (exec ins s'); eauto.

      apply IHprog; auto.
      apply approx_trans with (exec a s); eauto.
    Qed.

    Lemma iterate_pick_cp : forall ins s,
      In ins program
	-> approxStrict (exec ins s) s
	-> approxStrict
	(fold_left (fun st ins => exec ins st)
          program s) s.
      intros.
      eapply iterate_pick'; eauto.
    Qed.

    Lemma iterate_pick : forall ins s,
      In ins program
	-> ~approxStrict
	(fold_left (fun st ins => exec ins st)
          program s) s
	-> ~approxStrict (exec ins s) s.
      generalize iterate_pick_cp; firstorder.
    Qed.

    Definition iterate : {fp : state
      | approx init fp
	/\ forall ins,
	  In ins program
	    -> approx (exec ins fp) fp}.
      pose (iter := Fix approxStrict_wf
	(fun _ => state)
	(fun s self =>
	  let s' := fold_left (fun st ins => exec ins st) program s in
	    match approxStrict_dec s' s with
	      | left pf => self s' pf
	      | _ => s
	    end)).

      exists (iter init).
      intros.

      assert (Happrox : forall x, approx x (iter x)).
      intro x; pattern x.
      eapply well_founded_ind; intuition.
      eauto.
      unfold iter; rewrite Fix_eq.
      match goal with
	| [ |- context[approxStrict_dec ?X ?Y] ] => destruct (approxStrict_dec X Y)
      end.
      fold iter.
      apply approx_trans with (fold_left (fun (st : state) (ins0 : instruction) => exec ins0 st)
        program x0); auto.
      auto.
      intuition.
      match goal with
	| [ |- context[approxStrict_dec ?X ?Y] ] => destruct (approxStrict_dec X Y)
      end; trivial.

      assert (HapproxStrict : forall x, ~approxStrict
	(fold_left (fun st ins => exec ins st) program (iter x)) (iter x)).
      intro x; pattern x.
      eapply well_founded_ind; intuition.
      eauto.
      unfold iter in H0; rewrite Fix_eq in H0.
      match goal with
	| [ H : context[approxStrict_dec ?X ?Y] |- _ ] => destruct (approxStrict_dec X Y)
      end; auto.
      eauto.
      intuition.
      match goal with
	| [ |- context[approxStrict_dec ?X ?Y] ] => destruct (approxStrict_dec X Y)
      end; trivial.

      intuition.
      apply approxStrict_approx.
      auto.
      apply iterate_pick; eauto.
    Qed.

    Definition fixed_point : {fp : state
      | forall s, reachable_flowInsensitive init s
	-> approx s fp}.
      destruct iterate as [fp [Hinit Hfp]].
      exists fp.

      clear init_low.
      induction 1; intuition eauto.
    Qed.

  End approx.
End reachable.
