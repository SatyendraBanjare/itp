(** List utility stuff *)

Require Import List TheoryList.

Set Implicit Arguments.

Section ListUtil.
  Variable A : Set.

  Theorem nth_spec_implies_In : forall v (ls : list A) n,
    nth_spec ls n v
    -> In v ls.
    induction 1; intuition.
  Qed.

  Section eq_dec.
    Variable eq_dec : forall (x y : A), {x = y} + {x <> y}.

    Definition In_eq_dec : forall (x : A) (ls : list A), {In x ls} + {~In x ls}.
      induction ls; simpl; intuition.
      destruct (eq_dec a x); subst; intuition.
    Qed.

    Definition incl_eq_dec : forall (ls1 ls2 : list A), {incl ls1 ls2} + {~incl ls1 ls2}.
      induction ls1; simpl; intuition.
      unfold incl.
      left; intuition.
      inversion H.
      destruct (In_eq_dec a ls2).
      destruct (IHls1 ls2).
      intuition.
      right; intuition.
      apply f.
      do 2 intro.
      apply H; intuition.
      intuition.
    Qed.
  End eq_dec.

  Section AllS.
    Variable f : A -> Prop.

    Theorem AllS_In : forall ls, AllS f ls
      -> forall x, In x ls
	-> f x.
      induction 1; simpl; intuition.
      subst; trivial.
    Qed.

    Theorem AllS_deduce : forall ls,
      (forall x, In x ls
	-> f x)
      -> AllS f ls.
      induction ls; simpl; intuition.
    Qed.

    Hypothesis f_dec : forall x, {f x} + {~f x}.

    Definition AllS_dec : forall (ls : list A), {AllS f ls} + {~AllS f ls}.
      induction ls; simpl; intuition.
      destruct (f_dec a); intuition.
      right; intuition.
      apply f0.
      inversion H; trivial.

      right; intuition.
      apply b.
      inversion H; trivial.
    Qed.

    Definition AllS_dec_some : forall (ls : list A), {AllS f ls} + {~AllS f ls /\ ls <> nil}.
      destruct ls.
      intuition.

      destruct (AllS_dec (a :: ls)); intuition.
      right; intuition.
      discriminate.
    Qed.
    
    Theorem AllS_not : forall ls,
      ~AllS f ls
      -> ls = nil \/ exists x, In x ls /\ ~f x.
      induction ls; simpl; intuition.

      right.
      destruct (f_dec a).
      destruct ls.
      assert False; intuition.
      assert (AllS f (a0 :: ls) -> False).
      intuition.
      destruct (IHls H0) as [Hls | x [Hin Hf]]; subst.
    
      discriminate.
      firstorder.

      eauto.
    Qed.

    Theorem AllS_not_dec : forall ls,
      ~AllS f ls
      -> {x : A | In x ls /\ ~f x} + {ls = nil} .
      induction ls; simpl; intuition.

      left.
      destruct (f_dec a).
      destruct ls.
      assert False; intuition.
      assert (AllS f (a0 :: ls) -> False).
      intuition.
      destruct (IHls H0) as [[x [Hin Hf]] | Hls]; subst.

      exists x.
      intuition.
    
      discriminate.
      firstorder.
    Qed.
  End AllS.
End ListUtil.

Hint Resolve nth_spec_implies_In.

