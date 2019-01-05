Ltac find_if :=
  match goal with
    | [ |- if ?X then _ else _ ] => destruct X
  end.

Theorem duh : forall (a b c : bool),
  if a
    then if b
      then True
      else True
    else if c
      then True
      else True.
  intros.
  repeat find_if; constructor.
Qed.

Ltac find_if_inside :=
  match goal with
    | [ |- context[if ?X then _ else _] ] => destruct X
  end.

Theorem duh2 : forall (a b : bool),
  (if a then 42 else 42) = (if b then 42 else 42).
  intros.
  repeat find_if_inside; reflexivity.
Qed.

Ltac my_tauto :=
  repeat match goal with
	   | [ H : ?P |- ?P ] => exact H

	   | [ |- True ] => constructor
	   | [ |- _ /\ _ ] => constructor
	   | [ |- _ -> _ ] => intro

	   | [ H : False |- _ ] => destruct H
	   | [ H : _ /\ _ |- _ ] => destruct H
	   | [ H : _ \/ _ |- _ ] => destruct H

	   | [ H1 : ?P -> ?Q, H2 : ?P |- _ ] =>
	     let H := fresh "H" in
	       (generalize (H1 H2); clear H1; intro H)
	 end.

Section propositional.
  Variables P Q R : Prop.

  Theorem and_comm : (P \/ Q) /\ (P -> Q) -> Q.
    my_tauto.
  Qed.
End propositional.

Ltac use H e :=
  match type of e with
    | ?A -> ?B =>
      let H' := fresh "H'" in
	(assert (H' : A);
	  [idtac
	    | assert (H : B);
	      [exact (e H')
		| clear H']])
  end.

Section use.
  Variable T : Set.
  Variable e : T.
  
  Variables A B : T -> Prop.
  Hypothesis Ae : A e.
  Variable G : Prop.
  Variable BeG : B e -> G.
  
  Theorem thm : (forall x, A x -> B x) -> G.
    intros.
    use H' (H e).
    exact Ae.
    apply BeG; exact H'.
  Qed.
End use.

Ltac autoUse :=
  repeat match goal with
	   | [ H : ?A -> ?B |- _ ] =>
	     let H' := fresh "H'" with H'' := fresh "H''" in
	       (assert (H' : A);
		 [clear H; auto; fail
		   | assert (H'' : B);
		     [exact (H H')
		       | clear H H'; auto]])
	 end.

Section autoUse.
  Variables a b c : nat.
  
  Hypothesis H1 : a = a -> b = c.
  Hypothesis H2 : c = b -> c = a.

  Theorem thm2 : a = c.
    autoUse.
  Qed.
End autoUse.

Ltac crazyRewriter limit :=
  match limit with
    | O => auto
    | S ?limit' =>
      try match goal with
	    | [ H : forall _, _ = _ |- context[?E] ] =>
	      rewrite (H E); auto; crazyRewriter limit'; fail
	  end
  end.

Section crazyRewriter.
  Variable A : Set.
  Variable e : A.
  Variable f : A -> A.
  Variable g : A -> A -> A.

  Hypothesis f_inverse : forall x, x = f (f x).
  Hypothesis g_e : forall x, f (f (f x)) = g e x.

  Theorem t : f e = g e e.
    crazyRewriter 1.
  Qed.

  Hint Extern 2 (_ = _) => crazyRewriter 1.

  Theorem t' : 0 < 1 /\ f e = g e e.
    intuition.
  Qed.
End crazyRewriter.
