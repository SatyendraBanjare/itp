(** Homework Assignment 1#<br>#
#<a href="http://www.cs.berkeley.edu/~adamc/itp/">#Interactive Computer Theorem
Proving#</a><br>#
CS294-9, Fall 2006#<br>#
UC Berkeley *)

(** * Some useful tactics *)

(** Here is some support code to help you build proofs using the same natural
  deduction terminology that we used in class.  It's safe to skip over these.

  One potential gotcha that's important to remember: For tactics that take
  arguments, when one of the arguments contains spaces, enclose it in
  parentheses to avoid scary error messages.
  *)

Ltac elimer e := try exact e; let H := fresh "H" in (generalize e; intro H).

Ltac true_i := elimer I.

Ltac false_e Hfalse := destruct Hfalse.

Ltac imp_i := intro.
Ltac imp_e Himp Hant := elimer (Himp Hant).

Ltac and_i := split.
Ltac and_e1 Hand := elimer (proj1 Hand).
Ltac and_e2 Hand := elimer (proj2 Hand).

Ltac or_i1 := left.
Ltac or_i2 := right.
Ltac or_e Hor := destruct Hor.

Ltac not_i := intro.
Ltac not_e Hno Hyes := destruct (Hno Hyes).

Ltac forall_i := intro.
Ltac forall_e Hall x := elimer (Hall x).

Ltac exists_i x := exists x.
Ltac exists_e Hex := destruct Hex.

(** Plus the predefined tactics [assumption], [reflexivity], and [rewrite] *)


(** * Propositional Logic *)

(** We open a [Section], which is a mechanism for controlling the scoping of
   variables and assumptions.
  *)
Section propositional.
  (** We want to prove some theorems about arbitary propositions, so we declare
    three propositional variables, scoped within this [Section] only. *)
  Variables P Q R : Prop.

  (** OK, here's where the interactive part starts.  Prove these simple theorems
    in propositional logic.  Use a natural deduction style, by way of the tactics
    defined in the beginning of this source file.  They're the same that we used
    in class. *)

  (** Truth is true. *)
  Theorem truth : True.
    true_i.
  Qed.

  (** False implies anything *)
  Theorem contradiction_P : False -> P.
    imp_i.
    destruct H.
  Qed.

  (** [/\] is associative. *)
  Theorem and_associates : (P /\ Q) /\ R -> P /\ (Q /\ R).
    intros .
    split.
    and_e1 H.
    and_e1 H0.
    split.
    and_e1 H.
    and_e2 H0.
    and_e2 H.
  Qed.

  (** Dropping conjuncts preserves truth. *)
  Theorem cut_out_the_middle_man : P /\ Q /\ R -> P /\ R.
    intros.
    split.
    and_e1 H.
    and_e2 H.
    and_e2 H0.
  Qed.

  (** One or the other is true!  Can you figure out which? *)
  Theorem make_up_your_mind : True \/ False.
    left.
    true_i.
  Qed.

  (** \/ is commutative. *)
  Theorem or_commutes : P \/ Q -> Q \/ P.
    intros.
    destruct H.
    right. apply H.
    left. apply H.
  Qed.

  (** \/ is associative. *)
  Theorem or_associates : (P \/ Q) \/ R -> P \/ (Q \/ R).
    intros .
    destruct H.
    destruct H.
    left.
    apply H.
    right ; left.
    apply H.
    right; right.
    apply H.
  Qed.

  (** Something is fishy about the hypotheses, so we can deduce anything. *)
  Theorem something_fishy : (P -> Q) -> P -> ~Q -> R.
    intros .
    imp_e H H0.
    not_e H1 H2.
  Qed.

  (** The law of contraposition holds only in this direction in constructive
    logic. *)
  Theorem contrapositive : (P -> Q) -> ~Q -> ~P.
    intros.
    simpl.
    intro.
    imp_e H H1.
    not_e H0 H2.
  Qed.
End propositional.


(** * First-order logic *)

Section firstorder.
  (** We'll prove some theorems that draw their individuals an
    unspecified set [A]. *)
  Variable A : Set.

  (** Here's an arbitrary individual in [A]. *)
  Variable e : A.

  (** Here's a unary function symbol. *)
  Variable f : A -> A.

  (** Here are two unary predicate symbols. *)
  Variables P P' : A -> Prop.

  (** Here's a binary predicate symbol. *)
  Variable Q : A -> A -> Prop.

  (** If [P] holds for any value, then it must hold for [f e]. *)
  Theorem indeed : (forall x : A, P x) -> P (f e).
    intros.
    forall_e H (f e).
  Qed.

  (** If [P] holds for anything [f] returns, then [P] holds of something. *)
  Theorem ofcourse : (forall x : A, P (f x)) -> (exists y : A, P y).
    imp_i.
    exists_i (f e).
    forall_e H e.
  Qed.

  (** Swapping [exists] and [forall] in this way is always legal. *)
  Theorem swap_quantifiers :
    (exists x : A, forall y : A, Q x y)
    -> (forall y : A, exists x : A, Q x y).
    intros.
    destruct H.
    exists x.
    forall_e H y.
  Qed.

  (** If [P] maps everything to false, then we can't find anything it maps to
    true. *)
  Theorem nobody :
    (forall x : A, ~(P x))
    -> ~(exists x : A, P x).
    intros.
    intro.
    destruct H0.
    forall_e H x.
    not_e H1 H0.
  Qed.

  (** We can push a conjunction inside universal quantifications. *)
  Theorem coalesce1 : (forall x : A, P x) /\ (forall x : A, P' x)
    -> (forall x : A, P x /\ P' x).
    intros. split.
    and_e1 H.
    forall_e H0 x.
    and_e2 H.
    forall_e H0 x.
  Qed.

  (** We can push a universal quantification inside a conjunction. *)
  Theorem coalesce2 : (forall x : A, P x /\ P' x)
    -> (forall x : A, P x) /\ (forall x : A, P' x).
    forall_i.
    and_i.
    forall_i.
    forall_e H x.
    and_e1 H0.
    forall_i.
    forall_e H x.
    and_e2 H0.
  Qed.

  (** This one doesn't have any deeper meaning. :-) *)
  Theorem one_or_the_other :
    (forall x : A, P x -> P' e)
    -> ((forall y : A, P' y) \/ (exists z : A, P z))
    -> P' e.
    imp_i.
    imp_i.
    or_e H0.
    forall_e H0 e.
    exists_e H0.
    forall_e H x.
    imp_e H1 H0.
  Qed.

  (** A straightforward fact about equality and functions *)
  Theorem reverse_congruence : forall x : A, forall y : A,
    x = y -> f y = f x.
    forall_i.
    forall_i.
    imp_i.
    rewrite H.
    reflexivity.
  Qed.

  (** If the set [A] has only one member, then we can derive a particular
    equality. *)
  Theorem small_world : (exists x : A, forall y : A, x = y)
    -> e = f e.
    imp_i.
    exists_e H.
    forall_e H e.
    rewrite <- H0.
    forall_e H (f x).
  Qed.

  (** A complicated theorem about equality and functions *)
  Theorem nasty : forall x : A, forall y : A, forall z : A,
    f (f x) = x
    -> f z = f x
    -> f y = f z
    -> f (f (f (f (f x)))) = f y.
    forall_i.
    forall_i.
    forall_i.
    imp_i.
    imp_i.
    imp_i.
    rewrite H.
    rewrite H.
    rewrite <- H0.
    rewrite H1.
    reflexivity.
  Qed.
End firstorder.

