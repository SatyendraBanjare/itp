(** * Some useful tactics *)

(** Here are the tactic definitions from HW1. *)

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

(** Plus the predefined tactics [assumption], [assert], [reflexivity], and
  [rewrite] *)


(** * Some propositional logic theorems *)

Theorem True_and_True : True /\ True.
  and_i.
  true_i.
  true_i.
Qed.

Section propositional.
  Variables A B C : Prop.

  Theorem p1 : A -> A.
    imp_i.
    assumption.
  Qed.

  Theorem p2 : (A -> B) -> A -> B.
    imp_i.
    imp_i.
    imp_e H H0.
  Qed.

  Theorem p3 : (A -> B) -> (B -> C) -> (A -> C).
    imp_i.
    imp_i.
    imp_i.
    imp_e H H1.
    imp_e H0 H2.
  Qed.

  Theorem p4 : A \/ A -> A.
    imp_i.
    or_e H.
    assumption.
    assumption.
  Qed.

  Theorem p5 : (A -> C) -> (B -> C) -> A \/ B -> C.
    imp_i.
    imp_i.
    imp_i.
    or_e H1.
    imp_e H H1.
    imp_e H0 H1.
  Qed.

  Theorem p6 : ~False.
    not_i.
    assumption.
  Qed.

  Theorem p7 : ~~True.
    not_i.
    assert True.
    true_i.
    not_e H H0.
  Qed.

  Theorem p8 : ~(A \/ B) -> ~A /\ ~B.
    imp_i.
    and_i.
    not_i.
    assert (A \/ B).
    or_i1.
    assumption.
    not_e H H1.
    not_i.
    assert (A \/ B).
    or_i2.
    assumption.
    not_e H H1.
  Qed.
End propositional.


(** * Some first-order theorems *)

Section firstorder.
  Variable A : Set.
  Variable e : A.
  Variable f : A -> A.
  Variable P : A -> Prop.
  Variable Q : A -> A -> Prop.
  Variable R : Prop.

  Theorem f1 : (forall x : A, P x)
    -> P e.
    imp_i.
    forall_e H e.
  Qed.

  Theorem f2 : (forall x : A, P (f x))
    -> (P (f e) -> R)
    -> R.
    imp_i.
    imp_i.
    forall_e H e.
    imp_e H0 H1.
  Qed.

  Theorem f3 : P e
    -> (exists x : A, P x).
    imp_i.
    exists_i e.
    assumption.
  Qed.

  Theorem f4 : (exists x : A, P (f x))
    -> (forall x : A, P x -> R)
    -> R.
    imp_i.
    imp_i.
    exists_e H.
    forall_e H0 (f x).
    imp_e H1 H.
  Qed.

  Theorem f5 : (forall x : A, x = e -> R)
    -> R.
    imp_i.
    forall_e H e.
    assert (e = e).
    reflexivity.
    imp_e H0 H1.
  Qed.

  Theorem f6 : forall x : A, forall y : A, forall z : A,
    x = y
    -> y = z
    -> x = z.
    forall_i.
    forall_i.
    forall_i.
    imp_i.
    imp_i.
    rewrite H.
    assumption.
  Qed.

  Theorem f7 : (forall x : A, forall y : A, forall z : A, Q x y -> Q y z -> Q x z)
    -> (forall x : A, Q x (f x))
    -> (exists x : A, Q e (f (f x))).
    imp_i.
    imp_i.
    exists_i e.
    forall_e H e.
    forall_e H1 (f e).
    forall_e H2 (f (f e)).
    forall_e H0 e.
    forall_e H0 (f e).
    imp_e H3 H4.
    imp_e H6 H5.
  Qed.

  Theorem f8 :
    e = f e
    -> (forall x, P (f x))
    -> P e.
    imp_i.
    imp_i.
    forall_e H0 e.
    rewrite H.
    assumption.
  Qed.
End firstorder.
