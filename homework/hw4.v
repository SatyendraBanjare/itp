(** * Proof terms *)

Section propositional.
  Variables P Q R : Prop.

  Definition term1 : (P -> Q -> R) -> (Q -> P -> R) :=
    fun f : (P -> Q -> R) =>
      fun q : Q => fun p : P => f p q.

  Definition term2 : P /\ Q -> R \/ P :=
    fun x : (P /\ Q) => or_intror R (proj1 x).

  Definition term3 : P \/ Q -> (Q -> P) -> P :=
    fun pq : (P \/ Q) => fun f : (Q -> P) =>
      or_ind
      (fun H : P => H)
      (fun H : Q => f H)
      pq.

  Definition term4 : P -> ~~P :=
    fun p : P => fun np : ~P => np p.
End propositional.

Section firstorder.
  Variable A : Set.
  Variable Q : A -> A -> Prop.

  Definition swap_quantifiers :
    (forall (x : A) (y : A), Q x y)
    -> (forall (y : A) (x : A), Q x y) :=
    fun f : (forall (x : A) (y : A), Q x y) =>
      fun y : A => fun x : A => f x y.

  Definition swap_quantifiers2 :
    (exists x : A, forall y : A, Q x y)
    -> (forall y : A, exists x : A, Q x y) :=
    fun Hex : (exists x : A, forall y : A, Q x y) =>
      fun y : A =>
  let (x, Hx) := Hex in
    ex_intro (fun x : A => Q x y) x (Hx y).

  Definition eq_transitive :
    forall (x y z : A),
      x = y
      -> y = z
      -> x = z :=
      fun (x y z : A) (Hxy : x = y) (Hyz : y = z) =>
  eq_ind y (fun y' => x = y') Hxy z Hyz.
End firstorder.


(** * Induction principles *)

Section my_nat_ind.
  Variable P : nat -> Prop.
  Variable base : P O.
  Variable ind : forall n, P n -> P (S n).

  Fixpoint my_nat_ind (n : nat) : P n :=
    match n return (P n) with
      | O => base
      | S n' => ind n' (my_nat_ind n')
    end.
End my_nat_ind.

Require Import List.

Section my_list_ind.
  Variable A : Set.
  Variable P : list A -> Prop.
  Variable base : P nil.
  Variable ind : forall x ls, P ls -> P (x :: ls).

  Fixpoint my_list_ind (ls : list A) : P ls :=
    match ls return (P ls) with
      | nil => base
      | x :: ls' => ind x ls' (my_list_ind ls')
    end.
End my_list_ind.
