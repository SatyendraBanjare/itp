(** Homework Assignment 2#<br>#
#<a href="http://www.cs.berkeley.edu/~adamc/itp/">#Interactive Computer Theorem
Proving#</a><br>#
CS294-9, Fall 2006#<br>#
UC Berkeley *)

Require Import Arith Omega.

(** Submit your solution file for this assignment
  #<a href="mailto:adamc@cs.berkeley.edu?subject=ICTP HW2">#by e-mail#</a># with
  the subject "ICTP HW2" by the start of class on September 14.
  You should write your solutions entirely on your own.

  #<a href="HW2.v">#Template source file#</a>#
  *)

(** * Booleans *)

Definition bool_not (b : bool) :=
  match b with
    | false => true
    | true => false
  end.

Definition bool_xor (b1 b2 : bool) :=
  match b1 with
    | false => b2
    | true => bool_not b2
  end.

Definition bool_and (b1 b2 : bool) :=
  match b1 with
    | false => false
    | true => b2
  end.

Definition bool_or (b1 b2 : bool) :=
  match b1 with
    | false => b2
    | true => true
  end.

Definition bool_eq (b1 b2 : bool) :=
  match b1 with
    | false => bool_not b2
    | true => b2
  end.

Theorem xor_not_eq : forall b1 b2,
  bool_xor b1 b2 = bool_not (bool_eq b1 b2).
  destruct b1; destruct b2;  auto.
Qed.

Theorem not_and_or_not : forall b1 b2,
  bool_not (bool_and b1 b2) = bool_or (bool_not b1) (bool_not b2).
  destruct b1; destruct b2; auto.
Qed.


(** * Lists *)

Inductive list : Set :=
  | nil : list
  | cons : nat -> list -> list.

Fixpoint append (ls1 ls2 : list) {struct ls1} : list :=
  match ls1 with
    | nil => ls2
    | cons h t => cons h (append t ls2)
  end.

Fixpoint reverse (ls : list) : list :=
  match ls with
    | nil => nil
    | cons h t => append (reverse t) (cons h nil)
  end.

Fixpoint reverse'_helper (ls acc : list) {struct ls} : list :=
  match ls with
    | nil => acc
    | cons h t => reverse'_helper t (cons h acc)
  end.

Definition reverse' (ls : list) : list := reverse'_helper ls nil.

Theorem append_associative : forall ls1 ls2 ls3,
  append (append ls1 ls2) ls3 = append ls1 (append ls2 ls3).
  induction ls1; simpl; intuition.
  rewrite IHls1; intuition.
Qed.

Lemma reverse'_helper_correct : forall ls acc,
  reverse'_helper ls acc = append (reverse ls) acc.
  induction ls; simpl; intuition.
  rewrite IHls.
  rewrite append_associative.
  auto.
Qed.

Lemma append_nil : forall ls, append ls nil = ls.
  induction ls; simpl; intuition.
  congruence.
Qed.

Theorem reverse'_correct : forall ls, reverse' ls = reverse ls.
  intros.
  unfold reverse'.
  rewrite reverse'_helper_correct.
  apply append_nil.
Qed.


(** * Trees *)

Inductive tree : Set :=
  | Leaf : tree
  | Node : tree -> nat -> tree -> tree.

Definition isLeaf (t : tree) :=
  match t with
    | Leaf => True
    | Node _ _ _ => False
  end.

Theorem Leaf_neq_Node : forall t1 n t2, Leaf <> Node t1 n t2.
  intros t1 n t2 H.
  change (isLeaf (Node t1 n t2)).
  rewrite <- H.
  change True.
  trivial.
Qed.

Definition leftChild (t : tree) :=
  match t with
    | Leaf => Leaf
    | Node t' _ _ => t'
  end.

Theorem Node_inj : forall t11 n1 t12 t21 n2 t22,
  Node t11 n1 t12 = Node t21 n2 t22
  -> t11 = t21.
  intros t11 n1 t12 t21 n2 t22 H.
  change (leftChild (Node t11 n1 t12) = leftChild (Node t21 n2 t22)).
  rewrite H.
  reflexivity.
Qed.

Fixpoint insert (n : nat) (t : tree) {struct t} : tree :=
  match t with
    | Leaf => Node Leaf n Leaf
    | Node tle n' tgt =>
      if le_lt_dec n n'
	then Node (insert n tle) n' tgt
	else Node tle n' (insert n tgt)
  end.

Fixpoint size (t : tree) : nat :=
  match t with
    | Leaf => 0
    | Node tle _ tgt => S (size tle + size tgt)
  end.

Theorem insert_increases : forall (n : nat) (t : tree),
  size (insert n t) = S (size t).
  induction t; simpl; intuition.
  destruct (le_lt_dec n n0); simpl; omega.
Qed.

Fixpoint ordered' (min : nat) (max : option nat) (t : tree) {struct t} : Prop :=
  match t with
    | Leaf => True
    | Node t1 n t2 =>
      min <= n
      /\ match max with
	   | None => True
	   | Some max => n <= max
	 end
      /\ ordered' min (Some n) t1
      /\ ordered' (S n) max t2
  end.

Definition ordered (t : tree) : Prop :=
  ordered' O None t.