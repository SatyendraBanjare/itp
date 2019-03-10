(** Homework Assignment 3#<br>#
#<a href="http://www.cs.berkeley.edu/~adamc/itp/">#Interactive Computer Theorem
Proving#</a><br>#
CS294-9, Fall 2006#<br>#
UC Berkeley *)

Require Import List.

(** Submit your solution file for this assignment
  #<a href="mailto:adamc@cs.berkeley.edu?subject=ICTP HW3">#by e-mail#</a># with
  the subject "ICTP HW3" by the start of class on September 21.
  You should write your solutions entirely on your own, which includes not
  consulting any solutions to these problems that may be posted on the web.

  #<a href="HW3.v">#Template source file#</a>#
  *)


(** * Last elements of lists *)

Section last.
  Variable A : Set.

  Inductive last (a : A) : list A -> Prop :=
    | last_this : last a (a :: nil)
    | last_seek : forall x ls, last a ls -> last a (x :: ls).

  Fixpoint last_f (ls : list A) : option A :=
    match ls with
      | nil => None
      | a :: nil => Some a
      | _ :: ls' => last_f ls'
    end.

  Theorem lasts_agree1 : forall a ls,
    last a ls -> last_f ls = Some a.
    induction ls; simpl; inversion 1.
    - reflexivity.
    - destruct ls. intuition. discriminate.
      intuition. 
  Qed.

  Theorem lasts_agree2 : forall a ls,
    last_f ls = Some a -> last a ls.
    Admitted.
End last.


(** * Permutations *)

Section permutation.
  Variable A : Set.

  Inductive transpose : list A -> list A -> Prop :=
    | transpose_head : forall x y ls,
      transpose (x :: y :: ls) (y :: x :: ls)
    | transpose_seek : forall x ls ls',
      transpose ls ls'
      -> transpose (x :: ls) (x :: ls').

  Inductive permutation : list A -> list A -> Prop :=
    | permutation_done : forall ls,
      permutation ls ls
    | permutation_transpose : forall ls ls' ls'',
      permutation ls ls'
      -> transpose ls' ls''
      -> permutation ls ls''.

  Theorem permutation_reflexive : forall ls,
    permutation ls ls.
    intros.
    constructor.
  Qed.

  Theorem permutation_transitive : forall ls1 ls2 ls3,
    permutation ls1 ls2
    -> permutation ls2 ls3
    -> permutation ls1 ls3.
    induction 2; intuition.
    apply permutation_transpose with ls'; auto.
  Qed.

  (*Lemma permutation_transpose' : forall ls1 ls2 ls3,
    transpose ls1 ls2
    -> permutation ls2 ls3
    -> permutation ls1 ls3.
    induction 2; intuition.

    apply permutation_transpose with ls1; trivial; constructor.

    apply permutation_transitive with ls'; trivial.
    apply permutation_transpose with ls'; trivial; constructor.
  Qed.*)

  Lemma transpose_symmetric : forall ls1 ls2,
    transpose ls1 ls2
    -> transpose ls2 ls1.
    induction 1.
    constructor.
    constructor; auto.
  Qed.

  Theorem permutation_symmetric : forall ls1 ls2,
    permutation ls1 ls2
    -> permutation ls2 ls1.
    Admitted.
End permutation.
