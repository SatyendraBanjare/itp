Require Import Omega.

(** Proofs as terms **)
Parameter P Q R : Prop.

(** So convenient ... *)
Axiom FixMe: forall P : Prop, P.

Theorem t1 : P -> P.
auto.
Qed.

Print t1.


Definition t1' : P -> P := FixMe _.

Definition t2: P -> ((P -> Q) -> Q) := FixMe _.


Definition t3: (P -> Q) -> (Q -> R) -> (P -> R) := FixMe _.

(*** Logical connectives ***)
Check and_ind.

Check or_ind.
Check True_ind.

Check False_ind.

Print exist.

Check ex_ind.


(** Dropping conjuncts preserves truth. *)
Theorem cut1 : P /\ Q /\ R -> P /\ R.
Admitted.


Theorem ex1: exists n : nat, 2 <= 3.
Admitted.


Theorem ex2: forall n, 1 <= n -> exists m, n = S m.
Admitted.


(** Natural numbers in binary notation. Least significant bit at the top *)
Inductive bin : Set := 
  | bH : bin               (* end *)
  | bI : bin -> bin        (* 2x+1 *)
  | bO : bin -> bin        (* 2x   *)
.
Check bin_ind.

(** Evaluate a binary number *)
Fixpoint bval (b: bin) : nat := 
  match b with 
     bH => O
   | bI b => 1 + bval b + bval b
   | bO b => bval b + bval b
  end.


Eval compute in (bval (bO (bI (bI bH)))).


(** Write the generic recursion function *)
Check bin_rec.


(** Define an alternate bval using bin_rec *)
Axiom Magic: forall (A : Set), A.
Definition bval' (b: bin) : nat := Magic _.

(** increment a binary number *)
Fixpoint bincr (b: bin) : bin := 
  match b with 
     bH => bI bH
   | bO b => bI b
   | bI b => bO (bincr b)
 end
.

Theorem bincr_correct: forall b, bval (bincr b) = 1 + bval b.
Admitted.


(** Write the induction principle using recursion **)
Check bin_ind.


(** Challenge, show that for every nat there is a corresponding bin *)
