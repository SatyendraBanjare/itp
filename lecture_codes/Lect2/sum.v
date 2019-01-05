Require Import Arith ArithRing.

Ltac defn x := unfold x; fold x.

Fixpoint sum (n : nat) : nat :=
  match n with
    | O => O
    | S n => S n + sum n
  end.

Theorem sum_equals : forall n, 2 * sum n = n * (n + 1).
  induction n.

  trivial.

  defn sum.
  rewrite mult_plus_distr_l.
  rewrite IHn.
  ring_nat.
Qed.

Print sum_equals.
