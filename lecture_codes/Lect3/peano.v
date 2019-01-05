Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Check nat : Set.
Check O : nat.
Check S : nat -> nat.

Definition f n := match n with
		    | O => True
		    | S _ => False
		  end.

Theorem peano3 : forall n, S n <> O.
  unfold not.
  intros n H.
  change (f (S n)).
  rewrite H.
  change True.
  trivial.
Qed.

Theorem peano3_the_easy_way : forall n, S n <> O.
  intro.
  discriminate.
Qed.

Definition p n := match n with
		    | O => O
		    | S n' => n'
		  end.

Theorem peano4 : forall a b, S a = S b -> a = b.
  intros a b H.
  change (p (S a) = p (S b)).
  rewrite H.
  reflexivity.
Qed.

Theorem peano4_the_easy_way : forall a b, S a = S b -> a = b.
  intros.
  injection H.
  trivial.
Qed.

Check nat_ind : forall P : nat -> Prop,
  P O
  -> (forall n : nat, P n -> P (S n))
  -> forall n : nat, P n.

Fixpoint add (n m : nat) {struct n} : nat :=
  match n with
    | O => m
    | S n' => S (add n' m)
  end.

Theorem add_O_m : forall m, add O m = m.
  trivial.
Qed.

Theorem add_Sn_m : forall n m, add (S n) m = S (add n m).
  trivial.
Qed.

Theorem add_n_O_the_hard_way : forall n, add n O = n.
  induction n.

  simpl.
  reflexivity.

  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Theorem add_n_O : forall n, add n O = n.
  induction n; simpl; intuition congruence.
Qed.

Theorem add_n_Sm_the_hard_way : forall m n, add n (S m) = S (add n m).
  induction n.

  simpl.
  reflexivity.

  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Theorem add_n_Sm : forall m n, add n (S m) = S (add n m).
  induction n; simpl; intuition congruence.
Qed.

Theorem add_n_Sm' : forall n m, add n (S m) = S (add n m).
  induction n; simpl; intuition.
  generalize (IHn m).
  congruence.
Qed.

Definition g n := match n with
		    | O => S O
		    | S n' => n'
		  end.

Lemma n_neq_Sn : forall n, n <> S n.
  induction n; congruence.
Qed.

Theorem g_changes_the_hard_way : forall n, g n <> n.
  induction n.

  simpl.
  apply peano3.

  simpl.
  apply n_neq_Sn.
Qed.

Theorem g_changes : forall n, g n <> n.
  destruct n; simpl;
    [congruence
      | apply n_neq_Sn].
Qed.
