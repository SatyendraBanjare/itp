Require Import Arith List.


(** * Strongly-specified "pred" *)

Lemma eq_geq_contra : 0 > 0 -> False.
  inversion 1.
Qed.

Check False_rec.

Print pred.

Extraction pred.

Definition pred_strong1 : forall (n : nat), n > 0 -> nat :=
  fun n : nat =>
    match n return (n > 0 -> nat) with
      | O => fun pf : 0 > 0 => False_rec _ (eq_geq_contra pf)
      | S n' => fun _ => n'
    end.

Extraction pred_strong1.

Print sig.

Definition pred_strong2 : {n : nat | n > 0} -> nat :=
  fun s : {n : nat | n > 0} =>
    match s with
      | exist O pf => False_rec _ (eq_geq_contra pf)
      | exist (S n') _ => n'
    end.

Extraction pred_strong2.

Definition pred_strong3 : forall n, n > 0 -> {m : nat | n = S m} :=
  fun n : nat =>
    match n return (n > 0 -> {m : nat | n = S m}) with
      | O => fun pf : 0 > 0 => False_rec _ (eq_geq_contra pf)
      | S n' => fun _ => exist (fun m => S n' = S m) n' (refl_equal _)
    end.

Extraction pred_strong3.

Definition pred_strong4 : forall n, n > 0 -> {m : nat | n = S m}.
  intros n pf.
  destruct n.
  assert False.
  inversion pf.
  tauto.
  exists n.
  reflexivity.
Defined.

Extraction pred_strong4.

Definition pred_strong5 : forall n, n > 0 -> {m : nat | n = S m}.
  refine (fun n : nat =>
    match n return (n > 0 -> {m : nat | n = S m}) with
      | O => fun pf : 0 > 0 => False_rec _ _
      | S n' => fun _ => exist (fun m => S n' = S m) n' _
    end).
  inversion pf.
  reflexivity.
Defined.

Extraction pred_strong5.

Hint Resolve eq_geq_contra.

Definition pred_strong6 : forall n, n > 0 -> {m : nat | n = S m}.
  refine (fun n : nat =>
    match n return (n > 0 -> {m : nat | n = S m}) with
      | O => fun pf : 0 > 0 => False_rec _ _
      | S n' => fun _ => exist (fun m => S n' = S m) n' _
    end); auto.
Defined.

Extraction pred_strong6.


(** * Eliminations and extraction *)

Check eq_S.

Check (pairT sig ex).

Definition Set_to_Set (x : nat) (s : {y : nat | y = x + x}) : {y : nat | S y = S (x + x)} :=
  match s with
    | exist y pf => exist (fun y => S y = S (x + x)) y (eq_S _ _ pf)
  end.

Extraction Set_to_Set.

Definition Set_to_Prop (x : nat) (s : {y : nat | y = x + x}) : exists y, S y = S (x + x) :=
  match s with
    | exist y pf => ex_intro (fun y => S y = S (x + x)) y (eq_S _ _ pf)
  end.

Extraction Set_to_Prop.

Definition Prop_to_Prop (x : nat) (s : exists y, y = x + x) : exists y, S y = S (x + x) :=
  match s with
    | ex_intro y pf => ex_intro (fun y => S y = S (x + x)) y (eq_S _ _ pf)
  end.

Extraction Prop_to_Prop.

(*Definition Prop_to_Set (x : nat) (s : exists y, y = x + x) : {y : nat | S y = S (x + x)} :=
  match s with
    | ex_intro y pf => exist (fun y => S y = S (x + x)) y (eq_S _ _ pf)
  end.*)


(** * Decidable equality *)

Print sumbool.

Hint Extern 1 (_ <> _) => discriminate.

Definition bool_eq_dec1 : forall (x y : bool), {x = y} + {x <> y}.
  destruct x; destruct y; auto.
Defined.

Definition bool_eq_dec2 : forall (x y : bool), {x = y} + {x <> y}.
  refine (fun x : bool =>
    match x return (forall y : bool, {x = y} + {x <> y}) with
      | false => fun y : bool =>
	match y return ({false = y} + {false <> y}) with
	  | false => left _ _
	  | true => right _ _
	end
      | true => fun y : bool =>
	match y return ({true = y} + {true <> y}) with
	  | false => right _ _
	  | true => left _ _
	end
    end); auto.
Defined.

Extraction bool_eq_dec1.
Extraction bool_eq_dec2.

Definition nat_eq_dec1 : forall (x y : nat), {x = y} + {x <> y}.
  induction x; destruct y; firstorder.
Defined.

Definition nat_eq_dec2 : forall (x y : nat), {x = y} + {x <> y}.
  refine (fix nat_eq_dec2 (x : nat) : forall (y : nat), {x = y} + {x <> y} :=
    match x return (forall y : nat, {x = y} + {x <> y}) with
      | O => fun y : nat =>
	match y return ({O = y} + {O <> y}) with
	  | O => left _ _
	  | S _ => right _ _
	end
      | S x' => fun y : nat =>
	match y return ({S x' = y} + {S x' <> y}) with
	  | O => right _ _
	  | S y' =>
	    match nat_eq_dec2 x' y' with
	      | left _ => left _ _
	      | right _ => right _ _
	    end
	end
    end); auto.
Defined.

Extraction nat_eq_dec1.
Extraction nat_eq_dec2.

Definition bool_eq_dec : forall (x y : bool), {x = y} + {x <> y}.
  decide equality.
Defined.

Definition nat_eq_dec : forall (x y : nat), {x = y} + {x <> y}.
  decide equality.
Defined.

Extraction bool_eq_dec.
Extraction nat_eq_dec.


(** * List membership *)

Hint Extern 1 False =>
  match goal with
    | [ H : In _ (_ :: _) |- _ ] => inversion H; clear H; subst
  end.

Section In_dec.
  Variable A : Set.
  Variable A_eq_dec : forall (x y : A), {x = y} + {x <> y}.

  Definition In_dec : forall (x : A) (ls : list A), {In x ls} + {~In x ls}.
    refine (fix In_dec (x : A) (ls : list A) {struct ls}
      : {In x ls} + {~In x ls} :=
      match ls return {In x ls} + {~In x ls} with
	| nil => right _ _
	| x' :: ls' =>
	  if A_eq_dec x x'
	    then left _ _
	    else if In_dec x ls'
	      then left _ _
	      else right _ _
      end); intros; subst; intuition.
  Qed.
End In_dec.

Extraction In_dec.


(** * Association lists *)

Print sumor.

Hint Extern 1 False =>
  match goal with
    | [ H : (_, _) = (_, _) |- _ ] => injection H; clear H; intros; subst
  end.

Section assoc.
  Variables A B : Set.
  Variable A_eq_dec : forall (x y : A), {x = y} + {x <> y}.

  Definition assoc : forall (x : A) (ls : list (A * B)),
    {y : B | In (x, y) ls} + {forall y, ~In (x, y) ls}.
    refine (fix assoc (x : A) (ls : list (A * B)) {struct ls}
      : {y : B | In (x, y) ls} + {forall y, ~In (x, y) ls} :=
      match ls return {y : B | In (x, y) ls} + {forall y, ~In (x, y) ls} with
	| nil => inright _ _
	| (x', y) :: ls' =>
	  if A_eq_dec x x'
	    then inleft _ (exist _ y _)
	    else match assoc x ls' with
		   | inleft (exist y' _) => inleft _ (exist _ y' _)
		   | inright _ => inright _ _
		 end
      end); intros; subst; intuition; eauto.
  Qed.
End assoc.

Extraction assoc.


(** * Set signatures *)

Print sigS.

Definition makeSum (n : nat) : {m1 : nat & {m2 : nat | m1 + m2 = n}}.
  refine (fun n : nat =>
    match n return {m1 : nat & {m2 : nat | m1 + m2 = n}} with
      | O => existS (fun m1 => {m2 : nat | m1 + m2 = O}) O (exist _ O _)
      | S n' => existS (fun m1 => {m2 : nat | m1 + m2 = S n'}) 1 (exist _ n' _)
    end); auto.
Defined.

Extraction makeSum.


(** * (Not so) Finite state machines *)

Section tryAll.
  Variables A B : Set.
  Variable P : forall (x : A), B -> Prop.
  Variable P_dec : forall x, {y : B | P x y} + {forall y, ~P x y}.

  Definition tryAll : forall (ls : list A),
    {y : B | exists x, In x ls /\ P x y}
    + {forall x, In x ls -> forall y, ~P x y}.
    refine (fix tryAll (ls : list A)
      : {y : B | exists x, In x ls /\ P x y}
      + {forall x, In x ls -> forall y, ~P x y} :=
      match ls return {y : B | exists x, In x ls /\ P x y}
	+ {forall x, In x ls -> forall y, ~P x y} with
	| nil => inright _ _
	| x :: ls' =>
	  match P_dec x with
	    | inleft (exist y _) => inleft _ (exist _ y _)
	    | inright _ => match tryAll ls' with
			     | inleft (exist y _) => inleft _ (exist _ y _)
			     | inright _ => inright _ _
			   end
	  end
      end); simpl; intuition; subst; eauto.
    firstorder.
  Defined.
End tryAll.

Section FSM.
  Variable char : Set.
  Variable state : Set.
  Variable startState : state.
  Variable acceptingStates : list state.
  Variable transitions : state -> char -> list state.

  Variable state_eq_dec : forall (s1 s2 : state), {s1 = s2} + {s1 <> s2}.

  Definition word := list char.

  Inductive reach : state -> word -> state -> Prop :=
    | Done : forall (s : state),
      reach s nil s
    | Step : forall (s : state) (ch : char) (w : word) (s' s'' : state),
      In s' (transitions s ch)
      -> reach s' w s''
      -> reach s (ch :: w) s''.

  Hint Constructors reach.

  Hint Extern 1 False =>
    match goal with
      | [ H : reach _ nil _ |- _ ] => inversion H; clear H; subst
      | [ H : reach _ (_ :: _) _ |- _ ] => inversion H; clear H; subst
    end.

  Hint Extern 1 (reach _ _ _) =>
    match goal with
      | [ H : ex _ |- _ ] => destruct H; intuition
    end.

  Definition accepted : forall (w : word) (s : state),
    {s' : state | reach s w s' /\ In s' acceptingStates}
    + {forall s', ~(reach s w s' /\ In s' acceptingStates)}.
    refine (fix accepted (w : word) (s : state) {struct w}
      : {s' : state | reach s w s' /\ In s' acceptingStates}
      + {forall s', ~(reach s w s' /\ In s' acceptingStates)} :=
      match w return {s' : state | reach s w s' /\ In s' acceptingStates}
	+ {forall s', ~(reach s w s' /\ In s' acceptingStates)} with
	| nil =>
	  match In_dec _ _ s acceptingStates with
	    | left _ => inleft _ (exist _ s _)
	    | right _ => inright _ _
	  end
	| ch :: w' =>
	  match tryAll _ _ (fun s s' => reach s w' s' /\ In s' acceptingStates) (accepted w') (transitions s ch) with
	    | inleft (exist s' _) => inleft _ (exist _ s' _)
	    | inright _ => inright _ _
	  end
      end); intuition eauto; firstorder.
  Defined.
End FSM.

Recursive Extraction accepted.
