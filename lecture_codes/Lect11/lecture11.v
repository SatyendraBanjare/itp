Require Import Arith Bool.

Set Implicit Arguments.


(** * Easy reflection example: evenness of [nat]s *)

Inductive isEven : nat -> Prop :=
  | Even_O : isEven O
  | Even_SS : forall n, isEven n -> isEven (S (S n)).

Ltac prove_even :=
  repeat (apply Even_O || apply Even_SS).

Theorem even_256 : isEven 256.
  prove_even.
Qed.

Print even_256.

Fixpoint check_even (n : nat) : bool :=
  match n with
    | 0 => true
    | 1 => false
    | S (S n') => check_even n'
  end.

Hint Constructors isEven.

Lemma check_even_sound' : forall n, (check_even n = true -> isEven n)
  /\ (check_even (S n) = true -> isEven (S n)).
  induction n; simpl; intuition; discriminate.
Qed.

Theorem check_even_sound : forall n, check_even n = true -> isEven n.
  intros.
  generalize (check_even_sound' n); tauto.
Qed.

Ltac prove_even_reflective :=
  apply check_even_sound; reflexivity.

Theorem even_256' : isEven 256.
  prove_even_reflective.
Qed.

Print even_256'.


(** * Some support code: lists at sort Type *)

Section listT.
  Variable A : Type.
  
  Inductive listT : Type :=
    | nilT : listT
    | consT : A -> listT -> listT.
End listT.

Implicit Arguments nilT [A].


(** * A reflective tautology solver *)

Inductive formula : Set :=
  | Atomic : nat -> formula
  | Truth : formula
  | Falsehood : formula
  | And : formula -> formula -> formula
  | Or : formula -> formula -> formula
  | Imp : formula -> formula -> formula.

Section interp_formula.
  Variable atomics : nat -> Prop.

  Fixpoint interp_formula (f : formula) : Prop :=
    match f with
      | Atomic n => atomics n
      | Truth => True
      | Falsehood => False
      | And f1 f2 => interp_formula f1 /\ interp_formula f2
      | Or f1 f2 => interp_formula f1 \/ interp_formula f2
      | Imp f1 f2 => interp_formula f1 -> interp_formula f2
    end.
End interp_formula.

Definition asgn := nat -> bool.

Definition add (f : asgn) (n : nat) :=
  fun n' =>
    if eq_nat_dec n' n
      then true
      else f n'.

Fixpoint forward (hyps : asgn) (hyp : formula) (cont : asgn -> bool) {struct hyp} : bool :=
  match hyp with
    | Atomic n => cont (add hyps n)
    | Truth => cont hyps
    | Falsehood => true
    | And hyp1 hyp2 => forward hyps hyp1 (fun hyps' => forward hyps' hyp2 cont)
    | Or hyp1 hyp2 => forward hyps hyp1 cont && forward hyps hyp2 cont
    | Imp _ _ => cont hyps
  end.

Fixpoint backward (hyps : asgn) (goal : formula) {struct goal} : bool :=
  match goal with
    | Atomic n => hyps n
    | Truth => true
    | Falsehood => false
    | And goal1 goal2 => backward hyps goal1 && backward hyps goal2
    | Or goal1 goal2 => backward hyps goal1 || backward hyps goal2
    | Imp hyp goal' => forward hyps hyp (fun hyps' => backward hyps' goal')
  end.

Ltac bool_simpl :=
  repeat (match goal with
	    | [ H : _ |- _ ] =>
	      (generalize (andb_prop _ _ H)
		|| generalize (orb_prop _ _ H));
	      clear H; intro H
	  end
  || apply andb_true_intro
    || apply orb_true_intro).

Ltac simplify := repeat progress (simpl; intuition eauto; bool_simpl).

Hint Extern 1 False => discriminate.

Section prove_sound.
  Variable atomics : nat -> Prop.

  Lemma add_sound : forall (hyps : asgn) (n : nat),
    (forall n' : nat, hyps n' = true -> atomics n')
    -> atomics n
    -> forall n'', add hyps n n'' = true
      -> atomics n''.
    intuition.
    unfold add in H1.
    destruct (eq_nat_dec n'' n); subst; intuition.
  Qed.

  Hint Resolve add_sound.

  Theorem forward_sound : forall (hyp : formula)
    (hyps : nat -> bool)
    (cont : (nat -> bool) -> bool),
    (forall n, hyps n = true -> atomics n)
    -> interp_formula atomics hyp
    -> forward hyps hyp cont = true
    -> exists hyps' : nat -> bool,
      (forall n, hyps' n = true -> atomics n)
      /\ cont hyps' = true.
    induction hyp; simplify; firstorder.
  Qed.

  Theorem backward_sound : forall (goal : formula)
    (hyps : nat -> bool),
    (forall n, hyps n = true -> atomics n)
    -> backward hyps goal = true
    -> interp_formula atomics goal.
    induction goal; simplify;
      generalize forward_sound; firstorder.
  Qed.

  Theorem prover : forall (goal : formula),
    backward (fun _ => false) goal = true
    -> interp_formula atomics goal.
    intros.
    apply (backward_sound goal (fun _ => false));
      simpl; intuition; discriminate.
  Qed.
End prove_sound.

Fixpoint listT_atomics (ps : listT Prop) : nat -> Prop :=
  match ps with
    | nilT => fun _ => True
    | consT P ps' => fun n =>
      match n with
	| O => P
	| S n' => listT_atomics ps' n'
      end
  end.

Theorem test1 : True.
  apply (prover (listT_atomics nilT) Truth).
  reflexivity.
Qed.

Theorem test2 : forall (P : Prop), P -> P.
  intro.
  apply (prover (listT_atomics (consT P nilT)) (Imp (Atomic 0) (Atomic 0))).
  reflexivity.
Qed.

Ltac add_atomic atomics P :=
  match atomics with
    | nilT => constr:(consT P nilT)
    | consT P _ => atomics
    | consT ?Q ?atomics' =>
      let atomics'' := add_atomic atomics' P in
	constr:(consT Q atomics'')
  end.

Ltac enum_atomics' atomics P :=
  match P with
    | True => atomics
    | False => atomics
    | ?Q1 /\ ?Q2 => enum_atomics' ltac:(enum_atomics' atomics Q1) Q2
    | ?Q1 \/ ?Q2 => enum_atomics' ltac:(enum_atomics' atomics Q1) Q2
    | ?Q1 -> ?Q2 => enum_atomics' ltac:(enum_atomics' atomics Q1) Q2
    | _ => add_atomic atomics P
  end.

Ltac enum_atomics := enum_atomics' (@nilT Prop).

Ltac find_atomic atomics P :=
  match atomics with
    | consT P _ => constr:O
    | consT _ ?atomics' =>
      let n := find_atomic atomics' P in
	constr:(S n)
  end.

Ltac formulaify atomics P :=
  match P with
    | True => constr:Truth
    | False => constr:Falsehood
    | ?Q1 /\ ?Q2 =>
      let f1 := formulaify atomics Q1
	with f2 := formulaify atomics Q2 in
	constr:(And f1 f2)
    | ?Q1 \/ ?Q2 =>
      let f1 := formulaify atomics Q1
	with f2 := formulaify atomics Q2 in
	constr:(Or f1 f2)
    | ?Q1 -> ?Q2 =>
      let f1 := formulaify atomics Q1
	with f2 := formulaify atomics Q2 in
	constr:(Imp f1 f2)
    | _ => let n := find_atomic atomics P in
      constr:(Atomic n)
  end.

Ltac prover :=
  match goal with
    | [ |- ?P ] =>
      let atomics := enum_atomics P in
	let f := formulaify atomics P in
	  apply (prover (listT_atomics atomics) f);
	    reflexivity
  end.

Theorem t1 : True.
  prover.
Qed.

Print t1.

Theorem t2 : 1 = 1 -> 1 = 1.
  prover.
Qed.

Print t2.

Theorem t3 : False -> 1 + 1 = 2.
  prover.
Qed.

Print t3.

Theorem t4 : forall x y, x > y -> x > y \/ y > x.
  do 2 intro; prover.
Qed.

Theorem t5 : forall x y z, x > y \/ x > z -> x > z \/ x > y.
  do 3 intro; prover.
Qed.


(** * A quick example using the 'quote' tactic *)

Require Import Quote.

Inductive formula' : Set :=
  | Atomic' : index -> formula'
  | Truth' : formula'
  | Falsehood' : formula'
  | And' : formula' -> formula' -> formula'
  | Or' : formula' -> formula' -> formula'
  | Imp' : formula' -> formula' -> formula'.

Fixpoint interp_formula' (atomics : varmap Prop) (f : formula') {struct f} : Prop :=
  match f with
    | Atomic' v => varmap_find True v atomics
    | Truth' => True
    | Falsehood' => False
    | And' f1 f2 => interp_formula' atomics f1 /\ interp_formula' atomics f2
    | Or' f1 f2 => interp_formula' atomics f1 \/ interp_formula' atomics f2
    | Imp' f1 f2 => interp_formula' atomics f1 -> interp_formula' atomics f2
  end.

Theorem t1' : True.
  quote interp_formula'.
Admitted.

Theorem t2' : True /\ True.
  quote interp_formula'.
Admitted.

Theorem t3' : forall x y, x > y \/ x <= y.
  do 2 intro.
  quote interp_formula'.
Admitted.

Theorem t4' : True -> True.
  quote interp_formula'.
Admitted.
