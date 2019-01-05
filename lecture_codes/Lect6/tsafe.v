Require Import Arith List TheoryList.

Definition var := nat.

Inductive exp : Set :=
  | Num : nat -> exp
  | Bool : bool -> exp

  | Var : var -> exp

  | Plus : exp -> exp -> exp
  | Minus : exp -> exp -> exp

  | Eq : exp -> exp -> exp.

Definition env := var -> exp.

Inductive isValue : exp -> Prop :=
  | ValueNum : forall n, isValue (Num n)
  | ValueBool : forall n, isValue (Bool n).

Definition nat_eq n1 n2 :=
  if eq_nat_dec n1 n2
    then true
    else false.

Inductive step (G : env) : exp -> exp -> Prop :=
  | StepVar : forall x, step G (Var x) (G x)

  | StepPlus : forall n1 n2,
    step G (Plus (Num n1) (Num n2)) (Num (n1 + n2))
  | StepPlus1 : forall e1 e2 e1',
    step G e1 e1'
    -> step G (Plus e1 e2) (Plus e1' e2)
  | StepPlus2 : forall e1 e2 e2',
    isValue e1
    -> step G e2 e2'
    -> step G (Plus e1 e2) (Plus e1 e2')

  | StepMinus : forall n1 n2,
    step G (Minus (Num n1) (Num n2)) (Num (n1 - n2))
  | StepMinus1 : forall e1 e2 e1',
    step G e1 e1'
    -> step G (Minus e1 e2) (Minus e1' e2)
  | StepMinus2 : forall e1 e2 e2',
    isValue e1
    -> step G e2 e2'
    -> step G (Minus e1 e2) (Minus e1 e2')

  | StepEq_False : forall n1 n2,
    step G (Eq (Num n1) (Num n2)) (Bool (nat_eq n1 n2))
  | StepEq1 : forall e1 e2 e1',
    step G e1 e1'
    -> step G (Eq e1 e2) (Eq e1' e2)
  | StepEq2 : forall e1 e2 e2',
    isValue e1
    -> step G e2 e2'
    -> step G (Eq e1 e2) (Eq e1 e2').

Inductive type : Set :=
  | TyNum : type
  | TyBool : type.

Section typing.
  Variable Gtypes : var -> type.

  Inductive hasType : exp -> type -> Prop :=
    | HT_Num : forall n,
      hasType (Num n) TyNum
    | HT_Bool : forall b,
      hasType (Bool b) TyBool

    | HT_Var : forall x,
      hasType (Var x) (Gtypes x)

    | HT_Plus : forall e1 e2,
      hasType e1 TyNum
      -> hasType e2 TyNum
      -> hasType (Plus e1 e2) TyNum
    | HT_Minus : forall e1 e2,
      hasType e1 TyNum
      -> hasType e2 TyNum
      -> hasType (Minus e1 e2) TyNum
    | HT_Eq : forall e1 e2,
      hasType e1 TyNum
      -> hasType e2 TyNum
      -> hasType (Eq e1 e2) TyBool.

  Variable G : env.

  Hypothesis vars_values : forall x, isValue (G x).
  Hypothesis vars_typed : forall x, hasType (G x) (Gtypes x).

  Hint Constructors hasType isValue step.

  Ltac ics H := inversion H; clear H; subst.

  Ltac my_inversion :=
    match goal with
      | [ H : isValue (Var _) |- _ ] => inversion H
      | [ H : isValue (Plus _ _) |- _ ] => inversion H
      | [ H : isValue (Minus _ _) |- _ ] => inversion H
      | [ H : isValue (Eq _ _) |- _ ] => inversion H

      | [ H : hasType (Num _) _ |- _ ] => ics H
      | [ H : hasType (Bool _) _ |- _ ] => ics H
      | [ H : hasType (Var _) _ |- _ ] => ics H
      | [ H : hasType (Plus _ _) _ |- _ ] => ics H
      | [ H : hasType (Minus _ _) _ |- _ ] => ics H
      | [ H : hasType (Eq _ _) _ |- _ ] => ics H

      | [ H : hasType _ TyNum |- _ ] => ics H
      | [ H : hasType _ TyBool |- _ ] => ics H
    end.

  Ltac magic_solver := firstorder; repeat (eauto; my_inversion).

  Theorem progress : forall e t,
    hasType e t
    -> isValue e
    \/ exists e', step G e e'.
    induction 1; magic_solver.
  Qed.

  Theorem preservation : forall e e',
    step G e e'
    -> forall t, hasType e t
      -> hasType e' t.
    induction 1; magic_solver.
  Qed.
End typing.
