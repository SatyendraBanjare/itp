Require Import Arith List.

Set Implicit Arguments.


(** * A simple expression language and its semantics, the old-fashioned way *)

Inductive exp1 : Set :=
  | Num1 : nat -> exp1
  | Bool1 : bool -> exp1
  | Plus1 : exp1 -> exp1 -> exp1
  | Eq1 : exp1 -> exp1 -> exp1.

Definition eq_nat n1 n2 :=
  if eq_nat_dec n1 n2
    then true
    else false.

Inductive run_exp1 : exp1 -> exp1 -> Prop :=
  | RunNum1 : forall n,
    run_exp1 (Num1 n) (Num1 n)
  | RunBool1 : forall b,
    run_exp1 (Bool1 b) (Bool1 b)
  | RunPlus1 : forall e1 e2 n1 n2,
    run_exp1 e1 (Num1 n1)
    -> run_exp1 e2 (Num1 n2)
    -> run_exp1 (Plus1 e1 e2) (Num1 (n1 + n2))
  | RunEq1 : forall e1 e2 n1 n2,
    run_exp1 e1 (Num1 n1)
    -> run_exp1 e2 (Num1 n2)
    -> run_exp1 (Eq1 e1 e2) (Bool1 (eq_nat n1 n2)).

Inductive type1 : Set :=
  | TyNum1 : type1
  | TyBool1 : type1.

Inductive hasType1 : exp1 -> type1 -> Prop :=
  | HT_Num1 : forall n,
    hasType1 (Num1 n) TyNum1
  | HT_Bool1 : forall b,
    hasType1 (Bool1 b) TyBool1
  | HT_Plus1 : forall e1 e2,
    hasType1 e1 TyNum1
    -> hasType1 e2 TyNum1
    -> hasType1 (Plus1 e1 e2) TyNum1
  | HT_Eq1 : forall e1 e2,
    hasType1 e1 TyNum1
    -> hasType1 e2 TyNum1
    -> hasType1 (Eq1 e1 e2) TyBool1.


Hint Constructors run_exp1.

Inductive valueOf1 : exp1 -> type1 -> Prop :=
  | VO_Num1 : forall n, valueOf1 (Num1 n) TyNum1
  | VO_Bool1 : forall b, valueOf1 (Bool1 b) TyBool1.

Hint Constructors valueOf1.

Ltac ics H := inversion H; clear H; subst.

Ltac inverter1 :=
  match goal with
    | [ H : run_exp1 (Num1 _) _ |- _ ] => ics H
    | [ H : run_exp1 (Bool1 _) _ |- _ ] => ics H
    | [ H : run_exp1 (Plus1 _ _) _ |- _ ] => ics H
    | [ H : run_exp1 (Eq1 _ _) _ |- _ ] => ics H
  end.

Ltac magic_solver1 := repeat progress (firstorder eauto; repeat inverter1).

Theorem run_exp1_preserves : forall (e : exp1) (t : type1),
  hasType1 e t
  -> forall e', run_exp1 e e'
    -> valueOf1 e' t.
  induction 1; magic_solver1.
Qed.

Ltac use_preserves1 :=
  match goal with
    | [ H1 : hasType1 ?e1 _, H2 : run_exp1 ?e1 _ |- _ ] =>
      generalize (run_exp1_preserves H1 H2); clear H1; intro H1
  end.

Ltac inverter1' :=
  match goal with
    | [ H : valueOf1 _ TyNum1 |- _ ] => ics H
    | [ H : valueOf1 _ TyBool1 |- _ ] => ics H
  end.

Ltac magic_solver1' := repeat progress (magic_solver1; repeat use_preserves1; repeat inverter1').

Theorem run_exp1_terminates : forall (e : exp1) (t : type1),
  hasType1 e t
  -> exists e', run_exp1 e e'.
  induction 1; magic_solver1'.
Qed.

(** ** Let's start some running examples: *)

Hint Constructors hasType1.

Definition one : exp1 := Num1 1.

Theorem one_type : hasType1 one TyNum1.
  unfold one; auto.
Qed.

Print one_type.

Theorem one_result1 : run_exp1 one one.
  unfold one; auto.
Qed.

Print one_result1.

Definition zero : exp1 := Num1 0.
Definition test : exp1 := Eq1 (Plus1 one zero) (Plus1 zero one).

Theorem test_type : hasType1 test TyBool1.
  unfold test, zero, one; auto.
Qed.

Print test_type.

Theorem test_result1 : run_exp1 test (Bool1 true).
  unfold test, zero, one.
  change true with (eq_nat (1 + 0) (0 + 1)); auto.
Qed.

Print test_result1.


(** * Now let's try using a function instead of a relation.... *)

Inductive value2 : Set :=
  | VNum2 : nat -> value2
  | VBool2 : bool -> value2.

Fixpoint run_exp2 (e : exp1) : option value2 :=
  match e with
    | Num1 n => Some (VNum2 n)
    | Bool1 b => Some (VBool2 b)
    | Plus1 e1 e2 =>
      match run_exp2 e1, run_exp2 e2 with
	| Some (VNum2 n1), Some (VNum2 n2) =>
	  Some (VNum2 (n1 + n2))
	| _, _ => None
      end
    | Eq1 e1 e2 =>
      match run_exp2 e1, run_exp2 e2 with
	| Some (VNum2 n1), Some (VNum2 n2) =>
	  Some (VBool2 (eq_nat n1 n2))
	| _, _ => None
      end
  end.

Inductive valueOf2 : value2 -> type1 -> Prop :=
  | VO_Num2 : forall n, valueOf2 (VNum2 n) TyNum1
  | VO_Bool2 : forall b, valueOf2 (VBool2 b) TyBool1.

Hint Constructors valueOf2.

Ltac inverter2 :=
  match goal with
    | [ H : hasType1 (Num1 _) _ |- _ ] => ics H
    | [ H : hasType1 (Bool1 _) _ |- _ ] => ics H
    | [ H : hasType1 (Plus1 _ _) _ |- _ ] => ics H
    | [ H : hasType1 (Eq1 _ _) _ |- _ ] => ics H
  end.

Ltac magic_solver2 := repeat progress (simpl in *; subst; firstorder eauto; repeat inverter2).

Theorem run_exp2_preserves : forall (e : exp1) (t : type1),
  hasType1 e t
  -> match run_exp2 e with
       | None => True
       | Some v => valueOf2 v t
     end.
  intros until e;
    functional induction run_exp2 e;
      magic_solver2.
Qed.

Ltac use_preserves2 :=
  match goal with
    | [ H1 : hasType1 ?e1 _ |- _ ] =>
      generalize (run_exp2_preserves H1); clear H1
  end.

Ltac rewriter :=
  match goal with
    | [ H : _ |- _ ] => rewrite H
  end.

Ltac inverter2' :=
  match goal with
    | [ H : valueOf2 _ TyNum1 |- _ ] => ics H
    | [ H : valueOf2 _ TyBool1 |- _ ] => ics H
  end.

Ltac magic_solver2' := repeat progress (magic_solver2; repeat use_preserves2; repeat rewriter; repeat inverter2').

Theorem run_exp2_terminates : forall (e : exp1) (t : type1),
  hasType1 e t
  -> exists v, run_exp2 e = Some v.
  induction 1; magic_solver2'.
Qed.


(** ** Back to our running examples.... *)

Theorem one_result2 : run_exp2 one = Some (VNum2 1).
  reflexivity.
Qed.

Print one_result2.

Theorem test_result2 : run_exp2 test = Some (VBool2 true).
  reflexivity.
Qed.

Print test_result2.


(** * Time to wheel in the dependent types! *)

Definition value3 (t : type1) : Set :=
  match t with
    | TyNum1 => nat
    | TyBool1 => bool
  end.

Definition run_exp3 : forall (e : exp1) (t : type1), hasType1 e t -> value3 t.
  refine (fix run_exp3 (e : exp1) (t : type1) {struct e} : hasType1 e t -> value3 t :=
    match e return (hasType1 e t -> value3 t) with
      | Num1 n =>
	match t return (hasType1 (Num1 n) t -> value3 t) with
	  | TyNum1 => fun _ => n
	  | _ => fun pf => False_rec _ _
	end
      | Bool1 b =>
	match t return (hasType1 (Bool1 b) t -> value3 t) with
	  | TyBool1 => fun _ => b
	  | _ => fun pf => False_rec _ _
	end
      | Plus1 e1 e2 =>
	match t return (hasType1 (Plus1 e1 e2) t -> value3 t) with
	  | TyNum1 => fun pf => run_exp3 e1 TyNum1 _ + run_exp3 e2 TyNum1 _
	  | _ => fun pf => False_rec _ _
	end
      | Eq1 e1 e2 =>
	match t return (hasType1 (Eq1 e1 e2) t -> value3 t) with
	  | TyBool1 => fun pf => eq_nat (run_exp3 e1 TyNum1 _) (run_exp3 e2 TyNum1 _)
	  | _ => fun pf => False_rec _ _
	end
    end); magic_solver2.
Defined.


(** ** And the running examples: *)

Theorem one_result3 : run_exp3 one_type = 1.
  reflexivity.
Qed.

Print one_result3.

Theorem test_result3 : run_exp3 test_type = true.
  reflexivity.
Qed.

Print test_result3.


(** * Finally, the slickest formalization of this language :-) *)

Inductive exp4 : type1 -> Set :=
  | Num4 : nat -> exp4 TyNum1
  | Bool4 : bool -> exp4 TyBool1
  | Plus4 : exp4 TyNum1 -> exp4 TyNum1 -> exp4 TyNum1
  | Eq4 : exp4 TyNum1 -> exp4 TyNum1 -> exp4 TyBool1.

Fixpoint run_exp4 (t : type1) (e : exp4 t) {struct e} : value3 t :=
  match e in (exp4 t) return (value3 t) with
    | Num4 n => n
    | Bool4 b => b
    | Plus4 e1 e2 => run_exp4 e1 + run_exp4 e2
    | Eq4 e1 e2 => eq_nat (run_exp4 e1) (run_exp4 e2)
  end.


(** ** And the running examples: *)

Definition one4 : exp4 TyNum1 := Num4 1.

Theorem one_result4 : run_exp4 one4 = 1.
  reflexivity.
Qed.

Print one_result4.

Definition zero4 : exp4 TyNum1 := Num4 0.
Definition test4 : exp4 TyBool1 := Eq4 (Plus4 one4 zero4) (Plus4 zero4 one4).

Theorem test_result4 : run_exp4 test4 = true.
  reflexivity.
Qed.

Print test_result4.


(** * Now it's time for some lambda calculus. *)

Require Import LambdaTamer.LambdaTamer.
(** I haven't released this library yet.  If you want to run this code yourself,
  * e-mail me.... *)

Inductive ty : Set :=
  | Nat : ty
  | Arrow : ty -> ty -> ty.

Inductive term : list ty -> ty -> Set :=
  | Const : forall (G : list ty),
    nat
    -> term G Nat

  | EVar : forall (G : list ty) (t : ty),
    Var G t
    -> term G t
  | App : forall (G : list ty) (dom ran : ty),
    term G (Arrow dom ran)
    -> term G dom
    -> term G ran
  | Lam : forall (G : list ty) (dom ran : ty),
    term (dom :: G) ran
    -> term G (Arrow dom ran).

Fixpoint tyDenote (t : ty) : Set :=
  match t with
    | Nat => nat
    | Arrow t1 t2 => tyDenote t1 -> tyDenote t2
  end.

Fixpoint termDenote (G : list ty) (t : ty) (e : term G t) {struct e}
  : Subst tyDenote G -> tyDenote t :=
  match e in (term G t) return (Subst tyDenote G -> tyDenote t) with
    | Const _ n => fun _ => n
    | EVar _ _ x => fun s => VarDenote x s
    | App _ _ _ e1 e2 => fun s => (termDenote e1 s) (termDenote e2 s)
    | Lam _ _ _ e' => fun s => fun x => termDenote e' (SCons _ x s)
  end.


(** ** Some examples *)

Definition two : term nil Nat := Const _ 2.

Definition id : term nil (Arrow Nat Nat) := Lam (EVar (First _ _)).

Definition app_id : term nil Nat := App id two.

Eval compute in termDenote app_id (SNil _).


Definition call : term nil (Arrow (Arrow Nat Nat) (Arrow Nat Nat)) :=
  Lam (Lam (App (EVar (Next _ (First _ _))) (EVar (First _ _)))).

Eval compute in termDenote (App (App call id) two) (SNil _).


(** * A tiny compiler and its correctness proof *)

Inductive let_term : list ty -> ty -> Set :=
  | LConst : forall (G : list ty),
    nat
    -> let_term G Nat

  | LVar : forall (G : list ty) (t : ty),
    Var G t
    -> let_term G t
  | LApp : forall (G : list ty) (dom ran : ty),
    let_term G (Arrow dom ran)
    -> let_term G dom
    -> let_term G ran
  | LLam : forall (G : list ty) (dom ran : ty),
    let_term (dom :: G) ran
    -> let_term G (Arrow dom ran)

  | LLet : forall (G : list ty) (bound body : ty),
    let_term G bound
    -> let_term (bound :: G) body
    -> let_term G body.

Fixpoint let_termDenote (G : list ty) (t : ty) (e : let_term G t) {struct e}
  : Subst tyDenote G -> tyDenote t :=
  match e in (let_term G t) return (Subst tyDenote G -> tyDenote t) with
    | LConst _ n => fun _ => n
    | LVar _ _ x => fun s => VarDenote x s
    | LApp _ _ _ e1 e2 => fun s => (let_termDenote e1 s) (let_termDenote e2 s)
    | LLam _ _ _ e' => fun s => fun x => let_termDenote e' (SCons _ x s)

    | LLet _ _ _ e1 e2 => fun s => let_termDenote e2 (SCons _ (let_termDenote e1 s) s)
  end.

Fixpoint compiler (G : list ty) (t : ty) (e : let_term G t) {struct e} : term G t :=
  match e in (let_term G t) return (term G t) with
    | LConst _ n => Const _ n
    | LVar _ _ x => EVar x
    | LApp _ _ _ e1 e2 => App (compiler e1) (compiler e2)
    | LLam _ _ _ e' => Lam (compiler e')

    | LLet _ _ _ e1 e2 => App (Lam (compiler e2)) (compiler e1)
  end.

Check ext_eqT.

Theorem compiler_correct : forall G t (e : let_term G t),
  termDenote (compiler e) = let_termDenote e.
  induction e; simpl; intuition; repeat (apply ext_eqT; intro);
    repeat rewriter; trivial.
Qed.

