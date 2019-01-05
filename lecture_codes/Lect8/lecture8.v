Require Import List Specif TheoryList.

Set Implicit Arguments.

Ltac magic_solver := repeat progress (simpl; intuition eauto; subst).

Section sumbool.
  Variables A1 B1 A2 B2 : Prop.

  Definition sumbool_and (b1 : {A1} + {B1}) (b2 : {A2} + {B2})
    : {A1 /\ A2} + {B1 \/ B2}.
    intros.
    refine (if b1
      then if b2
	then left _ _
	else right _ _
      else right _ _); tauto.
  Defined.

  Definition sumbool_or (b1 : {A1} + {B1}) (b2 : {A2} + {B2})
    : {A1 \/ A2} + {B1 /\ B2}.
    intros.
    refine (if b1
      then left _ _
      else if b2
	then left _ _
	else right _ _); magic_solver.
  Defined.

  Definition reduce : (A1 -> A2) -> (B1 -> B2)
    -> {A1} + {B1} -> {A2} + {B2}.
    destruct 3; auto.
  Defined.
End sumbool.

About sumbool_and.
About sumbool_or.

Infix "&&" := sumbool_and (left associativity, at level 50).
Infix "||" := sumbool_or (left associativity, at level 51).

Notation "'Yes'" := (left _ _).
Notation "'No'" := (right _ _).

About reduce.

Notation "'Reduce'" := (reduce _ _).

Hint Extern 1 False => discriminate.

Definition nat_eq_dec : forall (x y : nat), {x = y} + {x <> y}.
  refine (fix nat_eq_dec (x y : nat) {struct x} : {x = y} + {x <> y} :=
    match x return {x = y} + {x <> y} with
      | O =>
	match y return {O = y} + {O <> y} with
	  | O => Yes
	  | S _ => No
	end
      | S x' =>
	match y return {S x' = y} + {S x' <> y} with
	  | O => No
	  | S y' => Reduce (nat_eq_dec x' y')
	end
    end); magic_solver.
Defined.

Hint Extern 2 (_ = _) => congruence.

Definition list_nat_eq_dec : forall (x y : list nat), {x = y} + {x <> y}.
  refine (fix list_nat_eq_dec (x y : list nat) {struct x} : {x = y} + {x <> y} :=
    match x return {x = y} + {x <> y} with
      | nil =>
	match y return {nil = y} + {nil <> y} with
	  | nil => Yes
	  | _ :: _ => No
	end
      | hx :: tx =>
	match y return {hx :: tx = y} + {hx :: tx <> y} with
	  | nil => No
	  | hy :: ty => Reduce (nat_eq_dec hx hy && list_nat_eq_dec tx ty)
	end
    end); magic_solver.
Defined.

Hint Extern 2 False =>
  match goal with
    | [ H : In _ (_ :: _) |- _ ] => inversion H; clear H; subst
  end.

Definition list_nat_In_dec : forall (n : nat) (ls : list nat), {In n ls} + {~In n ls}.
  refine (fix list_nat_In_dec (n : nat) (ls : list nat) {struct ls} : {In n ls} + {~In n ls} :=
    match ls return {In n ls} + {~In n ls} with
      | nil => No
      | n' :: ls' => Reduce (nat_eq_dec n n' || list_nat_In_dec n ls')
    end); magic_solver.
Defined.

Section sumor_and.
  Variables A1 A2 : Set.
  Variable P1 : A1 -> Prop.
  Variable P2 : A2 -> Prop.
  Variables Q1 Q2 : Prop.

  Definition sumor_and (b1 : sig P1 + {Q1}) (b2 : sig P2 + {Q2})
    : {x : A1 * A2 | P1 (fst x) /\ P2 (snd x)} + {Q1 \/ Q2}.
    intros.
    refine (match b1 with
	      | inleft (exist x1 _) =>
		match b2 with
		  | inleft (exist x2 _) => inleft _ (exist _ (x1, x2) _)
		  | inright _ => inright _ _
		end
	      | inright _ => inright _ _
	    end); magic_solver.
  Defined.
End sumor_and.

Section sumor_or.
  Variable A : Set.
  Variables P1 P2 : A -> Prop.
  Variables Q1 Q2 : Prop.

  Definition sumor_or (b1 : sig P1 + {Q1}) (b2 : sig P2 + {Q2})
    : {x : A | P1 x \/ P2 x} + {Q1 /\ Q2}.
    intros.
    refine (match b1 with
	      | inleft (exist x _) => inleft _ (exist _ x _)
	      | inright _ =>
		match b2 with
		  | inleft (exist x _) => inleft _ (exist _ x _)
		  | inright _ => inright _ _
		end
	    end); magic_solver.
  Defined.

  Definition reduceSumor : (forall x, P1 x -> P2 x) -> (Q1 -> Q2)
    -> sig P1 + {Q1} -> sig P2 + {Q2}.
    intros H1 H2 s.
    refine (match s with
	      | inleft (exist x _) => inleft _ (exist _ x _)
	      | inright _ => inright _ _
	    end); auto.
  Defined.
End sumor_or.

Infix "&&&" := sumor_and (left associativity, at level 50).
Infix "|||" := sumor_or (left associativity, at level 51).

Section sumor_consider.
  Variable A : Set.
  Variable P1 P2 : Prop.
  Variable P3 : A -> Prop.

  Definition consider : forall (x : A), (P1 -> P3 x)
    -> {P1} + {P2}
    -> sig P3 + {P2}.
    intros x H s.
    refine (if s
      then inleft _ (exist _ x _)
      else inright _ _); magic_solver.
  Defined.
End sumor_consider.

Notation "'This' x" := (inleft _ (exist _ x _)) (at level 30).
Notation "'Nobody'" := (inright _ _).
Notation "'Use'" := (reduceSumor _ _ _).
Notation "'Consider' x 'for' p 'when' y" := (consider p x _ y) (at level 30).

Definition assoc : forall (x : nat) (ls : list (nat * nat)),
  {y : nat | In (x, y) ls} + {forall y, ~In (x, y) ls}.
  refine (fix assoc (x : nat) (ls : list (nat * nat)) {struct ls}
    : {y : nat | In (x, y) ls} + {forall y, ~In (x, y) ls} :=
    match ls return {y : nat | In (x, y) ls} + {forall y, ~In (x, y) ls} with
      | nil => Nobody
      | (x', y) :: ls' =>
	Use (Consider y for (fun y' => In (x, y') ((x', y) :: ls')) when nat_eq_dec x x'
	  ||| assoc x ls')
    end); magic_solver.
Defined.

Section sumbool_monad.
  Variables P1 P2 Q1 Q2 : Prop.

  Definition sumbool_bind : {P1} + {P2}
    -> (P1 -> {Q1} + {Q2})
    -> (P2 -> Q2)
    -> {Q1} + {Q2}.
    destruct 1; eauto.
  Defined.
End sumbool_monad.

About sumbool_bind.

Notation "pf <-- m1 ; m2" := (sumbool_bind m1 (fun pf => m2) _)
  (right associativity, at level 30).

Hint Extern 1 False =>
  match goal with
    | [ H : AllS _ (_ :: _) |- _ ] => inversion H; clear H; subst
  end.

Section AllS_dec.
  Variable A : Set.
  Variable P : A -> Prop.
  Variable P_dec : forall (x : A), {P x} + {~P x}.

  Definition AllS_dec : forall (ls : list A), {AllS P ls} + {~AllS P ls}.
    refine (fix AllS_dec (ls : list A) : {AllS P ls} + {~AllS P ls} :=
      match ls return {AllS P ls} + {~AllS P ls} with
	| nil => Yes
	| x :: ls' =>
	  Hx <-- P_dec x;
  	  Hls' <-- AllS_dec ls';
	  Yes
      end); intuition.
  Defined.
End AllS_dec.

Section sumor_monad.
  Variables A1 A2 : Set.
  Variable P1 : A1 -> Prop.
  Variable P2 : A2 -> Prop.
  Variables Q1 Q2 : Prop.

  Definition sumor_bind : sig P1 + {Q1}
    -> (forall (x : A1), P1 x -> sig P2 + {Q2})
    -> (Q1 -> Q2)
    -> sig P2 + {Q2}.
    destruct 1; eauto.
    destruct s; eauto.
  Defined.
End sumor_monad.

Section sumbool_monad_sumor.
  Variables P1 P2 Q2 : Prop.
  Variable Q1 : Set.

  Definition sumbool_bind_sumor : {P1} + {P2}
    -> (P1 -> Q1 + {Q2})
    -> (P2 -> Q2)
    -> Q1 + {Q2}.
    destruct 1; eauto.
  Defined.
End sumbool_monad_sumor.

About sumor_bind.
About sumbool_bind_sumor.

Notation "x 'by' pf <- m1 ; m2" := (sumor_bind m1 (fun x pf => m2) _)
  (right associativity, at level 30).
Notation "pf <-- m1 ;; m2" := (sumbool_bind_sumor m1 (fun pf => m2) _)
  (right associativity, at level 30).

Inductive ty : Set :=
  | Nat : ty
  | Bool : ty.

Inductive exp : Set :=
  | Const : nat -> exp
  | Plus : exp -> exp -> exp
  | BConst : bool -> exp
  | Eq : exp -> exp -> exp.

Inductive hasType : exp -> ty -> Prop :=
  | HT_Const : forall n,
    hasType (Const n) Nat
  | HT_Plus : forall e1 e2,
    hasType e1 Nat
    -> hasType e2 Nat
    -> hasType (Plus e1 e2) Nat
  | HT_BConst : forall b,
    hasType (BConst b) Bool
  | HT_Eq : forall e1 e2,
    hasType e1 Nat
    -> hasType e2 Nat
    -> hasType (Eq e1 e2) Bool.

Hint Constructors hasType.

Ltac ics H := inversion H; clear H; subst.

Ltac my_inversion :=
  match goal with
    | [ H : hasType (Const _) _ |- _ ] => ics H
    | [ H : hasType (Plus _ _) _ |- _ ] => ics H
    | [ H : hasType (BConst _) _ |- _ ] => ics H
    | [ H : hasType (Eq _ _) _ |- _ ] => ics H
  end.

Hint Extern 1 (_ = _) => repeat my_inversion.
Hint Extern 1 False => repeat my_inversion.

Definition ty_eq_dec : forall (t1 t2 : ty), {t1 = t2} + {t1 <> t2}.
  decide equality.
Defined.

Theorem hasType_unique : forall e t1,
  hasType e t1
  -> forall t2, hasType e t2
    -> t1 = t2.
  induction 1; magic_solver.
Qed.

Hint Resolve hasType_unique.

Definition hasType_dec : forall (e : exp),
  {t : ty | hasType e t} + {forall t, ~hasType e t}.
  refine (fix hasType_dec (e : exp)
    : {t : ty | hasType e t} + {forall t, ~hasType e t} :=
    match e return {t : ty | hasType e t} + {forall t, ~hasType e t} with
      | Const _ => This Nat
      | Plus e1 e2 =>
	t1 by Ht1 <- hasType_dec e1;
        Heq1 <-- ty_eq_dec t1 Nat;;
        t2 by Ht2 <- hasType_dec e2;
        Heq2 <-- ty_eq_dec t2 Nat;;
        This Nat
      | BConst _ => This Bool
      | Eq e1 e2 =>
	t1 by Ht1 <- hasType_dec e1;
        Heq1 <-- ty_eq_dec t1 Nat;;
        t2 by Ht2 <- hasType_dec e2;
        Heq2 <-- ty_eq_dec t2 Nat;;
        This Bool
    end); clear hasType_dec; magic_solver.
Defined.

Recursive Extraction hasType_dec.
