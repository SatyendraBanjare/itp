Fixpoint le_f (n m : nat) {struct n} : Prop :=
  match n with
    | O => True
    | S n' =>
      match m with
	| O => False
	| S m' => le_f n' m'
      end
  end.

Theorem le_f_transitive : forall n1 n2 n3,
  le_f n1 n2
  -> le_f n2 n3
  -> le_f n1 n3.
  induction n1; simpl; intuition.

  destruct n2; intuition.
  simpl in H0.
  destruct n3; intuition.
  apply IHn1 with n2; assumption.
Qed.

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, le n m -> le n (S m).

Theorem le_transitive : forall n1 n2 n3,
  le n1 n2
  -> le n2 n3
  -> le n1 n3.
  induction 2; intros.

  assumption.

  apply le_S.
  apply IHle.
  assumption.
Qed.

Check le_ind.

Theorem le_transitive_easy : forall n1 n2 n3,
  n1 <= n2
  -> n2 <= n3
  -> n1 <= n3.
  induction 2; intuition.
Qed.

Lemma le_O' : forall n m, n <= m -> m = 0 -> n = 0.
  destruct 1.

  trivial.

  intro.
  discriminate.
Qed.

Theorem le_O : forall n, n <= 0 -> n = 0.
  intros.
  apply le_O' with 0.
  assumption.
  reflexivity.
Qed.

Theorem le_O_easy : forall n, n <= 0 -> n = 0.
  inversion 1; reflexivity.
Qed.


(** * Sorted lists *)

Require Import List.

Inductive sorted : list nat -> Prop :=
  | sorted_nil :
    sorted nil
  | sorted_one : forall n,
    sorted (n :: nil)
  | sorted_cons : forall n m ls,
    n <= m
    -> sorted (m :: ls)
    -> sorted (n :: m :: ls).

Theorem sorted_123 : sorted (1 :: 2 :: 3 :: nil).
  apply sorted_cons.
  auto.
  apply sorted_cons.
  auto.
  apply sorted_one.
Qed.

Theorem sorted_123_easy : sorted (1 :: 2 :: 3 :: nil).
  Hint Constructors sorted.
  auto.
Qed.

Inductive sublist : list nat -> list nat -> Prop :=
  | sub_nil :
    sublist nil nil
  | sub_keep : forall x ls ls',
    sublist ls ls'
    -> sublist (x :: ls) (x :: ls')
  | sub_drop : forall x ls ls',
    sublist ls ls'
    -> sublist (x :: ls) ls'.

Theorem sublist_1234_23 : sublist (1 :: 2 :: 3 :: 4 :: nil) (2 :: 3 :: nil).
  apply sub_drop.
  apply sub_keep.
  apply sub_keep.
  apply sub_drop.
  apply sub_nil.
Qed.

Theorem sublist_1234_23_easy : sublist (1 :: 2 :: 3 :: 4 :: nil) (2 :: 3 :: nil).
  Hint Constructors sublist.
  auto.
Qed.

Lemma sorted_sublist' : forall ls ls',
  sublist ls ls'
  -> sorted ls
  -> match ls, ls' with
       | x :: _, y :: _ => x <= y
       | _, _ => True
     end.
  induction 1; intuition.

  inversion H0; subst.

  inversion H.
  trivial.

  intuition.
  destruct ls'.
  trivial.
  apply le_transitive_easy with m; assumption.
Qed.

Theorem sorted_sublist : forall ls,
  sorted ls
  -> forall ls', sublist ls ls'
    -> sorted ls'.
  induction 1; intuition.

  inversion H.
  apply sorted_nil.

  inversion H; subst.
  inversion H3; subst.
  apply sorted_one.

  inversion H3; subst.
  apply sorted_nil.

  inversion H1; subst.
  destruct ls'0.

  apply sorted_one.

  apply sorted_cons.

  apply le_transitive_easy with m.
  assumption.
  apply (sorted_sublist' (m :: ls) (n0 :: ls'0)).
  assumption.
  assumption.

  apply IHsorted.
  assumption.

  apply IHsorted.
  assumption.
Qed.


(** * An interpreter *)

Definition var := nat.

Inductive exp : Set :=
  | Num : nat -> exp
  | Bool : bool -> exp

  | Var : var -> exp

  | Plus : exp -> exp -> exp
  | Eq : exp -> exp -> exp.

Require Import Arith.
Definition env := var -> exp.

Inductive isValue : exp -> Prop :=
  | ValueNum : forall n, isValue (Num n)
  | ValueBool : forall n, isValue (Bool n).

Inductive eval (G : env) : exp -> exp -> Prop :=
  | EvalValue : forall e, isValue e -> eval G e e
  | EvalVar : forall x, eval G (Var x) (G x)
  | EvalPlus : forall e1 e2 n1 n2,
    eval G e1 (Num n1)
    -> eval G e2 (Num n2)
    -> eval G (Plus e1 e2) (Num (n1 + n2))
  | EvalEq_True : forall e1 e2 n,
    eval G e1 (Num n)
    -> eval G e2 (Num n)
    -> eval G (Eq e1 e2) (Bool true)
  | EvalEq_False : forall e1 e2 n1 n2,
    eval G e1 (Num n1)
    -> eval G e2 (Num n2)
    -> n1 <> n2
    -> eval G (Eq e1 e2) (Bool false).

Inductive type : Set :=
  | TyNum : type
  | TyBool : type.

Section typing.
  Variable Gtypes : var -> type.
  Variable G : env.

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
    | HT_Eq : forall e1 e2,
      hasType e1 TyNum
      -> hasType e2 TyNum
      -> hasType (Eq e1 e2) TyBool.

  Definition Gtyped :=
    (forall x, isValue (G x))
    /\ (forall x,
      hasType (G x) (Gtypes x)).

  Hypothesis G_typed : Gtyped.

  Theorem eval_is_safe : forall e t,
    hasType e t
    -> exists v, eval G e v
      /\ isValue v
      /\ hasType v t.
    unfold Gtyped in G_typed.
    induction 1.

    exists (Num n).
    intuition.
    apply EvalValue.
    apply ValueNum.
    apply ValueNum.
    apply HT_Num.

    exists (Bool b).
    intuition.
    apply EvalValue.
    apply ValueBool.
    apply ValueBool.
    apply HT_Bool.

    exists (G x).
    intuition.
    apply EvalVar.

    firstorder.
    destruct H4.
    destruct H7.
    exists (Num (n + n0)).
    intuition.
    apply EvalPlus; assumption.
    apply ValueNum.
    apply HT_Num.

    inversion H8.
    inversion H5.

    firstorder.
    destruct H4.
    destruct H7.
    destruct (eq_nat_dec n n0).

    subst.
    exists (Bool true).
    intuition.
    apply EvalEq_True with n0; assumption.
    apply ValueBool.
    apply HT_Bool.

    exists (Bool false).
    intuition.
    apply EvalEq_False with n n0; assumption.
    apply ValueBool.
    apply HT_Bool.

    inversion H8.
    inversion H5.
  Qed.

  Hint Constructors isValue eval hasType.

  Lemma eval_Num : forall v,
    isValue v
    -> hasType v TyNum
    -> exists n, v = Num n.
    destruct 1.
    eauto.
    inversion 1.
  Qed.

  Theorem eval_is_safe_easier : forall e t,
    hasType e t
    -> exists v, eval G e v
      /\ isValue v
      /\ hasType v t.
    red in G_typed.
    induction 1; firstorder; eauto.

    generalize (eval_Num x H4 H5).
    generalize (eval_Num x0 H7 H8).
    firstorder; subst; eauto.

    generalize (eval_Num x H4 H5).
    generalize (eval_Num x0 H7 H8).
    firstorder; subst.
    destruct (eq_nat_dec x2 x1); subst; eauto.
  Qed.
End typing.

Inductive cmd : Set :=
  | Skip : cmd
  | Write : var -> exp -> cmd
  | Seq : cmd -> cmd -> cmd
  | If : exp -> cmd -> cmd -> cmd.

Definition bind (G : env) (x : var) (e : exp) :=
  fun (x' : var) =>
    if eq_nat_dec x x'
      then e
      else G x'.

Inductive exec : env -> cmd -> env -> Prop :=
  | ExecSkip : forall G, exec G Skip G

  | ExecWrite : forall G x e v,
    eval G e v
    -> exec G (Write x e) (bind G x v)

  | ExecSeq : forall G c1 c2 G' G'',
    exec G c1 G'
    -> exec G' c2 G''
    -> exec G (Seq c1 c2) G''

  | ExecIf_True : forall G e c1 c2 G',
    eval G e (Bool true)
    -> exec G c1 G'
    -> exec G (If e c1 c2) G'

  | ExecIf_False : forall G e c1 c2 G',
    eval G e (Bool false)
    -> exec G c2 G'
    -> exec G (If e c1 c2) G'.

Section cmd_typing.
  Variable Gtypes : var -> type.

  Inductive valid : cmd -> Prop :=
    | ValidSkip :
      valid Skip

    | ValidWrite : forall x e,
      hasType Gtypes e (Gtypes x)
      -> valid (Write x e)

    | ValidSeq : forall c1 c2,
      valid c1
      -> valid c2
      -> valid (Seq c1 c2)

    | ValidIf : forall e c1 c2,
      hasType Gtypes e TyBool
      -> valid c1
      -> valid c2
      -> valid (If e c1 c2).

  Hint Constructors exec valid.
  
  Hint Unfold Gtyped.

  Lemma eval_Bool : forall v,
    isValue v
    -> hasType Gtypes v TyBool
    -> exists b, v = Bool b.
    destruct 1.
    inversion 1.
    eauto.
  Qed.

  Theorem exec_is_safe: forall c,
    valid c
    -> forall G, Gtyped Gtypes G
      -> exists G', exec G c G'
	/\ Gtyped Gtypes G'.
    induction 1; intros.

    exists G; intuition.

    destruct (eval_is_safe Gtypes G H0 e (Gtypes x) H); intuition.
    exists (bind G x x0); intuition.
    red in H0.
    split; intros; unfold bind;
      destruct (eq_nat_dec x x1); subst; intuition.

    destruct (IHvalid1 _ H1); intuition.
    destruct (IHvalid2 _ H4); intuition.
    eauto.

    destruct (eval_is_safe Gtypes G H2 e TyBool H); intuition.
    destruct (eval_Bool x H3 H6); subst.
    destruct x0.

    destruct (IHvalid1 _ H2); intuition; eauto.
    destruct (IHvalid2 _ H2); intuition; eauto.
  Qed.

End cmd_typing.
