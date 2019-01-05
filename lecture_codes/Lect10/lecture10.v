Require Import List Omega.


(** * Programming with Ltac *)

Ltac add x y k :=
  match x with
    | O => k y
    | S ?X => add X y ltac:(fun r => k (S r))
  end.

Lemma add_test : exists n, 23 + 42 = n.
  add 23 42 ltac:(fun r => exists r).
  reflexivity.
Qed.

Ltac map f ls k :=
  match ls with
    | @nil ?A => k (@nil A)
    | ?head :: ?rest => f head ltac:(fun head' => map f rest ltac:(fun ls' => k (head' :: ls')))
  end.

Lemma map_test : exists ls, map (fun x => 2 + x) (1 :: 2 :: 3 :: nil) = ls.
  map ltac:(add 2) (1 :: 2 :: 3 :: nil) ltac:(fun r => exists r).
  reflexivity.
Qed.


(** * Parsing *)

Inductive Token : Set :=
  | TNat : nat -> Token
  | TPlus : Token
  | TLParen : Token
  | TRParen : Token
  | TSkip : Token
  | TIf : Token
  | TThen : Token
  | TElse : Token.

Inductive Expr : Set :=
  | Nat : nat -> Expr
  | Plus : Expr -> Expr -> Expr.

Ltac term toks k :=
  match toks with
    | TNat ?N :: ?REST => k (Nat N) REST
    | TLParen :: ?REST =>
      exp REST ltac:(fun ans rest =>
	match rest with
	  | TRParen :: ?REST2 => k ans REST2
	end)
  end

  with exp toks k :=
  term toks ltac:(fun ans1 rest1 =>
    match rest1 with
      | TPlus :: ?REST => exp REST ltac:(fun ans2 rest2 => k (Plus ans1 ans2) rest2)
      | _ => k ans1 rest1
    end).

Ltac parse toks :=
  exp toks ltac:(fun ans rest =>
    match rest with
      | nil => pose ans
    end).

Theorem parsing_playground : True.
  parse (TNat 1 :: nil).
  parse (TLParen :: TNat 1 :: TRParen :: nil).
  parse (TNat 1 :: TPlus :: TNat 2 :: nil).
  parse (TNat 1 :: TPlus :: TNat 2 :: TPlus :: TNat 3 :: nil).
  info parse (TLParen :: TNat 1 :: TPlus :: TNat 2 :: TRParen :: TPlus :: TNat 3 :: nil).
Abort.

Inductive Prog : Set :=
  | Skip 
  | IfThen : Expr -> Prog -> Prog
  | IfThenElse : Expr -> Prog -> Prog -> Prog.

Ltac prog toks k :=
  match toks with
    | TSkip :: ?REST => k Skip REST
    | TIf :: ?REST1 =>
      exp REST1 ltac:(fun ans1 rest1 =>
	match rest1 with
	  | TThen :: ?REST2 => prog REST2 ltac:(fun ans2 rest2 =>
	    match goal with
	      | _ => k (IfThen ans1 ans2) rest2
	      | _ =>
		match rest2 with
		  | TElse :: ?REST3 =>
		    prog REST3 ltac:(fun ans3 rest3 => k (IfThenElse ans1 ans2 ans3) rest3)
		end
	    end)
	end)
    | TLParen :: ?REST =>
      prog REST ltac:(fun ans rest =>
	match rest with
	  | TRParen :: ?REST2 => k ans REST2
	end)
  end.

Ltac parseProg toks :=
  prog toks ltac:(fun ans rest =>
    match rest with
      | nil => pose ans
    end).

Theorem parsing_playground2 : True.
  parseProg (TSkip :: nil).
  parseProg (TIf :: TNat 0 :: TThen :: TSkip :: nil).
  parseProg (TIf :: TNat 0 :: TThen :: TSkip :: TElse :: TSkip :: nil).
  parseProg (TIf :: TNat 0 :: TThen :: TIf :: TNat 1 :: TThen :: TSkip :: TElse :: TSkip :: nil).
  parseProg (TIf :: TNat 0 :: TThen :: TLParen :: TIf :: TNat 1 :: TThen :: TSkip :: TElse :: TSkip :: TRParen :: nil).
Abort.


(** * Brute-force search with Ltac *)

Ltac equation_solver' eqn n k :=
  (let t := type of (refl_equal _ : eqn n) in
    k n)
  || equation_solver' eqn (S n) k.

Ltac equation_solver :=
  match goal with
    | [ |- ex ?EQN ] => equation_solver' EQN O ltac:(fun r => exists r); reflexivity
  end.

Lemma equation_test1 : exists x, x + x * x = x.
  equation_solver.
Qed.

Lemma equation_test2 : exists x, x * x = 25.
  equation_solver.
Qed.

Lemma equation_test3 : exists x, x * x + x * x * x - x = 33.
  equation_solver.
Qed.

Ltac tryAll choices success :=
  match choices with
    | ?choice :: ?choices' =>
      success choice
      || tryAll choices' success
  end.

Ltac searcher children success state :=
  (let T := type of state in
    success (@nil T) state)
  || let ch := eval compute in (children state) in
    tryAll ch ltac:(fun state' => searcher children ltac:(fun history state'' => success (state :: history) state'') state').

Definition graph (n : nat) : list nat :=
  match n with
    | 0 => 2 :: 5 :: nil
    | 1 => 3 :: nil
    | 2 => 4 :: nil
    | 3 => 6 :: nil
    | 4 => 7 :: nil
    | 5 => 1 :: 2 :: nil
    | 6 => nil
    | 7 => 8 :: 9 :: nil
    | _ => nil
  end.

Theorem graph_playground : True.
  searcher graph ltac:(fun history state =>
    match state with
      | 6 => pose history
    end) 0.
Abort.

Ltac searcher' children success state :=
  (let T := type of state in
    success (@nil T) state)
  || children state ltac:(fun state' => searcher' children ltac:(fun history state'' => success (state :: history) state'') state').

Lemma equation_test3' : exists x, x * x + x * x * x - x = 33.
  searcher'
  ltac:(fun n success => success (S n))
  ltac:(fun _ n => (exists n; reflexivity))
  0.
Qed.

Theorem graph_playground : True.
  searcher'
  ltac:(fun state =>
    let ch := eval compute in (graph state) in
      tryAll ch)
  ltac:(fun history state =>
    match state with
      | 6 => pose history
    end) 0.
Abort.


(** * Automatic forward reasoning *)

(** Be careful with pattern variables inside foralls! *)

Ltac instantiate v :=
  match goal with
    | [ H : forall x, _ |- _ ] =>
      generalize (H v); clear H; intro H
  end.

Ltac instantiate' v :=
  match goal with
    | [ H : forall x, ?P |- _ ] =>
      generalize (H v); clear H; intro H
  end.

Section S1.
  Hypothesis P : nat -> Prop.
  Variable e : nat.

  Lemma t1 : (forall y, P y) -> P e.
    intro.
    (*instantiate' e.*)
    instantiate e.
    assumption.
  Qed.
End S1.

Ltac instantiater1 :=
  match goal with
    | [ H : forall (x : ?T), _, y : ?T |- _ ] =>
      generalize (H y); clear H; intro H
  end.

Section S2.
  Hypothesis P : nat -> Prop.
  Variable e : nat.

  Lemma t1' : (forall y, P y) -> P e.
    intro.
    instantiater1.
    assumption.
  Qed.

  Variable e' : nat.

  Lemma t1'' : (forall y, P y) -> P e.
    intro.
    instantiater1.
  Abort.
End S2.

Ltac instantiater2 :=
  match goal with
    | [ H : forall (x : ?T), _, y : ?T |- _ ] =>
      generalize (H y); clear H; intro H; instantiater2
    | _ => intuition; fail
  end.

Section S3.
  Hypothesis P : nat -> Prop.
  Variable e : nat.
  Variable e' : nat.

  Lemma t1''' : (forall y, P y) -> P e.
    intro.
    instantiater2.
  Qed.

  Variable R : nat -> nat -> Prop.

  Hypothesis H1 : forall x y, R x y -> exists z, x + z < y.

  Variable m : nat.

  Lemma t2 : R e m -> e < m.
    intros.
    (*instantiater2.*)
  Abort.
End S3.

Ltac instantiater3 :=
  match goal with
    | [ H : forall (x : ?T), _, y : ?T |- _ ] =>
      generalize (H y); clear H; intro H; instantiater3
    | [ H : ?P -> ?Q |- _ ] =>
      let Hlem := fresh "Hlem" in
	(assert (Hlem : P);
	  [auto; fail
	    | generalize (H Hlem); clear H Hlem; intro H; instantiater3])
    | [ H : ex _ |- _ ] =>
      let H' := fresh "H'" with x := fresh "x" in
	(destruct H as [x H']; clear H; rename H' into H; instantiater3)
    | _ => intuition; fail
  end.

Hint Extern 5 (_ < _) => omega.

Section S4.
  Hypothesis P : nat -> Prop.
  Variable e : nat.

  Variable R : nat -> nat -> Prop.

  Hypothesis H1 : forall x y, R x y -> exists z, x + z < y.

  Variable m : nat.

  Lemma t2 : R e m -> e < m.
    intros.
    instantiater3.
  Qed.
End S4.

Section S5.
  Hypothesis P : nat -> Prop.
  Variable e : nat.

  Variable R : nat -> nat -> Prop.
  Variable pointless : nat -> Prop.

  Hypothesis P1 : forall x y, x + y < 30 -> pointless (x - y).
  Hypothesis H1 : forall x y, R x y -> exists z, x + z < y.

  Variable m : nat.

  Lemma t2' : R e m -> e < m.
    intros.
    (*instantiater3.*)
  Abort.
End S5.

Ltac forward1' H :=
  match type of H with
    | forall (x : _), _ =>
      match goal with
	| [ y : _ |- _ ] => generalize (H y); clear H; intro H; forward1' H
      end
    | ?P -> _ =>
      let pf := fresh "pf" in
	(assert (pf : P);
	  [auto; fail
	    | generalize (H pf); clear H pf; intro H; forward1' H])
    | ex _ =>
      let H' := fresh "H'" with x := fresh "x" in
	(destruct H as [x H']; clear H; rename H' into H; forward1' H)
    | _ => idtac
  end.

Ltac forward1 :=
  intuition;
    repeat match goal with
	     | [ H : _ |- _ ] => progress forward1' H
	   end;
    intuition.

Section S6.
  Hypothesis P : nat -> Prop.
  Variable e : nat.

  Variable R : nat -> nat -> Prop.
  Variable pointless : nat -> Prop.

  Hypothesis P1 : forall x y, x + y < 30 -> pointless (x - y).
  Hypothesis H1 : forall x y, R x y -> exists z, x + z < y.

  Variable m : nat.

  Lemma t2' : R e m -> e < m.
    forward1.
  Qed.

  Variable Q : nat -> nat -> Prop.

  Variable f : nat -> nat.

  Hypothesis H2 : forall x y, 2 * x < 3 * y -> exists z, R (x + z) (f y).

  Theorem t3 : e < f e -> f (f e) < m -> e < m.
    forward1.
  Abort.
End S6.

Ltac forward2' inster H :=
  match type of H with
    | ?P -> ?Q =>
      let pf := fresh "pf" in
	(assert (pf : P);
	  [auto; fail
	    | generalize (H pf); clear H pf; intro H; forward2' ltac:inster H])
    | forall (x : ?T), _ =>
      inster T ltac:(fun y => (generalize (H y); clear H; intro H; forward2' ltac:inster H))
    | ex _ =>
      let H' := fresh "H'" with x := fresh "x" in
	(destruct H as [x H']; clear H; rename H' into H; forward2' ltac:inster H)
    | ?T =>
      match T with
	| forall x, _ => fail
	| _ => idtac
      end
  end.

Ltac forward2 inster :=
  intuition;
    repeat match goal with
	     | [ H : _ |- _ ] => progress forward2' ltac:inster H
	   end;
    intuition.

Section S7.
  Hypothesis P : nat -> Prop.
  Variable e : nat.

  Variable R : nat -> nat -> Prop.
  Variable pointless : nat -> Prop.

  Hypothesis P1 : forall x y, x + y < 30 -> pointless (x - y).
  Hypothesis H1 : forall x y, R x y -> exists z, x + z < y.

  Variable m : nat.

  Lemma t2'' : R e m -> e < m.
    forward2 ltac:(fun _ k => (k e || k m)).
  Qed.

  Ltac var_inster T k :=
    match goal with
      | [ x : T |- _ ] => k x
    end.

  Lemma t2''' : R e m -> e < m.
    forward2 ltac:var_inster.
  Qed.

  Variable Q : nat -> nat -> Prop.

  Variable f : nat -> nat.

  Hypothesis H2 : forall x y, 2 * x < 3 * y -> exists z, R (x + z) (f y).

  Theorem t3 : e < f e -> f (f e) < m -> e < m.
    forward2 ltac:var_inster.
  Abort.

  Ltac subterm_inster T k :=
    match goal with
      | [ |- context[?E] ] => k E
      | [ H : context[?E] |- _ ] => k E
    end.

  Theorem t3 : e < f e -> f (f e) < m -> e < m.
    forward2 ltac:subterm_inster.
  Qed.
End S7.
