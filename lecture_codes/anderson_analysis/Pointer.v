(** Points-to analysis *)

Require Import Arith List.
Require Import Machine Maps.

Set Implicit Arguments.

(** * The instruction language *)

Definition var := nat.

Inductive instruction : Set :=
  | Allocate : var -> instruction
  | Copy : var -> var -> instruction
  | Read : var -> var -> instruction
  | Write : var -> var -> instruction
  | Goto : nat -> instruction.

(** * Machine states *)

Module NatEq <: EQ.
  Definition dom := nat.
  Definition dom_eq_dec := eq_nat_dec.
End NatEq.
Module NatMap := FuncMap(NatEq).

Module VarMap : MAP with Definition dom := var := NatMap.

Record state : Set := {
  pc : nat;
  vars : VarMap.map nat;
  heap : NatMap.map nat;
  limit : nat
}.

Definition initState :=
  Build_state
  0
  (VarMap.init 0)
  (NatMap.init 0)
  0.


(** * Dynamic semantics *)

Definition exec (i : instruction) (s : state) : state :=
  match i with
    | Allocate dst =>
      Build_state
      (S (pc s))
      (VarMap.upd (vars s) dst (S (limit s)))
      (heap s)
      (S (limit s))
    | Copy dst src =>
      Build_state
      (S (pc s))
      (VarMap.upd (vars s) dst (VarMap.sel (vars s) src))
      (heap s)
      (limit s)
    | Read dst src =>
      match NatMap.sel (heap s) (VarMap.sel (vars s) src) with
	| O => s
	| addr =>
	  Build_state
	  (S (pc s))
	  (VarMap.upd (vars s) dst addr)
	  (heap s)
	  (limit s)
      end
    | Write dst src =>
      match VarMap.sel (vars s) dst with
	| O => s
	| addr =>
	  Build_state
	  (S (pc s))
	  (vars s)
	  (NatMap.upd (heap s) addr (VarMap.sel (vars s) src))
	  (limit s)
      end
    | Goto n =>
      Build_state
      n
      (vars s)
      (heap s)
      (limit s)
  end.


(** * Must-not-alias relation *)

Section mustNotAlias.
  Variable program : list instruction.
  Variables v1 v2 : var.

  Definition mustNotAlias :=
    forall s, reachable program pc exec initState s
      -> VarMap.sel (vars s) v1 = VarMap.sel (vars s) v2
      -> VarMap.sel (vars s) v1 = 0.

  Inductive mustNotAlias_answer : Set :=
    | Unknown : mustNotAlias_answer
    | NotAliased : mustNotAlias -> mustNotAlias_answer.
End mustNotAlias.

Definition mustNotAlias_procedure := forall program v1 v2,
  mustNotAlias_answer program v1 v2.
