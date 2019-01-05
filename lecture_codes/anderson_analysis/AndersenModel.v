Require Import List TheoryList.
Require Import Maps.
Require Import Pointer.

Set Implicit Arguments.

Definition allocation_site := nat.
Module AllocMap : MAP with Definition dom := allocation_site := NatMap.
Module AllocSet : SET with Definition dom := allocation_site := ListSet(NatEq).

Inductive abstract_instruction : Set :=
  | AbsAllocate : var -> allocation_site -> abstract_instruction
  | AbsCopy : var -> var -> abstract_instruction
  | AbsRead : var -> var -> abstract_instruction
  | AbsWrite : var -> var -> abstract_instruction.

Record abstract_state : Set := {
  avars : VarMap.map AllocSet.set;
  aheap : AllocMap.map AllocSet.set
}.

Definition abstract_exec (i : abstract_instruction) (s : abstract_state)
  : abstract_state :=
  match i with
    | AbsAllocate dst site =>
      Build_abstract_state
      (VarMap.upd (avars s) dst
	(AllocSet.add (VarMap.sel (avars s) dst) site))
      (aheap s)
    | AbsCopy dst src =>
      Build_abstract_state
      (VarMap.upd (avars s) dst
	(AllocSet.union (VarMap.sel (avars s) dst) (VarMap.sel (avars s) src)))
      (aheap s)
    | AbsRead dst src =>
      Build_abstract_state
      (VarMap.upd (avars s) dst
	(fold_left (fun known site => AllocSet.union known (AllocMap.sel (aheap s) site))
	  (AllocSet.elems (VarMap.sel (avars s) src)) (VarMap.sel (avars s) dst)))
      (aheap s)
    | AbsWrite dst src =>
      Build_abstract_state
      (avars s)
      (fold_left (fun known site => AllocMap.upd known site
	(AllocSet.union (AllocMap.sel (aheap s) site) (VarMap.sel (avars s) src)))
      (AllocSet.elems (VarMap.sel (avars s) dst)) (aheap s))
  end.

Fixpoint abstractProgram' (next : allocation_site)
  (program : list instruction) {struct program}
  : list abstract_instruction :=
  match program with
    | nil => nil
    | ins :: program' =>
      match ins with
	| Allocate dst => AbsAllocate dst next :: abstractProgram' (S next) program'
	| Copy dst src => AbsCopy dst src :: abstractProgram' next program'
	| Read dst src => AbsRead dst src :: abstractProgram' next program'
	| Write dst src => AbsWrite dst src :: abstractProgram' next program'
	| Goto _ => abstractProgram' next program'
      end
  end.

Definition abstractProgram := abstractProgram' 1.
