Require Import Arith List Omega.
Require Import Max.

Set Implicit Arguments.


(** * Recursion on proofs *)

Print positive.

Fixpoint div2 (n : nat) : nat :=
  match n with
    | S (S n') => S (div2 n')
    | _ => O
  end.

Inductive ntb_pred : nat -> Prop :=
  | ntb_1 : ntb_pred 1
  | ntb_div2 : forall n,
    ntb_pred (div2 n)
    -> ntb_pred n.

Fixpoint bin_to_nat (b : positive) : nat :=
  match b with
    | xH => 1
    | xO b' => 2 * bin_to_nat b'
    | xI b' => 1 + 2 * bin_to_nat b'
  end.

Lemma ntb_pred_positive : forall n,
  ntb_pred n
  -> n = 0
  -> False.
  induction 1; intuition; subst; auto.
Qed.

Hint Resolve ntb_pred_positive.

Hint Extern 5 False => omega.

Fixpoint isEven (n : nat) : bool :=
  match n with
    | 0 => true
    | 1 => false
    | S (S n') => isEven n'
  end.

Definition nat_to_bin (n : nat) (pf : ntb_pred n) : positive.
  refine (fix nat_to_bin (n : nat) (pf : ntb_pred n) {struct pf} : positive :=
    match n as n' return (n = n' -> _) with
      | 0 => fun Heq => False_rec _ _
      | 1 => fun Heq => xH
      | S (S n') => fun Heq =>
	match nat_to_bin (div2 n)
	  (match pf in (ntb_pred n') return (n = n' -> ntb_pred (div2 n')) with
	     | ntb_1 => fun Heq => False_ind _ _
	     | ntb_div2 _ pf' => fun _ => pf'
	   end (refl_equal _)) with
	  | b =>
	    if isEven n
	      then xO b
	      else xI b
	end
    end (refl_equal _)); clear nat_to_bin; eauto.
Defined.

Eval compute in nat_to_bin ntb_1.
Eval compute in nat_to_bin (ntb_div2 2 ntb_1).
Eval compute in nat_to_bin (ntb_div2 3 ntb_1).
Eval compute in nat_to_bin (ntb_div2 4 (ntb_div2 2 ntb_1)).
Eval compute in nat_to_bin (ntb_div2 5 (ntb_div2 2 ntb_1)).

Extraction nat_to_bin.


(** * Well-founded recursion: merge sort example *)

Section mergeSort.
  Variable A : Set.
  Variable le : A -> A -> Prop.

  Variable le_dec : forall x y, {le x y} + {~le x y}.

  Fixpoint insert (x : A) (ls : list A) {struct ls} : list A :=
    match ls with
      | nil => x :: nil
      | h :: ls' =>
	if le_dec x h
	  then x :: ls
	  else h :: insert x ls'
    end.

  Fixpoint merge (ls1 ls2 : list A) {struct ls1} : list A :=
    match ls1 with
      | nil => ls2
      | h :: ls' => insert h (merge ls' ls2)
    end.

  Fixpoint split (ls : list A) : list A * list A :=
    match ls with
      | nil => (nil, nil)
      | h :: nil => (h :: nil, nil)
      | h1 :: h2 :: ls' =>
	let (ls1, ls2) := split ls' in
	  (h1 :: ls1, h2 :: ls2)
    end.

  Definition lengthOrder (ls1 ls2 : list A) :=
    length ls1 < length ls2.

  Theorem lengthOrder_wf : well_founded lengthOrder.
    red.

    cut (forall len : nat, forall a : list A, length a <= len -> Acc lengthOrder a); eauto.
    
    induction len; intuition.

    destruct a; simpl in H.

    constructor; intros.
    inversion H0.

    inversion H.

    constructor; intros.
    red in H0.
    apply IHlen.
    omega.
  Qed.

  Ltac arith_contra :=
    assert False; [omega | tauto].

  Lemma split_lengthOrder1' : forall len ls,
    2 <= length ls <= len
    -> lengthOrder (fst (split ls)) ls.
    induction len; simpl; intuition; try arith_contra.

    destruct ls; simpl in *; try arith_contra.
    destruct ls; simpl in *; try arith_contra.

    red; simpl.

    destruct (le_lt_dec 2 (length ls)).

    generalize (IHlen ls).
    destruct (split ls); simpl.
    unfold lengthOrder; simpl.
    omega.
    
    destruct ls; simpl in *; try omega.
    destruct ls; simpl in *; omega.
  Qed.

  Lemma split_lengthOrder2' : forall len ls,
    2 <= length ls <= len
    -> lengthOrder (snd (split ls)) ls.
    induction len; simpl; intuition; try arith_contra.

    destruct ls; simpl in *; try arith_contra.
    destruct ls; simpl in *; try arith_contra.

    red; simpl.

    destruct (le_lt_dec 2 (length ls)).

    generalize (IHlen ls).
    destruct (split ls); simpl.
    unfold lengthOrder; simpl.
    omega.
    
    destruct ls; simpl in *; try omega.
    destruct ls; simpl in *; omega.
  Qed.

  Theorem split_lengthOrder1 : forall ls,
    2 <= length ls
    -> forall ls1 ls2, split ls = (ls1, ls2)
      -> lengthOrder ls1 ls.
    intros.
    replace ls1 with (fst (split ls)).
    eapply split_lengthOrder1'; eauto.
    rewrite H0; trivial.
  Qed.

  Theorem split_lengthOrder2 : forall ls,
    2 <= length ls
    -> forall ls1 ls2, split ls = (ls1, ls2)
      -> lengthOrder ls2 ls.
    intros.
    replace ls2 with (snd (split ls)).
    eapply split_lengthOrder2'; eauto.
    rewrite H0; trivial.
  Qed.

  Hint Resolve split_lengthOrder1 split_lengthOrder2.

  Definition mergeSort (ls : list A) : list A.
    refine (Fix lengthOrder_wf (fun _ => list A)
      (fun (ls : list A)
	(mergeSort : forall ls' : list A, lengthOrder ls' ls -> list A) =>
	if le_lt_dec 2 (length ls)
	  then match split ls as lss return (split ls = lss -> _) with
		 | (ls1, ls2) => fun Heq => merge (mergeSort ls1 _) (mergeSort ls2 _)
	       end (refl_equal _)
	  else ls)); eauto.
  Defined.

  Theorem mergeSort_rec : forall x y ls,
    mergeSort (x :: y :: ls) =
    match split (x :: y :: ls) as lss return (split (x :: y :: ls) = lss -> _) with
      | (ls1, ls2) => fun Heq => merge (mergeSort ls1) (mergeSort ls2)
    end (refl_equal _).
    intros.
    unfold mergeSort at 1.
    rewrite Fix_eq; intuition.

    destruct (le_lt_dec 2 (length x0)); intuition.
    generalize (split_lengthOrder1 x0 l).
    generalize (split_lengthOrder2 x0 l).
    destruct (split x0); intuition.
    repeat rewrite H.
    reflexivity.
  Qed.
End mergeSort.

Recursive Extraction mergeSort.


(** * Domain theory approach to general recursive programs *)

(** ** Foundational definitions *)

Set Implicit Arguments.

Section computation.
  Variable A : Set.

  Definition computation :=
    {f : nat -> option A
      | forall (n : nat) (v : A),
	f n = Some v
	-> forall (n' : nat), n' >= n
	  -> f n' = Some v}.

  Definition runTo (m : computation) (n : nat) (v : A) :=
    proj1_sig m n = Some v.

  Definition run (m : computation) (v : A) :=
    exists n, runTo m n v.
End computation.

Hint Unfold runTo.

Section Bottom.
  Variable A : Set.

  Definition Bottom : computation A.
    exists (fun _ : nat => @None A); intuition.
  Defined.
End Bottom.

Section Return.
  Variable A : Set.
  Variable v : A.

  Definition Return : computation A.
    intros.
    exists (fun _ : nat => Some v); intuition.
  Defined.

  Theorem run_Return : run Return v.
    red.
    unfold runTo, Return.
    exists 0; auto.
  Qed.
End Return.

Hint Resolve run_Return.

Ltac caseEq e := generalize (refl_equal e); pattern e at -1; case e.

Section Bind.
  Variables A B : Set.
  Variable m1 : computation A.
  Variable m2 : A -> computation B.

  Definition Bind : computation B.
    destruct m1 as [f1 Hf1].
    exists (fun n =>
      match f1 n with
	| None => None
	| Some v =>
	  let (f2, Hf2) := m2 v in
	    f2 n
      end); intuition.
    generalize (Hf1 n).
    destruct (f1 n); intuition; try discriminate.
    rewrite (H1 a (refl_equal _) _ H0); trivial.
    destruct (m2 a); eauto.
  Defined.

  Theorem run_Bind : forall (v1 : A) (v2 : B),
    run m1 v1
    -> run (m2 v1) v2
    -> run Bind v2.
    unfold Bind, run, runTo; intros v1 v2 H1 H2.

    destruct m1 as [f1 Hf1]; simpl in *; idtac.
    caseEq (m2 v1); intros f2 Hf2 Heq.
    rewrite Heq in H2.
    destruct H1 as [n1 Hn1].
    destruct H2 as [n2 Hn2].

    exists (max n1 n2).
    rewrite (Hf1 _ _ Hn1); auto with arith.
    rewrite Heq.
    rewrite (Hf2 _ _ Hn2); auto with arith.
  Qed.

  Theorem run_Bind' : forall (v2 : B),
    run Bind v2
    -> exists v1 : A,
      run m1 v1
      /\ run (m2 v1) v2.
    unfold Bind, run, runTo; intros v2 H1.

    destruct m1 as [f1 Hf1]; simpl in *; idtac.
    destruct H1 as [n1 Hn1].
    caseEq (f1 n1);
    [intros v1 Heq
      | intros Heq]; rewrite Heq in Hn1; try discriminate.
    exists v1; intuition eauto.
    destruct (m2 v1); simpl; eauto.
  Qed.
End Bind.

Hint Resolve run_Bind.

Notation "x <- m1 ; m2" :=
  (Bind m1 (fun x => m2)) (right associativity, at level 70).

Section monotone_runTo.
  Variable A : Set.
  Variable c : computation A.
  Variable v : A.

  Theorem monotone_runTo : forall (n1 : nat),
    runTo c n1 v
    -> forall n2, n2 >= n1
      -> runTo c n2 v.
    unfold runTo; intuition.
    destruct c; simpl in *; intuition eauto.
  Qed.
End monotone_runTo.

Hint Resolve monotone_runTo.

Section rewrite.
  Variable A : Set.
  Variable c : computation A.
  Variable n : nat.
  Variable v : A.

  Theorem fold_runTo :
    (proj1_sig c n = Some v)
    = runTo c n v.
    trivial.
  Qed.
End rewrite.

Section lattice.
  Variable A : Set.

  Definition leq (x y : option A) :=
    forall v, x = Some v -> y = Some v.
End lattice.

Hint Unfold leq.

Section Fix.
  Variables A B : Set.
  Variable f : (A -> computation B) -> (A -> computation B).

  Hypothesis f_continuous : forall n v v1 x,
    runTo (f v1 x) n v
    -> forall (v2 : A -> computation B), (forall x, leq (proj1_sig (v1 x) n) (proj1_sig (v2 x) n))
      -> runTo (f v2 x) n v.

  Fixpoint Fix' (n : nat) (x : A) {struct n} : computation B :=
    match n with
      | O => Bottom _
      | S n' => f (Fix' n') x
    end.

  Definition Fix : A -> computation B.
    intro x.
    exists (fun n => proj1_sig (Fix' n x) n).

    cut (forall (steps : nat) (n : nat) (v : B),
      proj1_sig (Fix' n x) steps = Some v ->
      forall (n' : nat), n' >= n
	-> proj1_sig (Fix' n' x) steps = Some v).

    intuition.
    eapply H; eauto.
    rewrite fold_runTo; eauto.

    intros steps n.
    generalize dependent x.
    induction n; simpl; intuition.

    discriminate.

    destruct n'.
    inversion H0.

    simpl.
    apply f_continuous with (Fix' n); clear f_continuous; auto.

    red; intros.
    eauto with arith.
  Defined.

  Definition extensional (f : (A -> computation B) -> (A -> computation B)) := 
    forall g1 g2 n,
      (forall x, proj1_sig (g1 x) n = proj1_sig (g2 x) n)
      -> forall x, proj1_sig (f g1 x) n = proj1_sig (f g2 x) n.

  Hypothesis f_extensional : extensional f.

  Theorem run_Fix : forall x v,
    run (f Fix x) v
    -> run (Fix x) v.
    intros.

    red; unfold runTo; simpl.
    red in H; unfold runTo in H; simpl in H.

    destruct H as [n Hn].
    exists (S n).
    simpl.

    rewrite fold_runTo.
    apply monotone_runTo with n; auto.

    red.
    rewrite (f_extensional (Fix' n) Fix n); intuition.
  Qed.
End Fix.

Hint Resolve run_Fix.

Notation "'dfix' f [ x ::: dom ] ::: ran := e" :=
  (Fix (A := dom) (B := ran) (fun f x => e) _) (at level 80).
Notation "'dfix' f [ '__' ::: dom ] ::: ran := e" :=
  (Fix (A := dom) (B := ran) (fun f _ => e) _) (at level 80).
Notation "'dfix' '__' [ x ::: dom ] ::: ran := e" :=
  (Fix (A := dom) (B := ran) (fun _ x => e) _) (at level 80).
Notation "'dfix' '__' [ '__' ::: dom ] ::: ran := e" :=
  (Fix (A := dom) (B := ran) (fun _ _ => e) _) (at level 80).


(** ** Examples *)

(** *** The constant-0 function *)

Definition const : nat -> computation nat.
  refine (dfix const [ x ::: nat ] ::: nat := Return 0); intuition.
Defined.

Eval compute in proj1_sig (const 0) 0.
Eval compute in proj1_sig (const 0) 1.
Eval compute in proj1_sig (const 8) 2.

Hint Unfold extensional.

Theorem const_correct : forall n, run (const n) 0.
  intros.
  unfold const.
  apply run_Fix; auto.
Qed.

Recursive Extraction const.


(** *** Natural number addition *)

Definition add : nat * nat -> computation nat.
  refine (Fix (fun (add : nat * nat -> computation nat) (ns : nat * nat) =>
    let (n1, n2) := ns in
      match n1 with
	| O => Return (snd ns)
	| S n1' => res <- add (n1', n2); Return (S res)
      end) _); intuition.

  destruct x; simpl in *; idtac.
  destruct n0; intuition.

  unfold runTo, Bind; simpl.
  unfold runTo, Bind in H; simpl in H.
  caseEq (v1 (n0, n1)); intros f1 Hf1 Heq.
  rewrite Heq in H; simpl in H.

  caseEq (f1 n); [intros V1 Heq' | intros Heq']; rewrite Heq' in H; try discriminate.

  generalize (H0 (n0, n1)); intro Hleq.
  red in Hleq.
  rewrite Heq in Hleq; simpl in Hleq.
  destruct (v2 (n0, n1)) as [f2 Hf2]; simpl in *; idtac.
  rewrite (Hleq V1); intuition.
Defined.

Eval compute in proj1_sig (add (0, 0)) 0.
Eval compute in proj1_sig (add (0, 0)) 1.
Eval compute in proj1_sig (add (1, 0)) 1.

Eval compute in proj1_sig (add (8, 13)) 9.

Theorem add_extensional : extensional
  (fun add (ns : nat * nat) => let (n1, n2) := ns in
    match n1 with
      | O => Return (snd ns)
      | S n1' => res <- add (n1', n2); Return (S res)
    end).
  red; intuition.
  destruct a; intuition.
  unfold Bind.
  generalize (H (a, b)).
  destruct (g1 (a, b)); simpl.
  destruct (g2 (a, b)); simpl.
  intro Heq.
  rewrite Heq.
  trivial.
Qed.

Hint Immediate add_extensional.

Theorem add_correct : forall n1 n2, run (add (n1, n2)) (n1 + n2).
  induction n1; unfold add; eauto.
Qed.

Recursive Extraction add.


(** *** Guarded infinite loop *)

Definition looper : bool -> computation unit.
  refine (dfix looper [b ::: bool] ::: unit :=
    if b
      then Return tt
      else looper b); intuition.

  destruct x; intuition.
  unfold leq in H0.
  eauto.
Defined.

Eval compute in proj1_sig (looper true) 0.
Eval compute in proj1_sig (looper true) 1.

Eval compute in proj1_sig (looper false) 0.
Eval compute in proj1_sig (looper false) 1.
Eval compute in proj1_sig (looper false) 10.

Theorem looper_extensional : extensional (fun looper (b : bool) =>
  if b
    then Return tt
    else looper b).
  red; intuition.
  destruct x; intuition.
Qed.

Hint Immediate looper_extensional.

Theorem looper_correct : run (looper true) tt.
  unfold looper; auto.
Qed.

Recursive Extraction looper.
