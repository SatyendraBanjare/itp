(** Homework Assignment 6#<br>#
#<a href="http://www.cs.berkeley.edu/~adamc/itp/">#Interactive Computer Theorem
Proving#</a><br>#
CS294-9, Fall 2006#<br>#
UC Berkeley *)

Require Import Arith Bool List.

Definition var := nat.
Definition lit := (bool * var)%type.

Definition clause := list lit.
Definition formula := list clause.

Definition asgn := var -> bool.

Definition satLit (l : lit) (a : asgn) :=
  a (snd l) = fst l.

Fixpoint satClause (cl : clause) (a : asgn) {struct cl} : Prop :=
  match cl with
    | nil => False
    | l :: cl' => satLit l a \/ satClause cl' a
  end.

Fixpoint satFormula (fm : formula) (a : asgn) {struct fm} : Prop :=
  match fm with
    | nil => True
    | cl :: fm' => satClause cl a /\ satFormula fm' a
  end.

Definition bool_eq_dec : forall (x y : bool), {x = y} + {x <> y}.
  decide equality.
Defined.

Lemma contradictory_assignment : forall s l cl a,
  s <> fst l
  -> satLit l a
  -> satLit (s, snd l) a
  -> satClause cl a.
  intros.
  red in H0, H1.
  simpl in H1.
  subst.
  tauto.
Qed.

Hint Resolve contradictory_assignment.

Definition upd (a : asgn) (l : lit) : asgn :=
  fun v : var =>
    if eq_nat_dec v (snd l)
      then fst l
      else a v.

Lemma satLit_upd_eq : forall l a,
  satLit l (upd a l).
  unfold satLit, upd; simpl; intros.
  destruct (eq_nat_dec (snd l) (snd l)); tauto.
Qed.

Hint Resolve satLit_upd_eq.

Lemma satLit_upd_neq : forall v l s a,
  v <> snd l
  -> satLit (s, v) (upd a l)
  -> satLit (s, v) a.
  unfold satLit, upd; simpl; intros.
  destruct (eq_nat_dec v (snd l)); tauto.
Qed.

Hint Resolve satLit_upd_neq.

Lemma satLit_upd_neq2 : forall v l s a,
  v <> snd l
  -> satLit (s, v) a
  -> satLit (s, v) (upd a l).
  unfold satLit, upd; simpl; intros.
  destruct (eq_nat_dec v (snd l)); tauto.
Qed.

Hint Resolve satLit_upd_neq2.

Lemma satLit_contra : forall s l a cl,
  s <> fst l
  -> satLit (s, snd l) (upd a l)
  -> satClause cl a.
  unfold satLit, upd; simpl; intros.
  destruct (eq_nat_dec (snd l) (snd l)); intuition.
  assert False; intuition.
Qed.

Hint Resolve satLit_contra.

Ltac magic_solver := simpl; intros; subst; intuition eauto; firstorder;
  match goal with
    | [ H1 : satLit ?l ?a, H2 : satClause ?cl ?a |- _ ] =>
      assert (satClause cl (upd a l)); firstorder
  end.

Definition setClause : forall (cl : clause) (l : lit),
  {cl' : clause |
    forall a, satClause cl (upd a l) <-> satClause cl' a}
  + {forall a, satLit l a -> satClause cl a}.
  refine (fix setClause (cl : clause) (l : lit) {struct cl}
    : {cl' : clause |
      forall a, satClause cl (upd a l) <-> satClause cl' a}
    + {forall a, satLit l a -> satClause cl a} :=
    match cl return {cl' : clause |
      forall a, satClause cl (upd a l) <-> satClause cl' a}
    + {forall a, satLit l a -> satClause cl a} with
      | nil => inleft _ (exist _ nil _)
      | (s, v) :: cl' =>
	if eq_nat_dec v (snd l)
	  then if bool_eq_dec s (fst l)
	    then inright _ _
	    else match setClause cl' l with
		   | inleft (exist cl'' _) => inleft _ (exist _ cl'' _)
		   | inright _ => inright _ _
		 end
	  else match setClause cl' l with
		 | inleft (exist cl'' _) => inleft _ (exist _ ((s, v) :: cl'') _)
		 | inright _ => inright _ _
	       end
    end); clear setClause; magic_solver.
Defined.

Definition setClauseSimple (cl : clause) (l : lit) :=
  match setClause cl l with
    | inleft (exist cl' _) => Some cl'
    | inright _ => None
  end.

Eval compute in setClauseSimple nil (true, 0).
Eval compute in setClauseSimple ((true, 0) :: nil) (true, 0).
Eval compute in setClauseSimple ((true, 0) :: nil) (false, 0).
Eval compute in setClauseSimple ((true, 0) :: nil) (true, 1).
Eval compute in setClauseSimple ((true, 0) :: nil) (false, 1).
Eval compute in setClauseSimple ((true, 0) :: (true, 1) :: nil) (true, 1).
Eval compute in setClauseSimple ((true, 0) :: (true, 1) :: nil) (false, 1).
Eval compute in setClauseSimple ((true, 0) :: (false, 1) :: nil) (true, 1).
Eval compute in setClauseSimple ((true, 0) :: (false, 1) :: nil) (false, 1).

Definition isNil : forall (A : Set) (ls : list A), {ls = nil} + {True}.
  destruct ls; eauto.
Defined.
Implicit Arguments isNil [A].

Lemma satLit_idem_lit : forall l a l',
  satLit l a
  -> satLit l' a
  -> satLit l' (upd a l).
  unfold satLit, upd; simpl; intros.
  destruct (eq_nat_dec (snd l') (snd l)); congruence.
Qed.

Hint Resolve satLit_idem_lit.

Lemma satLit_idem_clause : forall l a cl,
  satLit l a
  -> satClause cl a
  -> satClause cl (upd a l).
  induction cl; simpl; intuition.
Qed.

Hint Resolve satLit_idem_clause.

Lemma satLit_idem_formula : forall l a fm,
  satLit l a
  -> satFormula fm a
  -> satFormula fm (upd a l).
  induction fm; simpl; intuition.
Qed.

Hint Resolve satLit_idem_formula.

Definition setFormula : forall (fm : formula) (l : lit),
  {fm' : formula |
    forall a, satFormula fm (upd a l) <-> satFormula fm' a}
  + {forall a, satLit l a -> ~satFormula fm a}.
  refine (fix setFormula (fm : formula) (l : lit) {struct fm}
    : {fm' : formula |
      forall a, satFormula fm (upd a l) <-> satFormula fm' a}
    + {forall a, satLit l a -> ~satFormula fm a} :=
    match fm return {fm' : formula |
      forall a, satFormula fm (upd a l) <-> satFormula fm' a}
    + {forall a, satLit l a -> ~satFormula fm a} with
      | nil => inleft _ (exist _ nil _)
      | cl :: fm' =>
	match setClause cl l with
	  | inleft (exist cl' _) =>
	    if isNil cl'
	      then inright _ _
	      else match setFormula fm' l with
		     | inleft (exist fm'' _) => inleft _ (exist _ (cl' :: fm'') _)
		     | inright _ => inright _ _
		   end
	  | inright _ =>
	    match setFormula fm' l with
	      | inleft (exist fm'' _) => inleft _ (exist _ fm'' _)
	      | inright _ => inright _ _
	    end
	end
    end); clear setFormula; magic_solver.
Defined.

Definition setFormulaSimple (fm : formula) (l : lit) :=
  match setFormula fm l with
    | inleft (exist fm' _) => Some fm'
    | inright _ => None
  end.

Eval compute in setFormulaSimple nil (true, 0).
Eval compute in setFormulaSimple (((true, 0) :: nil) :: nil) (true, 0).
Eval compute in setFormulaSimple (((false, 0) :: nil) :: nil) (true, 0).
Eval compute in setFormulaSimple (((false, 1) :: nil) :: nil) (true, 0).
Eval compute in setFormulaSimple (((false, 1) :: (true, 0) :: nil) :: nil) (true, 0).
Eval compute in setFormulaSimple (((false, 1) :: (false, 0) :: nil) :: nil) (true, 0).

Hint Extern 1 False => discriminate.

Hint Extern 1 False =>
  match goal with
    | [ H : In _ (_ :: _) |- _ ] => inversion H; clear H; subst
  end.

Definition findUnitClause : forall (fm : formula),
  {l : lit | In (l :: nil) fm}
  + {forall l, ~In (l :: nil) fm}.
  refine (fix findUnitClause (fm : formula)
    : {l : lit | In (l :: nil) fm}
    + {forall l, ~In (l :: nil) fm} :=
    match fm return {l : lit | In (l :: nil) fm}
      + {forall l, ~In (l :: nil) fm} with
      | nil => inright _ _
      | (l :: nil) :: _ => inleft _ (exist _ l _)
      | _ :: fm' =>
	match findUnitClause fm' with
	  | inleft (exist l _) => inleft _ (exist _ l _)
	  | inright _ => inright _ _
	end
    end); clear findUnitClause; magic_solver.
Defined.

Lemma unitClauseTrue : forall l a fm,
  In (l :: nil) fm
  -> satFormula fm a
  -> satLit l a.
  induction fm; intuition.
  inversion H.
  inversion H; subst; simpl in H0; intuition.
Qed.

Hint Resolve unitClauseTrue.

Definition unitPropagate : forall (fm : formula), option (sigS (fun fm' : formula =>
  {l : lit |
    (forall a, satFormula fm a -> satLit l a)
    /\ forall a, satFormula fm (upd a l) <-> satFormula fm' a})
+ {forall a, ~satFormula fm a}).
  intro fm.
  refine (match findUnitClause fm with
	    | inleft (exist l _) =>
	      match setFormula fm l with
		| inleft (exist fm' _) =>
		  Some (inleft _ (existS (fun fm' : formula =>
		    {l : lit |
		      (forall a, satFormula fm a -> satLit l a)
		      /\ forall a, satFormula fm (upd a l) <-> satFormula fm' a})
		  fm' (exist _ l _)))
		| inright _ => Some (inright _ _)
	      end
	    | inright _ => None
	  end); magic_solver.
Defined.

Definition unitPropagateSimple (fm : formula) :=
  match unitPropagate fm with
    | None => None
    | Some (inleft (existS fm' (exist l _))) => Some (Some (fm', l))
    | Some (inright _) => Some None
  end.

Eval compute in unitPropagateSimple nil.
Eval compute in unitPropagateSimple (((true, 0) :: nil) :: nil).
Eval compute in unitPropagateSimple (((true, 0) :: nil) :: ((false, 0) :: nil) :: nil).
Eval compute in unitPropagateSimple (((true, 0) :: nil) :: ((false, 1) :: nil) :: nil).
Eval compute in unitPropagateSimple (((true, 0) :: nil) :: ((false, 0) :: (false, 1) :: nil) :: nil).
Eval compute in unitPropagateSimple (((false, 0) :: (false, 1) :: nil) :: ((true, 0) :: nil) :: nil).

Definition chooseSplit (fm : formula) :=
  match fm with
    | ((l :: _) :: _) => l
    | _ => (true, 0)
  end.

Definition negate (l : lit) := (negb (fst l), snd l).

Hint Unfold satFormula.

Lemma satLit_dec : forall l a,
  {satLit l a} + {satLit (negate l) a}.
  destruct l.
  unfold satLit; simpl; intro.
  destruct b; destruct (a v); simpl; auto.
Qed.

Definition alist := list lit.

Fixpoint interp_alist (al : alist) : asgn :=
  match al with
    | nil => fun _ => true
    | l :: al' => upd (interp_alist al') l
  end.

Definition boundedSat (bound : nat) (fm : formula)
  : option ({al : alist | satFormula fm (interp_alist al)}
    + {forall a, ~satFormula fm a}).
  refine (fix boundedSat (bound : nat) (fm : formula) {struct bound}
    : option ({al : alist | satFormula fm (interp_alist al)}
      + {forall a, ~satFormula fm a}) :=
    match bound with
      | O => None
      | S bound' =>
	if isNil fm
	  then Some (inleft _ (exist _ nil _))
	  else match unitPropagate fm with
		 | Some (inleft (existS fm' (exist l _))) =>
		   match boundedSat bound' fm' with
		     | None => None
		     | Some (inleft (exist al _)) => Some (inleft _ (exist _ (l :: al) _))
		     | Some (inright _) => Some (inright _ _)
		   end
		 | Some (inright _) => Some (inright _ _)
		 | None =>
		   let l := chooseSplit fm in
		     match setFormula fm l with
		       | inleft (exist fm' _) =>
			 match boundedSat bound' fm' with
			   | None => None
			   | Some (inleft (exist al _)) => Some (inleft _ (exist _ (l :: al) _))
			   | Some (inright _) =>
			     match setFormula fm (negate l) with
			       | inleft (exist fm' _) =>
				 match boundedSat bound' fm' with
				   | None => None
				   | Some (inleft (exist al _)) => Some (inleft _ (exist _ (negate l :: al) _))
				   | Some (inright _) => Some (inright _ _)
				 end
			       | inright _ => Some (inright _ _)
			     end
			 end
		       | inright _ =>
			 match setFormula fm (negate l) with
			   | inleft (exist fm' _) =>
			     match boundedSat bound' fm' with
			       | None => None
			       | Some (inleft (exist al _)) => Some (inleft _ (exist _ (negate l :: al) _))
			       | Some (inright _) => Some (inright _ _)
			     end
			   | inright _ => Some (inright _ _)
			 end
		     end
	       end
    end); simpl; intros; subst; intuition; try generalize dependent (interp_alist al).
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  assert (satFormula fm (upd a0 l)); firstorder.
  assert (satFormula fm (upd a0 l)); firstorder.
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  firstorder.
  destruct (satLit_dec l a);
    [assert (satFormula fm (upd a l))
      | assert (satFormula fm (upd a (negate l)))]; firstorder.
  destruct (satLit_dec l a);
    [assert (satFormula fm (upd a l))
      | assert (satFormula fm (upd a (negate l)))]; firstorder.
  destruct (satLit_dec l a);
    [assert (satFormula fm (upd a l))
      | assert (satFormula fm (upd a (negate l)))]; firstorder.
  destruct (satLit_dec l a);
    [assert (satFormula fm (upd a l))
      | assert (satFormula fm (upd a (negate l)))]; firstorder.
  destruct (satLit_dec l a); intuition eauto;
    assert (satFormula fm (upd a l)); firstorder.
  destruct (satLit_dec l a); intuition eauto;
    assert (satFormula fm (upd a l)); firstorder.
  firstorder.
  firstorder.
  destruct (satLit_dec l a); intuition eauto;
    assert (satFormula fm (upd a (negate l))); firstorder.
  destruct (satLit_dec l a); intuition eauto;
    assert (satFormula fm (upd a (negate l))); firstorder.
  destruct (satLit_dec l a);
    [assert (satFormula fm (upd a l))
      | assert (satFormula fm (upd a (negate l)))]; firstorder.
Defined.

Definition boundedSatSimple (bound : nat) (fm : formula) :=
  match boundedSat bound fm with
    | None => None
    | Some (inleft (exist a _)) => Some (Some a)
    | Some (inright _) => Some None
  end.

Eval compute in boundedSatSimple 100 nil.
Eval compute in boundedSatSimple 100 (((true, 0) :: nil) :: nil).
Eval compute in boundedSatSimple 100 (((true, 0) :: nil) :: ((false, 0) :: nil) :: nil).
Eval compute in boundedSatSimple 100 (((true, 0) :: (false, 1) :: nil) :: ((true, 1) :: nil) :: nil).
Eval compute in boundedSatSimple 100 (((true, 0) :: (false, 1) :: nil) :: ((true, 1) :: (false, 0) :: nil) :: nil).
Eval compute in boundedSatSimple 100 (((true, 0) :: (false, 1) :: nil) :: ((false, 0) :: (false, 0) :: nil) :: ((true, 1) :: nil) :: nil).
Eval compute in boundedSatSimple 100 (((false, 0) :: (true, 1) :: nil) :: ((false, 1) :: (true, 0) :: nil) :: nil).

Recursive Extraction boundedSat.
