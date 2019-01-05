Require Import Arith List.
Require Import Max.

Set Implicit Arguments.


(** * Some prelimiary set-up of lists at [Type] level *)

Section listT.
  Variable T : Type.

  Inductive listT : Type :=
    | nilT : listT
    | consT : T -> listT -> listT.

  Fixpoint appT (ls1 ls2 : listT) {struct ls1} : listT :=
    match ls1 with
      | nilT => ls2
      | consT x ls1' => consT x (appT ls1' ls2)
    end.

  Section listF.
    Variable f : T -> Type.

    Fixpoint listF (ts : listT) : Type :=
      match ts with
	| nilT => unit
	| consT t ts' => prodT (f t) (listF ts')
      end.

    Definition nilF : listF nilT := tt.
    Definition consF (x : T) (ts : listT) (v : f x) (ls : listF ts) : listF (consT x ts) :=
      pairT v ls.

    Definition headF (x : T) (ts : listT) (ls : listF (consT x ts)) : f x :=
      fstT ls.
    Definition tailF (x : T) (ts : listT) (ls : listF (consT x ts)) : listF ts :=
      sndT ls.
  End listF.
End listT.

Implicit Arguments nilT [T].
Implicit Arguments nilF [T f].
Implicit Arguments consF [T f x ts].
Implicit Arguments headF [T f x ts].
Implicit Arguments tailF [T f x ts].


(** * A reflective representation of simple inductive types *)

Inductive argument : Type :=
  | Self : argument
  | Other : Type -> argument.

Definition constructor := listT argument.

Section constructor.
  Variable self : Type.

  Definition interp_argument (a : argument) : Type :=
    match a with
      | Self => self
      | Other T => T
    end.

  Fixpoint argify (args: listT argument) (T : Type) {struct args} : Type :=
    match args with
      | nilT => T
      | consT t args' => interp_argument t -> argify args' T
    end.

  Fixpoint argApply (args : listT argument) (T : Type) {struct args}
    : argify args T -> listF interp_argument args -> T :=
    match args return (argify args T -> listF interp_argument args -> T) with
      | nilT => fun T' _ => T'
      | consT t args' => fun T' vals => argApply args' T (T' (headF vals)) (tailF vals)
    end.

  Definition constructorTy (con : constructor) : Type :=
    argify con self.

  Variable P : self -> Type.

  Fixpoint constructorIH (con : constructor) {struct con} : constructorTy con -> Type :=
    match con return (constructorTy con -> Type) with
      | nilT => fun v => P v
      | consT Self con' => fun T =>
	forall (x : self), P x -> constructorIH con' (T x)
      | consT (Other T') con' => fun T =>
	forall (x : T'), constructorIH con' (T x)
    end.

  Fixpoint rect (cons : listT constructor) : listF constructorTy cons -> Type :=
    match cons return (listF constructorTy cons -> Type) with
      | nilT => fun _ => forall (x : self), P x
      | consT con cons' => fun cvals =>
	constructorIH con (headF cvals) -> rect cons' (tailF cvals)
    end.
End constructor.


(** * Examples using these functions *)

Eval compute in interp_argument nat Self.
Eval compute in interp_argument nat (Other bool).

Eval compute in argify nat (consT Self (consT (Other bool) nilT)) nat.

Eval compute in argApply nat (consT Self (consT (Other bool) nilT)) nat
  (fun n b => if b then n else S n)
  (consF (f := interp_argument nat) (x := Self) O
    (consF (f := interp_argument nat) (x := Other bool) true nilF)).

Eval compute in constructorTy nat (consT Self (consT (Other bool) nilT)).

Definition O_con : constructor := nilT.
Definition S_con : constructor := consT Self nilT.

Eval simpl in constructorIH (fun n => n = n) O_con O.
Eval simpl in constructorIH (fun n => n = n) S_con S.

Definition nil_con : constructor := nilT.
Definition cons_con : constructor := consT (Other nat) (consT Self nilT).

Eval simpl in constructorIH (fun ls => ls = ls) nil_con (@nil nat).
Eval simpl in constructorIH (fun ls => ls = ls) cons_con (@cons nat).

Definition nat_conTypes := consT O_con (consT S_con nilT).
Definition nat_cons : listF (constructorTy nat) nat_conTypes :=
  consF (f := constructorTy nat) (x := O_con) O
  (consF (f := constructorTy nat) (x := S_con) S nilF).

Eval simpl in rect (fun n => n = n) nat_conTypes nat_cons.


(** * Reflected inductive types and examples *)

Record inductive : Type := Ind {
  indConTypes : listT constructor;
  indSelf : Type;
  indCons : listF (constructorTy indSelf) indConTypes;
  indRec : forall (P : indSelf -> Type), rect P indConTypes indCons
}.

Print bool.

Definition boolInd : inductive :=
  Ind
  (consT nilT
    (consT nilT
      nilT))
  (indSelf := bool)
  (consF (f := constructorTy bool) (x := nilT) true
    (consF (f := constructorTy bool) (x := nilT) false nilF))
  bool_rect.

Definition natInd : inductive :=
  Ind
  (consT nilT
    (consT (consT Self nilT)
      nilT))
  (indSelf := nat)
  (consF (f := constructorTy nat) (x := nilT) O
    (consF (f := constructorTy nat) (x := consT Self nilT) S nilF))
  nat_rect.

Definition natListInd : inductive :=
  Ind
  (consT nilT
    (consT (consT (Other nat) (consT Self nilT))
      nilT))
  (indSelf := list nat)
  (consF (f := constructorTy (list nat)) (x := nilT) (@nil nat)
    (consF (f := constructorTy (list nat)) (x := consT (Other nat) (consT Self nilT)) (@cons nat) nilF))
  (@list_rect nat).

Inductive natTree : Set :=
  | Leaf : nat -> natTree
  | Node : natTree -> natTree -> natTree.

Definition natTreeInd : inductive :=
  Ind
  (consT (consT (Other nat) nilT)
    (consT (consT Self (consT Self nilT))
      nilT))
  (indSelf := natTree)
  (consF (f := constructorTy natTree) (x := consT (Other nat) nilT) Leaf
    (consF (f := constructorTy natTree)
      (x := consT Self (consT Self nilT))
      Node nilF))
  natTree_rect.

(** We can't have our cake and eat it, too: *)
(*Definition argumentInd : inductive :=
  Ind
  (consT nilT
    (consT (consT (Other Type) nilT)
      nilT))
  (indSelf := argument)
  (consF (f := constructorTy argument) (x := nilT) Self
    (consF (f := constructorTy argument) (x := consT (Other Type) nilT) Other nilF))
  argument_rect.*)


(** * A generic size function *)

Definition sizeCase (self : Type) (con : constructor)
  (cval : constructorTy self con) (acc : nat)
  : constructorIH (fun _ => nat) con cval.
  induction con; simpl; intros.

  exact (S acc).

  destruct t; intros.

  exact (IHcon (cval x) (acc + H)).

  exact (IHcon (cval x) acc).
Defined.

Definition size (ind : inductive) : indSelf ind -> nat.
  destruct ind; simpl.
  generalize (indRec0 (fun _ => nat)); clear indRec0; intro indRec0.
  
  induction indConTypes0; simpl in *; intuition.
  
  generalize (IHindConTypes0
    (tailF indCons0)
    (indRec0 (sizeCase _ _ _ O))
    X); trivial.
Defined.

Eval compute in size boolInd false.
Eval compute in size boolInd true.
Eval compute in size boolInd.

Eval compute in size natInd O.
Eval compute in size natInd (S O).
Eval compute in size natInd.

Eval compute in size natListInd nil.
Eval compute in size natListInd (1 :: nil).
Eval compute in size natListInd (1 :: 2 :: nil).
Eval compute in size natListInd.

Eval compute in size natTreeInd (Leaf 5).
Eval compute in size natTreeInd (Node (Leaf 5) (Leaf 8)).
Eval compute in size natTreeInd (Node (Node (Leaf 5) (Leaf 6)) (Leaf 8)).
Eval compute in size natTreeInd.


Theorem natList_size : forall x ls, size natListInd (x :: ls) = S (size natListInd ls).
  reflexivity.
Qed.


(** * A generic fold function *)

Definition fold (ind : inductive) (A : Type)
  (f : forall (con : constructor) (cval : constructorTy (indSelf ind) con),
    A -> constructorIH (fun _ => A) con cval)
  : A -> indSelf ind -> A.
  destruct ind; simpl.
  intros A f i.
  generalize (indRec0 (fun _ => A)); clear indRec0; intro indRec0.

  induction indConTypes0; simpl in *; intros.

  exact (indRec0 X).

  generalize (IHindConTypes0
    (tailF indCons0)
    (indRec0 (f _ _ i))).
  intro IH.
  exact (IH X).
Defined.

Definition size' (ind : inductive) : indSelf ind -> nat :=
  fold ind (sizeCase _) O.

Eval compute in size' boolInd.
Eval compute in size' natInd.
Eval compute in size' natListInd.
Eval compute in size' natTreeInd.

Definition depthCase (self : Type) (con : constructor)
  (cval : constructorTy self con) (acc : nat)
  : constructorIH (fun _ => nat) con cval.
  induction con; simpl; intros.

  exact (S acc).

  destruct t; intros.

  exact (IHcon (cval x) (max acc H)).

  exact (IHcon (cval x) acc).
Defined.

Definition depth (ind : inductive) : indSelf ind -> nat :=
  fold ind (depthCase _) O.

Eval compute in depth boolInd.
Eval compute in depth natInd.
Eval compute in depth natListInd.
Eval compute in depth natTreeInd.

Definition inorderCase (self : Type) (con : constructor)
  (cval : constructorTy self con) (acc : listT self)
  : constructorIH (fun _ => listT self) con cval.
  induction con; simpl; intros.

  exact acc.

  destruct t; intros.

  exact (IHcon (cval x) (appT acc (consT x X))).

  exact (IHcon (cval x) acc).
Defined.

Definition inorder (ind : inductive) : indSelf ind -> listT (indSelf ind) :=
  fold ind (inorderCase (self := _)) nilT.

Eval compute in inorder boolInd false.
Eval compute in inorder boolInd true.
Eval compute in inorder boolInd.

Eval compute in inorder natInd O.
Eval compute in inorder natInd (S O).
Eval compute in inorder natInd (S (S O)).
Eval compute in inorder natInd.

Eval compute in inorder natListInd nil.
Eval compute in inorder natListInd (1 :: nil).
Eval compute in inorder natListInd (1 :: 2 :: nil).
Eval compute in inorder natListInd (1 :: 2 :: 3 :: nil).
Eval compute in inorder natListInd.

Eval compute in inorder natTreeInd (Leaf 5).
Eval compute in inorder natTreeInd (Node (Leaf 5) (Leaf 8)).
Eval compute in inorder natTreeInd (Node (Node (Leaf 1) (Leaf 2)) (Node (Leaf 3) (Leaf 4))).
Eval compute in inorder natTreeInd (Node (Node (Node (Leaf 0) (Leaf 1)) (Leaf 2)) (Node (Leaf 3) (Leaf 4))).
Eval compute in inorder natTreeInd.

