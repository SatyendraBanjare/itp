Require Import Tactics.

Require Import Pointer AndersenModel AndersenSound AndersenIter.

Lemma incl_intersect2 : forall s1 t1 s2 t2,
  AllocSet.incl s1 s2 = true
  -> AllocSet.incl t1 t2 = true
  -> AllocSet.incl (AllocSet.intersect s1 t1)
  (AllocSet.intersect s2 t2) = true.
  intros.
  generalize (AllocSet.incl_ok (AllocSet.intersect s1 t1) (AllocSet.intersect s2 t2));
    intuition.
  apply H3; intuition.
  destruct (AllocSet.In_intersect H1).
  caseEq (AllocSet.In x (AllocSet.intersect s2 t2)); intuition.
  destruct (AllocSet.In_intersect' H6); eauto.
Qed.

Definition andersen : mustNotAlias_procedure.
  red; intros.
  destruct (fixed_point (abstractProgram program)) as [fp Hfp].

  caseEq (AllocSet.incl (AllocSet.intersect
    (VarMap.sel (avars fp) v1) (VarMap.sel (avars fp) v2))
  AllocSet.empty); intro Hincl.

  apply NotAliased.
  apply andersen_sound; intuition.
  match goal with
    | [ |- ?X = false ] => caseEq X
  end; trivial; intro Heq.

  wrong.
  assert (approx' abs fp); auto.
  destruct H0.
  assert (AllocSet.In site AllocSet.empty = true).
  apply AllocSet.incl_In with (AllocSet.intersect (VarMap.sel (avars fp) v1)
    (VarMap.sel (avars fp) v2)); auto.
  apply AllocSet.incl_In with (AllocSet.intersect (VarMap.sel (avars abs) v1)
    (VarMap.sel (avars abs) v2)); auto.
  apply incl_intersect2; auto.

  rewrite AllocSet.In_empty in H0; discriminate.

  apply Unknown.
Qed.
