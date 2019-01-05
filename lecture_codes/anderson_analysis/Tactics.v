Ltac mySubst := repeat match goal with
			 | [ H : ?X = ?Y |- _ ] => subst X || subst Y
		       end.

Ltac wrong := assert False; [idtac | tauto].

Ltac simplify := repeat progress (
  repeat match goal with
	   | [ H : ?E = ?E |- _ ] => clear H
	 end;
  simpl in *; mySubst; intuition; intuition eauto;
    try omega; try (wrong; omega); try discriminate).

Ltac clear_all := repeat match goal with
			   | [ H : _ |- _ ] => clear H
			 end.

Ltac caseEq v := generalize (refl_equal v); pattern v at -1; case v.
