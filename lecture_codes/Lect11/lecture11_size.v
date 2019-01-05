Require Import lecture11.

Section Nasty.
  Variables A B C D E F G H I J K L M N O P Q R S T U V W X Y Z : Prop.

  (*Theorem t6 : A /\ B /\ C /\ D /\ E /\ F /\ G /\ H /\ I /\ J /\ K /\ L /\ M
    /\ N /\ O /\ P /\ Q /\ R /\ S /\ T /\ U /\ V /\ W /\ X /\ Y /\ Z
    -> Z.
    prover.
  Qed.*)

  Theorem t7 : (A \/ B) /\ (C \/ D) /\ (E \/ F) /\ (G \/ H) /\ (I \/ J)
    /\ (K \/ L) /\ (M \/ N)
    -> (B \/ A) /\ (D \/ C) /\ (F \/ E) /\ (H \/ G) /\ (J \/ I)
    /\ (L \/ K) /\ (N \/ M).
    prover.
  Qed.

  Print t7.
End Nasty.

