Section propositional.
  Variables P Q R : Prop.

  Definition term1 : (P -> Q -> R) -> (Q -> P -> R) :=
    fun f : (P -> Q -> R) =>
      fun q : Q => fun p : P => f p q.

  Definition term2 : P /\ Q -> R \/ P :=
    fun x : (P /\ Q) => or_intror R (proj1 x).

  Definition term3 : P \/ Q -> (Q -> P) -> P :=
    fun pq : (P \/ Q) => fun f : (Q -> P) =>
      or_ind
      (fun H : P => H)
      (fun H : Q => f H)
      pq.

  Definition term4 : P -> ~~P :=
    fun p : P => fun np : ~P => np p.
End propositional.

