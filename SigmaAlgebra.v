Require Import Coq.Vectors.Vector.

Class Signature (Sort: Set): Type :=
  { Operation: Set;
    arity: Operation -> nat;
    domain: forall o: Operation, t Sort (arity o);
    range: forall o: Operation, Sort
  }.
                               