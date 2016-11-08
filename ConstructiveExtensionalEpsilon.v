Require Import Coq.Logic.ConstructiveEpsilon.

Section ConstructiveExtensionalGroundEpsilon.

  Variable A B : Type.
  Variable f : (A -> B) -> nat.
  Variable g : nat -> (A -> B).

  Hypothesis gof_eq_id : forall (h : A -> B) (x: A), g (f h) x = h x.

  Variable P : (A -> B) -> Prop.
  Hypothesis P_decidable : forall h : A -> B, {P h} + {~ P h}.
  Hypothesis P_extensional: forall h h', (forall x, h x = h' x) -> P h -> P h'.

  Definition P' (x : nat) : Prop := P (g x).

  Lemma P'_decidable : forall n : nat, {P' n} + {~ P' n}.
  Proof.
    unfold P'.
    intro n.
    apply P_decidable.
  Qed.
    
  Lemma constructive_extensional_indefinite_ground_description : (exists h : A -> B, P h) -> {h : A -> B | P h}.
  Proof.
    intro exprf.
    assert (exn: exists n, P' n).
    { destruct exprf as [ h Ph ].
      exists (f h).
      unfold P'.
      apply (P_extensional h).
      - intro x; apply eq_sym; apply gof_eq_id.
      - assumption. }
    destruct (constructive_indefinite_ground_description_nat _ P'_decidable exn) as [ n P'n ].
    exists (g n); exact P'n.
  Qed.

End ConstructiveExtensionalGroundEpsilon.
