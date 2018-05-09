Require Import Coq.Vectors.Vector.

Require Import Cantor.

Class FunctionSpace (S: Type) (A B: Type): Type :=
  { take : S -> (A -> B);
    extensional : forall e1 e2, (forall x, take e1 x = take e2 x) -> e1 = e2 }.

Section TableSpaceDef.
  Variable A B : Type.
  Variable AFinite: Finite A.

  Definition takeVect: (t B (@cardinality A AFinite)) -> A -> B :=
    fun e a => nth e (toFin a).

  Lemma takeVectExt: forall e1 e2, (forall x, takeVect e1 x = takeVect e2 x) -> e1 = e2.
  Proof.
    intros e1 e2 prf.
    apply eq_nth_iff.
    intros x y xy_eq.
    rewrite xy_eq.
    rewrite <- (toFromFin_id y).
    apply prf.
  Qed.
End TableSpaceDef.

Instance TableSpace (A B: Type) `(AFinite : Finite A): FunctionSpace (t B (@cardinality A AFinite)) A B :=
  { take := takeVect A B AFinite;
    extensional := takeVectExt A B AFinite }.

Instance ConstantSpace (A B: Type) (x: B): FunctionSpace unit A B :=
  { take := fun _ _ => x;
    extensional := fun e1 e2 _ => match e1, e2 with tt, tt => eq_refl end }.

Instance IdSpace (A: Type): FunctionSpace unit A A :=
  { take := fun _ x => x;
    extensional := fun e1 e2 _ => match e1, e2 with tt, tt => eq_refl end }.
