Require Import List.

Require Import SigmaAlgebra.

Module Type SignatureWithSortSubcomponentProperty
       (Import SigSpec: SignatureSpec)
       (Import Alg: Algebraic(SigSpec)).

  Parameter subcomponents: Operation -> list (Sort EmptySet).
  Parameter Carrier: Sort EmptySet -> Type.
  Parameter Carrier_eq: forall s s', Carrier s -> Carrier s' -> Prop.
  
  Parameter SubcomponentProperty :
    forall s f,
      { f' : F Carrier s
      | F_eq Carrier Carrier_eq s s f f' /\
        forall alpha, exists op, In (subst Carrier s f' alpha) (subcomponents op) }.

  
  
  
End SignatureWithSubsortProperty.
  