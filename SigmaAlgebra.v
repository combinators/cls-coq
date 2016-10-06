Require Import Coq.Vectors.Vector.
Require Import Coq.Classes.RelationClasses.

Class Signature (Sort: Set -> Set): Type :=
  { Operation: Set;
    arity: Operation -> nat;
    variables: forall o: Operation, Set;
    domain: forall o: Operation, t (Sort (variables o)) (arity o);
    range: forall o: Operation, Sort (variables o)
  }.

Definition EmptySet: Set := False.
  
Section Algebraic.
  Variable Sort: Set -> Set.
  Variable subsorts: Sort EmptySet -> Sort EmptySet -> Prop.
  
  Context `{Sigma: `{Signature Sort}, subsorts_pre: `{PreOrder subsorts} }.

  
  Section WithCarrier.
    Variable Carrier: Sort EmptySet -> Type.
    
    Fixpoint F_args {n : nat} {Var: Set} (S : Sort Var -> Sort EmptySet)
             (argSorts : t (Sort Var) n) {struct argSorts}: Type :=
      match argSorts with
      | nil _ => unit
      | cons _ x _ xs => Carrier (S x) * F_args S xs
      end.

    Structure F (s : Sort EmptySet): Type :=
      mkF { op: Operation;
            subst: Sort (variables op) -> Sort EmptySet;
            args: F_args subst (domain op);
            subsort: subsorts s (subst (range op)) }.
    
    Definition SigmaAlgebra: Type := forall (s: Sort EmptySet), F s -> Carrier s.  
    Definition SigmaCoAlgebra: Type := forall (s: Sort EmptySet), Carrier s -> F s.
  End WithCarrier.
  
  Definition fmap_args
             C C' {Var} (S: Sort Var -> Sort EmptySet) {n} (argSorts: t (Sort Var) n)
             (f: forall s, C s -> C' s):
    F_args C S argSorts -> F_args C' S argSorts :=
    (fix fmap_args_rec n (argSorts: t (Sort Var) n): F_args C S argSorts -> F_args C' S argSorts := 
       match argSorts as argSorts' return
             F_args C S argSorts' -> F_args C' S argSorts'
       with
       | nil _ => fun x => x
       | cons _ x _ xs => fun args => (f (S x) (fst args), fmap_args_rec _ xs (snd args))
       end) _ argSorts.

  Proposition F_hom C C' (f : forall s, C s -> C' s): forall s, F C s -> F C' s.
  Proof.
    intros s x.
    destruct x.
    eapply mkF. 
    - eapply fmap_args; eassumption.
    - eassumption.
  Qed.
End Algebraic.

