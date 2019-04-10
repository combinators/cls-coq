(* Fix_F with heterogenious type dependent arguments *)

Section DependentFixPoint.
  Variable A: Type.
  Variable R: A -> A -> Prop.
  Variable Rwf: well_founded R.
  
  Variable T: Type.
  Variable TT: T -> Type.
  
  Variable P : forall (t: T), TT t -> Type.
  Variable f : forall (t: T), TT t -> A.
  Variable F : forall (t : T),
      forall (x : TT t),
        (forall (t' : T) (y : TT t'),
            R (f t' y) (f t x) -> P t' y) -> P t x.

  Fixpoint Fix_F (t: T) (x: TT t) (a: Acc R (f t x)) : P t x :=
    F t x (fun (t' : T) (y : TT t') (h : R (f t' y) (f t x)) =>
             Fix_F t' y (Acc_inv a h)).

  Definition DepFix (t: T) (x: TT t) := Fix_F t x (Rwf (f t x)).


  Hypothesis
    F_ext :
      forall (t: T) (x: TT t) (g g': forall (t': T) (y: TT t'), R (f t' y) (f t x) -> P t' y),
        (forall (t': T) (y: TT t') (p: R (f t' y) (f t x)), g t' y p = g' t' y p) -> F t x g = F t x g'.

  Fixpoint Fix_F_inv (t: T) (x: TT t) (r s: Acc R (f t x)) { struct r}: Fix_F t x r = Fix_F t x s.
  Proof.
    destruct r.
    destruct s.
    simpl.
    match goal with
    |[|- F t x ?lhs = F t x ?rhs ] =>
     apply (F_ext t x lhs rhs)
    end.
    intros.
    apply Fix_F_inv.
  Qed.
  
End DependentFixPoint.    