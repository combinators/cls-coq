Require Import Coq.Lists.List.
Require Import Coq.Vectors.Fin.
Require Import Coq.Vectors.Vector.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Eqdep_dec.
Import EqNotations.

Require Import SigmaAlgebra.
Require Import VarianceLabeledTree.
Require Import SortEmbeddings.
Require Import VectorQuantification.
Require Import Cantor.

Inductive Ty : Set :=
| Ty_Nat : Ty
| Ty_Arr : Ty -> Ty -> Ty
| Ty_Prod : Ty -> Ty -> Ty
| Ty_Unit : Ty
| Ty_Box : Ty -> Ty.

Inductive Term : Set :=
| T_Var : nat -> Term
| T_Lam : Term -> Term
| T_App : Term -> Term -> Term
| T_Box : Term -> Term
| T_Unbox : nat -> Term -> Term
| T_Pair : Term -> Term -> Term
| T_Fst : Term -> Term
| T_Snd : Term -> Term
| T_Unit : Term
| T_Zero : Term
| T_Succ : Term -> Term
| T_Case : Term -> Term -> Term -> Term
| T_Fix : Term -> Term.

Definition Context := list Ty.
Definition ContextStack := list Context.

Import ListNotations.

Inductive MiniMLBox: ContextStack -> Term -> Ty -> Prop :=
| TPI_Var : forall Gamma Psi n A,
    nth_error Gamma n = Some A ->
    MiniMLBox (Gamma :: Psi) (T_Var n) A
| TPI_Lam : forall Gamma Psi M A B,
    MiniMLBox ((A :: Gamma) :: Psi) M B ->
    MiniMLBox (Gamma :: Psi) (T_Lam M) (Ty_Arr A B)
| TPI_App : forall Gamma Psi M N A B,
    MiniMLBox (Gamma :: Psi) M (Ty_Arr A B) ->
    MiniMLBox (Gamma :: Psi) N A ->
    MiniMLBox (Gamma :: Psi) (T_App M N) B
| TPI_Box : forall Gamma Psi M A,
    MiniMLBox ([] :: Gamma :: Psi) M A ->
    MiniMLBox (Gamma :: Psi) (T_Box M) (Ty_Box A)
| TPI_Unbox : forall Gamma Psi Gammas M A,
    MiniMLBox (Gamma :: Psi) M (Ty_Box A) ->
    MiniMLBox (Gammas ++ (Gamma :: Psi)) (T_Unbox (length Gammas) M) A
| TPI_Pair : forall Gamma Psi M1 M2 A1 A2,
    MiniMLBox (Gamma :: Psi) M1 A1 ->
    MiniMLBox (Gamma :: Psi) M2 A2 ->
    MiniMLBox (Gamma :: Psi) (T_Pair M1 M2) (Ty_Prod A1 A2)
| TPI_Fst : forall Gamma Psi M A1 A2,
    MiniMLBox (Gamma :: Psi) M (Ty_Prod A1 A2) ->
    MiniMLBox (Gamma :: Psi) (T_Fst M) A1
| TPI_Snd : forall Gamma Psi M A1 A2,
    MiniMLBox (Gamma :: Psi) M (Ty_Prod A1 A2) ->
    MiniMLBox (Gamma :: Psi) (T_Snd M) A2
| TPI_Unit : forall Gamma Psi,
    MiniMLBox (Gamma :: Psi) T_Unit Ty_Unit
| TPI_Z : forall Gamma Psi,
    MiniMLBox (Gamma :: Psi) T_Zero Ty_Nat
| TPI_S : forall Gamma Psi M,
    MiniMLBox (Gamma :: Psi) M Ty_Nat ->
    MiniMLBox (Gamma :: Psi) (T_Succ M) Ty_Nat
| TPI_Case : forall Gamma Psi M1 M2 M3 A,
    MiniMLBox (Gamma :: Psi) M1 Ty_Nat ->
    MiniMLBox (Gamma :: Psi) M2 A ->
    MiniMLBox ((Ty_Nat :: Gamma) :: Psi) M3 A ->
    MiniMLBox (Gamma :: Psi) (T_Case M1 M2 M3) A
| TPI_Fix : forall Gamma Psi M A,
    MiniMLBox ((A :: Gamma) :: Psi) M A ->
    MiniMLBox (Gamma :: Psi) (T_Fix M) A.

Fixpoint T_Lift (n: nat) (M: Term) : Term :=
  match n with
  | 0 => M
  | S n' => T_Box (T_Lift n' M)
  end.

Fixpoint Ty_Lift (n: nat) (A: Ty): Ty :=
  match n with
  | 0 => A
  | S n' => Ty_Box (Ty_Lift n' A)
  end.

Lemma Ty_Lift_comm: forall n A, Ty_Lift n (Ty_Box A) = Ty_Lift (S n) A.
Proof.
  intro n.
  induction n as [ | n IH ].
  - intro; reflexivity.
  - intro A.
    simpl.
    rewrite IH.
    reflexivity.
Qed.
                                                          
Lemma TPI_Lift: forall Gamma Psi n M A,
    MiniMLBox ((List.repeat [] n) ++ (Gamma :: Psi)) M A ->
    MiniMLBox (Gamma :: Psi) (T_Lift n M) (Ty_Lift n A).
Proof.
  intros Gamma Psi n.
  revert Gamma Psi.
  induction n as [ | n IH ]; intros Gamma Psi M A.
  - intros; simpl; assumption.
  - intro prf.
    apply TPI_Box.
    fold (T_Lift n M).
    fold (Ty_Lift n A).
    assert (repeat_app: forall A n (x: A), List.repeat x (S n) = List.repeat x n ++ [x]).
    { clear ...
      intros A n x.
      induction n as [ | n IH ].
      - reflexivity.
      - simpl.
        simpl in IH.
        rewrite IH.
        reflexivity. }
    rewrite repeat_app in prf.
    rewrite <- List.app_assoc in prf.
    apply IH.
    exact prf.
Qed.

Fixpoint T_Unlift (n: nat) (M : Term) : Term :=
  match n with
  | 0 => M
  | S n' => T_Unbox 1 (T_Unlift n' M)
  end.

Lemma TPI_Unlift: forall Gamma Psi n M A,
    MiniMLBox (Gamma :: Psi) M (Ty_Lift n A) ->
    MiniMLBox ((List.repeat [] n) ++ (Gamma :: Psi)) (T_Unlift n M) A.
Proof.
  intros Gamma Psi n.
  revert Gamma Psi.
  induction n as [ | n IH ]; intros Gamma Psi M A.
  - simpl; intro; assumption.
  - intro prf.
    simpl.
    destruct n.
    + simpl.
      apply (TPI_Unbox _ _ [[]]).
      assumption.
    + simpl.
      apply (TPI_Unbox _ _ [[]]).
      apply IH.
      assert (Ty_Lift_comm: forall A n, Ty_Lift (S n) A = Ty_Lift n (Ty_Box A)).
      { clear ...
        intros A n.
        induction n as [ | n IH ].
        - reflexivity.
        - simpl.
          rewrite <- IH.
          reflexivity. }
      rewrite Ty_Lift_comm in prf.
      assumption.
Qed.

Lemma TPI_Shift: forall M A Gamma Psi Delta, MiniMLBox (Gamma :: Psi) M A -> MiniMLBox (Gamma :: (Psi ++ Delta)) M A.
Proof.
  intros M.
  induction M as [ | | | M IH | n M IH | | | | | | | | ];
    intros A Gamma Psi Delta Mprf.
  - inversion Mprf.
    apply TPI_Var.
    assumption.
  - inversion Mprf.
    apply TPI_Lam.
    auto.
  - inversion Mprf.
    eapply TPI_App; eauto.
  - inversion Mprf.
    apply TPI_Box.
    apply (IH _ [] (Gamma :: Psi)).
    assumption.
  - inversion Mprf as [ | | | | Gamma' Psi' Gammas M' A' MBoxPrf ctxtEq | | | | | | | | ].
    rewrite List.app_comm_cons.
    rewrite <- ctxtEq.
    rewrite <- (List.app_assoc Gammas).
    apply TPI_Unbox.
    apply IH.
    assumption.
  - inversion Mprf.
    apply TPI_Pair; auto.
  - inversion Mprf.
    eapply TPI_Fst; eauto.
  - inversion Mprf.
    eapply TPI_Snd; eauto.
  - inversion Mprf.
    apply TPI_Unit.
  - inversion Mprf.
    apply TPI_Z.
  - inversion Mprf.
    apply TPI_S; auto.
  - inversion Mprf.
    apply TPI_Case; auto.
  - inversion Mprf.
    apply TPI_Fix; auto.
Qed.    

Example T_MApp (n: nat) : Term := T_Lam (T_Lam (T_Lift n (T_App (T_Unlift n (T_Var 1)) (T_Unlift n (T_Var 0))))).
 
Example MApply: forall n A B,
    MiniMLBox [[]] (T_MApp (S n)) (Ty_Arr (Ty_Lift (S n) (Ty_Arr A B)) (Ty_Arr (Ty_Lift (S n) A) (Ty_Lift (S n) B))).
Proof.
  intros n A B.
  unfold T_MApp.
  apply TPI_Lam.
  apply TPI_Lam.
  apply TPI_Lift.
  simpl.
  apply (TPI_App _ _ _ _ A).
  - rewrite (eq_refl : T_Unbox 1 (T_Unlift n (T_Var 1)) = T_Unlift (S n) (T_Var 1)).
    rewrite  List.app_comm_cons.
    rewrite (eq_refl : ([] :: List.repeat [] n) = @List.repeat (list Ty) [] (S n)).
    apply TPI_Unlift.
    apply TPI_Var.
    reflexivity.
  - rewrite (eq_refl : T_Unbox 1 (T_Unlift n (T_Var 0)) = T_Unlift (S n) (T_Var 0)).
    rewrite  List.app_comm_cons.
    rewrite (eq_refl : ([] :: List.repeat [] n) = @List.repeat (list Ty) [] (S n)).
    apply TPI_Unlift.
    apply TPI_Var.
    reflexivity.
Qed.

Example T_Power :=
  T_Fix (T_Lam (T_Case (T_Var 0)
                       (T_Box (T_Succ T_Zero))
                       (T_Box (T_Succ (T_Unbox 1 (T_App (T_Var 2) (T_Var 0))))))).

Example Power: MiniMLBox [[]] T_Power (Ty_Arr Ty_Nat (Ty_Box Ty_Nat)).
Proof.
  unfold T_Power.
  apply TPI_Fix.
  apply TPI_Lam.
  apply TPI_Case.
  - apply TPI_Var.
    reflexivity.
  - apply TPI_Box.
    apply TPI_S.
    apply TPI_Z.
  - apply TPI_Box.
    apply TPI_S.
    apply (TPI_Unbox _ _ [[]]).
    eapply TPI_App.
    + apply TPI_Var.
      reflexivity.
    + apply TPI_Var.
      reflexivity.
Qed.

Fixpoint Ty_dec_eq (A B : Ty): { A = B } + { A <> B }.
Proof.
  destruct A as [ | A1 A2 | A1 A2 | | A ];
    destruct B as [ | B1 B2 | B1 B2 | | B ];
    try solve [ left; reflexivity
              | right; intro devil; inversion devil
              | destruct (Ty_dec_eq A B) as [ eq | ineq ];
                [ left; rewrite eq; reflexivity
                | right; intro devil; inversion devil; contradiction
                ]
              | destruct (Ty_dec_eq A1 B1) as [ eq1 | ineq1 ];
                [ destruct (Ty_dec_eq A2 B2) as [ eq2 | ineq2 ];
                  [ left; rewrite eq1; rewrite eq2; reflexivity
                  | right; intro devil; inversion devil; contradiction
                  ]
                | right; intro devil; inversion devil; contradiction
                ]
              ].
Defined.                                              

Fixpoint Term_dec_eq (M N: Term): { M = N } + { M <> N }. 
Proof.
  destruct M as [ x | M | M1 M2 | M | m M | M1 M2 | M | M | | | M | M1 M2 M3 | M ];
    destruct N as [ y | N | N1 N2 | N | n N | N1 N2 | N | N | | | N | N1 N2 N3 | N ];
    try solve
        [ left; reflexivity
        | right; intro devil; inversion devil
        | destruct (Term_dec_eq M N) as [ eq | ineq ];
          [ rewrite eq; left; reflexivity
          | right; intro devil; inversion devil; contradiction ]
        | destruct (Term_dec_eq M1 N1) as [ eq1 | ineq1 ];
          [ rewrite eq1;
            destruct (Term_dec_eq M2 N2) as [ eq2 | ineq2 ];
            [ rewrite eq2; left; reflexivity | right; intro devil; inversion devil; contradiction ]
          | right; intro devil; inversion devil; contradiction ]
        ].
  - destruct (Nat.eq_dec x y) as [ eq | ineq ];
      [ rewrite eq; left; reflexivity
      | right; intro devil; inversion devil; contradiction ].
  - destruct (Nat.eq_dec m n) as [ eq1 | ineq1 ];
      [ rewrite eq1;
        destruct (Term_dec_eq M N) as [ eq2 | ineq2 ];
        [ rewrite eq2; left; reflexivity | right; intro devil; inversion devil; contradiction ]
      | right; intro devil; inversion devil; contradiction ].
  - destruct (Term_dec_eq M1 N1) as [ eq1 | ineq1 ];
      [ rewrite eq1;
        destruct (Term_dec_eq M2 N2) as [ eq2 | ineq2 ];
        [ rewrite eq2;
          destruct  (Term_dec_eq M3 N3) as [ eq3 | ineq3 ];
          [ left; rewrite eq3; reflexivity | right; intro devil; inversion devil; contradiction ]
        | right; intro devil; inversion devil; contradiction ]
      | right; intro devil; inversion devil; contradiction ].
Defined.

Section WithImplementations.
  Variable Terms : list Term. 
  Variable Proofs : forall M, List.In M Terms -> { A : Ty | MiniMLBox [[]] M A }.

  Fixpoint BoxLevel (A: Ty) : nat :=
    match A with
    | Ty_Box A' => S (BoxLevel A')
    | Ty_Arr A' B => max (BoxLevel A') (BoxLevel B)
    | _ => 0
    end.
  
  Inductive ApplicativeFragment (maxBox: nat): Term -> Ty -> Prop :=
  | A_Impl : forall M (MIn: List.In M Terms),
      BoxLevel (proj1_sig (Proofs M MIn)) <= maxBox ->
      ApplicativeFragment maxBox M (proj1_sig (Proofs M MIn))
  | A_Box : forall M A,
      ApplicativeFragment maxBox M A ->
      BoxLevel (Ty_Box A) <= maxBox ->
      ApplicativeFragment maxBox (T_Box M) (Ty_Box A)
  | A_Unbox : forall M A,
      ApplicativeFragment maxBox M (Ty_Box A) ->
      ApplicativeFragment maxBox (T_Unbox 0 M) A
  | A_App : forall M N A B,
      ApplicativeFragment maxBox M (Ty_Arr A B) ->
      ApplicativeFragment maxBox N A ->
      ApplicativeFragment maxBox (T_App M N) B.

  Lemma ApplicativeFragment_empty:
    forall n M A,
      length Terms = 0 ->
      ApplicativeFragment n M A ->
      False.
  Proof.
    intros n M A lenprf apfrag.
    induction apfrag as [ M A inprf | | | ];
      try solve [ contradiction ].
    - destruct Terms; [ contradiction | inversion lenprf ].
  Qed.

 
    

  Definition IsLiftable n (toA: Ty) (B: Ty): Prop :=
    toA = Ty_Lift n B.
  
  Fixpoint IsSrc (ofA: Ty) (B: Ty): Prop :=
    match ofA with
    | Ty_Arr A ofA' => A = B \/ IsSrc ofA' B
    | Ty_Box ofA' => IsSrc ofA' B
    | _ => False
    end.

  Fixpoint IsTgt (ofA: Ty) (B: Ty): Prop :=
    (ofA = B) \/ (match ofA with
                 | Ty_Arr _ ofA' => IsTgt ofA' B
                 | Ty_Box ofA' => IsTgt ofA' B
                 | _ => False
                 end).

  Lemma IsTgt_tgt: forall A B C, IsTgt A (Ty_Arr B C) -> IsTgt A C.
  Proof.
    intro A.
    induction A;
      intros B C isTgt;
      inversion isTgt as [ eq | isTgt' ];
      try solve [ inversion eq
                | contradiction ].
    - rewrite eq.
      right; destruct C; left; reflexivity.
    - right; eauto.
    - right; eauto.
  Qed.

  Lemma IsTgt_trans: forall A B C, IsTgt A B -> IsTgt B C -> IsTgt A C.
  Proof.
    intro A.
    induction A;
      intros B C tgtAB;
      inversion tgtAB as [ eq | tgtRest ];
      solve [
          contradiction
        | inversion eq; intro; assumption
        | intro; right; eauto
        ].
  Qed.

  Lemma ApplicativeFragment_noAbstraction:
    forall n M A B, ApplicativeFragment n M (Ty_Arr A B) ->
               exists M' M'In, IsTgt (proj1_sig (Proofs M' M'In)) (Ty_Arr A B).
  Proof.
    intros n M A B.
    set (C := Ty_Arr A B).
    unfold C at 2.
    generalize (or_introl (eq_refl _) : IsTgt C (Ty_Arr A B)).
    generalize C.
    clear C.
    revert A B.
    induction M as [ | | M1 IHM1 M2 IHM2 | M IH | n' M IH | | | | | | | | ];
      intros A B C isTgt appfrag;
      inversion appfrag as [ M' MIn level M'eq Ceq
                           | M' A' appfrag' level Meq Ceq
                           | M' A' appfrag' [ nEq Meq ] Ceq
                           | M1' M2' A' B' appfrag1' appfrag2' ];
      try solve [
            rewrite <- Ceq in isTgt;
            eexists; exists MIn; exact isTgt ].
    - apply (IHM1 _ _ (Ty_Arr A' C) (or_intror _ isTgt) appfrag1').
    - rewrite <- Ceq in isTgt.
      inversion isTgt as [ devil | isTgt' ];
        [ inversion devil | ].
      apply (IH _ _ _ isTgt' appfrag').
    - apply (IH _ _ (Ty_Box C) (or_intror _ isTgt) appfrag').
  Qed.

  Lemma ApplicativeFragment_BoxTgt:
    forall n M A, ApplicativeFragment n M (Ty_Box A) ->
             exists M' M'In A' n', IsTgt (proj1_sig (Proofs M' M'In)) A' /\ IsLiftable (S n') (Ty_Box A) A'.
  Proof.
    intros n M A.
    set (C := Ty_Box A).
    unfold C at 2.
    assert (isTgt: IsTgt C A).
    { unfold C; right; destruct A; left; reflexivity. }
    revert isTgt.
    generalize C.
    clear C.
    revert A.
    induction M as [ | | M1 IHM1 M2 IHM2 | M IH | n' M IH | | | | | | | | ];
      intros A C isTgt appfrag;
      inversion appfrag as [ M' MIn level M'eq Ceq
                           | M' A' appfrag' level Meq Ceq
                           | M' A' appfrag' [ nEq Meq ] Ceq
                           | M1' M2' A' B' appfrag1' appfrag2' ];
      try solve [
            rewrite <- Ceq in isTgt;
            eexists; exists MIn, A, 0; split; [ exact isTgt | reflexivity ]].
    - apply (IHM1 _ (Ty_Arr A' C) (or_intror _ isTgt) appfrag1').
    - rewrite <- Ceq in isTgt.
      inversion isTgt as [ eq | isTgt' ].
      + assert (isTgt' : IsTgt A' A').
        { destruct A'; left; reflexivity. }
        destruct (IH _ _ isTgt' appfrag') as [ M'' [ M'In [ A'' [ n' [ isTgt'' isLiftable ] ] ] ] ].
        eexists; exists M'In, A'', (S n'); split.
        * assumption.
        * rewrite <- eq.
          unfold IsLiftable.
          rewrite isLiftable.
          reflexivity.
      + apply (IH _ _ isTgt' appfrag').
    - apply (IH _ (Ty_Box C) (or_intror _ isTgt) appfrag').
  Qed.

  Lemma ApplicativeFragment_level:
    forall n M A, ApplicativeFragment n M A -> BoxLevel A <= n.
  Proof.
    intros n M A appfrag.
    induction appfrag.
    - assumption.
    - assumption.
    - etransitivity; [ apply le_S; reflexivity | eassumption ].
    - etransitivity; [ eapply Nat.le_max_r | eassumption ].
  Qed.
    
  Inductive Op :=
  | OP_Use: forall M, List.In M Terms -> Op
  | OP_Box: Op
  | OP_Unbox: Op
  | OP_Apply : Op.

  Definition arity (op: Op): nat :=
    match op with
    | OP_Use _ _ => 0
    | OP_Box => 1
    | OP_Unbox => 1
    | OP_Apply => 2
    end.

  Inductive TyConstr: Set :=
  | TC_Nat : TyConstr
  | TC_Arr : TyConstr
  | TC_Prod : TyConstr
  | TC_Unit : TyConstr
  | TC_Box : TyConstr.

  Lemma TyConstr_eq_dec: forall (x y: TyConstr), { x = y } + { x <> y }.
  Proof.
    intros x y; destruct x; destruct y;
      solve [ left; reflexivity | right; intro devil; inversion devil ].
  Qed.

  Instance TyConstrInfo : LabelInfo TyConstr :=
    {| labelArity :=
         fun (constr: TyConstr) =>
           match constr with
           | TC_Nat => 0
           | TC_Arr => 2
           | TC_Prod => 2
           | TC_Unit => 0
           | TC_Box => 1
           end;
       successorVariance := fun _ _ => In |}.

  Definition tyConstrOrder := @eq TyConstr.

  Definition tyConstrToNat (ty: TyConstr) : nat :=
    match ty with
    | TC_Nat => 0
    | TC_Arr => 1
    | TC_Prod => 2
    | TC_Unit => 3
    | TC_Box => 4
    end.
  Definition natToTyConstr (n: nat) : TyConstr :=
    match n with
    | 0 => TC_Nat
    | 1 => TC_Arr
    | 2 => TC_Prod
    | 3 => TC_Unit
    | 4 => TC_Box
    | _ => TC_Nat
    end.
  Lemma tyConstrToNat_inj: forall ty, natToTyConstr (tyConstrToNat ty) = ty.
  Proof.
    intro ty.
    unfold tyConstrToNat.
    unfold natToTyConstr.
    destruct ty; reflexivity.
  Qed.
  Instance TyConstr_Countable : Countable TyConstr :=
    {| toNat := tyConstrToNat;
       fromNat := natToTyConstr;
       fromTo_id := tyConstrToNat_inj |}.
  
  Inductive SigVar : Set := alpha | beta | gamma.
  Lemma SigVar_eq_dec: forall (x y: SigVar), { x = y } + { x <> y }.
  Proof.
    intros x y;
      destruct x;
      destruct y;
      solve [ left; reflexivity | right; intro devil; inversion devil ].
  Qed.

  Instance SigVar_Finite : Finite SigVar :=
    {| cardinality := 4;
       toFin := fun x => match x with | alpha => F1 | beta => FS F1 | gamma => FS (FS F1) end;
       fromFin := fun x => match x with | F1 => alpha | Fin.FS F1 => beta | _ => gamma end;
       fromToFin_id := fun x => match x with | alpha => eq_refl | beta  => eq_refl | gamma => eq_refl end |}.

  Definition applyRange : VLTree TyConstr SigVar :=
    (Hole _ _ beta).
  Definition applyDom : t (VLTree TyConstr SigVar) 2 :=
    cons _ (Node _ _ TC_Arr (cons _ (Hole _ _ alpha) _ (cons _ (Hole _ _ beta) _ (nil _))))
         _ (cons _ (Hole _ _ alpha) _ (nil _)).

  Fixpoint typeToSort (ty: Ty) (Var : Set): VLTree TyConstr Var :=
    match ty with
    | Ty_Nat => Node _ _ (TC_Nat) (nil _)
    | Ty_Arr A B =>
      Node _ _ TC_Arr
           (cons _ (typeToSort A Var) _
                 (cons _ (typeToSort B Var) _ (nil _)))
    | Ty_Prod A B =>
      Node _ _ TC_Prod
           (cons _ (typeToSort A Var) _
                 (cons _ (typeToSort B Var) _ (nil _)))
    | Ty_Unit =>
      Node _ _ TC_Unit (nil _)
    | Ty_Box A =>
      Node _ _ TC_Box
           (cons _ (typeToSort A Var) _ (nil _))
    end.
     
  Definition Signature: Signature (VLTree TyConstr) SigVar Op :=
    {| SigmaAlgebra.arity := arity;
       domain :=
         fun op =>
           match op as op' return t (VLTree TyConstr SigVar) (arity op') with
           | OP_Use _ _ => nil _
           | OP_Box => cons _ (Hole _ _ gamma) _ (nil _)
           | OP_Unbox => cons _ (Node _ _ TC_Box (cons _ (Hole _ _ gamma) _ (nil _))) _ (nil _)
           | OP_MApply => applyDom
           end;
       range :=
         fun op =>
           match op with
           | OP_Use M MIn => typeToSort (proj1_sig (Proofs M MIn)) SigVar
           | OP_Box => Node _ _ TC_Box (cons _ (Hole _ _ gamma)_  (nil _))
           | OP_Unbox => Hole _ _ gamma
           | OP_MApply => applyRange
           end |}.  
  
  Fixpoint sortToType (s: VLTree TyConstr EmptySet): Ty :=
    match s with
    | Node _ _ TC_Nat _ => Ty_Nat
    | Node _ _ TC_Arr (cons _ A _ (cons _ B _ _)) =>
      Ty_Arr (sortToType A) (sortToType B)
    | Node _ _ TC_Prod (cons _ A _ (cons _ B _ _)) =>
      Ty_Prod (sortToType A) (sortToType B)
    | Node _ _ TC_Unit _ => Ty_Unit              
    | Node _ _ TC_Box (cons _ A _ _) =>
      Ty_Box (sortToType A)
    | _ => Ty_Nat
    end.

  Lemma sortType_inj: forall ty, sortToType (typeToSort ty _) = ty.
  Proof.
    intro ty.
    induction ty as [ | ? IH1 ? IH2 | ? IH1 ? IH2 | | ? IH ];
      solve [ reflexivity
            | simpl; rewrite IH1; rewrite IH2; reflexivity
            | simpl; rewrite IH; reflexivity ].
  Qed.

  Lemma sortType_sur: forall s, typeToSort (sortToType s) EmptySet = s.
  Proof.
    intro s.
    induction s as [ | l xs IH ]using VLTree_rect'.
    - contradiction.
    - destruct l;
        try solve
            [ simpl;
              apply f_equal;
              apply case0;
              reflexivity
            | simpl;
              generalize (Forall_nth _ _ (ForAll'Forall _ _ IH) Fin.F1);
              generalize (Forall_nth _ _ (ForAll'Forall _ _ IH) (Fin.FS Fin.F1));
              simpl in xs;
              apply (caseS' xs);
              intros A xs';
              apply (caseS' xs');
              intros B xs'';
              simpl;
              intros B_eq A_eq;
              rewrite B_eq;
              rewrite A_eq;
              repeat apply f_equal;
              apply case0;
              reflexivity
            | simpl;
              generalize (Forall_nth _ _ (ForAll'Forall _ _ IH) Fin.F1);
              simpl in xs;
              apply (caseS' xs);
              intros A xs';
              simpl;
              intro A_eq;
              rewrite A_eq;
              repeat apply f_equal;
              apply case0;
              reflexivity ].
  Qed.        

  Lemma typeSort_inj: forall s, (exists A, typeToSort A EmptySet = s) -> typeToSort (sortToType s) _ = s.
  Proof.
    intros s [ A Aeq ].
    rewrite <- Aeq.
    destruct A; rewrite sortType_inj; reflexivity.
  Qed.

  Definition MiniMLBoxCarrier: VLTree TyConstr EmptySet -> Type :=
    fun s => { M : Term | MiniMLBox [[]] M (sortToType s)  }.

  
  Definition max_BoxLevel : nat :=
    (fix max_BoxLevel_rec terms :=
       match terms as terms' return (forall M, List.In M terms' -> { A : Ty | MiniMLBox [[]] M A }) -> nat with
       | [] => fun _ => 0
       | M :: terms' =>
         fun prfs => max (BoxLevel (proj1_sig (prfs M (or_introl (eq_refl M)))))
                      (max_BoxLevel_rec terms' (fun M MIn => prfs M (or_intror MIn)))
       end) Terms Proofs.

  Lemma max_BoxLevel_ge: forall M MIn, BoxLevel (proj1_sig (Proofs M MIn)) <= max_BoxLevel.
  Proof.
    unfold max_BoxLevel.
    generalize Proofs.
    clear Proofs.
    induction Terms as [ | N terms IH ].
    - intros ? ? devil; contradiction.
    - intros proofs M MIn.
      destruct MIn as [ here | there ].
      + rewrite <- Nat.le_max_l.
        revert proofs.
        rewrite here.
        intros; reflexivity.
      + rewrite <- Nat.le_max_r.
        apply (IH (fun M MIn => proofs M (or_intror MIn))).
  Qed.      
  
  Inductive WF: (SigVar -> VLTree TyConstr EmptySet) -> Prop :=
  | WF_Arrow: forall S M MIn,
      IsTgt (proj1_sig (Proofs M MIn)) (Ty_Arr (sortToType (S alpha)) (sortToType (S beta))) ->
      sortToType (S gamma) = Ty_Unit ->
      WF S
  | WF_Box: forall S M MIn A n,
      S alpha = typeToSort (Ty_Unit) EmptySet ->
      S beta = typeToSort (Ty_Unit) EmptySet ->
      IsTgt (proj1_sig (Proofs M MIn)) A ->
      IsLiftable n (sortToType (S gamma)) A ->
      BoxLevel (sortToType (S gamma)) < max_BoxLevel ->
      WF S
  | WF_Default : forall S,
      S alpha = typeToSort (Ty_Unit) EmptySet ->
      S beta = typeToSort (Ty_Unit) EmptySet ->
      S gamma = typeToSort (Ty_Unit) EmptySet ->
      WF S.          

  Fixpoint liftbox_table (A: Ty): list Ty :=
    match A with
    | Ty_Box A' => (Ty_Box A') :: liftbox_table A'
    | A' => A' :: []
    end.

  Lemma liftbox_table_correct: forall A B, List.In B (liftbox_table A) <-> exists n, IsLiftable n A B.
  Proof.
    intro A.
    induction A as [ | A IH1 B' IH2 | A IH1 B' IH2 | | A IH ];
      intro B;
      try solve [ simpl;
                  split;
                  [ intro; exists 0; unfold IsLiftable; simpl; tauto
                  | unfold IsLiftable;
                    intros [ n lift_eq ];
                    destruct n;
                    [ left; assumption
                    | inversion lift_eq ] ] ].
    - simpl.
      split.
      + intros [ found | rec ].
        * exists 0; exact found.
        * destruct (proj1 (IH B) rec) as [ n prf ].
          exists (S n); rewrite prf; reflexivity.
      + intros [ n prf ].
        destruct n as [ | n ].
        * left; exact prf.
        * right; apply (proj2 (IH B)).
          exists n.
          inversion prf as [ prf' ].
          reflexivity.
  Qed.

  Fixpoint tgt_table (A: Ty): list Ty :=
    A :: (match A with
          | Ty_Arr _ B => tgt_table B
          | Ty_Box A' => tgt_table A'
          | _ => []
          end).

  Lemma tgt_table_correct:  forall A B, List.In B (tgt_table A) <-> IsTgt A B.
  Proof.
    intro A.
    induction A as [ | A IH1 B' IH2 | A IH1 B' IH2 | | A IH ];
      intro B; try solve [ simpl; tauto ].      
    - simpl.
      rewrite IH2.
      reflexivity.
    - simpl.
      rewrite IH.
      reflexivity.
  Qed.

  Fixpoint is_arrow (A: Ty): bool :=
    match A with
    | Ty_Arr _ _ => true
    | _ => false
    end.

  Lemma is_arrow_spec: forall A, (is_arrow A = true) <-> exists A' B', A = (Ty_Arr A' B').
  Proof.
    intro A.
    induction A;
      split;
      try solve [ intro devil; simpl in devil; inversion devil
                | intros [ ? [ ? devil ] ]; inversion devil ].
    - intro; repeat eexists.
    - intro; reflexivity.
  Qed.

  Definition tgt_arrow_table: list Ty :=
    (fix tgt_arrow_table_rec terms :=
       match terms as terms' return (forall M, List.In M terms' -> { A : Ty | MiniMLBox [[]] M A }) -> list Ty with
       | M :: terms' =>
         fun prf =>
           List.app
             (List.filter is_arrow (tgt_table (proj1_sig (prf M (or_introl (eq_refl M))))))
             (tgt_arrow_table_rec terms' (fun m mp => prf m (or_intror mp)))
       | [] => fun prf => []
       end) Terms Proofs.

  Lemma tgt_arrow_table_correct:
    forall A, (exists A' B' M MIn,
             IsTgt (proj1_sig (Proofs M MIn)) (Ty_Arr A' B') /\
             A = Ty_Arr A' B') <->
         List.In A tgt_arrow_table.
  Proof.
    intro A.
    unfold tgt_arrow_table.
    generalize Proofs.
    clear Proofs.
    induction Terms as [ | M Terms' IH ]; intro proofs.
    - split; [ intros [ ? [ ? [ ? [ ? [ MIn ? ] ] ] ] ] | intro ]; contradiction.
    - split.
      + intros [ A' [ B' [ N [ NIn [ tgtprf Aeq ] ] ] ] ].
        apply List.in_or_app.
        destruct NIn as [ here | there ].
        * left.
          rewrite <- here in tgtprf.
          rewrite Aeq.
          apply filter_In; split.
          { apply tgt_table_correct; assumption. }
          { apply is_arrow_spec; repeat eexists; eassumption. }
        * right.
          apply IH.
          repeat eexists; eassumption.
      + intro inprf.
        destruct (List.in_app_or _ _ _ inprf) as [ in_hd | in_rest ].
        * destruct (proj1 (filter_In _ _ _) in_hd) as [ in_table is_arrow ].
          destruct (proj1 (is_arrow_spec _) is_arrow) as [ A' [ B' Aeq ] ].
          exists A', B', M, (or_introl (eq_refl M)); split.
          { rewrite <- Aeq; apply tgt_table_correct; assumption. }
          { assumption. }
        * destruct (proj2 (IH (fun M MIn => proofs M (or_intror MIn))) in_rest)
            as [ A' [ B' [ M' [ M'In prfs ] ] ] ].
          exists A', B', M', (or_intror M'In); assumption.
  Qed.

  Definition liftings (n: nat) (A: Ty): list Ty :=
    (fix liftings_rec n A :=
       match n with
       | 0 => []
       | S n => Ty_Lift n A :: liftings_rec n A
       end) (n - BoxLevel A) A.

  Axiom card : nat.
  Axiom SubstitutionSpace_sound: Fin.t card -> { S : SigVar -> VLTree TyConstr EmptySet | WF S }.
  Axiom SubstitutionSpace_complete: { S : SigVar -> VLTree TyConstr EmptySet | WF S } -> Fin.t card.
  Axiom SubstitutionSpace_eq:
    forall WFS alpha, proj1_sig (SubstitutionSpace_sound (SubstitutionSpace_complete WFS)) alpha =
                 proj1_sig WFS alpha.
  Instance SubstitutionSpace_finite: Finite (Fin.t card) :=
    {| cardinality := card;
       toFin := fun x => x;
       fromFin := fun x => x;
       fromToFin_id := fun x => eq_refl |}.
       

  Definition ApplicativeFragment_carrier:
    forall M A, ApplicativeFragment max_BoxLevel M A ->
           MiniMLBoxCarrier (typeToSort A EmptySet).
  Proof.
    intros M A appfrag.
    exists M.
    induction appfrag;
      rewrite sortType_inj in *.
    - exact (proj2_sig (Proofs M MIn)).
    - apply TPI_Box.
      apply (TPI_Shift _ _ [] [] [[]]).
      assumption.
    - apply (TPI_Unbox _ _ []).
      assumption.
    - eapply TPI_App; eassumption.
  Defined.
  
  (*
  Lemma liftings_correct: forall n A B,
      (exists n', IsLiftable n' B A /\ BoxLevel B < n) <-> List.In B (liftings n A).
  Proof.
    intros n A B.
    split.
    - intros [ n' [ liftprf levelprf ] ].
      revert A liftprf.
      induction n' as [ | n' IH ].
      + admit.
      + intros A liftprf.
        inversion liftprf as [ Beq ].
        rewrite <- Beq.
        unfold liftings.
        assert (List.In B (liftings n (Ty_Box A))).
        { apply IH.
          rewrite <- Ty_Lift_comm in Beq.
          assumption. }

   *)

End WithImplementations.

Module Type MiniMLBoxOpsSpec.
  Parameter Terms : list Term. 
  Parameter Proofs : forall M, List.In M Terms -> { A : Ty | MiniMLBox [[]] M A }.
End MiniMLBoxOpsSpec.

Module Type MiniMLBoxTreeSpec(Ops: MiniMLBoxOpsSpec) <: TreeSpec.
  Definition Label := TyConstr.
  Definition Var := SigVar.
  Definition LOrder := tyConstrOrder.

  Instance Info: LabelInfo Label := TyConstrInfo.
  Instance LOrder_pre: PreOrder LOrder :=
    {| PreOrder_Reflexive := eq_Reflexive; PreOrder_Transitive := eq_Transitive |}.
  
  Definition Operation := Op Ops.Terms.
  Definition WellFormed := WF Ops.Terms Ops.Proofs.
  Instance Sigma : SigmaAlgebra.Signature (VLTree Label) Var Operation :=
    Signature Ops.Terms Ops.Proofs.

  Definition Var_eq_dec := SigVar_eq_dec.
  Definition Label_eq_dec := TyConstr_eq_dec.
  Definition LOrder_dec := TyConstr_eq_dec.

  Definition Vars_finite := SigVar_Finite.
  Definition Labels_countable := TyConstr_Countable.
  Definition GroundLabel: { l : Label | labelArity l = 0 } :=
    exist _ (TC_Nat) (@eq_refl _ 0).
End MiniMLBoxTreeSpec.

Module Type MkMiniMLBoxSigSpec(Ops: MiniMLBoxOpsSpec).
  Declare Module TreeSpec: MiniMLBoxTreeSpec(Ops).
  Declare Module TreeSigSpec: TreeSignatureSpec(TreeSpec).
  Declare Module SigSpec: TreeSortCLSignature(TreeSpec)(TreeSigSpec).
End MkMiniMLBoxSigSpec.

Module Type MiniMLBoxAlgebra
       (Ops: MiniMLBoxOpsSpec)
       (MkSpec: MkMiniMLBoxSigSpec(Ops))
       (Import Alg: Algebraic(MkSpec.SigSpec)).
  Import MkSpec.SigSpec.
  Import MkSpec.TreeSpec.
  Import Ops.

  Lemma subst_irrelevant: forall S ty, substitute S (typeToSort ty SigVar) = typeToSort ty EmptySet.
  Proof.
    intros S ty.
    induction ty as [ | src IH1 tgt IH2 | l IH1 r IH2 | | ty IH ];
      try solve
          [ reflexivity
          | simpl;
            rewrite IH1;
            rewrite IH2;
            reflexivity
          | simpl;
            rewrite IH;
            reflexivity ].
  Qed.

  Lemma subsort_eq: forall s s', subsorts s s' -> s = s'.
  Proof.
    intros s s'.
    apply (fun tgt =>
           @Fix_F_2 _ _ (fun x y => max (VLTree_size _ _ (fst x)) (VLTree_size _ _ (snd x)) <
                                 max (VLTree_size _ _ (fst y)) (VLTree_size _ _ (snd y)))
                    (fun x y => subsorts x y -> x = y)
                    tgt s s' (WF_VLTree_size_max _ (s, s'))).
    clear s s'; intros s s' IH.
    destruct s as [ l successors | ]; [ | contradiction].
    destruct s' as [ l' successors' | ]; [ | contradiction].
    intro le_prf.
    inversion le_prf
      as [ ? ? arity_eq variance_eq ? ?  l_eq successor_prfs [ ll successors_eq ] [ ll' successors'_eq ]].
    rewrite (vect_exist_eq _ _
                             (existT_fg_eq (t _)
                                           (fun l => match l with
                                                  | TC_Nat => 0
                                                  | TC_Arr => 2
                                                  | TC_Prod => 2
                                                  | TC_Unit => 0
                                                  | TC_Box => 1
                                                  end) _ _ _ successors_eq)) in successor_prfs.
    rewrite (vect_exist_eq _ _
                           (existT_fg_eq (t _)
                                         (fun l => match l with
                                                | TC_Nat => 0
                                                | TC_Arr => 2
                                                | TC_Prod => 2
                                                | TC_Unit => 0
                                                | TC_Box => 1
                                                end) _ _ _ successors'_eq)) in successor_prfs.
    revert l_eq successor_prfs IH.
    clear ...
    intro l_eq.
    revert successors' arity_eq.
    rewrite <- l_eq.
    intros successors' arity_eq.
    rewrite (UIP_dec (Nat.eq_dec) arity_eq eq_refl).
    unfold eq_rect_r.
    simpl eq_rect.
    clear arity_eq.
    intros successor_prfs IH.
    apply f_equal.    
    assert (succ_eq:
              forall k,
                nth successors k = nth successors' k).
    { intro k.
      apply IH.
      - unfold "_ < _".
        apply (proj1 (Nat.succ_le_mono _ _ )).
        apply (Nat.max_le_compat).
        + apply (proj2 (Nat.succ_le_mono _ _) (Forall_nth _ _ (VLTree_size_lt _ _ l successors) k)).
        + apply (proj2 (Nat.succ_le_mono _ _) (Forall_nth _ _ (VLTree_size_lt _ _ l successors') k)).
      - clear IH.
        assert (all_in: forall k', nth (map (successorVariance l) (positions (labelArity l))) k' = In).
        { intro k'.
          rewrite (nth_map _ _ _ k' eq_refl).
          reflexivity. }          
        induction successor_prfs as [ | | | ? ? ? ? ? ? ? ? ? IH ];
          try solve [ generalize (all_in Fin.F1); simpl; intro devil; inversion devil ].
        + inversion k.
        + apply (Fin.caseS' k).
          * assumption.
          * intro k'; apply (IH k' (fun k => all_in (Fin.FS k))). }
    revert succ_eq.
    clear ...
    induction successors as [ | successor n successors IH ].
    - intro; apply (fun r => case0 (fun xs => _ = xs) r successors'); reflexivity.
    - apply (caseS' successors'); clear successors'; intros successor' successors'.
      intro succ_eq.
      generalize (succ_eq Fin.F1).
      simpl.
      intro successor_eq.
      rewrite successor_eq.
      apply f_equal.
      apply IH.
      exact (fun k => succ_eq (Fin.FS k)).
  Qed.
    
  Lemma MiniMLBox_Algebra: SigmaAlgebra MiniMLBoxCarrier.
  Proof.
    unfold SigmaAlgebra.
    intros s Fs.
    destruct Fs as [ op subst wf_subst args subsort ].
    unfold MiniMLBoxCarrier.
    destruct op as [ M inprf | | | ].
    - exists M.
      generalize (subsort_eq _ _ subsort).
      intro s_eq; clear subsort.
      unfold range in s_eq.
      simpl in s_eq.
      rewrite (subst_irrelevant subst) in s_eq.
      rewrite <- s_eq.
      simpl.
      rewrite sortType_inj.
      exact (proj2_sig (Ops.Proofs M inprf)).
    - destruct (fst args) as [ M Mprf ].
      exists (T_Box M).
      generalize (subsort_eq _ _ subsort).
      intro s_eq; clear subsort.
      unfold range in s_eq.
      simpl in s_eq.
      rewrite <- s_eq.
      simpl.      
      apply TPI_Box.
      apply (TPI_Shift _ _ _ _ _ Mprf).
    - destruct (fst args) as [ M Mprf ].
      exists (T_Unbox 0 M).
      generalize (subsort_eq _ _ subsort).
      intro s_eq; clear subsort.
      unfold range in s_eq.
      simpl in s_eq.
      rewrite <- s_eq.
      simpl.      
      apply (TPI_Unbox _ _ []).
      exact Mprf.
    - simpl in args.
      destruct args as [ [ M Mprf ] [ [ N Nprf ] _ ] ].
      exists (T_App M N).
      generalize (TPI_App _ _ _ _ _ _ Mprf Nprf).
      simpl in subsort.
      rewrite (subsort_eq _ _ subsort).
      intro; assumption.
  Defined.

  Lemma MiniMLBox_Algebra_sound:
    forall s c, AlgebraicallyGenerated _ MiniMLBox_Algebra s c -> 
           ApplicativeFragment Ops.Terms Ops.Proofs (max 1 (max_BoxLevel Ops.Terms Ops.Proofs))
                               (proj1_sig c) (sortToType s).
  Proof.
    intros s c gen.
    induction gen as [ s op S WFS args subsort argsgen IH ] using AlgebraicallyGenerated_ind'.
    revert args subsort argsgen IH.
    destruct op as [ M MIn | | | ]; intros args subsort argsgen IH.
    - simpl.
      rewrite <- (subsort_eq _ _ subsort).
      simpl.
      rewrite (subst_irrelevant S).
      rewrite sortType_inj.
      apply A_Impl.
      rewrite max_BoxLevel_ge.
      apply (Nat.le_max_r 1). 
    - simpl in args.
      destruct args as [ [ M Mprf ] ? ].
      simpl.
      generalize (subsort_eq _ _ subsort).
      simpl.
      intro s_eq.
      rewrite <- s_eq.
      apply A_Box.
      + exact (IH F1).
      + inversion WFS as [ ? ? ? ? gamma_eq | | ? ? ? gamma_eq ].
        * fold (sortToType (S gamma)).
          rewrite gamma_eq.
          simpl.
          apply (Nat.le_max_l 1).
        * etransitivity; [ eassumption | eapply (Nat.le_max_r 1); eassumption ].
        * rewrite gamma_eq.
          simpl.
          apply (Nat.le_max_l 1).
    - simpl in args.
      destruct args as [ [ M Mprf ] ? ].
      simpl.
      generalize (subsort_eq _ _ subsort).
      simpl.
      intro s_eq.
      rewrite <- s_eq.
      apply A_Unbox.
      + exact (IH F1).
    - simpl in args.
      destruct args as [ [ M Mprf ] [ [ N Nprf ] ? ] ].
      simpl.
      eapply A_App.
      + generalize (IH F1).
        simpl.
        generalize (subsort_eq _ _ subsort).
        simpl.
        intro s_eq.
        rewrite s_eq.
        intro; eassumption.
      + apply (IH (FS F1)).
  Qed.

  Lemma MiniMLBox_Algebra_complete:
    forall M A (appfrag: ApplicativeFragment Ops.Terms Ops.Proofs (max_BoxLevel Ops.Terms Ops.Proofs) M A),
      exists Mprf, AlgebraicallyGenerated _ MiniMLBox_Algebra (typeToSort A EmptySet)
                                     (exist _ M Mprf).
  Proof.
    intros M A appfrag.
    induction appfrag as [ M MIn level | M A level IH | M A appfrag IH | M N A B appfragM IHM appfragN IHN ].
    - set (S := fun (v: SigVar) => typeToSort Ty_Unit EmptySet).
      assert (WF_S : WF Ops.Terms Ops.Proofs S).
      { apply WF_Default; reflexivity. }
      assert (sub: subsorts (applySubst S (typeToSort (proj1_sig (Ops.Proofs M MIn)) SigVar))
                            (typeToSort (proj1_sig (Ops.Proofs M MIn)) EmptySet)).
      { simpl.
        rewrite (subst_irrelevant S).
        reflexivity. }
      generalize (FromF _ MiniMLBox_Algebra _ (OP_Use _ M MIn) S WF_S tt sub (GeneratedArgs_nil _ _ _)).
      intro; eexists; eassumption.
    - set (S := fun (v: SigVar) => match v with | gamma => typeToSort A EmptySet | _ => typeToSort Ty_Unit EmptySet end).
      assert (WF_S : WF Ops.Terms Ops.Proofs S).
      { assert (WF_Contents: exists M MIn A n,
                   IsTgt (proj1_sig (Ops.Proofs M MIn)) A /\
                   IsLiftable n (sortToType (S gamma)) A).
        { revert level.
          clear ...
          intro level.
          induction level as [ M MIn level | M A appfrag IH | M A appfrag IH | M N A B levelAB IHAB levelA IHA ].
          - exists M, MIn, (proj1_sig (Ops.Proofs M MIn)), 0; split.
            + destruct (proj1_sig (Ops.Proofs M MIn)); left; reflexivity.
            + simpl.
              rewrite sortType_inj.
              reflexivity.
          - simpl in IH.
            destruct IH as [ N [ NIn [ A' [ n [ isTgt isLiftable ] ] ] ] ].
            exists N, NIn, A', (Datatypes.S n); split.
            + exact isTgt.
            + simpl.
              unfold IsLiftable.
              rewrite isLiftable.
              reflexivity.
          - simpl in IH.
            destruct IH as [ N [ NIn [ A' [ n [ isTgt isLiftable ] ] ] ] ].
            unfold IsLiftable in isLiftable.
            rewrite sortType_inj in isLiftable.
            simpl.
            rewrite sortType_inj.
            destruct n.
            + exists N, NIn, A, 0; split.
              * unfold IsTgt in isTgt.
                simpl in isLiftable.
                rewrite <- isLiftable in isTgt.
                induction (proj1_sig (Ops.Proofs N NIn));
                  try solve [ inversion isTgt as [ devil | ]; [ inversion devil | contradiction ] ].
                { simpl in isTgt.
                  right.
                  inversion isTgt as [ devil | ]; [ inversion devil | auto ]. }
                { inversion isTgt as [ Aeq | ]; [ | right; auto ].
                  right.
                  inversion Aeq.
                  unfold IsTgt.
                  destruct A; left; reflexivity. }
              * reflexivity.
            + exists N, NIn, A', n; split.
              * assumption.
              * inversion isLiftable as [ eq ].
                clear isLiftable eq.
                destruct n; reflexivity.
          - destruct IHAB as [ M' [ M'In [ A' [ n [ isTgt isLiftable ] ] ] ] ].
            exists M', M'In, B, 0; split.
            + unfold IsLiftable in isLiftable.
              rewrite sortType_inj in isLiftable.
              destruct n; [ | inversion isLiftable ].
              simpl in isLiftable.
              rewrite <- isLiftable in isTgt.
              clear IHA.
              induction (proj1_sig (Ops.Proofs M' M'In));
                try solve [
                      inversion isTgt as [ devil | ]; [ inversion devil | contradiction ]
                    ].
              * inversion isTgt as [ eq | goRight ].
                { inversion eq.
                  right.
                  destruct B; left; reflexivity. }
                { right; auto. }
              * inversion isTgt as [ devil | ]; [ inversion devil | right; auto ].
            + simpl.
              rewrite sortType_inj.
              reflexivity. }
        destruct WF_Contents as [ N [ NIn [ B [ n [ isTgt isLiftable ] ] ] ] ].
        apply (WF_Box _ _ S  N NIn B n); try solve [ reflexivity | assumption ].
        - simpl.
          rewrite sortType_inj.
          assumption. }
      destruct IH as [ Mprf genprf ].
      generalize (fun  gen => FromF _ MiniMLBox_Algebra (typeToSort (Ty_Box A) EmptySet)
                                 (OP_Box Ops.Terms) S WF_S (exist _ M Mprf, tt) (reflexivity _) gen).
      intro mkGenPrf.
      eexists; apply mkGenPrf.
      apply GeneratedArgs_cons.
      + exact genprf.
      + apply GeneratedArgs_nil.
    - set (S := fun (v: SigVar) => match v with | gamma => typeToSort A EmptySet | _ => typeToSort Ty_Unit EmptySet end).
      assert (WF_S : WF Ops.Terms Ops.Proofs S).
      { destruct (ApplicativeFragment_BoxTgt _ _ _ _ _ appfrag) as [ M' [ M'In [ A' [ n [ isTgt isLiftable ] ] ] ] ].
        apply (WF_Box _ _ S M' M'In A' n).
        + reflexivity.
        + reflexivity.
        + exact isTgt.
        + simpl.
          rewrite sortType_inj.
          unfold IsLiftable.
          unfold IsLiftable in isLiftable.
          inversion isLiftable.
          reflexivity.
        + simpl.
          rewrite sortType_inj.
          exact(ApplicativeFragment_level _ _ _ _ _ appfrag). }
      destruct IH as [ Mprf genprf ].
      generalize (fun  gen => FromF _ MiniMLBox_Algebra (typeToSort A EmptySet)
                                 (OP_Unbox Ops.Terms) S WF_S (exist _ M Mprf, tt) (reflexivity _) gen).
      intro mkGenPrf.
      eexists; apply mkGenPrf.
      apply GeneratedArgs_cons.
      + exact genprf.
      + apply GeneratedArgs_nil.
    - set (S := fun (v: SigVar) => match v with
                                | alpha => typeToSort A EmptySet
                                | beta => typeToSort B EmptySet
                                | _ => typeToSort Ty_Unit EmptySet
                                end).
      assert (WF_S : WF Ops.Terms Ops.Proofs S).
      { destruct (ApplicativeFragment_noAbstraction _ _ _ _ _ _ appfragM) as [ M' [ M'In isTgt ] ].
        apply (WF_Arrow _ _ S M' M'In).
        - simpl.
          rewrite sortType_inj.
          rewrite sortType_inj.
          assumption.
        - reflexivity. }
      destruct IHM as [ Mprf Mgenprf ].
      destruct IHN as [ Nprf Ngenprf ].
      generalize (fun gen => FromF _ MiniMLBox_Algebra (typeToSort B EmptySet)
                                (OP_Apply Ops.Terms) S WF_S (exist _ M Mprf, (exist _ N Nprf, tt))
                                (reflexivity _) gen).
      intro mkGenPrf.
      eexists; apply mkGenPrf.
      repeat apply GeneratedArgs_cons.
      + exact Mgenprf.
      + exact Ngenprf.
      + apply GeneratedArgs_nil.
  Qed.

  Lemma ApplicativeFragment_WellTyped: forall M A,
      ApplicativeFragment Ops.Terms Ops.Proofs (max_BoxLevel Ops.Terms Ops.Proofs) M A ->
      MiniMLBox [[]] M A.
  Proof.
    intros M A appfrag.
    destruct (MiniMLBox_Algebra_complete M A appfrag) as [ result _ ].
    rewrite sortType_inj in result.
    exact result.
  Qed.

  Definition TermEq : forall s1 s2, MiniMLBoxCarrier s1 -> MiniMLBoxCarrier s2 -> Prop :=
    fun _ _ c1 c2 => proj1_sig c1 = proj1_sig c2.

  Lemma TermEq_trans: forall s1 s2 s3 c1 c2 c3, TermEq s1 s2 c1 c2 -> TermEq s2 s3 c2 c3 -> TermEq s1 s3 c1 c3.
  Proof.
    intros s1 s2 s3 c1 c2 c3.
    destruct c1 as [ M1 M1prf ].
    destruct c2 as [ M2 M2prf ].
    destruct c3 as [ M3 M3prf ].
    unfold TermEq.
    simpl.
    intros; etransitivity; eassumption.
  Qed.

  Lemma TermEq_refl: forall s c, TermEq s s c c.
  Proof.
    intros; reflexivity.
  Qed.

  Lemma TermEq_congruence:
    forall s1 s2 f1 f2,
      F_eq _ TermEq s1 s2 f1 f2 ->
      TermEq s1 s2 (MiniMLBox_Algebra s1 f1) (MiniMLBox_Algebra s2 f2).
  Proof.
    intros s1 s2 f1 f2 feq.
    destruct f1 as [ op1 S1 WF_S1 args1 subsort1 ]. 
    destruct f2 as [ op2 S2 WF_S2 args2 subsort2 ].
    destruct feq as [ op_eq args_eq ].
    simpl in op_eq.
    revert args1 args2 subsort1 subsort2 args_eq.    
    rewrite op_eq.
    intros args1 args2 subsort1 subsort2 args_eq.
    assert (args_eq': forall k, TermEq _ _ (F_args_nth _ _ _ args1 k) (F_args_nth _ _ _ args2 k)).
    { revert args1 args2 args_eq.
      unfold op.
      unfold args.
      unfold subst.
      match goal with
      |[|- forall (args1: F_args _ _ ?dom) _, _ -> forall (k: Fin.t ?n), _ ] =>
       generalize n dom
      end.
      intros n dom.
      induction dom as [ | arg n dom IH ].
      - intros ? ? ? k; inversion k.
      - intros args1 args2 args_eq k.
        apply (Fin.caseS' k).
        + simpl.
          exact (proj1 args_eq).
        + intro k'.
          apply (IH _ _ (proj2 args_eq) k'). }
    revert args_eq'.
    clear ...
    unfold MiniMLBox_Algebra.
    destruct op2.
    - intros; reflexivity.
    - destruct args1 as [ arg1 [ ] ].
      destruct args2 as [ arg2 [ ] ].      
      intro arg_eq.
      generalize (arg_eq Fin.F1).
      simpl.
      unfold TermEq.
      destruct arg1 as [ term1 prf1 ].
      destruct arg2 as [ term2 prf2 ].
      simpl.
      intro res; rewrite res; reflexivity.
    - destruct args1 as [ arg1 [ ] ].
      destruct args2 as [ arg2 [ ] ].      
      intro arg_eq.
      generalize (arg_eq Fin.F1).
      simpl.
      unfold TermEq.
      destruct arg1 as [ term1 prf1 ].
      destruct arg2 as [ term2 prf2 ].
      simpl.
      intro res; rewrite res; reflexivity.
    - destruct args1 as [ arg11 [ arg12 [ ] ] ].
      destruct args2 as [ arg21 [ arg22 [ ] ] ].      
      intro args_eq.
      generalize (args_eq Fin.F1).
      generalize (args_eq (Fin.FS Fin.F1)).
      simpl.
      unfold TermEq.
      destruct arg11 as [ term11 prf11 ].
      destruct arg12 as [ term12 prf12 ].
      destruct arg21 as [ term21 prf21 ].
      destruct arg22 as [ term22 prf22 ].
      simpl.
      intros arg1_eq arg2_eq.
      rewrite arg1_eq.
      rewrite arg2_eq.
      reflexivity.
  Qed.
        
End MiniMLBoxAlgebra.
  
        
(*
          

  Definition lift_table: list Ty :=
    (fix lift_table_rec terms :=
       match terms as terms' return (forall M, List.In M terms' -> { A : Ty | MiniMLBox [[]] M A }) -> list Ty with
       | M :: terms' =>
         fun prf =>
           List.app
             (List.flat_map () (tgt_table (proj1_sig (prf M (or_introl (eq_refl M))))))
             (tgt_arrow_table_rec terms' (fun m mp => prf m (or_intror mp)))
       | [] => fun prf => []
       end) Terms Proofs.    

  

  Definition subst_table_pos: Fin.t (length subst_alpha_table) -> (SigVar -> VLTree TyConstr EmptySet).
  Proof.
    intros pos v.
    destruct (Fin.to_nat pos) as [ n n_le ].
    set (AB := List.nth n subst_alpha_table Ty_Nat).
    assert (liftprf: exists A' B' n, IsLiftable n AB (Ty_Arr A' B')).
    { destruct (proj2 (subst_alpha_table_correct AB) (List.nth_In subst_alpha_table Ty_Nat n_le))
        as [ A' [ B' [ n' [ ? [ ? [ ? liftprf ] ] ] ] ] ].
      repeat eexists; eassumption. }
    set (A := Ty_Lift (fst (fst (arrow_shape AB liftprf))) (snd (fst (arrow_shape AB liftprf)))).
    set (B := Ty_Lift (fst (fst (arrow_shape AB liftprf))) (snd (arrow_shape AB liftprf))).
    destruct v.
    - exact (typeToSort AB EmptySet).
    - exact (typeToSort A EmptySet).
    - exact (typeToSort B EmptySet).
  Defined.   

  Lemma subst_table_sound': forall (pos : Fin.t (length subst_alpha_table)), WF (subst_table_pos pos).
  Proof.
    intro pos.
    unfold subst_table_pos.
    destruct (Fin.to_nat pos) as [ n n_le ].
    set (AB := List.nth n subst_alpha_table Ty_Nat).
    match goal with
    |[|- WF (fun v => match v with
                  | alpha => _
                  | beta => typeToSort (Ty_Lift (fst (fst (arrow_shape AB ?lp))) _) EmptySet
                  | gamma => _
                  end) ] =>
     generalize lp
    end.
    intro liftprf.
    set (A := Ty_Lift (fst (fst (arrow_shape AB liftprf))) (snd (fst (arrow_shape AB liftprf)))).
    set (B := Ty_Lift (fst (fst (arrow_shape AB liftprf))) (snd (arrow_shape AB liftprf))).
    destruct (proj2 (subst_alpha_table_correct AB) (List.nth_In subst_alpha_table Ty_Nat n_le))
      as [ A' [ B' [ n' [ M [ MIn [ tgtprf liftprf' ] ] ] ] ] ].
    eapply WF_Proof.
    - intro v; destruct v; eexists; reflexivity.
    - rewrite sortType_inj.
      eassumption.
    - rewrite sortType_inj.
      eassumption.
    - rewrite sortType_inj.
      unfold A.
      generalize (arrow_shape_spec AB liftprf).
      unfold IsLiftable.
      intro liftprf''.
      rewrite liftprf'' in liftprf'.
      revert liftprf'.
      generalize (fst (fst (arrow_shape AB liftprf))).
      induction n' as [ | n' IH ]; intros n''.
      + simpl.
        destruct n''.
        * simpl.
          intro liftprf'.
          inversion liftprf' as [ [ A'_eq B'_eq ]  ].
          reflexivity.
        * simpl.
          intro liftprf'; inversion liftprf'.
      + destruct n''.
        * simpl.
          intro liftprf'.
          inversion liftprf'.
        * intro liftprf'.
          inversion liftprf' as [ liftprf''' ].
          generalize (IH _ liftprf''').
          intro res.
          simpl.
          rewrite res.
          reflexivity.
    - rewrite sortType_inj.
      unfold B.
      generalize (arrow_shape_spec AB liftprf).
      unfold IsLiftable.
      intro liftprf''.
      rewrite liftprf'' in liftprf'.
      revert liftprf'.
      generalize (fst (fst (arrow_shape AB liftprf))).
      induction n' as [ | n' IH ]; intros n''.
      + simpl.
        destruct n''.
        * simpl.
          intro liftprf'.
          inversion liftprf' as [ [ A'_eq B'_eq ]  ].
          reflexivity.
        * simpl.
          intro liftprf'; inversion liftprf'.
      + destruct n''.
        * simpl.
          intro liftprf'.
          inversion liftprf'.
        * intro liftprf'.
          inversion liftprf' as [ liftprf''' ].
          generalize (IH _ liftprf''').
          intro res.
          simpl.
          rewrite res.
          reflexivity.
  Defined.

  Definition pos_subst_table: (length subst_alpha_table > 0) -> (SigVar -> VLTree TyConstr EmptySet) -> Fin.t (length subst_alpha_table).
  Proof.
    intros nonempty S.
    set (AB := sortToType (S alpha)).
    revert nonempty.
    induction subst_alpha_table as [ | alpha table IH ].
    - intro devil.
      apply False_rect.
      inversion devil.
    - intro prf.
      destruct (Ty_dec_eq AB alpha).
      + exact Fin.F1.
      + destruct table.
        * exact Fin.F1.
        * apply Fin.FS.
          apply IH.
          apply le_n_S.
          apply le_0_n.
  Defined.

  Lemma WF_table_non_empty: forall S, WF S -> length subst_alpha_table > 0.
  Proof.
    intros S WF_S.
    destruct WF_S as [ S A B n M MIn exty tgtprf is_arrow betaprf gammaprf ].
    unfold subst_alpha_table.
    revert tgtprf.
    generalize Proofs.
    clear Proofs.
    induction Terms as [ | N terms IH ].
    - contradiction.
    - intros Proofs tgtprf.
      rewrite List.app_length.
      unfold "_ > _".
      match goal with
      |[|- 0 < ?x + ?y ] =>
       assert (xy_gt : 0 < x \/ 0 < y);
         [ | destruct xy_gt; [ apply Nat.add_pos_l | apply Nat.add_pos_r ]; assumption ]
      end.
      destruct MIn as [ here | there ].
      + left.
        generalize (proj2 (filter_In _ _ _)
                          (conj (proj2 (tgt_table_correct _ _) tgtprf)
                                (proj2 (is_lifted_arrow_spec _)
                                       (ex_intro _ n (ex_intro _ A (ex_intro _ B is_arrow)))))).
        rewrite <- here.
        match goal with
        |[|- _ -> 0 < length ?xs] => destruct xs
        end.
        * intro; contradiction.
        * intro; apply le_n_S; apply le_0_n.
      + right.
        apply (IH there _ tgtprf).
  Qed.          

  Definition pos_subst_table_complete': forall S, WF S -> Fin.t (length subst_alpha_table) :=
    fun S WF_S => pos_subst_table (WF_table_non_empty S WF_S) S.

  Definition subst_table_sound: Fin.t (length subst_alpha_table) -> { S : _ | WF S } :=
    fun pos => exist _ (subst_table_pos pos) (subst_table_sound' pos).
  Definition subst_table_complete: { S : _ | WF S } -> Fin.t (length subst_alpha_table) :=
    fun SWF => pos_subst_table_complete' (proj1_sig SWF) (proj2_sig SWF).

  Lemma SubstitutionSpace_eq:
    forall WFS v, proj1_sig (subst_table_sound (subst_table_complete WFS)) v =
             proj1_sig WFS v.
  Proof.
    simpl.    
    intros WFS v.
    set (step := subst_table_complete WFS).
    destruct WFS as [ _ [ S A' B' n' M MIn exty tgtprf is_arrow betaprf gammaprf ] ].
    simpl.
    unfold subst_table_pos.
    set (AB := typeToSort (List.nth (proj1_sig (to_nat step)) subst_alpha_table Ty_Nat) EmptySet).
    destruct (proj2 (subst_alpha_table_correct (List.nth (proj1_sig (to_nat step)) subst_alpha_table Ty_Nat))
                    (List.nth_In subst_alpha_table Ty_Nat (proj2_sig (to_nat step))))
      as [ A [ B [ n [ M' [ M'In [ tgtprf' liftprf ] ] ] ] ] ].
    set (arr := arrow_shape (List.nth (proj1_sig (to_nat step))
                                      subst_alpha_table Ty_Nat)
                            (ex_intro _ A (ex_intro _ B (ex_intro _ n liftprf)))).                             
    set (Ares := typeToSort (Ty_Lift (fst (fst arr)) (snd (fst arr))) EmptySet).                                  
    set (Bres := typeToSort (Ty_Lift (fst (fst arr)) (snd arr)) EmptySet).
    assert (match v with
            | alpha => AB
            | beta => Ares
            | gamma => Bres
            end = S v).
    { destruct v.
      - unfold AB.
        unfold step.
        unfold subst_table_complete.
        unfold pos_subst_table_complete'.
        unfold pos_subst_table.
        simpl.
        generalize (WF_table_non_empty S (WF_Proof S A' B' n' M MIn exty tgtprf is_arrow betaprf gammaprf)).
        generalize (proj1 (subst_alpha_table_correct (sortToType (S alpha)))
                          (ex_intro _ A' (ex_intro _ B' (ex_intro _ (ex_intro _ M (ex_intro _ MIn (conj tgtprf is_arrow))))))).
        clear AB arr Ares Bres step tgtprf' liftprf.
        induction subst_alpha_table as [ | C table IH ].
        + intro gtprf; inversion gtprf.
        + simpl.
          destruct (Ty_dec_eq (sortToType (S alpha)) C) as [ eq | ineq ].
          * simpl.
            intro.
            rewrite <- eq.
            rewrite (typeSort_inj _ (exty alpha)).
            reflexivity.
          * simpl.
            intro gtprf.
            
      
    

    
    destruct v.
    - simpl.
      unfold subst_table_pos.
      unfold subst_table_complete.
      unfold pos_subst_table_complete'.
      unfold pos_subst_table.
      generalize (WF_table_non_empty (proj1_sig WFS) (proj2_sig WFS)).
      destruct WFS as [ _ [ S A' B' n' M MIn exty tgtprf is_arrow betaprf gammaprf ] ].
      generalize (proj1 (subst_alpha_table_correct _)
                        (ex_intro
                           _ A'
                           (ex_intro
                              _ B'
                              (ex_intro
                                 _ n'
                                 (ex_intro _ M
                                           (ex_intro _ MIn
                                                     (conj tgtprf is_arrow))))))).
      induction subst_alpha_table as [ | A table IH ].
      + intro devil; apply False_rect; inversion devil.
      + intros inprf gtprf.
        simpl.
        destruct (Ty_dec_eq (sortToType (S alpha)) A) as [ eq | ineq ].
        * simpl.
          rewrite <- eq.          
          simpl.
          rewrite (typeSort_inj _ (exty alpha)).
          reflexivity.
        * assert (inprf' : List.In (sortToType (S alpha)) table).
          { destruct inprf as [ here | there ].
            - apply False_rect.
              apply ineq.
              apply eq_sym.
              assumption.
            - assumption. }
          assert (gtprf' : length table > 0).
          { destruct table.
            + contradiction.
            + apply le_n_S.
              apply le_0_n. }
          generalize (IH inprf' gtprf').
          intro S_eq.
          simpl proj1_sig in S_eq.
          rewrite <- S_eq.
          simpl.
          match goal with
          | [|- _ = (let (_, _) := to_nat ?pos in _)] =>
            generalize pos
          end.
          intro xxxxxxxxxx.
          destruct table.
          { inversion xxxxxxxxxx. }
          { simpl.
            

          destruct table.
          { destruct inprf as [ here | there ];
              [ | contradiction ].
            apply False_rect.
            apply ineq.
            exact (eq_sym here). }
          { destruct inprf as [ here | there ].
            - apply False_rect.
              apply ineq.
              exact (eq_sym here).
            - 
              match goal with
              | [|- (let (_, _) := to_nat (Fin.FS (list_rec _ _ _ _ ?gtprf')) in _) = _] =>
                generalize (IH there gtprf');
                  intro S_eq
              end.
              simpl.
              unfold proj1_sig in S_eq.
              rewrite <- S_eq.
              match goal with
              | [|- _ = (let (_, _) := to_nat ?pos in _)] =>
                generalize pos
              end.
              intro 
 
              assert (gtprf': length (t :: table) > 0).
              { unfold "_ > _".
                apply le_n_S.
                apply le_0_n. }
              
              
g
              simpl in IH.
              
              rewrite <- (IH there gtprf').
              simpl.

              eapply IH.
      simpl.
      simpl.
      un
      simpl.
    
    (*unfold subst_table_pos.
    simpl.
    unfold subst_table_complete.
    unfold pos_subst_table_complete'.
    generalize (WF_table_non_empty (proj1_sig WFS) (proj2_sig WFS)).
    intro lengthprf.
    unfold pos_subst_table.
    unfold subst_table_pos.*)
    unfold subst_table_pos.
    unfold subst_table_complete.
    unfold pos_subst_table_complete'.
    generalize (WF_table_non_empty (proj1_sig WFS) (proj2_sig WFS)).
    intro lengthprf.
    unfold pos_subst_table.
    match goal with
    |[|- 
    
    match goal with
    |[|- (let (_, _) := _ in
         fun v => match v with
               | alpha => _
               | beta => typeToSort (Ty_Lift (fst (fst (arrow_shape _ ?liftprf))) _) EmptySet
               | gamma => _
               end) v = _ ] =>
     (*generalize liftprf*) idtac
    end.
    intro liftprf.
    destruct WFS as [ _ [ S A B n' M MIn exty tgtprf is_arrow betaprf gammaprf ] ].
    simpl.
    destruct v.
    - rewrite <- (typeSort_inj _ (exty alpha)).
      generalize
        (proj1 (subst_alpha_table_correct _)
               (ex_intro
                  _ A (ex_intro
                         _ B
                         (ex_intro _ n'
                                   (ex_intro _ M (ex_intro _ MIn (conj tgtprf is_arrow))))))).
      
      clear ...
      induction subst_alpha_table; intros intprf.
      + contradiction.
      +  
    
    
  
  Definition get_subst_sound: Fin.t (length src_tgt_table) -> { S : _ | WF S }.
  Proof.
    intro pos.
    destruct (Fin.to_nat pos) as [ n n_le ].
    set (A := typeToSort (fst (List.nth n src_tgt_table (Ty_Nat, Ty_Nat))) EmptySet).
    set (B := typeToSort (snd (List.nth n src_tgt_table (Ty_Nat, Ty_Nat))) EmptySet).
    exists (fun v => match v with | alpha => A | beta => B end).
    assert (res:
              exists M MIn, IsSrc (proj1_sig (Proofs M MIn)) (sortToType A) /\
                       IsTgt (proj1_sig (Proofs M MIn)) (sortToType B)).
    { apply src_tgt_table_correct.
      unfold A.
      unfold B.
      rewrite sortType_inj.
      rewrite sortType_inj.
      rewrite <- surjective_pairing.
      apply List.nth_In.
      exact n_le. }
    destruct res as [ M [ MIn [ srcprf tgtprf ] ] ].
    eapply WF_Proof; try solve [ eassumption ].
    intro v; destruct v; eexists; reflexivity.
  Defined.

  Definition get_subst_complete: { S : _ | WF S } -> Fin.t (length src_tgt_table).
  Proof.
    intros [ S WF_S ].
    set (A := sortToType (S alpha)).
    set (B := sortToType (S beta)).
    assert (in_prf: List.In (A, B) src_tgt_table).
    { destruct WF_S as [ M MIn srcprf tgtprf ].
      apply src_tgt_table_correct.
      eexists; eexists; split; eassumption. }
    induction (src_tgt_table) as [ | [A' B'] table IH ].
    - contradiction.
    - destruct (Ty_dec_eq A' A);
        [ destruct (Ty_dec_eq B' B);
          [ exact Fin.F1 | ] | ];
        apply Fin.FS;
        apply IH;
        destruct in_prf as [ here | there ];
        solve [ inversion here; contradiction | assumption ].
  Defined.      
    
  Lemma SubstitutionSpace_eq:
    forall WFS alpha, proj1_sig (get_subst_sound (get_subst_complete WFS)) alpha =
                 proj1_sig WFS alpha.
  Proof.
    intros WFS alpha.
    destruct WFS as [ S WF_S ].
    inversion WF_S as [ S' M MIn ex_ty srcprf tgtprf S_eq ].
    clear S' S_eq.
    simpl proj1_sig at 2.
    set (step := get_subst_complete (exist _ S WF_S)).
    set (A := typeToSort (fst (List.nth (proj1_sig (Fin.to_nat step)) src_tgt_table (Ty_Nat, Ty_Nat))) EmptySet).
    set (B := typeToSort (snd (List.nth (proj1_sig (Fin.to_nat step)) src_tgt_table (Ty_Nat, Ty_Nat))) EmptySet).
    assert (outer_eq : (fun v => match v with | alpha => A | beta => B end) alpha =
                       proj1_sig (get_subst_sound step) alpha).
    { unfold get_subst_sound.
      destruct (Fin.to_nat step) as [ n prf ].
      simpl.
      reflexivity. }
    rewrite <- outer_eq.
    destruct alpha.
    - unfold A.
      unfold step.
      simpl.
      match goal with
      |[|- typeToSort (fst (List.nth (proj1_sig (to_nat (list_rec _ _ _ _ ?prf))) _ _)) _ = _] =>
       generalize prf
      end.
      generalize src_tgt_table.
      intro src_tgt_table.
      induction src_tgt_table as [ | [ A' B' ] table IH ] .
      + intro; contradiction.
      + simpl.
        destruct (Ty_dec_eq A' (sortToType (S alpha))) as [ eq1 | ineq1 ];
          [ destruct (Ty_dec_eq B' (sortToType (S beta))) as [ eq2 | ineq2 ]
          | ].
        * simpl.
          intro.
          rewrite eq1.
          rewrite (typeSort_inj _ (ex_ty alpha)).
          reflexivity.
        * intro rec_prf.
          simpl.
          destruct rec_prf as [ here | there ];
            [ inversion here; contradiction | ].
          simpl.
          rewrite <- (IH there).
          match goal with
          |[|- typeToSort ?x _ = typeToSort ?y _] =>
           assert (eq: x = y); [ | rewrite eq; reflexivity ]
          end.
          apply f_equal.
          match goal with
          |[|- match proj1_sig (let (i, P) := to_nat ?x in exist _ _ _) with | _ => _ end =
              List.nth (proj1_sig (to_nat _)) _ _] =>
           generalize x
          end.
          clear ...
          fold (List.length table).
          generalize (length table).
          intros n t.
          match goal with            
          |[|- match ?m with | _ => _ end = _ ] =>
           assert (m_eq: m = S (proj1_sig (to_nat t))); [ | rewrite m_eq; simpl; reflexivity ]
          end.
          destruct (to_nat t).
          reflexivity.
        * intro rec_prf.
          simpl.
          destruct rec_prf as [ here | there ];
            [ inversion here; contradiction | ].
          simpl.
          rewrite <- (IH there).
          match goal with
          |[|- typeToSort ?x _ = typeToSort ?y _] =>
           assert (eq: x = y); [ | rewrite eq; reflexivity ]
          end.
          apply f_equal.
          match goal with
          |[|- match proj1_sig (let (i, P) := to_nat ?x in exist _ _ _) with | _ => _ end =
              List.nth (proj1_sig (to_nat _)) _ _] =>
           generalize x
          end.
          clear ...
          fold (List.length table).
          generalize (length table).
          intros n t.
          match goal with            
          |[|- match ?m with | _ => _ end = _ ] =>
           assert (m_eq: m = S (proj1_sig (to_nat t))); [ | rewrite m_eq; simpl; reflexivity ]
          end.
          destruct (to_nat t).
          reflexivity.
    - unfold B.
      unfold step.
      simpl.
      match goal with
      |[|- typeToSort (snd (List.nth (proj1_sig (to_nat (list_rec _ _ _ _ ?prf))) _ _)) _ = _] =>
       generalize prf
      end.
      generalize src_tgt_table.
      intro src_tgt_table.
      induction src_tgt_table as [ | [ A' B' ] table IH ] .
      + intro; contradiction.
      + simpl.
        destruct (Ty_dec_eq A' (sortToType (S alpha))) as [ eq1 | ineq1 ];
          [ destruct (Ty_dec_eq B' (sortToType (S beta))) as [ eq2 | ineq2 ]
          | ].
        * simpl.
          intro.
          rewrite eq2.
          rewrite (typeSort_inj _ (ex_ty beta)).
          reflexivity.
        * intro rec_prf.
          simpl.
          destruct rec_prf as [ here | there ];
            [ inversion here; contradiction | ].
          simpl.
          rewrite <- (IH there).
          match goal with
          |[|- typeToSort ?x _ = typeToSort ?y _] =>
           assert (eq: x = y); [ | rewrite eq; reflexivity ]
          end.
          apply f_equal.
          match goal with
          |[|- match proj1_sig (let (i, P) := to_nat ?x in exist _ _ _) with | _ => _ end =
              List.nth (proj1_sig (to_nat _)) _ _] =>
           generalize x
          end.
          clear ...
          fold (List.length table).
          generalize (length table).
          intros n t.
          match goal with            
          |[|- match ?m with | _ => _ end = _ ] =>
           assert (m_eq: m = S (proj1_sig (to_nat t))); [ | rewrite m_eq; simpl; reflexivity ]
          end.
          destruct (to_nat t).
          reflexivity.
        * intro rec_prf.
          simpl.
          destruct rec_prf as [ here | there ];
            [ inversion here; contradiction | ].
          simpl.
          rewrite <- (IH there).
          match goal with
          |[|- typeToSort ?x _ = typeToSort ?y _] =>
           assert (eq: x = y); [ | rewrite eq; reflexivity ]
          end.
          apply f_equal.
          match goal with
          |[|- match proj1_sig (let (i, P) := to_nat ?x in exist _ _ _) with | _ => _ end =
              List.nth (proj1_sig (to_nat _)) _ _] =>
           generalize x
          end.
          clear ...
          fold (List.length table).
          generalize (length table).
          intros n t.
          match goal with            
          |[|- match ?m with | _ => _ end = _ ] =>
           assert (m_eq: m = S (proj1_sig (to_nat t))); [ | rewrite m_eq; simpl; reflexivity ]
          end.
          destruct (to_nat t).
          reflexivity.
  Qed.
*)  