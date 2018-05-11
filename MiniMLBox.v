Require Import Coq.Lists.List.
Require Import Coq.Vectors.Fin.
Require Import Coq.Vectors.Vector.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Eqdep_dec.
Import EqNotations.

Require Import SigmaAlgebra.
Require Import VarianceLabeledTree.
Require Import SortEmbeddings.
Require Import ComputationalPathLemma.
Require Import VectorQuantification.
Require Import Cantor.
Require Import FunctionSpace.
Require Import IntersectionTypes.
Require Import CombinatoryTerm.
Require Import CombinatoryLogic.
Require Import CombinatoryLogicAlgebra.
Require Import FiniteSubstitutionSpace.

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
  | A_Impl : forall M n (MIn: List.nth_error Terms n = Some M),
      BoxLevel (proj1_sig (Proofs M (List.nth_error_In _ _ MIn))) <= maxBox ->
      ApplicativeFragment maxBox M (proj1_sig (Proofs M (List.nth_error_In _ _ MIn)))
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
    induction apfrag as [ M n' inprf | | | ];
      try solve [ contradiction ].
    - destruct Terms.
      + destruct n'; inversion inprf.
      + inversion lenprf.
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
      inversion appfrag as [ M' Mpos MIn level M'eq Ceq
                           | M' A' appfrag' level Meq Ceq
                           | M' A' appfrag' [ nEq Meq ] Ceq
                           | M1' M2' A' B' appfrag1' appfrag2' ];
      try solve [
            rewrite <- Ceq in isTgt;
            eexists; exists (List.nth_error_In _ _ MIn); exact isTgt ].
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
      inversion appfrag as [ M' M'Pos MIn level M'eq Ceq
                           | M' A' appfrag' level Meq Ceq
                           | M' A' appfrag' [ nEq Meq ] Ceq
                           | M1' M2' A' B' appfrag1' appfrag2' ];
      try solve [
            rewrite <- Ceq in isTgt;
            eexists; exists (List.nth_error_In _ _ MIn), A, 0; split; [ exact isTgt | reflexivity ]].
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
  | OP_Use: forall M n, List.nth_error Terms n = Some M -> Op
  | OP_Box: Op
  | OP_Unbox: Op
  | OP_Apply : Op.

  Definition Op_toNat (o : Op): nat :=
    match o with
    | OP_Use _ n _ => 3 + n
    | OP_Box => 0
    | OP_Unbox => 1
    | OP_Apply => 2
    end.

  Definition Op_fromNat (n: nat): Op :=
    match n with
    | 0 => OP_Box
    | 1 => OP_Unbox
    | 2 => OP_Apply
    | S (S (S k)) =>
      match List.nth_error Terms k with
      | Some M => fun eq => OP_Use M k eq
      | _ => fun eq => OP_Box
      end eq_refl
    end.

  Definition Term_option_eq_dec: forall (x y: option Term), { x = y } + { x <> y }.
  Proof.
    intros x y;
      destruct x as [ x | ]; destruct y as [ y | ];
        try solve [ right; intro devil; inversion devil ].
    - destruct (Term_dec_eq x y).
      + left; apply f_equal; assumption.
      + right; intro devil; inversion devil; contradiction.
    - left; reflexivity.
  Defined.
  
  Lemma Op_fromToNat_id: forall o, Op_fromNat (Op_toNat o) = o.
  Proof.
    intro o.
    destruct o as [ M n prf | | | ]; try solve [ reflexivity ].
    simpl.
    generalize (eq_refl (nth_error Terms n)).
    set (P := fun M eq => OP_Use M n eq).
    fold (P M prf).
    generalize P; clear P.
    revert prf.
    generalize (nth_error Terms n).
    intros o prf.
    rewrite prf.
    intros P eq.
    rewrite (UIP_dec Term_option_eq_dec eq eq_refl).
    reflexivity.
  Qed.

  Lemma Op_toNatLt: forall o, Op_toNat o < 3 + length Terms.
  Proof.
    intro o.
    destruct o as [ M n eq | | | ];
      try solve [ apply (Nat.lt_lt_add_r); auto ].
    - simpl.
      do 3 (apply (proj1 (Nat.succ_lt_mono _ _))).
      apply nth_error_Some.
      intro devil.
      rewrite devil in eq.
      inversion eq.
  Qed.

  Lemma Op_toFromNat_id: forall n, n < 3 + length Terms -> Op_toNat (Op_fromNat n) = n.
  Proof.
    intro n.
    do 3 (destruct n as [ | n ]; [ reflexivity | ]).
    intro prf.
    do 3 (generalize (proj2 (Nat.succ_lt_mono _ _) prf); clear prf; intro prf).
    simpl.
    generalize (eq_refl (nth_error Terms n)).
    set (P x := forall e: nth_error Terms n = x,
            Op_toNat (match x as x' return (nth_error Terms n = x' -> Op) with
                      | Some M => fun eq => OP_Use M n eq
                      | None => fun _ => OP_Box
                      end e) = S (S (S n))).
    fold (P (nth_error Terms n)).
    generalize (proj2 (nth_error_Some Terms n) prf).
    generalize (nth_error Terms n).
    intros o o_ineq.
    unfold P.
    destruct o as [ M | ]; [ | contradiction ].
    intros; reflexivity.
  Qed.

  Lemma Op_toFromFin_id: forall x, Fin.of_nat_lt (Op_toNatLt (Op_fromNat (proj1_sig (Fin.to_nat x)))) = x.
  Proof.
    intro x.
    match goal with
    |[|- of_nat_lt ?prf = x] => generalize prf
    end.
    rewrite (Op_toFromNat_id (proj1_sig (to_nat x)) (proj2_sig (to_nat x))).
    intro lt.
    rewrite (Fin.of_nat_ext lt (proj2_sig (to_nat x))).
    apply (Fin.of_nat_to_nat_inv).
  Qed.

  Lemma Op_fromToFin_id: forall x, Op_fromNat (proj1_sig (Fin.to_nat (Fin.of_nat_lt (Op_toNatLt x)))) = x.
  Proof.
    intro x.
    rewrite Fin.to_nat_of_nat.
    simpl.
    apply Op_fromToNat_id.
  Qed.
    
  Instance Op_Finite: Finite Op :=
    {| cardinality := 3 + length Terms;
       toFin x := Fin.of_nat_lt (Op_toNatLt x);
       fromFin x := Op_fromNat (proj1_sig (Fin.to_nat x));
       fromToFin_id := Op_fromToFin_id;
       toFromFin_id := Op_toFromFin_id |}.
    
  Definition arity (op: Op): nat :=
    match op with
    | OP_Use _ _ _ => 0
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

  Definition SigVar_card := 3.
  Definition SigVar_toFin: SigVar -> Fin.t SigVar_card :=
    fun x => match x with | alpha => F1 | beta => FS F1 | gamma => FS (FS F1) end.
  Definition SigVar_fromFin: Fin.t SigVar_card -> SigVar :=
    fun x => match x with | F1 => alpha | Fin.FS F1 => beta | Fin.FS (Fin.FS _) => gamma end.
  Lemma SigVar_fromToFin_id: forall alpha, SigVar_fromFin (SigVar_toFin alpha) = alpha.
  Proof.
    intro alpha.
    destruct alpha; reflexivity.
  Qed.

  Lemma SigVar_toFromFin_id: forall alpha, SigVar_toFin (SigVar_fromFin alpha) = alpha.
  Proof.
    intro alpha.
    repeat (apply (Fin.caseS' alpha); [ reflexivity | clear alpha; intro alpha ]).
    inversion alpha.
  Qed.
  
  Instance SigVar_Finite : Finite SigVar :=
    {| cardinality := SigVar_card;
       toFin := SigVar_toFin;
       fromFin := SigVar_fromFin;
       fromToFin_id := SigVar_fromToFin_id;
       toFromFin_id := SigVar_toFromFin_id
    |}.
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
           | OP_Use _ _ _ => nil _
           | OP_Box => cons _ (Hole _ _ gamma) _ (nil _)
           | OP_Unbox => cons _ (Node _ _ TC_Box (cons _ (Hole _ _ gamma) _ (nil _))) _ (nil _)
           | OP_MApply => applyDom
           end;
       range :=
         fun op =>
           match op with
           | OP_Use M _ MIn => typeToSort (proj1_sig (Proofs M (List.nth_error_In _ _ MIn))) SigVar
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

  Lemma BoxLevel_Lift: forall n A, BoxLevel (Ty_Lift n A) = n + BoxLevel A.
  Proof.
    intro n.
    induction n as [ | n IH ]; intro A.
    - reflexivity.
    - simpl.
      rewrite (IH A).
      reflexivity.
  Qed.
  
  Lemma liftings_correct: forall A n B, List.In A (liftings n B) <-> exists n', BoxLevel A < n /\ IsLiftable n' A B.
  Proof.
    intros A n.
    revert A.
    unfold liftings.
    induction n as [ | n IH]; intros A B.
    - split; [ contradiction | intros [n [ devil ? ]]; inversion devil ].
    - split.
      + destruct (Nat.le_gt_cases (BoxLevel B) n) as [ n_ge | devil ].
        * rewrite (Nat.sub_succ_l _ _ n_ge).
          intro prf.
          destruct prf as [ here | there ].
          { exists (n - BoxLevel B); split.
            - rewrite <- here.
              rewrite BoxLevel_Lift.
              rewrite (Nat.sub_add); [ apply Nat.le_refl | assumption].
            - exact (eq_sym here). }
          { destruct (proj1 (IH A B) there) as [ n' [ level_lt liftable ] ].
            exists n'; split; [ etransitivity; [ eassumption | apply Nat.le_refl ] | assumption ]. }
        * rewrite (proj2 (Nat.sub_0_le _ _) devil).
          intro; contradiction.
      + intros [ n' [ level_lt liftable ] ].
        unfold IsLiftable in liftable.
        inversion level_lt as [ level_n | ? level_lt' ];
          rewrite liftable in *;
          rewrite BoxLevel_Lift in *.
        * rewrite (Nat.add_assoc 1).
          rewrite <- (Nat.add_sub_assoc);  [ | apply (Nat.le_refl _) ].
          rewrite (Nat.sub_diag).
          rewrite (Nat.add_0_r).
          simpl.
          left; reflexivity.
        * rewrite (Nat.sub_succ_l).
          { right.
            eapply IH.
            exists n'; split.
            - rewrite BoxLevel_Lift.
              exact level_lt'.
            - reflexivity. }
          { etransitivity; [ | exact level_lt' ].
            rewrite (Nat.add_assoc 1).
            rewrite (Nat.add_comm).
            apply (Nat.le_add_r). }
  Qed.

  Definition liftbox_tgt_table: list Ty :=
    (fix liftbox_tgt_table_rec terms :=
       match terms as terms' return (forall M, List.In M terms' -> { A : Ty | MiniMLBox [[]] M A}) -> list Ty with
       | M :: terms' =>
         fun prf =>
           List.app
             (List.flat_map (liftings max_BoxLevel)
                            (tgt_table (proj1_sig (prf M (or_introl (eq_refl M))))))
             (liftbox_tgt_table_rec terms' (fun M prf' => prf M (or_intror prf')))
       | [] => fun _ => []
       end) Terms Proofs.

  Lemma liftbox_tgt_table_correct:
    forall A, (exists A' M MIn n,
             IsTgt (proj1_sig (Proofs M MIn)) A' /\
             IsLiftable n A A' /\
             BoxLevel A < max_BoxLevel) <-> List.In A liftbox_tgt_table.
  Proof.
    intro A.
    unfold liftbox_tgt_table.
    generalize max_BoxLevel.
    generalize Proofs.
    clear Proofs.
    revert A.
    induction Terms as [ | M Terms' IH ]; intros A proofs max_BoxLevel.
    - split;
        intro devil;
        repeat (let x := fresh "dx" in
                inversion devil as [ x devil' ];
                clear devil;
                rename devil' into devil);
        contradiction.
    - split.
      + intros [ A' [ M' [ M'In [ n  [ isTgt [ isLiftable lvl_ok ] ] ] ] ] ].
        destruct M'In as [ here | there ].
        * apply (List.in_or_app); left.
          rewrite <- here in isTgt.
          apply (List.in_flat_map).
          exists A'; split.
          { apply tgt_table_correct; assumption. }
          { apply liftings_correct.
            exists n; split; assumption. }     
        * apply (List.in_or_app); right.
          apply (proj1 (IH A (fun M' prf' => proofs _ (or_intror prf')) max_BoxLevel)).
          exists A', M', there, n; repeat split; assumption.
      + intro inprf.
        destruct (List.in_app_or _ _ _ inprf) as [ in_hd | in_tail ].
        * destruct (proj1 (List.in_flat_map _ _ _) in_hd) as [ A' [ tgt_A' maxlevel_A ] ].
          destruct (proj1 (liftings_correct _ _ _) maxlevel_A) as [ n [ maxBoxLevel_A liftA ] ].
          exists A', M, (or_introl eq_refl), n; repeat split;
            solve [ exact (proj1 (tgt_table_correct _ _) tgt_A') | assumption ].
        * destruct (proj2 (IH A (fun M prf' => proofs M (or_intror prf')) max_BoxLevel) in_tail)
            as [ A' [ M' [  M'In result ] ] ].
          exists A', M', (or_intror M'In).
          exact result.
  Qed.

  Definition wf_set : list (t (VLTree TyConstr EmptySet) (@cardinality SigVar SigVar_Finite)) :=
    nodup (Vector_eq_dec (Tree_eq_dec _ _ TyConstr_eq_dec (fun x => False_rect _ x)))
          (List.app
             (List.map
                (fun ty =>
                   match ty with
                   | Ty_Arr A B =>
                     of_list [ typeToSort A _; typeToSort B _; typeToSort Ty_Unit _]
                   | _ => of_list [ typeToSort Ty_Unit _; typeToSort Ty_Unit _; typeToSort Ty_Unit _ ]
                   end) tgt_arrow_table)
             (List.app (@List.map _ (t _ (@cardinality SigVar SigVar_Finite))
                          (fun ty =>
                             of_list [ typeToSort Ty_Unit EmptySet; typeToSort Ty_Unit _; typeToSort ty _])
                          liftbox_tgt_table)
                       [of_list [ typeToSort Ty_Unit EmptySet; typeToSort Ty_Unit _; typeToSort Ty_Unit _]])).

  Definition SubstSpaceFromVector :
    FunctionSpace (t (VLTree TyConstr EmptySet) (@cardinality _ SigVar_Finite)) SigVar (VLTree TyConstr EmptySet) :=
    TableSpace _ _ SigVar_Finite.

  Definition WellFormed := Fin.t (length wf_set).
  Definition WF_take (S: WellFormed): SigVar -> VLTree TyConstr EmptySet :=
    take (nth (of_list wf_set) S).
  Lemma WF_take_ext: forall e1 e2, (forall x, WF_take e1 x = WF_take e2 x) -> e1 = e2.
  Proof.
    generalize (NoDup_nodup _ _ : NoDup wf_set).
    intros wf_set_set e1 e2 prf.
    destruct (Fin.eq_dec e1 e2) as [ | devil ]; [ assumption | ].
    assert (vect_eq: nth (of_list wf_set) e1 = nth (of_list wf_set) e2).
    { apply (eq_nth_iff _ _ (nth (of_list wf_set) e1) (nth (of_list wf_set) e2)).
      intros p1 p2 p_eq.
      rewrite p_eq.
      rewrite <- (toFromFin_id p2).
      apply prf. }
    apply Fin.to_nat_inj.
    eapply NoDup_nth_error; [ eassumption | | ].
    - exact (proj2_sig (to_nat e1)).
    - rewrite (List_nth_nth _ _ (proj2_sig (to_nat e1))).
      rewrite (List_nth_nth _ _ (proj2_sig (to_nat e2))).
      apply f_equal.
      rewrite (Fin.of_nat_to_nat_inv).
      rewrite (Fin.of_nat_to_nat_inv).
      assumption.
  Qed.
  
  Instance WellFormedSpace : FunctionSpace WellFormed SigVar (VLTree TyConstr EmptySet) :=
    {| take := WF_take;
       extensional := WF_take_ext |}.

  Lemma WF_nonempty: length wf_set = 0 -> False.
  Proof.
    unfold wf_set.
    intro devil.
    match goal with
    |[ devil: length (nodup ?d (?xs ++ ?ys ++ [?zs])) = _ |- _] =>
     assert (inprf: List.In zs (nodup d (xs ++ ys ++ [zs])));
       [ | destruct (nodup d (xs ++ ys ++ [zs])); [ contradiction | inversion devil ] ]
    end.
    apply (List.nodup_In).
    repeat (apply (List.in_or_app); right).
    left; reflexivity.
  Qed.
  
  Instance WellFormedSpace_finite: NonEmptyFinite WellFormed :=
    {| IsFinite := FinFinite (length wf_set);
       cardinality_nonempty := WF_nonempty |}.

  Lemma WellFormedSpace_complete: forall (S : SigVar -> VLTree TyConstr EmptySet), WF S -> { e: WellFormed | forall x, @take _ _ _ WellFormedSpace e x = S x }.
  Proof.
    intros S WF_S.
    assert (inprf: List.In (of_list [S alpha; S beta; S gamma]) wf_set).
    { unfold wf_set.
      apply (List.nodup_In).
      apply (List.in_or_app).
      destruct WF_S.
      - left.
        apply (List.in_map_iff).
        exists (Ty_Arr (sortToType (S alpha)) (sortToType (S beta))); split.
        + repeat (rewrite typeSort_inj; [ simpl; apply f_equal | ]);
            try solve [
                  match goal with
                  |[M : Term, MIn: List.In M Terms, H: IsTgt _ _ |- _] =>
                   induction (proj1_sig (Proofs M MIn));
                   simpl in H; destruct H as [ x | y ];
                       try solve [ inversion x | contradiction | eauto ]
                  end;
                  try (inversion x;
                       match goal with |[ eq: _ = sortToType ?rhs |- context [ ?rhs ]] => exists (sortToType rhs) end;
                       apply sortType_sur)
                ].
          * apply (f_equal (fun x => cons  _ x _ (nil _))).
            rewrite <- (sortType_sur (S gamma)).
            match goal with
            |[ eq: _ = Ty_Unit |- _] => rewrite eq
            end.
            reflexivity.
        + apply tgt_arrow_table_correct.
          repeat eexists; eassumption.
      - right; apply (List.in_or_app); left.
        apply (List.in_map_iff).
        exists (sortToType (S gamma)); split.
        + repeat match goal with
                 |[ eq: ?lhs = _ |- context [ ?lhs ] ] =>
                  rewrite eq; simpl; apply f_equal
                 end.
          rewrite (typeSort_inj); [ simpl; reflexivity |].
          eexists.
          rewrite sortType_sur.
          reflexivity.
        + apply liftbox_tgt_table_correct.
          repeat eexists; eassumption.
      - right; apply (List.in_or_app); right.
        repeat match goal with
                 |[ eq: ?lhs = _ |- context [ ?lhs ] ] =>
                  rewrite eq
               end.
        left; reflexivity. }
    revert inprf.
    unfold WellFormed.
    unfold take.
    simpl.
    unfold WF_take.
    induction wf_set as [ | hd tl IH ]; intro prf.
    - inversion prf.
    - match goal with
      |[ prf: List.In ?l _ |- _ ]=>
       destruct (Vector_eq_dec (Tree_eq_dec _ _ TyConstr_eq_dec (fun x => False_rect _ x)) l hd) as [ eq | ineq ]
      end.
      + exists Fin.F1.
        simpl.
        unfold takeVect.
        rewrite <- eq.
        intro x; destruct x; reflexivity.
      + match goal with
        |[prf : List.In ?l (hd :: tl) |- _] =>
         assert (prf': List.In l tl); [ destruct prf as [ devil | ok];
                                        [ generalize (ineq (eq_sym devil)); intro; contradiction
                                        | exact ok ] |]
        end.
        destruct (IH prf') as [ e e_prf ].
        exists (Fin.FS e); assumption.
  Qed.

  Lemma WellFormedSpace_sound:
    forall e: WellFormed,  { S : SigVar -> VLTree TyConstr EmptySet
                      | WF S /\ (forall x, @take _ _ _ WellFormedSpace e x = S x) }.
  Proof.
    intro e.
    exists (take e); split.
    - unfold take.
      simpl.
      unfold WF_take.
      unfold take.
      simpl.
      unfold takeVect.
      match goal with
      |[|- WF (fun _ => nth ?x _)]  =>
       generalize (proj1 (List.nodup_In _ _ _) (In_ListIn _ x e eq_refl))
      end.
      intro wf_in.
      destruct (List.in_app_or _ _ _ wf_in) as [ tgt_table | in_rest ].
      + destruct (proj1 (List.in_map_iff _ _ _) tgt_table) as [ ty [ ty_eq ty_in ] ].
        destruct (proj2 (tgt_arrow_table_correct _) ty_in) as [ A [ B [ M [ MIn [isTgt A_eq ]]]] ].
        apply (WF_Arrow  _ M MIn);
          rewrite <- ty_eq;
          rewrite A_eq;
          simpl.
        * repeat rewrite sortType_inj.
          assumption.
        * reflexivity.
      + destruct (List.in_app_or _ _ _ in_rest) as [ lift_table | unit_case ].
        * destruct (proj1 (List.in_map_iff _ _ _) lift_table) as [ ty [ ty_eq ty_in ] ].
          destruct (proj2 (liftbox_tgt_table_correct _) ty_in) as [ A [ M [ MIn [ n [ isTgt [ isLiftable A_lvl ]]]]]].
          rewrite <- ty_eq.
          apply (WF_Box _ M MIn A n); try solve [ reflexivity | simpl; try rewrite sortType_inj; assumption ].
        * destruct unit_case as [ eq | devil ]; [| contradiction].
          rewrite <- eq.
          apply WF_Default; reflexivity.
    - intro; reflexivity.
  Qed.            

  Definition ApplicativeFragment_carrier:
    forall M A, ApplicativeFragment max_BoxLevel M A ->
           MiniMLBoxCarrier (typeToSort A EmptySet).
  Proof.
    intros M A appfrag.
    exists M.
    induction appfrag;
      rewrite sortType_inj in *.
    - exact (proj2_sig (Proofs _ _)).
    - apply TPI_Box.
      apply (TPI_Shift _ _ [] [] [[]]).
      assumption.
    - apply (TPI_Unbox _ _ []).
      assumption.
    - eapply TPI_App; eassumption.
  Defined.
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
  Definition WellFormed := WellFormed Ops.Terms Ops.Proofs.
  Instance WellFormedSpace: FunctionSpace WellFormed SigVar (VLTree TyConstr EmptySet) :=
    WellFormedSpace Ops.Terms Ops.Proofs.
  Instance WellFormedSpace_finite: NonEmptyFinite WellFormed :=
    WellFormedSpace_finite _ _.
  Instance WellFormedSpace_countable: Countable WellFormed :=
    @CountableFromFinite _ WellFormedSpace_finite.
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

Module Type NonEmptyFiniteWellFormedSpaceMiniMLSignature
       (Import Ops: MiniMLBoxOpsSpec)
       (Import TreeSpec: MiniMLBoxTreeSpec(Ops))
       (Import SigSpec: TreeSignatureSpec(TreeSpec)) <: NonEmptyFiniteWellFormedSpaceSignature(SigSpec).
  Instance WellFormedSpace_finite: NonEmptyFinite WellFormed := TreeSpec.WellFormedSpace_finite.
  Instance WellFormedSpace_countable: Countable WellFormed := TreeSpec.WellFormedSpace_countable.
End NonEmptyFiniteWellFormedSpaceMiniMLSignature.

Module Type MkMiniMLBoxSigSpec(Ops: MiniMLBoxOpsSpec).
  Declare Module TreeSpec: MiniMLBoxTreeSpec(Ops).
  Declare Module MkCLSig: MakeTreeSortCLSignature(TreeSpec).
  Declare Module WFFiniteSig: NonEmptyFiniteWellFormedSpaceMiniMLSignature(Ops)(TreeSpec)(MkCLSig.SigSpec).
End MkMiniMLBoxSigSpec.

Module Type MiniMLBoxAlgebra
       (Ops: MiniMLBoxOpsSpec)
       (MkSpec: MkMiniMLBoxSigSpec(Ops))
       (Import Alg: Algebraic(MkSpec.MkCLSig.SigSpec)).
  Import MkSpec.MkCLSig.SigSpec.
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
    destruct Fs as [ op subst args subsort ].
    unfold MiniMLBoxCarrier.
    destruct op as [ M n inprf | | | ].
    - exists M.
      generalize (subsort_eq _ _ subsort).
      intro s_eq; clear subsort.
      unfold range in s_eq.
      simpl in s_eq.
      rewrite (subst_irrelevant (WF_take Terms Proofs subst)) in s_eq.
      rewrite <- s_eq.
      simpl.
      rewrite sortType_inj.
      exact (proj2_sig (Ops.Proofs M (List.nth_error_In _ _ inprf))).
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
    induction gen as [ s op S args subsort argsgen IH ] using AlgebraicallyGenerated_ind'.
    revert args subsort argsgen IH.
    destruct op as [ M MIn | | | ]; intros args subsort argsgen IH.
    - simpl.
      rewrite <- (subsort_eq _ _ subsort).
      simpl.
      rewrite (subst_irrelevant (WF_take Terms Proofs S)).
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
      destruct (WellFormedSpace_sound _ _ S) as [ S' [ WFS S_eq ] ].
      apply A_Box.
      + exact (IH F1).
      + inversion WFS as [ ? ? ? ? gamma_eq | | ? ? ? gamma_eq ].
        * fold (sortToType (S' gamma)).
          rewrite <- S_eq in gamma_eq.
          simpl in gamma_eq.
          unfold sortToType in gamma_eq.
          rewrite gamma_eq.
          simpl.
          apply (Nat.le_max_l 1).
        * rewrite <- S_eq in *.
          etransitivity; [ eassumption | eapply (Nat.le_max_r 1); eassumption ].
        * rewrite <- S_eq in gamma_eq.
          simpl in gamma_eq.
          rewrite gamma_eq.          
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
    induction appfrag as [ M MPos MIn level | M A level IH | M A appfrag IH | M N A B appfragM IHM appfragN IHN ].
    - set (S := fun (v: SigVar) => typeToSort Ty_Unit EmptySet).
      assert (WF_S : WF Ops.Terms Ops.Proofs S).
      { apply WF_Default; reflexivity. }
      assert (sub: subsorts (applySubst (take (proj1_sig (WellFormedSpace_complete _ _ S WF_S)))
                                        (typeToSort (proj1_sig (Ops.Proofs M (List.nth_error_In _ _ MIn))) SigVar))
                            (typeToSort (proj1_sig (Ops.Proofs M (List.nth_error_In _ _ MIn))) EmptySet)).
      { simpl.
        rewrite (subst_irrelevant _).
        reflexivity. }     
      generalize (FromF _ MiniMLBox_Algebra _ (OP_Use _ M _ MIn)
                        (proj1_sig (WellFormedSpace_complete _ _ S WF_S))
                        tt sub (GeneratedArgs_nil _ _ _)).
      intro; eexists; eassumption.
    - set (S := fun (v: SigVar) => match v with | gamma => typeToSort A EmptySet | _ => typeToSort Ty_Unit EmptySet end).
      assert (WF_S : WF Ops.Terms Ops.Proofs S).
      { assert (WF_Contents: exists M MIn A n,
                   IsTgt (proj1_sig (Ops.Proofs M MIn)) A /\
                   IsLiftable n (sortToType (S gamma)) A).
        { revert level.
          clear ...
          intro level.
          induction level as [ M MPos MIn level | M A appfrag IH | M A appfrag IH | M N A B levelAB IHAB levelA IHA ].
          - exists M, (List.nth_error_In _ _ MIn), (proj1_sig (Ops.Proofs M  (List.nth_error_In _ _ MIn))), 0; split.
            + destruct (proj1_sig (Ops.Proofs M  (List.nth_error_In _ _ MIn))); left; reflexivity.
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
      assert (A_eq: (typeToSort A EmptySet) =
                    (applySubst (take (proj1_sig (WellFormedSpace_complete Terms Proofs S WF_S)))
                                            (Hole TyConstr SigVar gamma))).
      { generalize (proj2_sig (WellFormedSpace_complete _ _ S WF_S)).
        simpl.
        intro prf.
        rewrite prf.
        reflexivity. }
      revert Mprf genprf.
      rewrite A_eq.
      intros Mprf genprf.
      assert (subs: subsorts (applySubst (take
                                      (proj1_sig (WellFormedSpace_complete
                                                    Terms Proofs S WF_S)))
                                         (range (OP_Box Terms)))
                             (typeToSort (Ty_Box A) EmptySet)).
      { simpl.
        rewrite A_eq.
        reflexivity. }
      generalize (fun  gen => FromF _ MiniMLBox_Algebra (typeToSort (Ty_Box A) EmptySet)
                                 (OP_Box Ops.Terms) (proj1_sig (WellFormedSpace_complete _ _ S WF_S))
                                 (exist _ M Mprf, tt) subs gen).
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
      assert (A_eq: (typeToSort A EmptySet) =
                    (applySubst (take (proj1_sig (WellFormedSpace_complete Terms Proofs S WF_S)))
                                            (Hole TyConstr SigVar gamma))).
      { generalize (proj2_sig (WellFormedSpace_complete _ _ S WF_S)).
        simpl.
        intro prf.
        rewrite prf.
        reflexivity. }
      revert Mprf genprf.
      simpl.
      rewrite A_eq.
      intros Mprf genprf.
      generalize (fun  gen => FromF _ MiniMLBox_Algebra (applySubst (take
                                                                    (proj1_sig (WellFormedSpace_complete
                                                                                  Terms Proofs S WF_S)))
                                                                 (range (OP_Unbox Terms)))
                                 (OP_Unbox Ops.Terms)
                                 (proj1_sig (WellFormedSpace_complete _ _ S WF_S))
                                 (exist _ M Mprf, tt) (reflexivity _) gen).
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
      assert (A_eq: (typeToSort A EmptySet) =
                    (applySubst (take (proj1_sig (WellFormedSpace_complete Terms Proofs S WF_S)))
                                            (Hole TyConstr SigVar alpha))).
      { generalize (proj2_sig (WellFormedSpace_complete _ _ S WF_S)).
        simpl.
        intro prf.
        rewrite prf.
        reflexivity. }
      assert (B_eq: (typeToSort B EmptySet) =
                    (applySubst (take (proj1_sig (WellFormedSpace_complete Terms Proofs S WF_S)))
                                            (Hole TyConstr SigVar beta))).
      { generalize (proj2_sig (WellFormedSpace_complete _ _ S WF_S)).
        simpl.
        intro prf.
        rewrite prf.
        reflexivity. }
      revert Mprf Nprf Mgenprf Ngenprf.
      simpl.
      rewrite A_eq.
      rewrite B_eq.
      intros Mprf Nprf Mgenprf Ngenprf.
      generalize (fun gen => FromF _ MiniMLBox_Algebra
                                (applySubst (take (proj1_sig (WellFormedSpace_complete Terms Proofs S WF_S)))
                                            (Hole TyConstr SigVar beta))
                                (OP_Apply Ops.Terms)
                                (proj1_sig (WellFormedSpace_complete _ _ S WF_S))
                                (exist _ M Mprf, (exist _ N Nprf, tt))
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
    destruct f1 as [ op1 S1 args1 subsort1 ]. 
    destruct f2 as [ op2 S2 args2 subsort2 ].
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

Module Type MkMiniBoxCLAlgebra(Import Ops: MiniMLBoxOpsSpec).
  Declare Module MkSpec : MkMiniMLBoxSigSpec(Ops).
  Declare Module Types: IntersectionTypes(MkSpec.MkCLSig.Signature).
  Declare Module Terms: Terms(MkSpec.MkCLSig.Signature).
  Declare Module TypesCountable: CountableTypes(MkSpec.MkCLSig.Signature)(Types).
  Declare Module Embedding: ProperTreeSortEmbedding(MkSpec.TreeSpec)(MkSpec.MkCLSig)(Types).
  Module Type WFMod
  <: CountableProperWellFormedPredicate(MkSpec.MkCLSig.Signature)(Types)(Embedding)
  <: FiniteWellFormedPredicate(MkSpec.MkCLSig.Signature)(Types).
    Include EmbedWellFormedSpace(MkSpec.MkCLSig.Signature)(Types)(Embedding).
    Instance SubstitutionSpace_finite: Finite WellFormed := @IsFinite _ (WellFormedSpace_finite Terms Proofs).
    Instance SubstitutionSpace_countable: Countable WellFormed :=
      @CountableFromFinite _ (WellFormedSpace_finite Terms Proofs).
  End WFMod.    
  Declare Module WF: WFMod.  
  Declare Module CL: CombinatoryLogic(MkSpec.MkCLSig.Signature)(Types)(Terms)(WF).
  Declare Module CPL: ComputationalPathLemma(MkSpec.MkCLSig.Signature)(Types)(Terms)
                                            (TypesCountable)(WF)(CL).
  Declare Module Alg: Algebraic(MkSpec.MkCLSig.SigSpec).
  Declare Module MiniMLBoxAlg: MiniMLBoxAlgebra(Ops)(MkSpec)(Alg).
  Declare Module CLAlg : CombinatoryLogicAlgebra
                           (MkSpec.MkCLSig.Signature)
                           (Types)
                           (Terms)
                           (Embedding)
                           (TypesCountable)
                           (WF)
                           (CL)
                           (CPL)
                           (Alg).
  Declare Module CLFin: CombinatoryLogicWithFiniteSubstitutionSpace
                          (MkSpec.MkCLSig.Signature)
                          (Types)
                          (Terms)
                          (WF)
                          (CL).
  Declare Module CombinatorsFin: FiniteCombinators(MkSpec.MkCLSig.Signature).
  Declare Module CLInhab: CLFin.Inhabitation(CombinatorsFin).
End MkMiniBoxCLAlgebra.

Module ToMiniBoxCLAlgebra(Ops: MiniMLBoxOpsSpec) <: MkMiniBoxCLAlgebra(Ops).
  Include MkMiniBoxCLAlgebra(Ops).
End ToMiniBoxCLAlgebra.
