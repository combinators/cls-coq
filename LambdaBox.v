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

Inductive Ty: Set :=
| Const : nat -> Ty
| Arrow : Ty -> Ty -> Ty
| BoxTy : Ty -> Ty.


Definition pushVar {m: nat} (Context: Fin.t m -> Ty) (ty: Ty): Fin.t (S m) -> Ty :=
  fun (x: Fin.t (S m)) =>
    match x in Fin.t (S k) return (Fin.t k -> Ty) -> Ty with
    | Fin.F1 => fun _ => ty
    | Fin.FS k => fun ctxt => ctxt k
    end Context.

Definition popVar {m: nat} (Context: Fin.t (S m) -> Ty): Fin.t m -> Ty :=
  fun x => Context (Fin.FS x).

Definition topVarTy {m: nat} (Context: Fin.t (S m) -> Ty): Ty :=
  Context (Fin.F1).

Lemma pushTopTy_eq:
  forall {m : nat} (Context: Fin.t m -> Ty) (ty: Ty), topVarTy (pushVar Context ty) = ty.
Proof.
  intros m Context ty.
  reflexivity.
Qed.

Lemma pushPop_eq:
  forall {m : nat} (Context: Fin.t m -> Ty) (ty: Ty), popVar (pushVar Context ty) = Context.
Proof.
  intros m Context ty.
  unfold pushVar.
  unfold popVar.
  reflexivity.
Qed.

Inductive LambdaBox: forall {n m} (Delta: Fin.t n -> Ty) (Gamma: Fin.t m -> Ty), Ty -> Type :=
| Var : forall {n m : nat} (Delta: Fin.t n -> Ty) (Gamma: Fin.t m -> Ty) x, LambdaBox Delta Gamma (Gamma x)
| MVar : forall {n m: nat} (Delta: Fin.t n -> Ty) (Gamma: Fin.t m -> Ty) u, LambdaBox Delta Gamma (Delta u)
| App : forall {n m: nat} (Delta: Fin.t n -> Ty) (Gamma: Fin.t m -> Ty) sigma tau,
    LambdaBox Delta Gamma (Arrow sigma tau) ->
    LambdaBox Delta Gamma sigma ->
    LambdaBox Delta Gamma tau
| Lam : forall {n m: nat} (Delta: Fin.t n -> Ty) (Gamma: Fin.t (S m) -> Ty) tau,
    LambdaBox Delta Gamma tau ->
    LambdaBox Delta (popVar Gamma) (Arrow (topVarTy Gamma) tau)
| MLam : forall {n m: nat} (Delta: Fin.t (S n) -> Ty) (Gamma: Fin.t m -> Ty) tau,
    LambdaBox Delta Gamma tau ->
    LambdaBox (popVar Delta) Gamma (Arrow (topVarTy Delta) tau)
| Box: forall {n m: nat} (Delta: Fin.t n -> Ty) (Gamma: Fin.t 0 -> Ty) (Gamma': Fin.t m -> Ty) tau,
    LambdaBox Delta Gamma tau ->
    LambdaBox Delta Gamma' (BoxTy tau)
| LetBox: forall {n m: nat} (Delta: Fin.t (S n) -> Ty) (Gamma: Fin.t m -> Ty) sigma,
    LambdaBox (popVar Delta) Gamma (BoxTy (topVarTy Delta)) ->
    LambdaBox Delta Gamma sigma ->
    LambdaBox (popVar Delta) Gamma sigma.

Definition permute_gamma:
  forall {m n: nat} (Delta: Fin.t m -> Ty) (Gamma Gamma': Fin.t n -> Ty) sigma,
    (forall k, { k': _ | Gamma k = Gamma' k' }) ->
    LambdaBox Delta Gamma sigma ->
    LambdaBox Delta Gamma' sigma.
Proof.
  intros m n Delta Gamma Gamma' sigma gamma_gamma' Msigma.
  induction Msigma as [ ? ? ? ? x | | | ? ? ? ? ? ? IH | | | ].
  - destruct (gamma_gamma' x) as [ x' gamma_eq ].
    rewrite gamma_eq.
    exact (Var _ _ x').
  - eapply MVar.
  - eapply App; eauto.
  - assert (push_permute: forall k, { k' : Fin.t (S m) | Gamma k = pushVar Gamma' (topVarTy Gamma) k' }).
    { intro k.
      apply (Fin.caseS' k).
      - exists Fin.F1. reflexivity.
      - intro k'.
        destruct (gamma_gamma' k') as [ k'' gamma_eq ].
        exists (Fin.FS k'').
        simpl.
        rewrite <- gamma_eq.
        reflexivity. }     
    exact (Lam _ _ _ (IH _ push_permute)).
  - eapply MLam; eauto.
  - eapply Box; eauto.
  - eapply LetBox; eauto.
Defined.

Definition permute_delta:
  forall {m n: nat} (Delta Delta': Fin.t m -> Ty) (Gamma: Fin.t n -> Ty) sigma,
    (forall k, { k': _ | Delta k = Delta' k' }) ->
    LambdaBox Delta Gamma sigma ->
    LambdaBox Delta' Gamma sigma.
Proof.
  intros m n Delta Delta' Gamma sigma delta_delta' Msigma.
  induction Msigma as [ | ? ? ? ? u | | | ? ? ? ? ? ? IH | | ? ? ? ? ? ? IH ? IH' ].
  - eapply Var.
  - destruct (delta_delta' u) as [ u' delta_eq ].
    rewrite delta_eq.
    exact (MVar _ _ u').
  - eapply App; eauto.
  - eapply Lam; eauto.
  - assert (push_permute: forall k, { k' : Fin.t (S n) | Delta k = pushVar Delta' (topVarTy Delta) k' }).
    { intro k.
      apply (Fin.caseS' k).
      - exists Fin.F1. reflexivity.
      - intro k'.
        destruct (delta_delta' k') as [ k'' delta_eq ].
        exists (Fin.FS k'').
        simpl.
        rewrite <- delta_eq.
        reflexivity. }     
    exact (MLam _ _ _ (IH _ push_permute)).
  - eapply Box; eauto.
  - assert (push_permute: forall k, { k' : Fin.t (S n) | Delta k = pushVar Delta' (topVarTy Delta) k' }).
    { intro k.
      apply (Fin.caseS' k).
      - exists Fin.F1. reflexivity.
      - intro k'.
        destruct (delta_delta' k') as [ k'' delta_eq ].
        exists (Fin.FS k'').
        simpl.
        rewrite <- delta_eq.
        reflexivity. }
    exact (LetBox _ _ _ (IH _ delta_delta') (IH' _ push_permute)).
Defined.
 

Definition weaken_gamma:
  forall {m n: nat} (Delta: Fin.t m -> Ty) (Gamma: Fin.t n -> Ty) sigma tau,
    LambdaBox Delta Gamma sigma -> LambdaBox Delta (pushVar Gamma tau) sigma.
Proof.
  intros m n Delta Gamma sigma tau Msigma.
  induction Msigma as [ ? ? ? ? x | ? ? ? ? u | | ? ? ? ? sigma ? IH  | | | ].
  - exact (Var _ _ (Fin.FS x)).
  - exact (MVar _ _ u).
  - eapply App; eauto.
  - assert (IH': LambdaBox Delta (pushVar (pushVar (popVar Gamma) tau) (topVarTy Gamma)) sigma).
    { eapply permute_gamma; [ | exact IH ].
      intro k.
      apply (Fin.caseS' k); clear k.
      - exists (Fin.FS Fin.F1); reflexivity.
      - intro k.
        apply (Fin.caseS' k); clear k.
        + exists (Fin.F1); reflexivity.
        + intro k.
          exists (Fin.FS (Fin.FS k)); reflexivity. }
    generalize (Lam _ _ _ IH').
    rewrite pushPop_eq.
    rewrite pushTopTy_eq.
    intro; assumption.
  - eapply MLam; eauto.
  - eapply Box; eauto.
  - eapply LetBox; eauto.
Defined.

Definition weaken_delta:
  forall {m n: nat} (Delta: Fin.t m -> Ty) (Gamma: Fin.t n -> Ty) sigma tau,
    LambdaBox Delta Gamma sigma -> LambdaBox (pushVar Delta tau) Gamma sigma.
Proof.
  intros m n Delta Gamma sigma tau Msigma.
  induction Msigma as [ ? ? ? ? x | ? ? ? ? u | | | ? ? ? ? sigma ? IH  | | ? ? ? ? ? ? IH ? IH' ].
  - exact (Var _ _ x).
  - exact (MVar _ _ (Fin.FS u)).
  - eapply App; eauto.
  - eapply Lam; eauto.
  - assert (IH': LambdaBox (pushVar (pushVar (popVar Delta) tau) (topVarTy Delta)) Gamma sigma).
    { eapply permute_delta; [ | exact IH ].
      intro k.
      apply (Fin.caseS' k); clear k.
      - exists (Fin.FS Fin.F1); reflexivity.
      - intro k.
        apply (Fin.caseS' k); clear k.
        + exists (Fin.F1); reflexivity.
        + intro k.
          exists (Fin.FS (Fin.FS k)); reflexivity. }
    generalize (MLam _ _ _ IH').
    rewrite pushPop_eq.
    rewrite pushTopTy_eq.
    intro; assumption.
  - eapply Box; eauto.
  - assert (IH_perm: LambdaBox (popVar (pushVar (pushVar (popVar Delta) tau) (topVarTy Delta))) Gamma
                           (BoxTy (topVarTy Delta))).
    { eapply permute_delta; [ | exact IH ].
      intro k.
      rewrite pushPop_eq.
      exists k; reflexivity. }
    assert (topTy_eq: topVarTy Delta = topVarTy (pushVar (pushVar (popVar Delta) tau) (topVarTy Delta))).
    { rewrite pushTopTy_eq.
      reflexivity. }
    rewrite topTy_eq in IH_perm.
    assert (IH'_perm: LambdaBox (pushVar (pushVar (popVar Delta) tau) (topVarTy Delta)) Gamma sigma).
    { eapply permute_delta; [ | exact IH' ].
      intro k.
      apply (Fin.caseS' k); clear k.
      - exists (Fin.FS Fin.F1); reflexivity.
      - intro k.
        apply (Fin.caseS' k); clear k.
        + exists (Fin.F1); reflexivity.
        + intro k.
          exists (Fin.FS (Fin.FS k)); reflexivity. }
    generalize (LetBox _ _ _ IH_perm IH'_perm).
    rewrite pushPop_eq.
    intro; assumption.
Defined.

Definition MApp
           {m n: nat} (Delta: Fin.t m -> Ty) (Gamma: Fin.t n -> Ty)
           sigma tau
           (M: LambdaBox Delta Gamma (BoxTy (Arrow sigma tau)))
           (N: LambdaBox Delta Gamma (BoxTy sigma)): LambdaBox Delta Gamma (BoxTy tau).
Proof.
  rewrite <- (pushPop_eq Delta (Arrow sigma tau)).
  apply LetBox.
  - rewrite pushPop_eq.
    rewrite pushTopTy_eq.
    exact M.
  - rewrite <- (pushPop_eq _ sigma).
    apply LetBox.
    + rewrite pushPop_eq.
      rewrite pushTopTy_eq.
      apply weaken_delta.
      exact N.
    + apply (Box _ (fun k => Const 0) Gamma).
      apply (App _ _ sigma).
      * exact (MVar _ _ (Fin.FS (Fin.F1))).
      * exact (MVar _ _ Fin.F1).
Defined.


Section ClosedImplementations.
  Context { EmptyContext : Fin.t 0 -> Ty }.
  Definition Implementations := list { ty : _ & LambdaBox EmptyContext EmptyContext (BoxTy ty) }.

  Inductive TyConstr: Set :=
  | TyConstr_Const : nat -> TyConstr
  | TyConstr_Arrow : TyConstr
  | TyConstr_Box : TyConstr.

  Lemma TyConstr_eq_dec: forall (x y: TyConstr), { x = y } + { x <> y }.
  Proof.
    intros x y;
      destruct x as [ n | |];
      destruct y as [ m | |];
      solve [ left; reflexivity
            | right; intro devil; inversion devil
            | destruct (Nat.eq_dec n m) as [ eq | ineq ];
              [ left; rewrite eq; reflexivity
              | right; intro devil; inversion devil; contradiction ] ].
  Qed.              

  Instance TyConstrInfo : LabelInfo TyConstr :=
    {| labelArity :=
         fun (constr: TyConstr) =>
           match constr with
           | TyConstr_Const _ => 0
           | TyConstr_Arrow => 2
           | TyConstr_Box => 1
           end;
       successorVariance := fun _ _ => In |}.

  Definition tyConstrOrder := @eq TyConstr.

  Definition tyConstrToNat (ty: TyConstr) : nat :=
    match ty with
    | TyConstr_Const n => cantor_sum (inl n)
    | TyConstr_Arrow => cantor_sum (inr (cantor_sum (inl 0)))
    | TyConstr_Box => cantor_sum (inr (cantor_sum (inr 0)))
    end.
  Definition natToTyConstr (n: nat) : TyConstr :=
    match cantor_sum_inv n with
    | inl n => TyConstr_Const n
    | inr n =>
      match cantor_sum_inv n with
      | inl _ => TyConstr_Arrow
      | inr _ => TyConstr_Box
      end
    end.
  Lemma tyConstrToNat_inj: forall ty, natToTyConstr (tyConstrToNat ty) = ty.
  Proof.
    intro ty.
    unfold tyConstrToNat.
    unfold natToTyConstr.
    destruct ty;
      repeat rewrite cantor_sum_inj; reflexivity.
  Qed.
  Instance TyConstr_Countable : Countable TyConstr :=
    {| toNat := tyConstrToNat;
       fromNat := natToTyConstr;
       fromTo_id := tyConstrToNat_inj |}.
  
  Inductive SigVar : Set := alpha | beta.
  Lemma SigVar_eq_dec: forall (x y: SigVar), { x = y } + { x <> y }.
  Proof.
    intros x y;
      destruct x;
      destruct y;
      solve [ left; reflexivity | right; intro devil; inversion devil ].
  Qed.

  Instance SigVar_Finite : Finite SigVar :=
    {| cardinality := 2;
       toFin := fun x => match x with | alpha => F1 | beta => FS F1 end;
       fromFin := fun x => match x with | F1 => alpha | Fin.FS _ => beta end;
       fromToFin_id := fun x => match x with | alpha => eq_refl | beta  => eq_refl end |}.

  Inductive SigOp (from: Implementations): Set :=
  | TermOp : forall impl, List.In impl from -> SigOp from
  | ApplyOp : SigOp from
  | MApplyOp : SigOp from.

  Definition applyDom : t (VLTree TyConstr SigVar) 2 :=
    cons _ (Node _ _ TyConstr_Arrow (cons _ (Hole _ _ alpha) _ (cons _ (Hole _ _ beta) _ (nil _))))
         _ (cons _ (Hole _ _ alpha) _ (nil _)).

  Definition applyRange : VLTree TyConstr SigVar := (Hole _ _ beta).
  Definition mapplyRange : VLTree TyConstr SigVar :=
    Node _ _ TyConstr_Box
         (cons _ (Hole _ _ beta) _ (nil _)).
  
  Definition mapplyDom : t (VLTree TyConstr SigVar) 2 :=
    cons _ (Node _ _ TyConstr_Box
                 (cons _ (Node _ _ TyConstr_Arrow (cons _ (Hole _ _ alpha) _ (cons _ (Hole _ _ beta) _ (nil _))))
                       _ (nil _)))
         _ (cons _ (Node _ _ TyConstr_Box
                         (cons _ (Hole _ _ alpha) _ (nil _))) _ (nil _)).

  Fixpoint typeToSort (ty: Ty) (Var : Set): VLTree TyConstr Var :=
    match ty with
    | Const n => Node _ _ (TyConstr_Const n) (nil _)
    | Arrow sigma tau =>
      Node _ _ TyConstr_Arrow
           (cons _ (typeToSort sigma Var) _
                 (cons _ (typeToSort tau Var) _ (nil _)))
    | BoxTy sigma =>
      Node _ _ TyConstr_Box
           (cons _ (typeToSort sigma Var) _ (nil _))
    end.

     
  Definition MakeSignature (from: Implementations): Signature (VLTree TyConstr) SigVar (SigOp from) :=
    {| arity :=
         fun op =>
           match op with
           | TermOp _ _ _ => 0
           | ApplyOp _ => 2
           | MApplyOp _ => 2
           end;
       domain :=
         fun op =>
           match op as op' return t (VLTree TyConstr SigVar) (match op' with
                                                              | TermOp _ _ _ => 0
                                                              | ApplyOp _ => 2
                                                              | MApplyOp _ => 2
                                                              end) with
           | TermOp _ _ _ => nil _
           | ApplyOp _ => applyDom
           | MApplyOp _ => mapplyDom
           end;
       range :=
         fun op =>
           match op with
           | TermOp _ impl _ => typeToSort (BoxTy (projT1 impl)) SigVar
           | ApplyOp _ => applyRange
           | MApplyOp _ => mapplyRange
           end |}.
             
  
  Fixpoint sortToType (s: VLTree TyConstr EmptySet): Ty :=
    match s with
    | Node _ _ (TyConstr_Const n) _ => Const n
    | Node _ _ TyConstr_Arrow (cons _ sigma _ (cons _ tau _ _)) =>
      Arrow (sortToType sigma) (sortToType tau)
    | Node _ _ TyConstr_Box (cons _ sigma _ _) =>
      BoxTy (sortToType sigma)
    | _ => Const 0
    end.

  Lemma sortType_inj: forall ty, sortToType (typeToSort ty _) = ty.
  Proof.
    intro ty.
    induction ty as [ | src IH_src tgt IH_tgt | ty IH ].
    - reflexivity.
    - simpl.
      rewrite IH_src.
      rewrite IH_tgt.
      reflexivity.
    - simpl; rewrite IH; reflexivity.
  Qed.

  Definition LambdaBoxCarrier: VLTree TyConstr EmptySet -> Type :=
    fun s => LambdaBox EmptyContext EmptyContext (sortToType s).    
  
End ClosedImplementations.

Module Type LambdaBoxOpsSpec.
  Parameter EmptyContext : Fin.t 0 -> Ty.
  Parameter Terms : @Implementations EmptyContext.
  Parameter WellFormed: (SigVar -> @VLTree TyConstr TyConstrInfo EmptySet) -> Prop.
End LambdaBoxOpsSpec.

Module Type LambdaBoxTreeSpec(Ops: LambdaBoxOpsSpec) <: TreeSpec.
  Definition Label := TyConstr.
  Definition Var := SigVar.
  Definition LOrder := tyConstrOrder.

  Instance Info: LabelInfo Label := TyConstrInfo.
  Instance LOrder_pre: PreOrder LOrder :=
    {| PreOrder_Reflexive := eq_Reflexive; PreOrder_Transitive := eq_Transitive |}.
  
  Definition Operation := SigOp Ops.Terms.
  Definition WellFormed := Ops.WellFormed.
  Instance Sigma: Signature (VLTree Label) Var Operation :=
    MakeSignature Ops.Terms.

  Definition Var_eq_dec := SigVar_eq_dec.
  Definition Label_eq_dec := TyConstr_eq_dec.
  Definition LOrder_dec := TyConstr_eq_dec.

  Definition Vars_finite := SigVar_Finite.
  Definition Labels_countable := TyConstr_Countable.
  Definition GroundLabel: { l : Label | labelArity l = 0 } :=
    exist _ (TyConstr_Const 0) (@eq_refl _ 0).
End LambdaBoxTreeSpec.

Module Type MkLambdaBoxSigSpec(Ops: LambdaBoxOpsSpec).
  Declare Module TreeSpec: LambdaBoxTreeSpec(Ops).
  Declare Module TreeSigSpec: TreeSignatureSpec(TreeSpec).
  Declare Module SigSpec: TreeSortCLSignature(TreeSpec)(TreeSigSpec).
End MkLambdaBoxSigSpec.

Module Type LambdaBoxAlgebra
       (Ops: LambdaBoxOpsSpec)
       (MkSpec: MkLambdaBoxSigSpec(Ops))
       (Import Alg: Algebraic(MkSpec.SigSpec)).
  Import MkSpec.SigSpec.
  Import MkSpec.TreeSpec.
  Import Ops.

  Lemma subst_irrelevant: forall S ty, substitute S (typeToSort ty SigVar) = typeToSort ty EmptySet.
  Proof.
    intros S ty.
    induction ty as [ | src IH_src tgt IH_tgt | ty' IH ].
    - reflexivity.
    - simpl.
      rewrite IH_src.
      rewrite IH_tgt.
      reflexivity.
    - simpl; rewrite IH; reflexivity.
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
                                                  | TyConstr_Const _ => 0
                                                  | TyConstr_Arrow => 2
                                                  | TyConstr_Box => 1
                                                  end) _ _ _ successors_eq)) in successor_prfs.
    rewrite (vect_exist_eq _ _
                           (existT_fg_eq (t _)
                                         (fun l => match l with
                                                | TyConstr_Const _ => 0
                                                | TyConstr_Arrow => 2
                                                | TyConstr_Box => 1
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
    
  Lemma CL_Algebra: SigmaAlgebra (@LambdaBoxCarrier EmptyContext).
  Proof.
    unfold SigmaAlgebra.
    intros s Fs.
    destruct Fs as [ op subst wf_subst args subsort ].
    unfold LambdaBoxCarrier.
    destruct op as [ [ ty impl ] inprf | | ].
    - generalize (subsort_eq _ _ subsort).
      intro s_eq; clear subsort.
      unfold range in s_eq.
      simpl in s_eq.
      rewrite (subst_irrelevant subst) in s_eq.
      rewrite <- s_eq.
      simpl.
      rewrite sortType_inj.
      assumption.
    - simpl in args.
      destruct args as [ f [ x _ ] ].
      generalize (App _ _ _ _ f x).
      simpl in subsort.
      rewrite (subsort_eq _ _ subsort).
      intro; assumption.
    - simpl in args.
      destruct args as [ f [ x _ ] ].
      generalize (MApp _ _ _ _ f x).
      simpl in subsort.
      rewrite <- (subsort_eq _ _ subsort).
      intro; assumption.
  Defined.
  
End LambdaBoxAlgebra.