Require Import Coq.Classes.RelationClasses.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Vectors.Fin.
Require Import Coq.Vectors.Vector.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Eqdep_dec.
Require Import VectorQuantification.

Module Type SymbolSpecification.
  Parameter ConstructorSymbol: Set.
  Parameter constructorArity: ConstructorSymbol -> nat.
  Parameter ConstructorTaxonomy : ConstructorSymbol -> ConstructorSymbol -> Prop.
  Parameter CTPreorder : PreOrder ConstructorTaxonomy.

  Parameter VariableSymbol: Set.
  Parameter CombinatorSymbol: Set.

  Parameter VariableSymbol_eq_dec:
    forall (alpha beta: VariableSymbol), {alpha = beta} + {alpha <> beta}.
  Parameter ConstructorSymbol_eq_dec:
    forall (C1 C2: ConstructorSymbol), {C1 = C2} + {C1 <> C2}.

  Parameter ConstructorTaxonomy_dec:
    forall (C1 C2: ConstructorSymbol), { ConstructorTaxonomy C1 C2 } + { ConstructorTaxonomy C1 C2 -> False }.
End SymbolSpecification.

Module Type CombinatoryLogic(Symbols : SymbolSpecification).

  Export Symbols.

  
    
  Inductive PreType {T: Set}: Set :=
  | PT_omega: PreType 
  | PT_Const: forall (C: ConstructorSymbol), t T (constructorArity C) -> PreType
  | PT_Arrow: forall (sigma tau : T), PreType
  | PT_Inter: forall (sigma tau: T), PreType.
           
  Inductive TypeScheme: Set :=
  | Var: forall alpha: VariableSymbol, TypeScheme
  | Skeleton: forall skel: @PreType TypeScheme, TypeScheme.

  Fixpoint TypeScheme_rect'
           (P: TypeScheme -> Type)
           (var_case: forall alpha, P (Var alpha))
           (omega_case: P (Skeleton PT_omega))
           (const_case: forall C (ts: t TypeScheme (constructorArity C))
                          (ps: ForAll' P ts),
               P (Skeleton (PT_Const C ts)))
           (arrow_case: forall sigma tau,
               P sigma -> P tau ->
               P (Skeleton (PT_Arrow sigma tau)))
           (inter_case: forall sigma tau,
               P sigma -> P tau ->
               P (Skeleton (PT_Inter sigma tau)))
           (type: TypeScheme) {struct type}: P type :=
    match type with
    | Var alpha => var_case alpha
    | Skeleton (PT_omega) => omega_case
    | Skeleton (PT_Const C types) =>
      const_case C types
                 ((fix proof_args n (args: t TypeScheme n): ForAll' P args :=
                     match args with
                     | nil _ => ForAll'_nil _
                     | cons _ ty _ tys =>
                       ForAll'_cons _ _ _
                                   (TypeScheme_rect' P
                                                    var_case omega_case
                                                    const_case arrow_case
                                                    inter_case ty)
                                   (proof_args _ tys)
                     end) _ types)
    | Skeleton (PT_Arrow sigma tau) =>
      arrow_case _ _
                 (TypeScheme_rect' P var_case omega_case
                                  const_case arrow_case
                                  inter_case sigma)
                 (TypeScheme_rect' P var_case omega_case
                                  const_case arrow_case
                                  inter_case tau)
    | Skeleton (PT_Inter sigma tau) =>
      inter_case _ _
                 (TypeScheme_rect' P var_case omega_case
                                  const_case arrow_case
                                  inter_case sigma)
                 (TypeScheme_rect' P var_case omega_case
                                  const_case arrow_case
                                  inter_case tau)
    end.
            
  Inductive IntersectionType: Set :=
  | Ty: forall sigma : @PreType IntersectionType, IntersectionType.

  
  Fixpoint IntersectionType_rect'
           (P: IntersectionType -> Type)
           (omega_case: P (Ty PT_omega))
           (const_case: forall C (ts: t IntersectionType (constructorArity C)),
                          ForAll' P ts -> (P (Ty (PT_Const C ts))))
           (arrow_case: forall sigma tau,
               P sigma -> P tau ->
               P (Ty (PT_Arrow sigma tau)))
           (inter_case: forall sigma tau,
               P sigma -> P tau ->
               P (Ty (PT_Inter sigma tau)))
           (type: IntersectionType) {struct type}: P type :=
    match type with
    | Ty (PT_omega) => omega_case
    | Ty (PT_Const C types) =>
      const_case _ _
                 ((fix proof_args n (args: t IntersectionType n): ForAll' P args :=
                     match args as args return ForAll' P args with
                     | nil _  => ForAll'_nil _
                     | cons _ arg _ args' =>
                       ForAll'_cons _ _ _
                                    (IntersectionType_rect' P omega_case
                                                            const_case arrow_case
                                                            inter_case
                                                            arg)
                                    (proof_args _ args')
                     end) _ types)
    | Ty (PT_Arrow sigma tau) =>
      arrow_case _ _
                 (IntersectionType_rect' P omega_case
                                  const_case arrow_case
                                  inter_case sigma)
                 (IntersectionType_rect' P omega_case
                                  const_case arrow_case
                                  inter_case tau)
    | Ty (PT_Inter sigma tau) =>
      inter_case _ _
                 (IntersectionType_rect' P omega_case
                                  const_case arrow_case
                                  inter_case sigma)
                 (IntersectionType_rect' P omega_case
                                  const_case arrow_case
                                  inter_case tau)
    end.

  Fixpoint IntersectionType_eq_dec (sigma tau : IntersectionType) {struct sigma}: {sigma = tau} + {sigma <> tau}.
  Proof.
    revert tau.
    destruct sigma as [ [ | C ts | sigma1 sigma2 | sigma1 sigma2 ]  ] ;
      intros [ tau ];
      destruct tau;
      try solve [
            left; reflexivity
          | right; intro devil; inversion devil
          | destruct (IntersectionType_eq_dec sigma1 sigma)
            as [ sigma_eq | sigma_ineq ];
            [ | right; intro devil; injection devil as devil; contradiction ];
            destruct (IntersectionType_eq_dec sigma2 tau)
              as [ tau_eq | tau_ineq ];
              [ | right; intro devil; injection devil as devil; contradiction ];
            left; rewrite sigma_eq; rewrite tau_eq; reflexivity
          ].
    - match goal with
      | [ |- context[ Ty (PT_Const ?C ?ts) = Ty (PT_Const ?C' ?ts') ] ] =>
        destruct (ConstructorSymbol_eq_dec C C') as [ CC'_eq | CC'_not_eq ];
          [ revert ts';
            rewrite <- CC'_eq;
            intro ts';
            clear C' CC'_eq;
            destruct (Vector_eq_dec IntersectionType_eq_dec ts ts')
              as [ ts_eq  | ts_ineq ];
            [ left; rewrite ts_eq; reflexivity | right; intro devil ]
          | right; intro devil; inversion devil; contradiction ]
      end.
      contradict ts_ineq.
      injection devil as devil.
      apply (inj_pair2_eq_dec _ (ConstructorSymbol_eq_dec) _ _ _ _ devil).
  Qed.

  Definition liftPreType (sigma: @PreType IntersectionType): IntersectionType :=
    Ty sigma.
  
  Definition omega: IntersectionType := liftPreType PT_omega.
  Definition Const (C : ConstructorSymbol)
             (sigmas: t IntersectionType (constructorArity C)): IntersectionType :=
    liftPreType (PT_Const C sigmas).
  Definition Arrow (sigma tau: IntersectionType): IntersectionType :=
    liftPreType (PT_Arrow sigma tau).
  Definition Inter (sigma tau: IntersectionType): IntersectionType :=
    liftPreType (PT_Inter sigma tau).

  Definition omegaScheme: TypeScheme := Skeleton PT_omega.
  Definition ConstScheme (C : ConstructorSymbol)
             (sigmas: t TypeScheme (constructorArity C)): TypeScheme :=
    Skeleton (PT_Const C sigmas).
  Definition ArrowScheme (sigma tau: TypeScheme): TypeScheme :=
    Skeleton (PT_Arrow sigma tau).
  Definition InterScheme (sigma tau: TypeScheme): TypeScheme :=
    Skeleton (PT_Inter sigma tau).

  Fixpoint unfreeze (sigma: IntersectionType): TypeScheme :=
    match sigma with
    | Ty (PT_omega) => Skeleton (PT_omega)
    | Ty (PT_Const c tys) => Skeleton (PT_Const c (map unfreeze tys))
    | Ty (PT_Arrow src tgt) => Skeleton (PT_Arrow (unfreeze src) (unfreeze tgt))
    | Ty (PT_Inter l r) => Skeleton (PT_Inter (unfreeze l) (unfreeze r))
    end.

  Fixpoint intersect {n : nat} (sigmas: t IntersectionType n): IntersectionType :=
    match sigmas with
    | nil _ => omega
    | cons _ h _ (nil _) => h
    | cons _ h _ tl => Inter h (intersect tl)
    end.

  Fixpoint intersectSchemes {n : nat} (sigmas: t TypeScheme n): TypeScheme :=
    match sigmas with
    | nil _ => omegaScheme
    | cons _ h _ (nil _) => h
    | cons _ h _ tl => InterScheme h (intersectSchemes tl)
    end.
    
  Local Open Scope type_scope.
  Import EqNotations.
  Inductive Subtypes : IntersectionType -> IntersectionType -> Prop :=
  | ST_Ax: forall C_1 C_2 (arityEq: constructorArity C_1 = constructorArity C_2),
      ConstructorTaxonomy C_1 C_2 ->
      forall sigmas taus,
        Forall2 Subtypes sigmas (rew <- arityEq in taus) ->
        Const C_1 sigmas <= Const C_2 taus
  | ST_InterMeetLeft: forall sigma tau,
      Inter sigma tau <= sigma
  | ST_InterMeetRight: forall sigma tau,
      Inter sigma tau <= tau
  | ST_InterIdem: forall sigma,
      sigma <= Inter sigma sigma
  | ST_InterArrowDistrib: forall sigma tau_1 tau_2,
      Inter (Arrow sigma tau_1) (Arrow sigma tau_2) <= Arrow sigma (Inter tau_1 tau_2)
  | ST_InterConstDistrib: forall C sigmas taus,
      Inter (Const C sigmas) (Const C taus) <= Const C (map2 Inter sigmas taus)
  | ST_SubtypeDistrib: forall sigma_1 tau_1 sigma_2 tau_2,
      sigma_1 <= sigma_2 ->
      tau_1 <= tau_2 ->
      Inter sigma_1 tau_1 <= Inter sigma_2 tau_2
  | ST_CoContra: forall sigma_1 tau_1 sigma_2 tau_2,
      sigma_2 <= sigma_1 ->
      tau_1 <= tau_2 ->
      Arrow sigma_1 tau_1 <= Arrow sigma_2 tau_2
  | ST_OmegaTop: forall sigma, sigma <= omega
  | ST_OmegaArrow: omega <= Arrow omega omega
  | ST_Trans: forall sigma tau rho,
      sigma <= tau -> tau <= rho -> sigma <= rho
  where "sigma <= tau" := (Subtypes sigma tau).

  Instance ST_Trans': Transitive Subtypes := ST_Trans.
  Instance ST_Refl: Reflexive Subtypes.
  Proof.
    intro sigma.
    transitivity (Inter sigma sigma).
    - apply ST_InterIdem.
    - apply ST_InterMeetLeft.
  Qed.

  Instance ST_Preorder : PreOrder Subtypes :=
    {| PreOrder_Reflexive := ST_Refl;
       PreOrder_Transitive := ST_Trans' |}.

  Definition ST_Both: forall sigma tau rho, sigma <= tau -> sigma <= rho -> sigma <= Inter tau rho.
  Proof.
    intros sigma tau rho sigmatau sigmarho.
    transitivity (Inter sigma sigma).
    - apply ST_InterIdem.
    - apply ST_SubtypeDistrib; assumption.
  Defined.

  Definition ST_ReassocRight: forall sigma tau rho,
      Inter sigma (Inter tau rho) <= Inter (Inter sigma tau) rho.
  Proof.
    intros sigma tau rho.
    apply ST_Both.
    - apply ST_Both.
      + apply ST_InterMeetLeft.
      + transitivity (Inter tau rho).
        * apply ST_InterMeetRight.
        * apply ST_InterMeetLeft.
    - transitivity (Inter tau rho).
      + apply ST_InterMeetRight.
      + apply ST_InterMeetRight.
  Qed.

  Definition ST_ReassocLeft: forall sigma tau rho,
      Inter (Inter sigma tau) rho <= Inter sigma (Inter tau rho).
  Proof.
    intros sigma tau rho.
    apply ST_Both.
    - transitivity (Inter sigma tau).
      + apply ST_InterMeetLeft.
      + apply ST_InterMeetLeft.
    - apply ST_Both.
      + transitivity (Inter sigma tau).
        * apply ST_InterMeetLeft.
        * apply ST_InterMeetRight.
      + apply ST_InterMeetRight.
  Qed.

  Lemma ST_intersect: forall sigma {n} (taus: t IntersectionType n),
      Forall (fun tau => sigma <= tau) taus -> sigma <= intersect taus.
  Proof.
    intros sigma n taus.
    induction taus; intro prfs.
    - apply ST_OmegaTop.
    - inversion prfs
        as [ | ? ? ? prfTau prfTaus nEq [ tauEq tausEq ] ].
      dependent rewrite tausEq in prfTaus.
      clear nEq tauEq tausEq.
      destruct taus.
      + assumption.
      + apply ST_Both; auto.
  Qed.

  Lemma ST_intersect_ge: forall sigma {n} (taus: t IntersectionType n),
      sigma <= intersect taus -> Forall (fun tau => sigma <= tau) taus.
  Proof.
    intros sigma n taus.
    induction taus as [ | ? ? ? IHtaus ]; intro sigma_le.
    - apply Forall_nil.
    - apply Forall_cons.
      + destruct taus; simpl in sigma_le.
        * assumption.
        * rewrite (ST_InterMeetLeft) in sigma_le.
          assumption.
      + destruct taus; simpl in sigma_le.
        * apply IHtaus.
          apply ST_OmegaTop.
        * rewrite (ST_InterMeetRight) in sigma_le.
          apply IHtaus.
          assumption.
  Qed.

  Lemma ST_intersect_map_le_hom:
    forall {n} (taus: t IntersectionType n)
      (f: IntersectionType -> IntersectionType)
      (f_le: forall sigma, f sigma <= sigma),
      intersect (map f taus) <= intersect taus.
  Proof.
    intros n taus f f_le.
    induction taus as [ | tau n taus IH ].
    - reflexivity.
    - destruct taus as [ | tau' taus ].
      + apply f_le.
      + apply ST_Both.
        * etransitivity; [ | apply (f_le tau)].
          apply ST_InterMeetLeft.
        * etransitivity; [ | apply IH ].
          apply ST_InterMeetRight.
  Qed.

  Lemma ST_intersect_map_ge_hom:
    forall {n} (taus: t IntersectionType n)
      (f: IntersectionType -> IntersectionType)
      (f_ge: forall sigma, sigma <= f sigma),
      intersect taus <= intersect (map f taus).
  Proof.
    intros n taus f f_ge.
    induction taus as [ | tau n taus IH ].
    - reflexivity.
    - destruct taus as [ | tau' taus ].
      + apply f_ge.
      + apply ST_Both.
        * etransitivity; [ | apply (f_ge tau)].
          apply ST_InterMeetLeft.
        * etransitivity; [ | apply IH ].
          apply ST_InterMeetRight.
  Qed.

  Lemma ST_intersect_map2_fst_le_hom {T : Type}:
    forall {n} (taus: t IntersectionType n) (xs: t T n)
      (f: IntersectionType -> T -> IntersectionType)
      (f_le: forall sigma x, f sigma x <= sigma),
      intersect (map2 f taus xs) <= intersect taus.
  Proof.
    intros n.
    induction n as [ | n IH ]; intros taus xs f f_le.
    - apply (fun r => case0 (fun taus => intersect (map2 f taus _) <= intersect taus) r taus).
      apply (fun r => case0 (fun xs => intersect (map2 f _ xs) <= intersect _) r xs).
      reflexivity.
    - apply (caseS' taus).
      clear taus; intros tau taus.
      apply (caseS' xs).
      clear xs; intros x xs.
      destruct taus.
      + apply (fun r => case0 (fun xs => intersect (map2 _ _ (cons _ x _ xs)) <= _) r xs).
        apply f_le.
      + apply (caseS' xs).
        clear xs; intros x' xs.
        apply ST_Both.
        * etransitivity; [ apply ST_InterMeetLeft | apply f_le ].
        * etransitivity; [ apply ST_InterMeetRight | apply IH ].
          apply f_le.
  Qed.

  Lemma ST_intersect_map2_fst_ge_hom {T : Type}:
    forall {n} (taus: t IntersectionType n) (xs: t T n)
      (f: IntersectionType -> T -> IntersectionType)
      (f_ge: forall sigma x, sigma <= f sigma x ),
      intersect taus <= intersect (map2 f taus xs).
  Proof.
    intros n.
    induction n as [ | n IH ]; intros taus xs f f_ge.
    - apply (fun r => case0 (fun taus => intersect taus <= intersect (map2 f taus _)) r taus).
      apply (fun r => case0 (fun xs => _ <= intersect (map2 f _ xs)) r xs).
      reflexivity.
    - apply (caseS' taus).
      clear taus; intros tau taus.
      apply (caseS' xs).
      clear xs; intros x xs.
      destruct taus.
      + apply (fun r => case0 (fun xs => _ <= intersect (map2 _ _ (cons _ x _ xs))) r xs).
        apply f_ge.
      + apply (caseS' xs).
        clear xs; intros x' xs.
        apply ST_Both.
        * etransitivity; [ apply ST_InterMeetLeft | apply f_ge ].
        * etransitivity; [ apply ST_InterMeetRight | ].
          apply (IH (cons _ _ _ taus) (cons _ x' _ xs)).
          apply f_ge.
  Qed.
      
  
  Inductive Path: IntersectionType -> Prop :=
  | Path_Const: forall C args, PathArgs args -> Path (Const C args)
  | Path_Arr: forall sigma tau, Path tau -> Path (Arrow sigma tau)
  with PathArgs: forall {n}, t IntersectionType n -> Prop :=
       | PathArgs_nil: PathArgs (nil _)
       | PathArgs_cons_arg: forall n sigma, Path sigma -> PathArgs (cons _ sigma _ (const omega n))
       | PathArgs_cons_omega: forall n args, PathArgs args -> PathArgs (cons _ omega n args).

  Fixpoint Path_tgt (sigma: IntersectionType): IntersectionType :=
    match sigma with
    | Ty (PT_Arrow _ tgt) => Path_tgt tgt
    | x => x
    end.

  Fixpoint Path_params (sigma: IntersectionType): { n : _ & t IntersectionType n }:=
    match sigma with
    | Ty (PT_Arrow src tgt) =>
      match Path_params tgt with
      | existT _ n params => existT _ _ (cons _ src _ params)
      end
    | x => existT _ _ (nil _)
    end.

  Inductive Organized: IntersectionType -> Prop :=
  | Organized_Path: forall sigma, Path sigma -> Organized sigma
  | Organized_Cons: forall sigma tau, Path sigma -> tau <> omega -> Organized tau -> Organized (Inter sigma tau)
  | Organized_Omega: Organized omega. 

  Lemma ST_omegas {n: nat} (ts: t IntersectionType n):
    Forall2 Subtypes ts (const omega n).
  Proof.
    induction ts.
    - apply Forall2_nil.
    - apply Forall2_cons.
      + apply ST_OmegaTop.
      + assumption.
  Qed.
  
  Lemma ST_Diag {n: nat} (args: t IntersectionType n):
    Forall (Forall2 Subtypes args) (diag omega args).
  Proof.
    apply nth_Forall.
    intro k.
    rewrite (diag_spec_outer).
    induction args as [ | h n tl IHargs ].
    - inversion k.
    - apply (Fin.caseS' k).
      + apply Forall2_cons.
        * reflexivity.
        * apply ST_omegas.
      + intro k'.
        apply Forall2_cons.
        * apply ST_OmegaTop.
        * simpl.
          fold (dirac omega (nth tl k') k').
          apply IHargs.
  Qed.
  
  Lemma ST_Diag_Ctor (C: ConstructorSymbol) (args: t IntersectionType (constructorArity C)):
    Const C args <= intersect (map (Const C) (diag omega args)).
  Proof.
    apply ST_intersect.
    apply (Forall_map).
    rewrite (map_id _ (fun x => x) (fun x => eq_refl _)).
    apply (map_Forall (diag omega args) (Subtypes (Const C args)) (Const C)).
    apply (Forall_ap _ (Forall2 Subtypes args)).
    + apply Forall_tautology.
      intros xs le_xs.
      apply (ST_Ax C C eq_refl).
      * reflexivity.
      * assumption.
    + apply ST_Diag.
  Qed.  

  Definition intersect_pointwise {n: nat} {m: nat} (xss: t (t IntersectionType n) m): t IntersectionType n := 
    match xss with
    | nil _ => const omega n
    | xss => fold_right (map2 Inter) (shiftout xss) (last xss)
    end.

  Lemma intersect_pointwise_shiftout {n: nat} {m: nat}:
    forall (xs: t IntersectionType n) (xss: t (t IntersectionType n) (S m)),
      intersect_pointwise (cons _ xs _ xss) = map2 Inter xs (intersect_pointwise xss).
  Proof.
    intro xs.
    destruct m;
      intros xss;
      apply (caseS' xss).
      clear xss; intros xs' xss.
    - apply
        (fun r =>
           case0 (fun xss => intersect_pointwise (cons _ _ _ (cons _ _ _ xss)) = _)
                 r xss).
      reflexivity.
    - reflexivity.
  Qed.     

  Lemma intersect_pointwise_spec {n: nat} {m: nat}:
    forall (xss: t (t IntersectionType n) m) k,
      nth (intersect_pointwise xss) k = intersect (map (fun xs => nth xs k) xss).
  Proof.
    induction m as [ | m IHm ].
    - intros xss k.
      apply (fun r => case0 (fun xss => nth (intersect_pointwise xss) k = _) r xss).
      apply (const_nth).
    - intros xss k.
      apply (caseS' xss).
      clear xss; intros xs xss.
      destruct xss.
      + reflexivity.
      + rewrite (intersect_pointwise_shiftout _ _).
        rewrite (nth_map2 _ _ _ _ _ _ eq_refl eq_refl).
        rewrite (IHm _ k).
        reflexivity.
  Qed.
        

  Lemma ST_intersect_pointwise_ConstDistrib {n: nat} (C: ConstructorSymbol):
    forall (argss : t (t IntersectionType (constructorArity C)) n),
      n > 0 ->
      intersect (map (Const C) argss) <= Const C (intersect_pointwise argss).
  Proof.
    induction n as [ | n IHn ]; intros argss nPositive.
    - inversion nPositive.
    - apply (caseS' argss).
      clear argss.
      intros args argss.
      destruct argss as [ | args' ? argss ].
      + reflexivity.
      + set (IH := IHn (cons _ args' _ argss) (Nat.lt_0_succ _)).
        transitivity (Inter (Const C args) (Const C (intersect_pointwise (cons _ args' _ argss)))).
        * apply ST_Both.
          { apply ST_InterMeetLeft. }
          { etransitivity; [ apply ST_InterMeetRight | exact IH ]. }
        * apply ST_InterConstDistrib.
  Qed.

 

  Lemma ST_diag_pointwise {n : nat}:
    forall (xs: t IntersectionType n),
      Forall2 Subtypes (intersect_pointwise (diag omega xs)) xs.
  Proof.
    intro xs.
    apply nth_Forall2.
    intro k.
    rewrite intersect_pointwise_spec.
    rewrite diag_diag.
    induction k as [ | ? k IHk ].
    - destruct n.
      + reflexivity.
      + etransitivity; [ apply ST_InterMeetLeft | reflexivity ].
    - apply (caseS' xs).
      clear xs; intros x xs.
      simpl.
      destruct (dirac omega (nth xs k) k) eqn:dx_eq.
      + inversion k.
      + rewrite <- dx_eq.
        etransitivity; [ apply ST_InterMeetRight | apply IHk].
  Qed.   

  Lemma ST_Ctor_Diag (C: ConstructorSymbol) (args: t IntersectionType (constructorArity C)):
    constructorArity C > 0 ->
    intersect (map (Const C) (diag omega args)) <= Const C args.
  Proof.
    intros arityPositive.
    rewrite (ST_intersect_pointwise_ConstDistrib C _ arityPositive).
    apply (ST_Ax C C eq_refl).
    + reflexivity.
    + apply ST_diag_pointwise.
  Qed.

  Fixpoint factorize (sigma: IntersectionType): { n : nat & t IntersectionType n } :=
    match sigma with
    | Ty (PT_omega) => existT _ 0 (nil _)
    | Ty (PT_Inter sigma tau) =>
      let sigmaFactors := factorize sigma in
      let tauFactors := factorize tau in
        existT _ ((projT1 sigmaFactors) + (projT1 tauFactors))%nat
               (append (projT2 sigmaFactors) (projT2 tauFactors))
    | sigma => existT _ 1 (cons _ sigma _ (nil _))
    end.

    
  Lemma ST_intersect_append_le {n m : nat}:
    forall (sigmas: t IntersectionType n) (taus : t IntersectionType m),
      intersect (append sigmas taus) <= Inter (intersect sigmas) (intersect taus).
  Proof.
    intros sigmas taus.
    induction sigmas as [ | sigma ? sigmas IH ].
    - apply ST_Both; [ apply ST_OmegaTop | reflexivity ].
    - destruct sigmas as [ | sigma' ? sigmas ].
      + destruct taus.
        * apply ST_Both; [ reflexivity | apply ST_OmegaTop ].
        * reflexivity.
      + simpl.
        etransitivity;
          [ |
            exact (ST_ReassocRight sigma (intersect (cons _ sigma' _ sigmas)) (intersect taus))
          ].
        apply ST_Both.
        * apply ST_InterMeetLeft.
        * rewrite ST_InterMeetRight.
          exact IH.
  Qed.
  
  Lemma ST_intersect_append_ge {n m : nat}:
    forall (sigmas: t IntersectionType n) (taus : t IntersectionType m),
      Inter (intersect sigmas) (intersect taus) <= intersect (append sigmas taus).
  Proof.
    intros sigmas taus.
    induction sigmas as [ | sigma ? sigmas IH ].
    - apply ST_InterMeetRight.
    - destruct sigmas as [ | sigma' ? sigmas ].
      + simpl.
        destruct taus.
        * apply ST_InterMeetLeft.
        * reflexivity.
      + simpl.
        etransitivity;
          [ exact (ST_ReassocLeft sigma (intersect (cons _ sigma' _ sigmas)) (intersect taus))
          | ].
        apply ST_Both.
        * apply ST_InterMeetLeft.
        * rewrite ST_InterMeetRight.
          exact IH.
  Qed.
          
  
  Lemma ST_factorize_le:
    forall sigma, intersect (projT2 (factorize sigma)) <= sigma.
  Proof.
    intro sigma.
    induction sigma using IntersectionType_rect';
      try solve [ simpl; reflexivity ].
    simpl.     
    rewrite ST_intersect_append_le.
    apply ST_Both.
    - rewrite ST_InterMeetLeft.
      assumption.
    - rewrite ST_InterMeetRight.
      assumption.
  Qed.

  Lemma ST_factorize_ge:
    forall sigma, sigma <= intersect (projT2 (factorize sigma)).
  Proof.
    intro sigma.
    induction sigma as [ | | | sigma1 sigma2 IHsigma1 IHsigma2 ] using IntersectionType_rect' ;
      try solve [ simpl; reflexivity ].
    simpl.
    etransitivity.
    - apply ST_Both.
      + etransitivity; [ apply ST_InterMeetLeft | ].
        apply IHsigma1.
      + etransitivity; [ apply ST_InterMeetRight | ].
        apply IHsigma2.
    - apply ST_intersect_append_ge.
  Qed.

  Definition factorize_argument (C: ConstructorSymbol)
             (args: t IntersectionType (constructorArity C))
             (pos: Fin.t (constructorArity C)): { n : _ & t IntersectionType (S n) }:=
    match factorize (nth args pos) with
    | existT _ _ (nil _) =>
      existT _ 0 (map (fun arg => Const C (replace args pos arg)) (cons _ omega _ (nil _)))
    | existT _ _ xs =>
      existT _ _ (map (fun arg => Const C (replace args pos arg)) xs)
    end.


  Lemma ST_omega_factors: forall sigma, factorize sigma = existT _ 0 (nil _) -> omega <= sigma.
  Proof.
    intro sigma.
    induction sigma
      as [ | | | sigma1 sigma2 IHsigma1 IHsigma2 ] using IntersectionType_rect';
      intro factors_eq;
      try solve [ inversion factors_eq ].
    - reflexivity.
    - apply ST_Both;
      [ apply IHsigma1 | apply IHsigma2 ];
      simpl in factors_eq;
      destruct (factorize sigma1) as [ n_sigma1 [ | x ? xs ] ];
        destruct (factorize sigma2) as [ n_sigma2 [ | y ? ys ] ];
        solve [ reflexivity | inversion factors_eq ].
  Qed.        
        
  Lemma ST_factorize_argument_le (C: ConstructorSymbol) (args: t IntersectionType (constructorArity C)):
    forall pos, intersect (projT2 (factorize_argument C args pos)) <= Const C args.
  Proof.
    intro pos.      
    unfold factorize_argument.
    destruct (factorize (nth args pos)) as [ n [ | x n_xs xs ] ] eqn:argfactors_eq.
    - simpl.
      apply (ST_Ax C C eq_refl); [ reflexivity | ].
      apply nth_Forall2.
      intro k.
      destruct (Fin.eq_dec k pos) as [ pos_eq | pos_ineq ].
      + rewrite (replace_replaced _ _ _ _ pos_eq).
        unfold eq_rect_r.
        simpl.
        apply ST_omega_factors.
        rewrite pos_eq.
        assumption.
      + rewrite (replace_others _ _ _ _ pos_ineq).
        unfold eq_rect_r.
        simpl.
        reflexivity.
    - simpl.
      rewrite map_fg.
      rewrite (ST_intersect_pointwise_ConstDistrib C (map (replace args pos) (cons _ x _ xs)) (Nat.lt_0_succ _)).
      apply (ST_Ax _ _ eq_refl); [ reflexivity | ].
      apply nth_Forall2.
      intro k.
      destruct (Fin.eq_dec k pos) as [ pos_eq | pos_ineq ].
      + rewrite intersect_pointwise_spec.
        rewrite <- map_fg.
        rewrite (map_extensional _ _ _ (fun x => replace_replaced _ _ _ x pos_eq)).
        rewrite (map_id _ _ (fun x => eq_refl x)).
        rewrite pos_eq.
        set (argfactors_eq' := f_equal (fun xs => intersect (projT2 xs)) argfactors_eq).
        simpl in argfactors_eq'.
        simpl.
        rewrite <- argfactors_eq'.
        apply (ST_factorize_le).
      + rewrite intersect_pointwise_spec.
        rewrite <- map_fg.
        rewrite (map_extensional _ _ _ (fun x => replace_others _ _ _ x pos_ineq)).
        rewrite (map_const _ _ (nth args k) (fun x => eq_refl)).
        simpl.
        destruct (const (nth args k) n_xs).
        * reflexivity.
        * apply ST_InterMeetLeft.
  Qed.

  Lemma ST_intersect_nth {n: nat}:
    forall (xs : t IntersectionType n) k, intersect xs <= nth xs k.
  Proof.
    intro xs.
    induction xs as [ | ? ? xs IHxs ]; intro k.
    - inversion k.
    - apply (Fin.caseS' k).
      + destruct xs.
        * reflexivity.
        * apply ST_InterMeetLeft.
      + intro k'.
        destruct xs.
        * inversion k'.
        * etransitivity; [ apply ST_InterMeetRight | ].
          apply (IHxs k').
  Qed.
          

  Lemma ST_factorize_argument_ge (C: ConstructorSymbol) (args: t IntersectionType (constructorArity C)):
    forall pos, Const C args <= intersect (projT2 (factorize_argument C args pos)).
  Proof.
    intro pos.
    unfold factorize_argument.
    rewrite map_fg.
    apply (ST_intersect).
    destruct (factorize (nth args pos))
      as  [ n [ | argfactor ? argfactors ] ] eqn:argfactors_eq; 
      apply (map_Forall);
      apply (nth_Forall);
      intro k;
      [ apply (ST_Ax _ _ eq_refl); [ reflexivity | ] .. ];
      apply (nth_Forall2);
      intro k';
      destruct (Fin.eq_dec k' pos) as [ pos_eq | pos_ineq ];
      unfold eq_rect_r;
      try rewrite (nth_map _ _ _ _ (eq_refl _));
      try solve [ simpl eq_rect_r; simpl; rewrite (replace_others _ _ _ _ pos_ineq); reflexivity ].
    - simpl eq_rect.
      rewrite (replace_replaced _ _ _ _ pos_eq).
      apply (Fin.caseS' k).
      + apply ST_OmegaTop.
      + intro p; inversion p.
    - simpl.
      rewrite (replace_replaced _ _ _ _ pos_eq).
      etransitivity.
      + apply (ST_factorize_ge).
      + rewrite pos_eq.
        rewrite argfactors_eq.
        apply (ST_intersect_nth (cons _ argfactor _ argfactors) k).
  Qed.

  Definition intersect_many {m : nat} (types: t { n : _ & t IntersectionType n } m): IntersectionType :=
    intersect (projT2 (factorize (intersect (map (fun xs => intersect (projT2 xs)) types)))).

  Definition organizeConstructor' {n : nat} (organize: IntersectionType -> IntersectionType)  (args: t IntersectionType n) (C: ConstructorSymbol) (n_eq: n = constructorArity C) : IntersectionType :=
    match n as n' return (t IntersectionType n') -> (n' = constructorArity C) -> IntersectionType with
    | 0 => fun args n_eq => Const C (rew n_eq in args)
    | n =>
      fun args n_eq =>
        intersect_many
          (map2
             (fun args pos =>
                existT _ (S (projT1 (factorize_argument C (rew n_eq in args) (rew n_eq in pos))))
                       (projT2 (factorize_argument C (rew n_eq in args) (rew n_eq in pos))))
             (diag omega (map organize args))
             (positions n))
    end args n_eq.

  Definition organizeConstructor
             (organize: IntersectionType -> IntersectionType)
             (C: ConstructorSymbol)
             (args: t IntersectionType (constructorArity C)): IntersectionType :=
    organizeConstructor' organize args C eq_refl.
    

  Lemma ST_intersect_map2_map_parallel_le {T: Type} {m n: nat}:
    forall (xss: t (t IntersectionType n) m) (ys: t T m)
      (f : t IntersectionType n -> T -> IntersectionType)
      (g : t IntersectionType n -> IntersectionType)
      (fg_le: forall k, f (nth xss k) (nth ys k) <= g (nth xss k)),
      intersect (map2 f xss ys) <= intersect (map g xss).
  Proof.
    intros xss.
    induction xss; intros ys f g.
    - intros.
      apply (fun r => case0 (fun ys => intersect (map2 f _ ys) <= _) r ys).
      reflexivity.
    - destruct xss as [ | x' ? xss ].
      + apply (caseS' ys).
        clear ys; intros y ys.
        apply (fun r => case0 (fun ys => _ -> intersect (map2 f _ (cons _ y _ ys)) <= _) r ys).
        intro fg_le.
        apply (fg_le F1).
      + apply (caseS' ys).
        clear ys; intros y ys.
        apply (caseS' ys).
        clear ys; intros y' ys.
        intro fg_le.
        simpl.
        apply ST_Both.
        * etransitivity; [ apply ST_InterMeetLeft | apply (fg_le F1)  ].
        * etransitivity; [ apply ST_InterMeetRight | ].
          apply (IHxss (cons _ y' _ ys) f g).
          intro k.
          apply (fg_le (FS k)).
  Qed.

  Lemma ST_intersect_map2_map_parallel_ge {T: Type} {m n: nat}:
    forall (xss: t (t IntersectionType n) m) (ys: t T m)
      (f : t IntersectionType n -> T -> IntersectionType)
      (g : t IntersectionType n -> IntersectionType)
      (fg_ge: forall k,  g (nth xss k) <= f (nth xss k) (nth ys k)),
      intersect (map g xss) <= intersect (map2 f xss ys).
  Proof.
    intros xss.
    induction xss; intros ys f g.
    - intros.
      apply (fun r => case0 (fun ys => _ <= intersect (map2 f _ ys)) r ys).
      reflexivity.
    - destruct xss as [ | x' ? xss ].
      + apply (caseS' ys).
        clear ys; intros y ys.
        apply (fun r => case0 (fun ys => _ -> _ <= intersect (map2 f _ (cons _ y _ ys))) r ys).
        intro fg_ge.
        apply (fg_ge F1).
      + apply (caseS' ys).
        clear ys; intros y ys.
        apply (caseS' ys).
        clear ys; intros y' ys.
        intro fg_ge.
        simpl.
        apply ST_Both.
        * etransitivity; [ apply ST_InterMeetLeft | apply (fg_ge F1)  ].
        * etransitivity; [ apply ST_InterMeetRight | ].
          apply (IHxss (cons _ y' _ ys) f g).
          intro k.
          apply (fg_ge (FS k)).
  Qed.

  Lemma ST_intersect_map2_map_parallel_le' {T: Type} {n n': nat}:
    forall (n_eq: n = n')
      (xss: t (t IntersectionType n) n) (ys: t T n)
      (f : t IntersectionType n -> T -> IntersectionType)
      (g : t IntersectionType n' -> IntersectionType)
      (fg_le: forall k, f (nth xss k) (nth ys k) <= g (nth (rew [fun n => t (t _ n) n] n_eq in xss) (rew n_eq in k))),
      intersect (map2 f xss ys) <= intersect (map g (rew [fun n => t (t _ n) n] n_eq in xss)).
  Proof.
    destruct n; destruct n';
      intro n_eq;
      try solve [ inversion n_eq ].
    - destruct n_eq.
      apply (ST_intersect_map2_map_parallel_le).
    - inversion n_eq as [ n_eq' ].
      generalize n_eq.
      clear n_eq.
      rewrite n_eq'.
      intro n_eq.
      intro xss.
      rewrite <- (eq_rect_eq_dec (Nat.eq_dec) (fun n => t (t _ n) n) xss n_eq).
      intros ys f g fg_le.
      apply (ST_intersect_map2_map_parallel_le).
      intro k.
      rewrite (eq_rect_eq_dec (Nat.eq_dec) Fin.t _ n_eq) at 3.
      apply fg_le.      
  Qed.

   Lemma ST_intersect_map2_map_parallel_ge' {T: Type} {n n': nat}:
    forall (n_eq: n = n')
      (xss: t (t IntersectionType n) n) (ys: t T n)
      (f : t IntersectionType n -> T -> IntersectionType)
      (g : t IntersectionType n' -> IntersectionType)
      (fg_ge: forall k, g (nth (rew [fun n => t (t _ n) n] n_eq in xss) (rew n_eq in k)) <= f (nth xss k) (nth ys k)),
      intersect (map g (rew [fun n => t (t _ n) n] n_eq in xss)) <= intersect (map2 f xss ys).
  Proof.
    destruct n; destruct n';
      intro n_eq;
      try solve [ inversion n_eq ].
    - destruct n_eq.
      apply (ST_intersect_map2_map_parallel_ge).
    - inversion n_eq as [ n_eq' ].
      generalize n_eq.
      clear n_eq.
      rewrite n_eq'.
      intro n_eq.
      intro xss.
      rewrite <- (eq_rect_eq_dec (Nat.eq_dec) (fun n => t (t _ n) n) xss n_eq).
      intros ys f g fg_ge.
      apply (ST_intersect_map2_map_parallel_ge).
      intro k.
      rewrite (eq_rect_eq_dec (Nat.eq_dec) Fin.t _ n_eq) at 1.
      apply fg_ge.      
  Qed. 

  Lemma diag_size_distrib {T: Type} {n n': nat} (zero: T):
    forall (n_eq: n = n') (xs: t T n), rew [fun n => t (t T n) n] n_eq in diag zero xs = diag zero (rew n_eq in xs).
  Proof.
    destruct n; destruct n';
      intro n_eq;
      try solve [ inversion n_eq ].
    - destruct n_eq.
      intros; reflexivity.
    - inversion n_eq as [ n_eq' ].
      generalize n_eq.
      clear n_eq.
      rewrite n_eq'.
      intro n_eq.
      intro xs.
      rewrite <- (eq_rect_eq_dec (Nat.eq_dec) (fun n => t (t _ n) n) (diag zero xs) n_eq).
      rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ xs n_eq).
      reflexivity.
  Qed.

  Lemma ST_organizeConstructor'_le {n: nat} (C: ConstructorSymbol) (args: t IntersectionType n) (n_eq : n = constructorArity C):
    forall (organize : IntersectionType -> IntersectionType)
      (organize_le: Forall (fun arg => organize arg <= arg) args),
      organizeConstructor' organize args C n_eq <= Const C (rew n_eq in args).
  Proof.
    intros organize organize_le.
    destruct n.
    - reflexivity.
    - simpl.
      transitivity (Const C (rew [t IntersectionType] n_eq in map organize args)).
      + rewrite <- (ST_Ctor_Diag _ _ (rew n_eq in Nat.lt_0_succ _)).
        unfold intersect_many.
        etransitivity.
        * apply (ST_factorize_le).
        * rewrite (map_map2_fg).
          simpl.
          rewrite <- diag_size_distrib.
          apply (ST_intersect_map2_map_parallel_le').
          etransitivity.
          { simpl.
            apply (ST_factorize_argument_le).
          }
          { apply (ST_Ax C C eq_refl); [ reflexivity | ].
            apply (nth_Forall2).
            intro k'.
            rewrite (nth_k).
            unfold eq_rect_r.
            simpl.
            rewrite (nth_rew n_eq (diag omega (map organize args)) k).
            rewrite (nth_k).
            reflexivity. }
      + apply (ST_Ax _ _ eq_refl); [ reflexivity | ].
        unfold eq_rect_r.
        simpl.
        rewrite <- n_eq.
        simpl.
        clear n_eq.
        induction args as [ | arg ? args IHargs ].
        * apply Forall2_nil.
        * apply Forall2_cons.
          { inversion organize_le.
            assumption. }
          { apply IHargs.
            inversion organize_le as [ | ? ? ? ? ? n_eq [ arg_eq args_eq ] ].
            dependent rewrite <- args_eq.
            assumption. }
  Qed.

  Lemma ST_organizeConstructor_le
        (C: ConstructorSymbol)
        (args: t IntersectionType (constructorArity C)):
    forall (organize : IntersectionType -> IntersectionType)
      (organize_le: Forall (fun arg => organize arg <= arg) args),
      organizeConstructor organize C args <= Const C args.
  Proof.
    intros; apply ST_organizeConstructor'_le; assumption.
  Qed.


  Lemma ST_organizeConstructor'_ge {n: nat} (C: ConstructorSymbol) (args: t IntersectionType n) (n_eq : n = constructorArity C):
    forall (organize : IntersectionType -> IntersectionType)
      (organize_le: Forall (fun arg => arg <= organize arg) args),
      Const C (rew n_eq in args) <= organizeConstructor' organize args C n_eq.
  Proof.
    intros organize organize_ge.
    destruct n.
    - reflexivity.
    - simpl.
      transitivity (Const C (rew [t IntersectionType] n_eq in map organize args)).
      + apply (ST_Ax C C eq_refl); [ reflexivity | ].
        unfold eq_rect_r; simpl.
        rewrite <- n_eq.
        simpl; clear n_eq.
        induction args as [ | arg ? args IHargs ].
        * apply Forall2_nil.
        * apply Forall2_cons.
          { inversion organize_ge.
            assumption. }
          { apply IHargs.
            inversion organize_ge as [ | ? ? ? ? ? n_eq [ arg_eq args_eq ] ].
            dependent rewrite <- args_eq.
            assumption. }
      + rewrite (ST_Diag_Ctor C (rew n_eq in map organize args)).
        unfold intersect_many.
        etransitivity.
        * apply (ST_factorize_ge).
        * rewrite (map_map2_fg).
          rewrite <- diag_size_distrib.
          etransitivity; [ apply ST_factorize_le | ].
          etransitivity; [ | apply ST_factorize_ge ].
          apply (ST_intersect_map2_map_parallel_ge').
          etransitivity.
          { apply (ST_factorize_argument_ge _ _ (rew n_eq in k)). }
          { rewrite (positions_spec (S n)).
            simpl.
            rewrite (ST_factorize_argument_le).
            etransitivity; [ | apply (ST_factorize_argument_ge) ].
            apply (ST_Ax C C eq_refl); [ reflexivity | ].
            apply nth_Forall2.
            intro k'.
            unfold eq_rect_r.
            simpl.
            rewrite (nth_rew n_eq (diag omega (map organize args)) k).
            rewrite nth_k.
            reflexivity. }
  Qed.
          
  Lemma ST_organizeConstructor_ge
        (C: ConstructorSymbol)
        (args: t IntersectionType (constructorArity C)):
    forall (organize : IntersectionType -> IntersectionType)
      (organize_le: Forall (fun arg => arg <= organize arg) args),
      Const C args <= organizeConstructor organize C args.
  Proof.
    intros; apply (ST_organizeConstructor'_ge _ _ eq_refl); assumption.
  Qed.

  Lemma factorize_path:
    forall sigma, Path sigma -> factorize sigma = existT _ 1 (cons _ sigma _ (nil _)).
  Proof.
    intro sigma.
    induction sigma using IntersectionType_rect';
      intro sigmaPath;
      solve [ inversion sigmaPath | reflexivity ].
  Qed.
  
  Lemma factorize_intersect_size_eq {n : nat}: 
    forall (xs: t IntersectionType n)
      (xs_paths: Forall Path xs),
      projT1 (factorize (intersect xs)) = n.
  Proof.
    induction n as [ | n IH ]; intros xs xs_paths.
    - apply (fun r => case0 (fun xs => projT1 (factorize (intersect xs)) = _) r xs).
      reflexivity.
    - revert xs_paths.
      apply (caseS' xs).
      clear xs; intros x xs.
      intro xs_paths.
      inversion xs_paths as [ | n' ? xs' pathx xs_paths' n'_eq [ x_eq xs_eq ] ].
      simpl.      
      destruct xs as [ | x' n xs ].
      + rewrite (factorize_path _ pathx).
        reflexivity.
      + simpl.
        rewrite (factorize_path _ pathx).
        dependent rewrite xs_eq in xs_paths'.
        set (rhs_eq := IH _ xs_paths').
        simpl in rhs_eq.
        rewrite rhs_eq.
        reflexivity.
  Qed.
  
  Lemma factorize_intersect_eq {n : nat}: 
    forall (xs: t IntersectionType n)
      (xs_paths: Forall Path xs)
      (xs_size_eq: projT1 (factorize (intersect xs)) = n),
      rew xs_size_eq in projT2 (factorize (intersect xs)) = xs.
  Proof.
    induction n; intros xs xs_paths.
    - apply (fun r => case0 (fun xs => forall (xs_size_eq:  projT1 (factorize (intersect xs)) = 0),
                              rew _ in projT2 (factorize (intersect xs)) = xs) r xs).
      simpl.
      intro xs_size_eq.
      rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ xs_size_eq).
      reflexivity.
    - revert xs_paths.
      apply (caseS' xs).
      clear xs; intros x xs.
      intro xs_paths.
      inversion xs_paths as [ | n' ? xs' pathx xs_paths' n'_eq [ x_eq xs_eq ] ].
      simpl.      
      destruct xs as [ | x' n xs ].
      + rewrite (factorize_path _ pathx).
        intro xs_size_eq.
        rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ xs_size_eq).
        reflexivity.
      + dependent rewrite xs_eq in xs_paths'.
        simpl.
        rewrite (factorize_path _ pathx).
        simpl.
        intro xs_size_eq.
        inversion xs_size_eq as [ xs_size_eq' ].
        set (IH := IHn _ xs_paths' xs_size_eq').
        rewrite <- IH.
        simpl.
        revert xs_size_eq.
        rewrite <- xs_size_eq'.
        intro xs_size_eq.
        rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ xs_size_eq).
        reflexivity.
  Qed.

  Lemma organized_intersect_paths {n: nat}:
    forall (xs: t IntersectionType n) (xs_paths: Forall Path xs),
      Organized (intersect xs).
  Proof.
    intro xs.
    induction xs as [ | ? ? ? IH ]; intro xs_paths.
    - apply Organized_Omega.
    - inversion xs_paths as [ | ? ? ? ? Paths_xxs Sn_eq [ x_eq xs_eq ]].
      destruct xs.
      + apply Organized_Path.
        assumption.
      + apply Organized_Cons.
        * assumption.
        * destruct xs.
          { dependent rewrite xs_eq in Paths_xxs.
            inversion Paths_xxs as [ | ? ? ? Path_x ].
            unfold not; intro omega_eq.
            rewrite omega_eq in Path_x.
            inversion Path_x. }
          { unfold not; intro omega_eq; inversion omega_eq. }
        * apply IH.
          dependent rewrite <- xs_eq.
          assumption.
  Qed.

  Lemma factorize_path_intersections {m: nat}:
    forall (xss: t { n : _ & t IntersectionType n } m)
      (xss_paths: Forall (fun xs => Forall Path (projT2 xs)) xss),
      Forall Path (projT2 (factorize (intersect (map (fun xs => intersect (projT2 xs)) xss)))).
  Proof.
    intro xss.
    induction xss as [ | xs n xss IH ].
    - intros; apply Forall_nil.
    - intro xss_paths.
      simpl.
      destruct xss as [ | xs' n' xss ].
      + simpl.
        inversion xss_paths as [ | ? ? ? xs_paths ] .
        rewrite <- (rewrite_vect (fun n xs => Forall Path xs)
                                (factorize_intersect_size_eq (projT2 xs) xs_paths)).
        rewrite (factorize_intersect_eq _ xs_paths).
        assumption.
      + apply (Forall_append).
        * inversion xss_paths as [ | ? ? ? xs_paths ] .
          rewrite <- (rewrite_vect (fun n xs => Forall Path xs)
                                  (factorize_intersect_size_eq (projT2 xs) xs_paths)).
          rewrite (factorize_intersect_eq _ xs_paths).
          assumption.
        * apply IH.
          inversion xss_paths as [ | ? ? ? xs_paths xss'_paths n_eq [ xs_eq xss'_eq ] ].
          dependent rewrite xss'_eq in xss'_paths.
          assumption.
  Qed.

  Lemma factorize_organized_not_empty:
    forall sigma, Organized sigma -> sigma = omega \/ projT1 (factorize sigma) > 0.
  Proof.
    intro sigma.
    induction sigma
      as [ | | | sigma1 sigma2 IHsigma1 IHsigma2 ]
           using IntersectionType_rect'.
    - intros; left; reflexivity.
    - intros; right; apply Nat.lt_0_succ.
    - intros; right; apply Nat.lt_0_succ.
    - intro org_sigma.
      right.
      simpl.
      apply (Nat.add_pos_l).
      inversion org_sigma
        as [ ? path_sigma | sigma tau Path_sigma1 not_omega_sigma2 Org_sigma2 arg_eq | ].
      + inversion path_sigma.
      + rewrite (factorize_path _ Path_sigma1).
        apply (Nat.lt_0_succ).
  Qed.

  Lemma factorize_organized:
    forall sigma, Organized sigma -> sigma = intersect (projT2 (factorize sigma)).
  Proof.
    intro sigma.
    induction sigma
      as [ | | sigma1 sigma2 IHsigma1 IHsigma2 | ]
           using IntersectionType_rect';
      try solve [ intros; reflexivity ].
    intro org_sigma.
    inversion org_sigma
      as [ ? path_sigma | sigma tau Path_sigma1 not_omega_sigma2 Org_sigma2 arg_eq | ].
    - inversion path_sigma.
    - simpl.
      inversion Path_sigma1; solve [
        simpl;
        rewrite <- (IHsigma2 Org_sigma2);
        destruct (factorize_organized_not_empty _ Org_sigma2)
          as [ | factorize_gt ];
        [ contradict (not_omega_sigma2); assumption
        | destruct (projT2 (factorize sigma2));
          [ inversion factorize_gt
          | reflexivity ] ] ].
  Qed.


  Lemma PathArgs_const_omega {n: nat}: PathArgs (const omega n).
  Proof.
    induction n.
    - apply PathArgs_nil.
    - apply PathArgs_cons_omega.
      assumption.
  Qed.

  Lemma PathArgs_from_spec {n: nat} (args: t IntersectionType n):
    forall (k: Fin.t n) (omega_args: forall k', k' <> k -> nth args k' = omega) (path_k: Path (nth args k) \/ nth args k = omega),
      PathArgs args.
  Proof.
    intro k.
    induction k as [ | n k IH ].
    - apply (caseS' args); clear args; intros arg args.
      intros omega_args path_k.
      assert (args_const_omega: args = const omega _).
      { apply nth_const.
        intro k'.
        apply (omega_args (FS k')).
        unfold not; intro devil; inversion devil. }
      rewrite args_const_omega.
      destruct path_k as [ | omega_arg ].
      + apply PathArgs_cons_arg.
        assumption.
      + simpl in omega_arg.
        rewrite omega_arg.
        apply PathArgs_cons_omega.
        apply PathArgs_const_omega.
    - apply (caseS' args); clear args; intros arg args.
      intros omega_args path_k.
      assert (arg_omega: arg = omega).
      { apply (omega_args F1).
        unfold not; intro devil; inversion devil. }
      rewrite arg_omega.
      apply PathArgs_cons_omega.
      apply IH.
      + intros k' k_ineq.
        apply (omega_args (FS k')).
        unfold not; intro devil.
        apply k_ineq.
        apply FS_inj.
        assumption.
      + assumption.
  Qed.

  Lemma factorize_omega_args {n: nat} {C : ConstructorSymbol}:
    forall (n_eq: n = constructorArity C) k,
      Forall Path
             (projT2 (factorize_argument C (rew [t IntersectionType] n_eq in const omega n)
                                         (rew [Fin.t] n_eq in k))).
  Proof.
    intros n_eq k.
    assert (args_eq: rew [t IntersectionType] n_eq in const omega n = const omega (constructorArity C)).
    { rewrite <- n_eq.
      reflexivity. }
    unfold factorize_argument.
    rewrite args_eq.
    rewrite const_nth.
    simpl.
    apply Forall_cons; [ | apply Forall_nil].
    apply Path_Const.
    assert (all_omega: replace (const omega _) (rew [Fin.t] n_eq in k) omega = const omega _).
    { apply nth_const.
      intro k'.
      destruct (Fin.eq_dec (rew [Fin.t] n_eq in k) k') as [ k_eq | k_ineq ].
      - rewrite <- k_eq.
        apply replace_replaced.
        reflexivity.
      - rewrite (replace_others).
        + apply const_nth.
        + apply not_eq_sym.
          assumption. }
    rewrite all_omega.
    apply PathArgs_const_omega.
  Qed.

  Lemma organized_path_factors:
    forall sigma, Organized sigma -> Forall Path (projT2 (factorize sigma)).
  Proof.
    intro sigma.
    induction sigma
      as [ | | | sigma1 sigma2 IHsigma1 IHsigma2 ]
           using IntersectionType_rect'; intro org_sigma.
    - apply Forall_nil.
    - apply Forall_cons; [ | apply Forall_nil ].
      inversion org_sigma; assumption.
    - apply Forall_cons; [ | apply Forall_nil ].
      inversion org_sigma; assumption.
    - inversion org_sigma as [ ? path_sigma | ? ? path_sigma ? org_sigmas | ].
      + inversion path_sigma.
      + simpl.
        rewrite (factorize_path _ path_sigma).
        apply Forall_cons.
        * assumption.
        * apply IHsigma2.
          assumption.
  Qed. 
        
  Lemma Path_factorize_argument {n : nat} (C: ConstructorSymbol) (args: t IntersectionType n) (n_eq : n = constructorArity C):
    forall (k: Fin.t n) (organized_arg: Organized (nth args k)) (omega_args: forall k', k' <> k -> nth args k' = omega),
      Forall Path (projT2 (factorize_argument C (rew n_eq in args) (rew n_eq in k))).
  Proof.
    intros k org_kth omega_others.
    destruct (factorize_organized_not_empty _ org_kth) as [ kth_omega | factors_kth ].
    - assert (omega_args: args = const omega n).
      { apply nth_const.
        intro k'.
        destruct (Fin.eq_dec k' k) as [ k_eq | k_ineq ].
        - rewrite k_eq; assumption.
        - apply omega_others; assumption. }
      rewrite omega_args.
      apply (factorize_omega_args).
    - unfold factorize_argument.
      destruct (factorize (nth (rew [t IntersectionType] n_eq in args) (rew [Fin.t] n_eq in k)))
               as [ m [ | x ? xs ]] eqn:factors_eq.
      + rewrite <- n_eq in factors_eq.
        contradict factors_eq.
        simpl.
        unfold not; intro devil.
        rewrite devil in factors_kth.
        inversion factors_kth.
      + apply nth_Forall.
        intro k'.
        unfold projT2.
        set (map_eq := nth_map (fun arg => Const C (replace (rew [t IntersectionType] n_eq in args) (rew [Fin.t] n_eq in k) arg)) (cons _ x _ xs) _ _ (eq_refl k')).
        simpl.
        simpl in map_eq.
        rewrite map_eq.
        apply Path_Const.
        apply (PathArgs_from_spec _ (rew [Fin.t] n_eq in k)).
        * intros k'' k''_ineq.
          rewrite replace_others.
          { rewrite nth_k.
            apply omega_others.
            unfold not; intro devil.
            apply k''_ineq.
            set (devil' := f_equal (fun x => rew [Fin.t] n_eq in x) devil).
            simpl in devil'.
            rewrite (rew_opp_r) in devil'.
            exact devil'. }
          assumption.
        * left.
          rewrite replace_replaced.
          { clear map_eq.
            revert k'.
            simpl.
            apply (Forall_nth (cons _ x _ xs) Path).
            set (kth_eq := factorize_organized (nth args k) org_kth).
            rewrite <- n_eq in factors_eq.
            simpl in factors_eq.
            rewrite factors_eq in kth_eq.
            simpl in kth_eq.
            revert kth_eq.
            induction (nth args k) using IntersectionType_rect'.
            - inversion factors_eq.
            - inversion factors_eq.
              intro c_eq.
              apply Forall_cons; [  | apply Forall_nil ].
              inversion org_kth.
              assumption.
            - inversion factors_eq.
              intro arr_eq.
              apply Forall_cons; [ | apply Forall_nil ].
              inversion org_kth.
              assumption.
            - inversion factors_eq.
              intro inter_eq.
              inversion org_kth.
              + inversion H.
              + rewrite (factorize_path _ H3).
                apply Forall_cons.
                * assumption.
                * apply organized_path_factors.
                  assumption.
          }
          { reflexivity. }
  Qed.
  
  Lemma organizeConstructor'_organized {n: nat} (C: ConstructorSymbol) (args: t IntersectionType n) (n_eq : n = constructorArity C):
    forall (organize: IntersectionType -> IntersectionType)
      (organize_org: Forall (fun arg => Organized (organize arg)) args),
      Organized (organizeConstructor' organize args C n_eq).
  Proof.
    intros organize organize_org.
    destruct n.
    - apply Organized_Path.
      apply Path_Const.
      apply (fun r => case0 (fun args => PathArgs (rew n_eq in args)) r args).
      destruct (constructorArity C).
      + destruct n_eq.
        apply (PathArgs_nil).
      + inversion n_eq.
    - simpl.
      unfold intersect_many.
      apply (organized_intersect_paths).
      apply (factorize_path_intersections).
      apply (nth_Forall).
      intro k.
      apply (nth_Forall).
      rewrite (nth_map2 (fun args pos => existT _ _ _)
                        (diag omega (map organize args))
                        (cons _ F1 _ (map FS (positions n)))
                        k k k eq_refl eq_refl).
      apply Forall_nth.
      apply Path_factorize_argument.
      + rewrite (diag_spec_one).
        * rewrite (nth_map _ _ _ _ (eq_refl)).
          apply Forall_nth.
          apply organize_org.
        * apply eq_sym.
          apply (positions_spec).
      + intros k' k'_ineq.
        rewrite (diag_spec_zero).
        * reflexivity.
        * rewrite (positions_spec) in k'_ineq.
          apply (not_eq_sym).
          assumption.
  Qed.
    
  Lemma organizeConstructor_organized (C: ConstructorSymbol) (args: t IntersectionType (constructorArity C)):
    forall (organize: IntersectionType -> IntersectionType)
      (organize_org: Forall (fun arg => Organized (organize arg)) args),
      Organized (organizeConstructor organize C args).
  Proof.
    intros organize organize_org.
    apply organizeConstructor'_organized; assumption.
  Qed.

  Fixpoint organize (sigma: IntersectionType): IntersectionType :=
    match sigma with
    | Ty PT_omega => omega
    | Ty (PT_Const C args) => organizeConstructor organize C args
    | Ty (PT_Inter sigma tau) =>
      intersect (append (projT2 (factorize (organize sigma))) (projT2 (factorize (organize tau))))
    | Ty (PT_Arrow sigma tau) =>
      match organize tau with
      | Ty PT_omega => Ty PT_omega
      | tau' => intersect (map (fun tau => Ty (PT_Arrow sigma tau)) (projT2 (factorize tau')))
      end
    end.

  Lemma arrows_organized {n : nat}:
    forall (taus: t IntersectionType n) sigma,
      Forall Path taus ->
      Organized (intersect (map (fun tau => Arrow sigma tau) taus)).
  Proof.
    intro taus.
    induction taus as [ | tau n' taus IH ].
    - intros; apply Organized_Omega.
    - intros sigma paths_taus.
      destruct taus.
      + simpl.
        apply Organized_Path.
        apply Path_Arr.
        simpl in paths_taus.
        inversion paths_taus.
        assumption.
      + apply Organized_Cons.
        * apply Path_Arr.
          inversion paths_taus.
          assumption.
        * destruct taus;
            simpl;
            unfold not;
            intro devil;
            inversion devil.
        * apply IH.
          inversion paths_taus as [ | ? ? ? ? ? n_eq [ h_eq tl_eq ] ].
          dependent rewrite <- tl_eq.
          assumption.
  Qed.

  Lemma organize_organized:
    forall sigma, Organized (organize sigma).
  Proof.
    intro sigma.
    induction sigma
      as [ | | sigma tau IHsigma IHtau | sigma1 sigma2 IHsigma1 IHsigma2 ]
           using IntersectionType_rect'.
    - apply Organized_Omega.
    - simpl.
      apply organizeConstructor_organized.
      apply ForAll'Forall.
      assumption.
    - simpl.
      clear IHsigma.
      revert IHtau.
      induction (organize tau)
                as [ | | | l r IHl IHr ]using IntersectionType_rect'.
      + intros; apply Organized_Omega.
      + intro org_sigma.
        inversion org_sigma.
        apply Organized_Path.
        apply Path_Arr.
        assumption.
      + intro org_sigma.
        inversion org_sigma.
        apply Organized_Path.
        apply Path_Arr.
        assumption.
      + intro org_sigma.
        apply (arrows_organized (append (projT2 (factorize l)) (projT2 (factorize r))) sigma).      
        inversion org_sigma as [ ? path_sigma | ? ? ? r_not_omega org_r | ].
        * inversion path_sigma.
        * rewrite (factorize_path); [ | assumption ].
          apply Forall_cons; [ assumption | ].
          apply (organized_path_factors).
          assumption.
    - simpl.
      apply organized_intersect_paths.
      apply Forall_append;
        apply organized_path_factors; assumption.
  Qed.

  Lemma ST_intersect_tgts {n: nat}:
    forall (taus: t IntersectionType n) sigma tau,
      intersect taus <= tau ->
      intersect (map (fun tau => Arrow sigma tau) taus) <= Arrow sigma tau.
  Proof.
    intros taus sigma tau taus_le.
    transitivity (Arrow sigma (intersect taus)).
    - clear taus_le.
      induction taus as [ | tau' n taus IHtaus ].
      + simpl.
        etransitivity.
        * apply (ST_OmegaArrow).
        * apply ST_CoContra; [ apply ST_OmegaTop | reflexivity ].
      + transitivity (Inter (Arrow sigma tau') (Arrow sigma (intersect taus))).
        * apply ST_Both.
          { destruct taus.
            - reflexivity.
            - apply ST_InterMeetLeft. }
          { destruct taus.
            - simpl.
              apply ST_CoContra.
              + reflexivity.
              + apply ST_OmegaTop.
            - simpl.
              etransitivity; [ apply ST_InterMeetRight | ].
              exact IHtaus. }
        * rewrite ST_InterArrowDistrib.
          apply ST_CoContra.
          { reflexivity. }
          { simpl.
            destruct taus.
            - apply ST_InterMeetLeft.
            - reflexivity. }
    - apply ST_CoContra.
      + reflexivity.
      + assumption.
  Qed.        

  Lemma ST_organize_le:
    forall sigma, organize sigma <= sigma.
  Proof.
    intro sigma.
    induction sigma
      as [ | | sigma tau IHsigma IHtau | sigma1 sigma2 IHsigma1 IHsigma2 ]
           using IntersectionType_rect'.
    - reflexivity.
    - apply ST_organizeConstructor_le.
      apply ForAll'Forall.
      assumption.
    - revert IHtau.
      simpl.
      induction (organize tau) as [ | | | l r ] using IntersectionType_rect'.
      + intros omega_tau.
        rewrite (ST_OmegaArrow).
        apply (ST_CoContra).
        * apply ST_OmegaTop.
        * assumption.
      + intro const_tau.
        apply ST_CoContra.
        * reflexivity.
        * assumption.
      + intro arrow_tau.
        apply ST_CoContra.
        * reflexivity.
        * assumption.
      + intro inter_tau.
        apply ST_intersect_tgts.
        rewrite (ST_intersect_append_le).
        transitivity (Inter l r).
        * apply ST_Both.
          { rewrite ST_InterMeetLeft.
            apply ST_factorize_le. }
          { rewrite ST_InterMeetRight.
            apply ST_factorize_le. }
        * assumption.
    - simpl.
      apply ST_Both.
      + rewrite (ST_intersect_append_le).
        etransitivity.
        * apply ST_InterMeetLeft.
        * rewrite <- (factorize_organized); [ assumption | ].
          apply organize_organized.
      + rewrite (ST_intersect_append_le).
        etransitivity.
        * apply ST_InterMeetRight.
        * rewrite <- (factorize_organized); [ assumption | ].
          apply organize_organized.
  Qed.

  Lemma ST_organize_ge:
     forall sigma, sigma <= organize sigma.
  Proof.
    intro sigma.
    induction sigma
      as [ | | sigma tau IHsigma IHtau | sigma1 sigma2 IHsigma1 IHsigma2 ]
           using IntersectionType_rect'.
    - reflexivity.
    - apply ST_organizeConstructor_ge.
      apply ForAll'Forall.
      assumption.
    - simpl.
      revert IHtau.
      simpl.
      induction (organize tau) as [ | | | l r ] using IntersectionType_rect'.
      + intros; apply ST_OmegaTop.
      + intro tau_const.
        apply ST_CoContra.
        * reflexivity.
        * assumption.
      + intro tau_arrow.
        apply ST_CoContra.
        * reflexivity.
        * assumption.
      + intro tau_inter.
        apply ST_intersect.
        apply map_Forall.
        apply nth_Forall.
        intro k.
        apply ST_CoContra.
        * reflexivity.
        * revert k.
          apply Forall_nth.
          apply Forall_append.
          { apply ST_intersect_ge.
            transitivity l.
            - rewrite tau_inter.
              apply ST_InterMeetLeft.
            - apply ST_factorize_ge. }
          { apply ST_intersect_ge.
            transitivity r.
            - rewrite tau_inter.
              apply ST_InterMeetRight.
            - apply ST_factorize_ge. }
    - simpl.     
      transitivity (Inter (organize sigma1) (organize sigma2)).
      + apply ST_Both.
        * rewrite <- IHsigma1.
          apply ST_InterMeetLeft.
        * rewrite <- IHsigma2.
          apply ST_InterMeetRight.
      + transitivity (Inter (intersect (projT2 (factorize (organize sigma1))))
                            (intersect (projT2 (factorize (organize sigma2))))).
        * apply ST_Both.
          { etransitivity; [ apply ST_InterMeetLeft | ].
            apply ST_factorize_ge. }
          { etransitivity; [ apply ST_InterMeetRight | ].
            apply ST_factorize_ge. }
        * apply ST_intersect_append_ge.
  Qed.

  Fixpoint Omega (sigma: IntersectionType): Prop :=
    match sigma with
    | Ty (PT_omega) => True
    | Ty (PT_Const C args) => False
    | Ty (PT_Arrow sigma tau) => Omega tau
    | Ty (PT_Inter sigma tau) => Omega sigma /\ Omega tau
    end.

  Lemma Omega_sound: forall sigma, Omega sigma -> omega <= sigma.
  Proof.
    intro sigma.
    induction sigma using IntersectionType_rect'; intro omegaSigma.
    - reflexivity.
    - contradict omegaSigma.
    - rewrite ST_OmegaArrow.
      apply ST_CoContra.
      + apply ST_OmegaTop.
      + auto.
    - destruct omegaSigma.
      apply ST_Both; auto.
  Qed.

  Lemma Omega_complete: forall sigma tau, sigma <= tau -> Omega sigma -> Omega tau.
  Proof.
    intros sigma tau prf.
    induction prf; intro omegaSigma.
    - contradict omegaSigma.
    - destruct omegaSigma; assumption.
    - destruct omegaSigma; assumption.
    - split; assumption.
    - split; destruct omegaSigma; assumption.
    - destruct omegaSigma as [ devil ]; contradict devil.
    - destruct omegaSigma; split; auto.
    - simpl in *; auto.
    - simpl; trivial.
    - simpl; trivial.
    - auto.
  Qed.
  
  Lemma Omega_path: forall sigma, Path sigma -> Omega sigma -> False.
  Proof.
    intro sigma.
    induction sigma using IntersectionType_rect';
      intros path_sigma omega_sigma;
      try solve [ inversion path_sigma ].
    - inversion omega_sigma.
    - inversion path_sigma.
      auto.
  Qed.

  Lemma Omega_dec: forall sigma, { Omega sigma } + { Omega sigma -> False }.
  Proof.
    intro sigma.
    induction sigma
      as [ | | | ? ? IH1 IH2 ]
           using IntersectionType_rect'.
    - left; exact I.
    - right; intro; contradiction.
    - simpl; assumption.
    - destruct IH1;
        destruct IH2;
        try solve [ right; intro devil; inversion devil; contradiction ].
      left; split; assumption.
  Qed.   

  Inductive ConstFilter C args: IntersectionType -> Prop :=
  | CF_Const: forall C' (args': t IntersectionType (constructorArity C')) (arity_eq: constructorArity C = constructorArity C'),
      ConstructorTaxonomy C C' ->
      Forall2 Subtypes args (rew <- arity_eq in args') ->
      ConstFilter C args (Const C' args')
  | CF_Omega: forall tau, Omega tau -> ConstFilter C args tau
  | CF_Inter: forall sigma tau,
      ConstFilter C args sigma -> ConstFilter C args tau ->
      ConstFilter C args (Inter sigma tau).

  Lemma ST_args_dec (n: nat) (args: t IntersectionType n):
    forall m (args': t IntersectionType m) (nm_eq: n = m),
      ForAll' (fun arg => forall tau, { arg <= tau } + { arg <= tau -> False }) args ->
      { Forall2 Subtypes args (rew <- nm_eq in args') } +
      { Forall2 Subtypes args (rew <- nm_eq in args') -> False }.
  Proof.
    induction args as [ | ? ? ? IH ].
    - intros m args' nm_eq _; left.
      destruct m; [ | inversion nm_eq ].
      unfold eq_rect_r.
      rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ (eq_sym nm_eq)).
      apply case0.
      apply Forall2_nil.
    - intros m args' nm_eq dec_rec.
      inversion dec_rec as [ | ? ? ? dec_hd dec_tl n_eq [ hd_eq tl_eq ] ].
      dependent rewrite tl_eq in dec_tl.
      destruct m as [ | m]; inversion nm_eq as [ nm_eq' ].
      apply (caseS' args').
      clear args'; intros arg' args'.
      destruct (dec_hd arg') as [ hd_le | not_hd_le ].
      + destruct (IH _ args' nm_eq' dec_tl) as [ tl_le | not_tl_le ].
        * generalize nm_eq.
          revert args' tl_le.
          rewrite <- nm_eq'.
          intros args' tl_le nm_eq''.
          unfold eq_rect_r.
          rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ (eq_sym nm_eq'')).
          left.
          apply Forall2_cons; assumption.
        * generalize nm_eq.
          revert args' not_tl_le.
          rewrite <- nm_eq'.
          intros args' tl_le nm_eq''.
          unfold eq_rect_r.        
          rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ (eq_sym nm_eq'')).
          right.
          apply discharge_Forall2_tail.
          assumption.
      + generalize nm_eq.
        revert args'.
        rewrite <- nm_eq'.
        intros args' nm_eq''.
        unfold eq_rect_r.        
        rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ (eq_sym nm_eq'')).
        right.
        apply discharge_Forall2_head.
        assumption.
  Qed.
          
  Lemma CF_dec: forall C args sigma,
      ForAll' (fun arg => forall tau, {arg <= tau} + {arg <= tau -> False}) args ->
      { ConstFilter C args sigma } + { ConstFilter C args sigma -> False }.
  Proof.
    intros C args sigma args_dec.
    induction sigma
      as [ | C' args' | src tgt | l r IHl IHr ]
           using IntersectionType_rect'.
    - left; apply CF_Omega; exact I.
    - destruct (Nat.eq_dec (constructorArity C) (constructorArity C')) as [ arity_eq | not_arity_eq ].
      + destruct (ConstructorTaxonomy_dec C C') as [ C_le | not_C_le ].
        * destruct (ST_args_dec _ _ _ args' arity_eq args_dec) as [ args_le | not_args_le ].
          { left; apply (CF_Const _ _ _ _ arity_eq); assumption. }
          { right.
            intro devil.
            inversion devil as [ ? ? arity_eq' ? args_le [ C'_eq args_eq ] | | ].
            + set (args_eq' := vect_exist_eq _ _ (existT_fg_eq _ _ _ _ _ args_eq)).
              rewrite args_eq' in args_le.
              apply not_args_le.
              rewrite (UIP_dec (Nat.eq_dec) arity_eq arity_eq').
              assumption.
            + contradiction. }
        * right.
          intro devil.
          inversion devil; contradiction.
      + right.
        intro devil.
        inversion devil; contradiction.              
    - destruct (Omega_dec tgt) as [ omega_tgt | not_omega_tgt ].
      + left; apply CF_Omega; simpl; assumption.
      + right.
        intro CF_C.
        inversion CF_C.
        contradiction.
    - destruct (Omega_dec (Inter l r)) as [ omega_lr | not_omega_lr ].
      + left; apply CF_Omega; assumption.
      + destruct IHl;
          destruct IHr;
          try solve [ right; intro devil; inversion devil; contradiction ].
        left; apply CF_Inter; assumption.
  Qed.

  Lemma CF_trans': forall C args C' args' sigma,
      ConstFilter C args (Const C' args') ->
      ConstFilter C' args' sigma ->
      ConstFilter C args sigma.
  Proof.
    intros C args C' args' sigma CF_C.
    inversion CF_C as [ C1 args1 arity_eq1 C_tax1 args_le1 [ C1_eq args1_eq ] | ? devil | ].
    - dependent rewrite <- args1_eq.
      clear CF_C args1_eq args'.
      intro CF_C'.
      induction CF_C' as [ C2 args2 arity_eq2 C_tax2 args_le2 tau_eq2 | | ].
      + apply (CF_Const _ _ _ _ (eq_trans arity_eq1 arity_eq2)).
        { transitivity C'; assumption. }
        { apply (nth_Forall2).
          intro k.
          etransitivity.
          - apply (Forall2_nth _ _ _ args_le1).
          - unfold eq_rect_r.
            rewrite (nth_k (eq_sym arity_eq1)).
            rewrite (nth_k (eq_sym (eq_trans arity_eq1 arity_eq2))).
            etransitivity.
            + apply (Forall2_nth _ _ _ args_le2).
            + unfold eq_rect_r.
              rewrite (nth_k (eq_sym arity_eq2)).
              assert (k_eq: forall n m o (k: Fin.t n) (eq1 : n = m) (eq2 : m = o),
                         (rew <- eq_sym eq2 in rew (eq_sym (eq_sym eq1)) in k) =
                         (rew eq_sym (eq_sym (eq_trans eq1 eq2)) in k)).
                { intros n m o k' eq1 eq2.
                  destruct n;
                    destruct m;
                    try solve [ inversion eq1 ];
                    destruct o;
                    try solve [ inversion eq2 ].
                  - inversion k'.
                  - inversion eq1 as [ eq1' ].
                    revert eq1.
                    inversion eq2 as [ eq2' ].
                    revert eq2.
                    revert k'.
                    rewrite eq1'.
                    rewrite eq2'.
                    intros k' eq2 eq1.
                    rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ (eq_sym (eq_sym eq1))).
                    unfold eq_rect_r.
                    rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ (eq_sym (eq_sym eq2))).
                    rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ (eq_sym (eq_sym (eq_trans eq1 eq2)))).
                    reflexivity. }
                rewrite k_eq.
                reflexivity. }
      + apply CF_Omega; assumption.
      + apply CF_Inter; assumption.
    - inversion devil.
  Qed.

  Lemma CF_trans: forall C args sigma tau, sigma <= tau -> ConstFilter C args sigma -> ConstFilter C args tau.
  Proof.
    intros C args sigma tau sigma_le.
    induction sigma_le as [ C1 C2 arity_eq C_tax args1 args2 | | | | | | ? ? ? ? sigma1_le ? sigma2_le | | | | ];
      intro CF_sigma.
    - apply (CF_trans' _ _ C1 args1).
      + assumption.
      + apply (CF_Const _ _ _ _ arity_eq); assumption.
    - inversion CF_sigma as [ | ? omega_sigma | ].
      + apply CF_Omega.
        inversion omega_sigma.
        assumption.
      + assumption.
    - inversion CF_sigma as [ | ? omega_sigma | ].
      + apply CF_Omega.
        inversion omega_sigma.
        assumption.
      + assumption.
    - apply CF_Inter; assumption.
    - apply CF_Omega.
      inversion CF_sigma as [ | ? omega_sigma | ? ? CF_l CF_r ].
      + inversion omega_sigma.
        split; assumption.
      + inversion CF_l.
        inversion CF_r.
        split; assumption.
    - inversion CF_sigma as [ | ? omega_sigma | ? ? CF_l CF_r [ sigma_eq tau_eq ] ].
      + inversion omega_sigma; contradiction.
      + inversion CF_l as [ ? ? arity_eq' C_tax' args_le'  [ C_eq args_eq ] | ? omega_sigma | ].
        * clear CF_sigma.
          revert dependent taus.
          dependent rewrite <- args_eq.
          intros taus CF_r tau_eq.
          clear args_eq.
          inversion CF_r as [ ? ? ? ? args_le [ C_eq' args_eq' ] | ? omega_tau | ].
          { revert dependent args'.
            revert arity_eq'.
            dependent rewrite <- args_eq'.
            intros arity_eq' args' args_le'.
            apply (CF_Const _ _ _ _ arity_eq').
            - assumption.
            - apply (nth_Forall2).
              intro k.
              unfold eq_rect_r.
              rewrite (nth_k (eq_sym arity_eq')).
              rewrite (nth_map2 _ _ _ _ _ (rew <- eq_sym arity_eq' in k) eq_refl eq_refl).
              apply ST_Both.
              + rewrite <- (nth_k (eq_sym arity_eq')).
                apply (Forall2_nth).
                assumption.
              + rewrite <- (nth_k _).
                etransitivity.
                * apply (Forall2_nth _ _ _ args_le).
                * unfold eq_rect_r.
                  assert (xs_eq : forall n m (xs: t IntersectionType n) (eq: m = n) (eq': m = n), rew [fun n => t IntersectionType n] eq_sym eq in xs = rew [t IntersectionType] eq_sym eq' in xs).
                  { intros n m xs eq eq'.
                    destruct m; destruct n; try solve [ inversion eq ].
                    - rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ (eq_sym eq)).
                      rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ (eq_sym eq')).
                      reflexivity.
                    - inversion eq as [ eq'' ].
                      revert eq eq'.
                      rewrite eq''.
                      intros eq eq'.
                      rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ (eq_sym eq)).
                      rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ (eq_sym eq')).
                      reflexivity. }
                  rewrite (xs_eq _ _ _ arity_eq arity_eq').
                  reflexivity. }
          { inversion omega_tau. }
        * inversion omega_sigma.
    - inversion CF_sigma as [ | ? omega_sigma | ].
      + apply CF_Omega.
        destruct omega_sigma.
        split.
        * apply (Omega_complete _ _ sigma1_le); assumption.
        * apply (Omega_complete _ _ sigma2_le); assumption.
      + apply CF_Inter; auto.
    - inversion CF_sigma as [ | ? sigma_omega | ].
      apply CF_Omega.
      simpl.
      simpl in sigma_omega.
      apply (fun r => Omega_complete _ _ r sigma_omega).
      assumption.
    - apply CF_Omega; exact I.
    - apply CF_Omega; exact I.
    - auto.
  Qed.     
        
  Lemma CF_complete: forall C args sigma, Const C args <= sigma -> ConstFilter C args sigma.
  Proof.
    intros C args sigma C_le.
    remember (Const C args) as lhs eqn:lhs_eq.
    revert lhs_eq.
    generalize C args.
    clear C args.
    induction C_le as [ ? ? arity_eq | | | | | | | | | | sigma rho tau sigma_le IHsigma rho_le IHtau ] ;
      intros C' args' lhs_eq;
      try solve [ inversion lhs_eq ].
    - inversion lhs_eq.
      apply (CF_Const _ _ _ _ arity_eq); assumption.
    - rewrite lhs_eq.
      apply CF_Inter;
        solve [
            apply (CF_Const _ _ _ _ eq_refl);
            [ reflexivity
            | apply nth_Forall2; intro k; reflexivity ]
          ].
    - apply CF_Omega; exact I.
    - apply (CF_trans _ _ _ _ rho_le).
      auto.
  Qed.

  Lemma CF_sound: forall C args sigma, ConstFilter C args sigma -> Const C args <= sigma.
  Proof.
    intros C args sigma CF_sigma.
    induction CF_sigma as [ ? ? arity_eq | | ].
    - apply (ST_Ax _ _ arity_eq); assumption.
    - transitivity omega.
      + apply (ST_OmegaTop).
      + apply Omega_sound; assumption.
    - apply ST_Both; assumption.
  Qed.

  Inductive ArrowFilter (src: IntersectionType) (tgt: IntersectionType): IntersectionType -> Prop :=
  | AF_CoContra: forall src' tgt', src' <= src -> tgt <= tgt' -> ArrowFilter src tgt (Arrow src' tgt')
  | AF_Inter: forall sigma tau, ArrowFilter src tgt sigma -> ArrowFilter src tgt tau -> ArrowFilter src tgt (Inter sigma tau)
  | AF_Omega: forall sigma, Omega sigma -> ArrowFilter src tgt sigma.

  Lemma ArrowFilter_sound: forall src tgt sigma, ArrowFilter src tgt sigma -> Arrow src tgt <= sigma.
  Proof.
    intros src tgt sigma AF_sigma.
    induction AF_sigma.
    - apply ST_CoContra; assumption.
    - apply ST_Both; assumption.
    - transitivity omega.
      + apply ST_OmegaTop.
      + apply Omega_sound; assumption.
  Qed.

  Lemma AF_trans: forall src tgt sigma tau, sigma <= tau -> ArrowFilter src tgt sigma -> ArrowFilter src tgt tau.
  Proof.
    intros src tgt sigma tau sigma_le.
    induction sigma_le;
      intro AF_sigma;
      try solve [ inversion AF_sigma ].
    - inversion AF_sigma; contradiction.
    - inversion AF_sigma as [ | | ? omega_sigma ].
      + assumption.
      + apply AF_Omega.
        inversion omega_sigma; assumption.
    - inversion AF_sigma as [ | | ? omega_sigma ].
      + assumption.
      + apply AF_Omega.
        inversion omega_sigma; assumption.
    - apply AF_Inter; assumption.
    - inversion AF_sigma as [ | ? ? AF_tau1 AF_tau2 | ? omega_sigma ].
      + inversion AF_tau1 as [ ? ? ge_src le_tgt_tau1 | | ].
        * inversion AF_tau2 as [ ? ? ? le_tgt_tau2 | | ].
          { apply AF_CoContra.
            - assumption.
            - apply ST_Both; assumption. }
          { apply AF_CoContra.
            - assumption.
            - apply ST_Both.
              + assumption.
              + transitivity omega.
                * apply ST_OmegaTop.
                * apply Omega_sound; assumption. }
        * inversion AF_tau2 as [ ? ? ? le_tgt_tau2 | | ].
          { apply AF_CoContra.
            - assumption.
            - apply ST_Both.
              + transitivity omega.
                * apply ST_OmegaTop.
                * apply Omega_sound; assumption.
              + assumption. }
          { apply AF_Omega.
            split; assumption. }
      + apply AF_Omega.
        inversion omega_sigma.
        split; assumption.        
    - inversion AF_sigma as [ | ? ? AF_sigma1 | ? omega_sigma ].
      + inversion AF_sigma1.
        contradiction.
      + inversion omega_sigma; contradiction.
    - inversion AF_sigma as [ | | ? omega_sigma ].
      + apply AF_Inter; auto.
      + inversion omega_sigma.
        apply AF_Omega.
        split.
        * eapply Omega_complete.
          eassumption.
          assumption.
        * eapply Omega_complete.
          eassumption.
          assumption.
    - inversion AF_sigma as [ ? ? ge_src le_tgt | | ? omega_sigma ].
      + apply AF_CoContra.
        * etransitivity; [ eassumption | apply ge_src ].
        * etransitivity; [ apply le_tgt | assumption ].
      + apply AF_Omega.
        simpl.
        eapply Omega_complete.
        eassumption.
        assumption.        
    - apply AF_Omega.
      exact I.
    - apply AF_Omega.
      exact I.
    - auto.
  Qed.

  Lemma AF_complete: forall src tgt sigma, Arrow src tgt <= sigma -> ArrowFilter src tgt sigma.
  Proof.
    intros src tgt sigma sigma_ge.
    remember (Arrow src tgt) as lhs eqn:lhs_eq.
    revert lhs_eq.
    generalize src tgt.
    clear src tgt.
    induction sigma_ge;
      intros src tgt lhs_eq;
      try solve [ inversion lhs_eq ].
    - rewrite lhs_eq.
      apply AF_Inter;
        apply AF_CoContra; reflexivity.
    - inversion lhs_eq as [ [ src_eq tgt_eq ] ].
      rewrite <- src_eq.
      rewrite <- tgt_eq.
      apply AF_CoContra; assumption.
    - apply AF_Omega; exact I.
    - eapply AF_trans.
      + eassumption.
      + auto.
  Qed.

  Lemma AF_decidable:
    forall src tgt sigma,
      (forall src', { src' <= src } + { src' <= src -> False }) ->
      (forall tgt', { tgt <= tgt' } + { tgt <= tgt' -> False }) ->
      { ArrowFilter src tgt sigma } +  { ArrowFilter src tgt sigma -> False }.
  Proof.
    intros src tgt sigma src_dec tgt_dec.
    induction sigma
      as [ | | src' tgt' | l r IHl IHr ]
           using IntersectionType_rect'.
    - left; apply AF_Omega; exact I.
    - right; intro devil; inversion devil; contradiction.
    - destruct (Omega_dec tgt') as [ omega_tgt | not_omega_tgt ].
      + left; apply AF_Omega; assumption.
      + destruct (src_dec src') as [ src_ge | not_src_ge ].
        * destruct (tgt_dec tgt') as [ tgt_ge | not_tgt_ge ].
          { left; apply AF_CoContra; assumption. }
          { right; intro devil; inversion devil; contradiction. }
        * right; intro devil; inversion devil; contradiction.
    - destruct (Omega_dec l) as [ omega_l | not_omega_l ].
      + destruct (Omega_dec r) as [ omega_r | not_omega_r ].
        * left; apply AF_Omega; split; assumption.
        * destruct IHr as [ AF_r | not_AF_r ].
          { left; apply AF_Inter.
            - apply AF_Omega; assumption.
            - assumption. }
          { right; intro devil; inversion devil as [ | | ? omega_lr ].
            - contradiction.
            - inversion omega_lr; contradiction. }
      + destruct IHl as [ AF_l | not_AF_l ].
        * destruct IHr as [ AF_r | not_AF_r ].
          { left; apply AF_Inter; assumption. }
          { destruct (Omega_dec r) as [ omega_r | not_omega_r ].
            - left; apply AF_Inter.
              + assumption.
              + apply AF_Omega; assumption.
            - right; intro devil.
              inversion devil as [ | | ? omega_lr ].
              + contradiction.
              + inversion omega_lr; contradiction. }
        * right; intro devil.
          inversion devil as [ | | ? omega_lr ].
          { contradiction. }
          { inversion omega_lr; contradiction. }
  Qed.

  Lemma ST_Const_Arrow:
    forall C args sigma tau,
      Const C args <= Arrow sigma tau -> Omega tau.
  Proof.
    intros C args sigma tau C_le.
    set (CF_C := CF_complete _ _ _ C_le).
    inversion CF_C.
    assumption.
  Qed.
      

  Lemma ST_Arrow_Const:
    forall C args sigma tau,
      Arrow sigma tau <= Const C args -> False.
  Proof.
    intros C args sigma tau Arrow_le.
    set (AF_C := AF_complete _ _ _ Arrow_le).
    inversion AF_C.
    contradiction.
  Qed.

  Lemma ST_path_path_tgt:
    forall sigma tau, sigma <= tau -> Path sigma -> Path tau -> Path_tgt sigma <= Path_tgt tau.
  Proof.
    intros sigma.
    induction sigma
      as [ | | ? ? ? IHtgt | ]
           using IntersectionType_rect';
      intros tau sigma_le path_sigma;
      try solve [ inversion path_sigma ].
    - induction tau
        as [ | | sigma' tau' | ]
             using IntersectionType_rect';
        intro path_tau;
        try solve [ inversion path_tau ].
      + assumption.
      + set (devil := ST_Const_Arrow _ _ _ _ sigma_le).
        inversion path_tau as [ | ? ? path_tau' ].
        set (err := Omega_path _ path_tau' devil).
        contradiction.
    - induction tau using IntersectionType_rect';
        intro path_tau;
        try solve [ inversion path_tau ].
      + contradict sigma_le.
        unfold not.
        apply ST_Arrow_Const.
      + set (AF_sigma := AF_complete _ _ _ sigma_le).
        inversion AF_sigma as [ | | ? omega_sigma ].
        * simpl.
          inversion path_sigma.
          inversion path_tau.
          apply IHtgt; assumption.
        * contradict omega_sigma.
          unfold not.
          apply Omega_path; assumption.
  Qed.

  Lemma Path_params_size_spec_cons:
    forall src tgt, projT1 (Path_params (Arrow src tgt)) = S (projT1 (Path_params tgt)).
  Proof.
    intros src tgt.
    simpl.
    destruct (Path_params tgt).
    reflexivity.
  Qed.

  Lemma Path_params_spec_cons:
    forall src tgt, Path_params (Arrow src tgt) =
               existT _ (S (projT1 (Path_params tgt))) (cons _ src _ (projT2 (Path_params tgt))).
  Proof.
    intros src tgt.
    simpl.
    destruct (Path_params tgt).
    simpl.
    reflexivity.
  Qed.
  
  Lemma ST_path_path_params:
    forall sigma tau, sigma <= tau -> Path sigma -> Path tau ->
                 { params_eq: projT1 (Path_params sigma) = projT1 (Path_params tau) |
                   Forall2 Subtypes
                           (projT2 (Path_params tau))
                           (rew params_eq in (projT2 (Path_params sigma))) }.
  Proof.
    intros sigma.
    induction sigma as [ | | src tgt ? IHtgt | ] using IntersectionType_rect';
      intros tau sigma_le path_sigma;
      try solve [ inversion path_sigma ].
    - induction tau
        as [ | | | ] using IntersectionType_rect';
        intro path_tau;
        try solve [ inversion path_tau ].
      + exists eq_refl.
        apply Forall2_nil.
      + generalize (ST_Const_Arrow _ _ _ _ sigma_le).
        intro devil.
        inversion path_tau.
        contradict devil.
        unfold not.
        apply Omega_path; assumption.
    - induction tau
        as [ | | src' tgt' | ] using IntersectionType_rect';
        intro path_tau;
        try solve [ inversion path_tau ].
      + contradict sigma_le.
        unfold not.
        apply ST_Arrow_Const.
      + inversion path_sigma as [ | ? ? path_tgt ].
        inversion path_tau as [ | ? ? path_tgt' ].
        set (AF_sigma := AF_complete _ _ _ sigma_le).        
        inversion AF_sigma as [ ? ? src_ge tgt_le | | omega_sigma ].
        * destruct (IHtgt _ tgt_le path_tgt path_tgt') as [ tl_eq tl_le ].
          set (params_eq := Path_params_spec_cons src tgt).
          set (params_eq' := Path_params_spec_cons src' tgt').
          simpl in params_eq, params_eq'.
          simpl.
          rewrite params_eq.        
          rewrite params_eq'.
          simpl.
          exists (f_equal S tl_eq).
          assert (rew_eq :
              (rew [fun n => t IntersectionType n] f_equal S tl_eq in (cons _ src _ (projT2 (Path_params tgt)))) =
              cons _ src _ (rew tl_eq in projT2 (Path_params tgt))).
          { clear tl_le.
            revert tl_eq.
            generalize (Path_params tgt) (Path_params tgt').
            intro l.
            destruct l as [ m xs ].
            simpl.
            intro r.
            destruct r as [ n ys ].
            simpl.
            destruct m;
              destruct n;
              intro tl_eq;
              inversion tl_eq as [ tl_eq' ].
            - rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ tl_eq).
              rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ (f_equal S tl_eq)).
              reflexivity.
            - revert tl_eq.
              rewrite <- tl_eq'.
              intro tl_eq.
              rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ tl_eq).
              rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ (f_equal S tl_eq)).
              reflexivity. }
          rewrite rew_eq.
          apply Forall2_cons; assumption.
        * contradict path_tgt'.
          unfold not.
          intro path_tgt'.
          apply (Omega_path _ path_tgt').
          assumption.
  Qed.
  
  Axiom ST_path: forall sigma tau,
      sigma <= tau ->
      Path tau ->
      Exists (fun sigma => Path sigma /\ sigma <= tau) (projT2 (factorize (organize sigma))).

  Lemma ST_organization: forall sigma tau,
      sigma <= tau ->
      Forall (fun tau' => Exists (fun sigma => Path sigma /\ sigma <= tau') (projT2 (factorize (organize sigma)))) (projT2 (factorize (organize tau))).
  Proof.
    intros sigma tau sigma_le.
    generalize (organize_organized tau).
    generalize (ST_organize_ge tau).
    induction (organize tau) as [ | | | l r IHl IHr ] using IntersectionType_rect'.
    - intros; apply Forall_nil.
    - intros org_ge org_C.
      apply Forall_cons; [ | apply Forall_nil].
      inversion org_C.
      apply ST_path.
      + transitivity tau; assumption.
      + assumption.
    - intros org_ge org_Arr.
      apply Forall_cons; [ | apply Forall_nil].
      inversion org_Arr.
      apply ST_path.
      + transitivity tau; assumption.
      + assumption.
    - intros org_ge org_Inter.
      inversion org_Inter as [ ? devil | ? ? path_l not_omega_r path_r | ].
      + inversion devil.
      + simpl.
        rewrite (factorize_path _ path_l).
        apply Forall_cons.
        * apply ST_path.
          { transitivity tau.
            - assumption.
            - etransitivity; [ eassumption | apply ST_InterMeetLeft ]. }
          { assumption. }
        * apply IHr.
          { etransitivity; [ eassumption | apply ST_InterMeetRight ]. }
          { assumption. }
  Qed.
  
  
  (*
  Lemma ST_path: forall sigma tau,
      sigma <= tau ->
      Path tau ->
      Exists (fun sigma => Path sigma /\ sigma <= tau) (projT2 (factorize (organize sigma))).
  Proof.
    intros sigma tau sigma_le.
    induction sigma_le;
      intros path_tau;
      try solve [ inversion path_tau ].
    - apply Exists_cons_hd.
      split.
      + inversion org_sigma; assumption.
      + eapply ST_Ax; eassumption.
    - simpl.
      rewrite (factorize_path _ path_tau).
      simpl.
      apply Exists_cons_hd.
      split; [ assumption | reflexivity ].
    - simpl.
      inversion org_sigma as [ ? devil | ? ? path_sigma | ].
      + inversion devil.
      + rewrite (factorize_path _ path_tau). 
        rewrite (factorize_path _ path_sigma).
        apply Exists_cons_tl.
        apply Exists_cons_hd.
        split; [ assumption | reflexivity ].
    - inversion path_tau as [ | ? ? devil ].
      inversion devil.
    - simpl.
      apply Exists_cons_hd.
      split.
      + inversion org_sigma as [ ? devil | | ].
        * inversion devil.
        * assumption.
      + apply (ST_Ax _ _ eq_refl); [ reflexivity | ].
        clear org_sigma.
        inversion path_tau as [ C' args pathargs_taus [ C_eq taus_eq ] | ].
        dependent rewrite taus_eq in pathargs_taus.
        clear C' C_eq taus_eq args path_tau.
        revert taus sigmas pathargs_taus.
        generalize (constructorArity C).
        clear C.
        unfold eq_rect_r.
        simpl.
        intros n.
        destruct n.
        * intros taus sigmas.
          apply (fun r => case0 (fun xs => PathArgs (map2 Inter xs _) -> Forall2 _ xs (map2 _ xs _)) r sigmas).
          apply (fun r => case0 (fun xs => PathArgs (map2 Inter _ xs) -> Forall2 _ _ (map2 _ _ xs)) r taus).
          intro.
          apply Forall2_nil.
        * intros taus sigmas.
          apply (caseS' sigmas).
          clear sigmas; intros sigma sigmas.
          apply (caseS' taus).
          clear taus; intros tau taus.
          intro pathargs_taus.
          inversion pathargs_taus as [ | ? ? devil | ].
          inversion devil.
    - inversion org_sigma as [ ? path_sigma | | ].
      rewrite (factorize_path _ path_sigma).
      apply (Exists_cons_hd).
      split.
      + assumption.
      + apply ST_CoContra; assumption.
    - inversion path_tau as [ | ? ? devil ].
      inversion devil.
    - 
      *)
      
  
  Definition Substitution: Type := VariableSymbol -> IntersectionType.
  Fixpoint Apply (S: Substitution) (sigma: TypeScheme): IntersectionType :=
    match sigma with
    | Var alpha => S alpha
    | Skeleton s =>
      match s with
      | PT_omega => omega
      | PT_Const C sigmas => Const C (map (Apply S) sigmas)
      | PT_Arrow sigma tau => Arrow (Apply S sigma) (Apply S tau)
      | PT_Inter sigma tau => Inter (Apply S sigma) (Apply S tau)
      end
    end.

  Inductive Term : Set :=
  | Symbol: forall (c : CombinatorSymbol), Term
  | App: forall (M N: Term), Term.

  Fixpoint rootOf (M: Term): CombinatorSymbol :=
    match M with
    | Symbol c => c
    | App M' N => rootOf M'
    end.

  Fixpoint argumentCount (M: Term): nat :=
    match M with
    | Symbol c => 0
    | App M' N => 1 + (argumentCount M')
    end.

  Fixpoint argumentsOf (M: Term): t Term (argumentCount M) :=
    match M as M' return t Term (argumentCount M') with
    | Symbol c => nil _
    | App M' N => shiftin N (argumentsOf M')
    end.

  Module Type TypeSystem.
    Parameter WellFormed: Substitution -> Prop.
      
    Definition Context: Type := CombinatorSymbol -> TypeScheme.

    Inductive CL (Gamma : Context): Term -> IntersectionType -> Prop :=
    | CL_Var: forall c S, WellFormed S -> CL Gamma (Symbol c) (Apply S (Gamma c))
    | CL_MP: forall M N sigma tau,
        CL Gamma M (Arrow sigma tau) ->
        CL Gamma N sigma ->
        CL Gamma (App M N) tau
    | CL_II: forall M sigma tau,
        CL Gamma M sigma ->
        CL Gamma M tau ->
        CL Gamma M (Inter sigma tau)
    | CL_ST: forall M sigma tau,
        CL Gamma M sigma ->
        sigma <= tau ->
        CL Gamma M tau. 

    Lemma CL_omega (S: Substitution) (WF_S: WellFormed S): forall Gamma M, CL Gamma M omega.
    Proof.
      intros Gamma M.
      induction M as [ c | M IHM N IHN ].
      - apply (CL_ST _ _ (Apply S (Gamma c)) omega).
        + exact (CL_Var _ _ _ WF_S).
        + apply ST_OmegaTop.
      - apply (CL_MP _ _ _ omega omega).
        + apply (CL_ST _ _ omega _).
          * assumption.
          * apply ST_OmegaArrow.
        + assumption.
    Qed.

    Lemma MP_generation: forall Gamma M N tau,
        CL Gamma (App M N) tau -> exists sigma, CL Gamma M (Arrow sigma tau) /\ CL Gamma N sigma.
    Proof.
      intros Gamma M N tau prf.
      remember (App M N) as MN eqn:MN_eq.
      generalize M N MN_eq.
      clear M N MN_eq.
      induction prf as [ | | M' tau1 tau2 M'tau1 IHtau1 M'tau2 IHtau2 | ? ? tau_ge prf IH ].
      - intros ? ? MN_eq; inversion MN_eq.
      - intros ? ? MN_eq.
        inversion MN_eq as [ [ M_eq N_eq ] ].
        rewrite <- M_eq.
        rewrite <- N_eq.
        eexists; split; eassumption.
      - intros M N MN_eq.
        destruct (IHtau1 _ _ MN_eq) as [ sigma1 [ Msigma1tau1 Nsigma1 ] ].
        destruct (IHtau2 _ _ MN_eq) as [ sigma2 [ Msigma2tau2 Nsigma2 ] ].
        exists (Inter sigma1 sigma2).
        split.
        + eapply CL_ST.
          * apply CL_II; [ exact Msigma1tau1 | exact Msigma2tau2 ].
          * etransitivity; [ | apply ST_InterArrowDistrib ].
            apply ST_Both;
             [ rewrite ST_InterMeetLeft | rewrite ST_InterMeetRight ];
             apply ST_CoContra;
             solve [ apply ST_InterMeetLeft || apply ST_InterMeetRight | reflexivity ].
        + apply CL_II; assumption.
      - intros ? ? MN_eq.
        destruct (IH _ _ MN_eq) as [ ? [ ? ? ] ].
        eexists.
        split.
        + eapply CL_ST.
          * eassumption.
          * apply ST_CoContra; [ reflexivity | assumption ].
        + assumption.
    Qed.

    Lemma MinimalSubst_PerPath: forall Gamma c tau,
        CL Gamma (Symbol c) tau ->
        Forall (fun tau' =>
                  exists S, WellFormed S /\ Apply S (Gamma c) <= tau') (projT2 (factorize (organize tau))).
    Proof.
      intros Gamma c tau prf.
      remember (Symbol c) as c' eqn:c'_eq.
      generalize c c'_eq.
      clear c'_eq c.
      induction prf as [ | | M sigma tau | M sigma tau prf IH sigma_le ].
      - intros ? c'_eq.
        inversion c'_eq as [ c_eq ].
        rewrite <- c_eq.
        apply (nth_Forall).
        intro k.
        eexists; split.
        + eassumption.
        + rewrite <- (ST_intersect_nth).
          rewrite <- (factorize_organized).
          * apply ST_organize_ge.
          * apply organize_organized.
      - intros ? c'_eq; inversion c'_eq.
      - intros c M_eq.
        simpl.
        assert (all_paths: Forall Path (append (projT2 (factorize (organize sigma)))
                                               (projT2 (factorize (organize tau))))).
        { apply Forall_append;
            apply organized_path_factors;
            apply organize_organized. }
        generalize (factorize_intersect_size_eq _ all_paths).
        intro xs_size_eq.
        rewrite <- (rewrite_vect _ xs_size_eq).
        set (factors_eq := factorize_intersect_eq _ all_paths xs_size_eq).
        rewrite factors_eq.
        apply Forall_append; auto.
      - intros.
        apply (nth_Forall).
        intro k.
        assert (kth_path : Path (nth (projT2 (factorize (organize tau))) k)).
        { apply (Forall_nth).
          apply (organized_path_factors).
          apply (organize_organized). }
        assert (kth_ge : sigma <= nth (projT2 (factorize (organize tau))) k).
        { rewrite sigma_le.
          etransitivity; [ apply ST_organize_ge | ].
          rewrite (factorize_organized _ (organize_organized _)) at 1.
          apply (ST_intersect_nth). }
        generalize (IH _ c'_eq).
        clear IH.
        induction (ST_path _ _ kth_ge kth_path) as [ ? ? ? [ ? x_le ] | ? ? ? ? IH' ]; intro IH.
        + inversion IH as [ | ? ? ? [ S [ WF_S ? ] ] ].
          exists S; split; [ assumption | etransitivity; [ eassumption | apply x_le ] ].          
        + inversion IH as [ | ? ? ? ? ? n_eq [ x_eq xs_eq ] ].
          dependent rewrite <- xs_eq in IH'.
          auto.
    Qed.
        
    Lemma SingleMinimalSubst: forall Gamma c sigma,
        CL Gamma (Symbol c) sigma -> Path sigma -> exists S, WellFormed S /\ Apply S (Gamma c) <= sigma.
    Proof.
      intros Gamma c sigma prf path_sigma.
      generalize (MinimalSubst_PerPath _ _ _ prf).
      induction (ST_path _ _ (ST_Refl sigma) path_sigma) as [ n x xs [ path_x sigma_gt ] | ].
      - intro exsubsts. 
        inversion exsubsts as [ | ? ? ? [ S [ WF_S S_le ] ] ].
        exists S; split.
        + assumption.
        + rewrite S_le; assumption.
      - intro exsubsts.
        inversion exsubsts as [ | ? ? ? ? exsubsts' n_eq [ x_eq xs_eq ] ].
        dependent rewrite xs_eq in exsubsts'.
        auto.
    Qed.

    Fixpoint src_count (sigma: IntersectionType): nat :=
      match sigma with
      | Ty (PT_Arrow _ tgt) => S (src_count tgt)
      | _ => 0
      end.

    Fixpoint split_path (sigma: IntersectionType) (n: nat) (nOk: (n <= src_count sigma)%nat) {struct n}: (t IntersectionType n) * IntersectionType  :=
      match n with
      | 0 => fun _ => ((nil _), sigma)
      | S n' =>
        fun nOk => 
          match sigma as sigma' return (S n' <= src_count sigma')%nat -> _ with
          | Ty (PT_Arrow src tgt) =>
            fun nOk =>
              (cons _ src _ (fst (split_path tgt n' (proj2 (Nat.succ_le_mono _ _) nOk))),
               snd (split_path tgt n' (proj2 (Nat.succ_le_mono _ _) nOk)))
          | _ => fun _ => (const omega _, omega)
          end nOk
      end nOk.

    Fixpoint mkArrow {n : nat} (srcs: t IntersectionType n) (tgt: IntersectionType): IntersectionType :=
      match srcs with
      | nil _ => tgt
      | cons _ src _ srcs => Arrow src (mkArrow srcs tgt)
      end.

    Lemma split_path_spec: forall sigma n (nOk: (n <= src_count sigma)%nat),
        mkArrow (fst (split_path sigma n nOk)) (snd (split_path sigma n nOk)) = sigma.
    Proof.
      intros sigma n nOk.
      revert sigma nOk.
      induction n as [ | n IH ];
        intros sigma nOk.
      - reflexivity.
      - destruct sigma using IntersectionType_rect';
          try solve [ inversion nOk ].
        simpl; unfold Arrow.
        apply f_equal.
        apply f_equal.
        apply IH.
    Qed.
  
    Lemma factors_map_distrib:
      forall sigma tau,
        (Omega tau -> False) ->
        (factorize (organize (Arrow sigma tau))) =
        existT _ _ (map (Arrow sigma) (projT2 (factorize (organize tau)))).
    Proof.
      intros sigma tau not_omega_tau.
      simpl.
      destruct tau as [ | C args | sigma' tau | sigma1 sigma2 ] using IntersectionType_rect'.
      - contradict not_omega_tau; exact I.
      - simpl.
        generalize (organize_organized (Const C args)).
        simpl.
        destruct (organizeConstructor organize C args)
          as [ | | | l r ]
               eqn:ctor_eq using IntersectionType_rect'.
        + contradict not_omega_tau.
          apply (Omega_complete _ _ (ST_organize_le (Const C args))).
          simpl.
          rewrite ctor_eq.
          exact I.
        + reflexivity.
        + reflexivity.
        + intro org_inter.
          assert (paths_inter : Forall Path (map (fun tau => Ty (PT_Arrow sigma tau)) (append (projT2 (factorize l)) (projT2 (factorize r))))).
          { set (paths_inter := organized_path_factors _ org_inter).
            simpl in paths_inter.
            apply (map_Forall).
            apply (Forall_ap _ (Path)).
            - apply Forall_tautology.
              intro; apply Path_Arr.
            - assumption. }         
          assert (expand_factorize :
                    existT _ (projT1 _)
                           (projT2 (factorize (intersect
                                                 (map (Arrow sigma)
                                                      (append (projT2 (factorize l))
                                                              (projT2 (factorize r))))))) =
                    factorize (intersect (map (fun tau => Ty (PT_Arrow sigma tau))
                                              (append (projT2 (factorize l))
                                                      (projT2 (factorize r)))))
                 ).
          { unfold Arrow.
            unfold liftPreType.
            destruct (factorize (intersect (map (fun tau => Ty (PT_Arrow sigma tau))
                                                (append (projT2 (factorize l))
                                                        (projT2 (factorize r)))))).
            reflexivity. }
          rewrite <- expand_factorize.
          set (size_eq := factorize_intersect_size_eq _ paths_inter).
          apply (existT_eq _ _ _ _ _ size_eq).
          unfold Arrow.
          apply (factorize_intersect_eq _ paths_inter).
      - generalize (organize_organized (Ty (PT_Arrow sigma' tau))).
        destruct (organize (Ty (PT_Arrow sigma' tau)))
                 as [ | | | l r ] eqn:arr_eq
                       using IntersectionType_rect'.
        + contradict not_omega_tau.
          apply (Omega_complete _ _ (ST_organize_le (Ty (PT_Arrow sigma' tau)))).
          rewrite arr_eq.
          exact I.
        + reflexivity.
        + reflexivity.
        + intro org_inter.
          assert (paths_inter : Forall Path (map (fun tau => Ty (PT_Arrow sigma tau)) (append (projT2 (factorize l)) (projT2 (factorize r))))).
          { set (paths_inter := organized_path_factors _ org_inter).
            simpl in paths_inter.
            apply (map_Forall).
            apply (Forall_ap _ (Path)).
            - apply Forall_tautology.
              intro; apply Path_Arr.
            - assumption. }         
          assert (expand_factorize :
                    existT _ (projT1 _)
                           (projT2 (factorize (intersect
                                                 (map (Arrow sigma)
                                                      (append (projT2 (factorize l))
                                                              (projT2 (factorize r))))))) =
                    factorize (intersect (map (fun tau => Ty (PT_Arrow sigma tau))
                                              (append (projT2 (factorize l))
                                                      (projT2 (factorize r)))))
                 ).
          { unfold Arrow.
            unfold liftPreType.
            destruct (factorize (intersect (map (fun tau => Ty (PT_Arrow sigma tau))
                                                (append (projT2 (factorize l))
                                                        (projT2 (factorize r)))))).
            reflexivity. }
          rewrite <- expand_factorize.
          set (size_eq := factorize_intersect_size_eq _ paths_inter).
          apply (existT_eq _ _ _ _ _ size_eq).
          unfold Arrow.
          apply (factorize_intersect_eq _ paths_inter).
      - generalize (organize_organized (Ty (PT_Inter sigma1 sigma2))).
        destruct (organize (Ty (PT_Inter sigma1 sigma2)))
                 as [ | | | l r ] eqn:arr_eq
                                        using IntersectionType_rect'.
        + contradict not_omega_tau.
          apply (Omega_complete _ _ (ST_organize_le (Ty (PT_Inter sigma1 sigma2)))).
          rewrite arr_eq.
          exact I.
        + reflexivity.
        + reflexivity.
        + intro org_inter.
          assert (paths_inter : Forall Path (map (fun tau => Ty (PT_Arrow sigma tau)) (append (projT2 (factorize l)) (projT2 (factorize r))))).
          { set (paths_inter := organized_path_factors _ org_inter).
            simpl in paths_inter.
            apply (map_Forall).
            apply (Forall_ap _ (Path)).
            - apply Forall_tautology.
              intro; apply Path_Arr.
            - assumption. }         
          assert (expand_factorize :
                    existT _ (projT1 _)
                           (projT2 (factorize (intersect
                                                 (map (Arrow sigma)
                                                      (append (projT2 (factorize l))
                                                              (projT2 (factorize r))))))) =
                    factorize (intersect (map (fun tau => Ty (PT_Arrow sigma tau))
                                              (append (projT2 (factorize l))
                                                      (projT2 (factorize r)))))
                 ).
          { unfold Arrow.
            unfold liftPreType.
            destruct (factorize (intersect (map (fun tau => Ty (PT_Arrow sigma tau))
                                                (append (projT2 (factorize l))
                                                        (projT2 (factorize r)))))).
            reflexivity. }
          rewrite <- expand_factorize.
          set (size_eq := factorize_intersect_size_eq _ paths_inter).
          apply (existT_eq _ _ _ _ _ size_eq).
          unfold Arrow.
          apply (factorize_intersect_eq _ paths_inter).
    Qed.

    Lemma organize_omega: forall sigma, Omega sigma -> organize sigma = omega.
    Proof.
      intros sigma.
      induction sigma as [ | | ? tau ? IH | ? ? IHsigma1 IHsigma2 ] using IntersectionType_rect'.
      - reflexivity.
      - intro devil; inversion devil.
      - intro omega_arr.
        simpl.
        rewrite (IH omega_arr).
        reflexivity.
      - intro omega_inter.
        destruct omega_inter as [ omega_sigma1 omega_sigma2 ].
        simpl.
        rewrite (IHsigma1 omega_sigma1).
        rewrite (IHsigma2 omega_sigma2).
        reflexivity.
    Qed.

    Lemma factorize_intersect_cons_omega {n: nat}:
      forall sigmas, factorize (intersect (cons _ omega n sigmas)) = factorize (intersect sigmas).
    Proof.
      intro sigmas.
      simpl.
      destruct sigmas as [ | sigma n sigmas ].
      - reflexivity.
      - simpl.
        destruct (factorize (match sigmas with
                             | nil _ => sigma
                             | cons _ _ _ _ => Inter sigma (intersect sigmas)
                             end)).
        reflexivity.
    Qed.          

    Lemma factorize_intersect_append {m n : nat}:
      forall (sigmas: t IntersectionType m) (taus: t IntersectionType n),
        factorize (intersect (append sigmas taus)) = existT _ _ (append (projT2 (factorize (intersect sigmas)))
                                                                        (projT2 (factorize (intersect taus)))).
    Proof.
      intros sigmas.
      induction sigmas as [ | sigma m sigmas IH ].
      - simpl.
        intro taus.
        destruct (factorize (intersect taus)).
        reflexivity.
      - intro taus.
        destruct sigma using IntersectionType_rect'.
        + destruct sigmas.
          * simpl.
            destruct taus; reflexivity.
          * simpl append at 1.
            match goal with
            | [ |- factorize (@intersect ?m (cons _ (Ty (PT_omega)) ?n ?xs)) = _ ] =>
              assert (xxs_eq :
                        @intersect m (cons _ (Ty (PT_omega)) _ xs) =
                        @intersect (S n) (cons _ (Ty PT_omega) n xs));
              [ simpl; reflexivity | ]
            end.
            rewrite xxs_eq.
            rewrite (factorize_intersect_cons_omega).
            rewrite (factorize_intersect_cons_omega).
            apply IH.
        + destruct sigmas.
          * simpl; destruct taus; reflexivity.
          * simpl.
            set (IH' := IH taus).
            simpl in IH'.
            rewrite IH'.
            reflexivity.
        + destruct sigmas.
          * simpl; destruct taus; reflexivity.
          * simpl.
            set (IH' := IH taus).
            simpl in IH'.
            rewrite IH'.
            reflexivity.
        + destruct sigmas.
          * simpl; destruct taus.
            { simpl.
              rewrite Vector_append_nil.
              reflexivity. }
            { simpl.
              reflexivity. }
          * simpl.
            set (IH' := IH taus).
            simpl in IH'.
            rewrite IH'.
            simpl.
            apply (existT_eq _ _ _ _ _ (Nat.add_assoc _ _ _)).
            rewrite <- (Vector_append_assoc).
            reflexivity.
    Qed.

    Lemma Path_src_count:
      forall sigma tau, sigma <= tau -> Path sigma -> Path tau -> src_count sigma = src_count tau.
    Proof.
      intros sigma tau sigma_le path_sigma.
      revert tau sigma_le.
      induction path_sigma as [ | sigma' tau' path_sigma IH ].
      - intros tau sigma_le path_tau.
        inversion path_tau as [ | sigma' tau' path_tau' tau_eq ].
        + reflexivity.
        + rewrite <- tau_eq in sigma_le.
          contradict sigma_le.
          unfold not; intro sigma_le.
          set (sigma_le' := CF_complete _ _ _ sigma_le).
          inversion sigma_le'.
          apply (Omega_path _ path_tau').
          assumption.
      - intros tau sigma_le path_tau.
        inversion path_tau as [ C args path_C tau_eq | sigma'' tau'' path_tau'' tau_eq ].
        + rewrite <- tau_eq in sigma_le.
          contradict sigma_le.
          unfold not; intro sigma_le.
          set (sigma_le' := AF_complete _ _ _ sigma_le).
          inversion sigma_le'.
          contradiction.
        + simpl.
          apply f_equal.
          apply IH.
          * rewrite <- tau_eq in sigma_le.
            set (sigma_le' := AF_complete _ _ _ sigma_le).
            inversion sigma_le' as [ | | ? omega_tau'' ].
            { assumption. }
            { contradict omega_tau''.
              unfold not.
              apply Omega_path.
              apply Path_Arr.
              assumption. }
          * assumption.
    Qed.

    Lemma Path_split_path: forall sigma n prf, Path sigma -> Path (snd (split_path sigma n prf)).
    Proof.
      intros sigma n prf path_sigma.
      revert n prf.
      induction path_sigma; intros n prf.
      - destruct n.
        + apply Path_Const; assumption.
        + inversion prf.
      - destruct n.
        + apply Path_Arr; assumption.
        + simpl; auto.
    Qed.

    Lemma split_path_shiftin: forall sigma n prf prf',
        fst (split_path sigma (S n) prf) = shiftin (last (fst (split_path sigma (S n) prf)))
                                                   (fst (split_path sigma n prf')).
    Proof.
      intros sigma. 
      induction sigma as [ | | ? ? IHsigma IHtau | ] using IntersectionType_rect';
        destruct n;
        intros prf prf';
        try solve [ inversion prf ].
      - reflexivity.
      - simpl.
        apply f_equal.
        eapply IHtau.
    Qed.

    Lemma source_count_plus: forall sigma n prf,
        src_count sigma = (n + (src_count (snd (split_path sigma n prf))))%nat.
    Proof.
      intros sigma.
      induction sigma using IntersectionType_rect';
        intros n prf;
        destruct n;
        try solve [ reflexivity | inversion prf ].
      simpl.
      auto.
    Qed.      
    
    Lemma CL_Path: forall Gamma M sigma,
        CL Gamma M sigma ->
        Forall (fun sigma' =>
                  exists S, WellFormed S /\
                       Exists (fun path =>
                                 Path path /\
                                 exists argCountPrf : (argumentCount M <= src_count path)%nat,
                                   Forall2 (CL Gamma) (argumentsOf M)
                                           (fst (split_path path _ argCountPrf)) /\
                                   (snd (split_path path _ argCountPrf)) <= sigma'
                              )
                              (projT2 (factorize (organize (Apply S (Gamma (rootOf M)))))))
               (projT2 (factorize (organize sigma))).
    Proof.
      intros Gamma M sigma prf.
      induction prf as
          [ c S
          | M N sigma tau Msigmatau IHM Nsigma IHN
          | ? sigma tau
          | ? sigma tau prf IH sigma_le ].
      - apply (nth_Forall).
        intro k.
        eexists; split.
        + eassumption.
        + simpl.
          generalize (Forall_nth _ _ (organized_path_factors _ (organize_organized (Apply S (Gamma c))))).
          revert k.
          generalize (factorize (organize (Apply S (Gamma c)))).
          intros [ n factors ].
          simpl.
          intro k.
          induction k as [ | ? k IH ].
          * apply (caseS' factors).
            clear factors; intros factor factors.
            intro kth_path.
            apply Exists_cons_hd; split.
            { exact (kth_path F1). }
            { exists (le_0_n _); split.
              - apply Forall2_nil.
              - reflexivity. }
          * apply (caseS' factors).
            clear factors; intros factor factors.
            intro kth_path.
            apply Exists_cons_tl.
            simpl.
            apply IH.
            intro k'.
            exact (kth_path (FS k')).
      - clear IHN.
        simpl rootOf.
        destruct (Omega_dec tau) as [ omega_tau | not_omega_tau ].
        + rewrite (organize_omega _ omega_tau).
          apply Forall_nil.
        + rewrite (factors_map_distrib _ _ not_omega_tau) in IHM.
          simpl in IHM.
          generalize (organized_path_factors _ (organize_organized tau)).
          generalize (Forall_map _ _ _ IHM).
          clear IHM.
          intro IHM.
          induction IHM as [ | n factor factors factor_prf factors_prf IH ].
          * intros.
            apply Forall_nil.
          * intro factor_paths.
            apply Forall_cons.
            { destruct factor_prf as [ S [ WF_S ex_prf ] ].
              exists S; split; [ assumption | ].
              induction ex_prf as
                  [ n' factor' factors' [ path_factor' [ argCountPrf [ args_prf tgt_prf ]]]
                  | n' factor' factors' IHex
                  ].
              - apply Exists_cons_hd; split.
                + assumption.
                + assert (argCountPrf' : (argumentCount (App M N) <= src_count factor')%nat).
                  { inversion factor_paths as [  | ? ? ? path_factor ].
                    set (tgt_S_n := Path_src_count _ _ tgt_prf (Path_split_path _ _ _ path_factor')
                                                   (Path_Arr _ _ path_factor)).
                    rewrite (source_count_plus _ _ argCountPrf).
                    simpl.
                    rewrite tgt_S_n.
                    simpl.
                    rewrite <- (Nat.add_succ_comm).
                    apply (Nat.le_add_r). }
                  exists argCountPrf'; split.
                  * rewrite (split_path_shiftin _ _ _ argCountPrf).
                    
              - apply Exists_cons_tl; assumption. }
            { apply IH.
              inversion factor_paths as [ | ? ? ? ? ? n_eq [ factor_eq factors_eq ]].
              dependent rewrite <- factors_eq.
              assumption. }
      - simpl.
        rewrite (factorize_intersect_append).
        simpl.
        rewrite <- (factorize_organized _ (organize_organized sigma)).
        rewrite <- (factorize_organized _ (organize_organized tau)).
        apply Forall_append; assumption.
      - generalize (ST_organization _ _ sigma_le).
        intro sigma_paths.
        induction sigma_paths as [ | ? ? ? prf' ].
        + apply Forall_nil.
        + apply Forall_cons.
          clear sigma_paths.
          * induction prf' as [ sigma' ? ?  [ path_sigma' sigma'_le ] | ? ? ? ? IH' ].
            { inversion IH as [ | ? ? ? [ S [ WF_S prfs ] ] ].
              exists S; split; [ assumption | ].
              induction prfs as [ ? path ? [ path_path [ argPrf [ args_le tgt_le ] ] ] | ].
              - apply Exists_cons_hd.
                split; [ assumption | ].
                exists argPrf; split.
                + assumption.
                + rewrite <- sigma'_le.
                  assumption.
              - apply Exists_cons_tl.
                assumption. }
            { inversion IH as [ | ? ? ? ? ? n_eq [ hd_eq tl_eq ] ].
              apply IH'.
              dependent rewrite <- tl_eq.
              assumption. }             
          * assumption.
    Qed.
    
(*
    Lemma MP_generation: forall Gamma M N tau,
        CL Gamma (App M N) tau -> { sigma: _ | CL Gamma M (Arrow sigma tau) /\ CL Gamma N sigma }.
    Proof.
      intros Gamma M N tau prf.
      remember (App M N) as MN eqn:MN_eq.
      generalize M N MN_eq.
      clear MN_eq M N.      
      induction prf; intros M' N' MN_eq.
      - inversion MN_eq.
      - exists sigma.
        inversion MN_eq as [ [ M_eq N_eq ] ].
        rewrite <- M_eq.
        rewrite <- N_eq.
        split; assumption.
      - destruct (IHprf1 _ _ MN_eq) as [ src1 [ M'_prf1' N'_prf'1 ] ].
        destruct (IHprf2 _ _ MN_eq) as [ src2 [ M'_prf2' N'_prf'2 ] ].
        exists (Inter src1 src2).
        split.
        + apply (CL_ST _ _ (Inter (Arrow src1 sigma) (Arrow src2 tau))).
          * apply CL_II; assumption.
          * transitivity (Inter (Arrow (Inter src1 src2) sigma)
                              (Arrow (Inter src1 src2) tau)).
            { apply ST_Both.
              - transitivity (Arrow src1 sigma).
                + apply ST_InterMeetLeft.
                + apply ST_CoContra.
                  * apply ST_InterMeetLeft.
                  * reflexivity.
              - transitivity (Arrow src2 tau).
                + apply ST_InterMeetRight.
                + apply ST_CoContra.
                  * apply ST_InterMeetRight.
                  * reflexivity.
            }
            { apply ST_InterArrowDistrib. }
        + apply CL_II; assumption.
      - destruct (IHprf _ _ MN_eq) as [ src [ M_prf' N_prf' ] ].
        exists src.
        split.
        + apply (CL_ST _ _ (Arrow src sigma)).
          * assumption.
          * apply ST_CoContra; [ reflexivity | assumption ].
        + assumption.
    Qed.


    Fixpoint makeArrow {n: nat} (sources: t IntersectionType n) (tgt: IntersectionType): IntersectionType :=
      match sources with
      | nil _ => tgt
      | cons _ source _ sources' => Arrow source (makeArrow sources' tgt)
      end.

    Lemma makeArrow_shiftin: forall {n : nat} (sources: t IntersectionType n) (source tgt: IntersectionType),
      makeArrow (shiftin source sources) tgt = makeArrow sources (Arrow source tgt).
    Proof.
      intros n sources.
      induction sources as [ | ? ? ? IH ].
      - intros; trivial.
      - intros source tgt.
        simpl.
        rewrite IH.
        trivial.
    Qed.

    Lemma MP_generation_iterated: forall Gamma M tau,
        CL Gamma M tau -> { sigmas : t IntersectionType (argumentCount M) |
                           CL Gamma (Symbol (rootOf M)) (makeArrow sigmas tau) /\
                           Forall2 (CL Gamma) (argumentsOf M) sigmas }.
    Proof.
      intros Gamma M.
      induction M as [ | M' IHM' N IHN ].
      - intros tau prf.
        exists (nil _).
        split.
        + exact prf.
        + apply Forall2_nil.
      - intros tau prf.
        destruct (MP_generation _ _ _ _ prf) as [ sigma [ M'prf Nprf ] ].
        destruct (IHM' _ M'prf) as [ sigmas [ M'rootPrf M'args ] ].
        exists (shiftin sigma sigmas).
        split.
        + simpl.
          rewrite (makeArrow_shiftin).
          assumption.
        + simpl.
          apply ForAll2'_shiftin; assumption.
    Qed.


    Lemma map_append: forall {S T} {m n}  (f: S -> T) (xs: t S m) (ys: t S n),
        map f (append xs ys) = append (map f xs) (map f ys).
    Proof.
      intros S T m n f xs.
      induction xs as [ | ? ? ? IH ]; intro ys.
      - reflexivity.
      - simpl.
        rewrite (IH _).
        reflexivity.
    Qed.

    Lemma intersect_cons:
      forall {n} x (xs: t IntersectionType n),
        intersect (cons _ x _ xs) <= Inter x (intersect xs).
    Proof.
      intros n x xs.
      induction xs.
      - apply ST_Both.
        + reflexivity.
        + apply ST_OmegaTop.
      - reflexivity.
    Qed.          

    Lemma intersect_append:
      forall {m n} (xs: t IntersectionType m) (ys: t IntersectionType n),
        intersect (append xs ys) <= Inter (intersect xs) (intersect ys).
    Proof.
      intros m n xs.
      induction xs; intros ys.
      - apply ST_Both.
        + apply ST_OmegaTop.
        + reflexivity.
      - simpl.     
        destruct xs.
        + destruct ys; simpl.
          * apply ST_Both.
            { reflexivity. }
            { apply ST_OmegaTop. }
          * reflexivity.
        + rewrite <- (ST_ReassocRight h (intersect (cons _ _ _ xs))).
          apply ST_Both.
          * destruct (append (cons _ h0 _ xs) ys).
            { reflexivity. }
            { apply ST_InterMeetLeft. }
          * simpl.
            etransitivity.
            { apply ST_InterMeetRight. }
            { exact (IHxs ys). }
    Qed.

    Lemma minimalCombinatorType: forall Gamma c tau,
        CL Gamma (Symbol c) tau ->
        { k : _ &
              { Ss: t Substitution (S k)
              | Forall WellFormed Ss
              /\ intersect (map (fun S => Apply S (Gamma c)) Ss) <= tau } }.
    Proof.
      intros Gamma c tau prf.
      remember (Symbol c) as M eqn:Meq.
      induction prf
        as [ ? S WFS
           |
           | ? sigma tau cSigma IHsigma cTau IHtau
           | ? ? ? cSigma IHsigma sigmatau ]; inversion Meq.
      - exists 0.
        exists (cons _ S _ (nil _)); split.
        + apply Forall_cons.
          * assumption.
          * apply Forall_nil.
        + reflexivity.
      - destruct (IHsigma Meq) as [ k1 [ Ss1 [ WFSs1 SS1sigma ] ] ].
        destruct (IHtau Meq) as [ k2 [ Ss2 [ WFSs2 SS2tau ] ] ].
        exists (plus k1 (S k2)).
        exists (append Ss1 Ss2); split.
        + apply (Forall_append (m := S k2) (n := S k1)); assumption.
        + rewrite (map_append (m := S k1) (n := S k2)).
          etransitivity.
          * apply (intersect_append (m := S k1) (n := S k2)).
          * apply ST_Both.
            { rewrite <- SS1sigma; apply ST_InterMeetLeft. }
            { rewrite <- SS2tau; apply ST_InterMeetRight. }
      - destruct (IHsigma Meq)
          as [ k [ Ss [ WFSs Sssigma ] ] ].
        exists k. exists Ss; split.
        + assumption.
        + rewrite <- sigmatau; assumption.
    Qed. *)
            
  End TypeSystem.    
End CombinatoryLogic.

Module Type SymbolsWithoutVariables := SymbolSpecification with Definition VariableSymbol := False.

Module Type ForbidVariablesIn(Symbols: SymbolSpecification) <: SymbolsWithoutVariables
    with Definition ConstructorSymbol := Symbols.ConstructorSymbol
    with Definition constructorArity := Symbols.constructorArity
    with Definition ConstructorTaxonomy := Symbols.ConstructorTaxonomy
    with Definition CTPreorder := Symbols.CTPreorder
    with Definition CombinatorSymbol := Symbols.CombinatorSymbol.
    Include SymbolsWithoutVariables
      with Definition ConstructorSymbol := Symbols.ConstructorSymbol
      with Definition constructorArity := Symbols.constructorArity
      with Definition ConstructorTaxonomy := Symbols.ConstructorTaxonomy
      with Definition CTPreorder := Symbols.CTPreorder
      with Definition CombinatorSymbol := Symbols.CombinatorSymbol.
End ForbidVariablesIn.  

Module Type FiniteCombinatoryLogic (Symbols: SymbolsWithoutVariables)
  <: CombinatoryLogic(Symbols).
  Include CombinatoryLogic(Symbols).
  Module Type FCL
    <: TypeSystem with
          Definition WellFormed := fun (S: Substitution) => True.
    Include TypeSystem with Definition WellFormed := fun (S : Substitution) => True.

    Hint Unfold WellFormed.
    
    Lemma substition_irrelevant:
      forall sigma S S', Apply S sigma = Apply S' sigma.
    Proof.
      intros sigma S S'.
      induction sigma
        as [ | | ? ? ps | ? ? IHsigma IHtau | ? ? IHsigma IHtau ]
             using TypeScheme_rect'; try solve [ auto ].
      - contradiction.
      - simpl.
        apply f_equal.
        induction ps as [ | ? ? ? IHH ? IHT ].
        + reflexivity.
        + simpl.
          rewrite IHH.
          rewrite IHT.
          reflexivity.
      - simpl.
        rewrite IHsigma.
        rewrite IHtau.
        reflexivity.
      - simpl.
        rewrite IHsigma.
        rewrite IHtau.
        reflexivity.
    Qed.
        
    Lemma context_specialization:
      forall Gamma c sigma S, CL Gamma (Symbol c) sigma -> Apply S (Gamma c) <= sigma.
    Proof.
      intros Gamma c sigma S.
      remember (Symbol c) as M eqn:M_eq.
      intro prf.
      induction prf as [ ? S' | | ? ? ? ? IHsigma IHtau | ? ? ? ? IH ].
      - rewrite (substition_irrelevant _ S S').
        inversion M_eq.
        reflexivity.
      - inversion M_eq.
      - apply ST_Both; auto using IHsigma, IHtau.
      - transitivity sigma; auto using IH.
    Qed.

    (*Lemma II_Admissible:
      forall (Gamma : Context)
        (P : Term -> IntersectionType -> Prop),
        (forall (c : CombinatorSymbol) (S : Substitution),
            WellFormed S -> P (Symbol c) (Apply S (Gamma c))) ->
        (forall (M N : Term) (sigma tau : IntersectionType),
            CL Gamma M (Arrow sigma tau) ->
            P M (Arrow sigma tau) ->
            CL Gamma N sigma -> P N sigma -> P (App M N) tau) ->
        (forall (M : Term) (sigma tau : IntersectionType),
            CL Gamma M sigma -> P M sigma -> sigma <= tau -> P M tau) ->
        forall (M : Term) (tau : IntersectionType), CL Gamma M tau -> P M tau.
    Proof.
      intros Gamma P Var_case MP_case ST_case M.
      induction M; intros tau prf.
      - apply (ST_case _ (Apply (fun x => omega) (Gamma c))).
        + apply CL_Var.
          auto.
        + apply Var_case.
          auto.
        + apply context_specialization.
          assumption.
      - inversion prf.        
        destruct (MP_generation _ _ _ _ prf) as [ sigma [ M1_prf M2_prf ] ].
        apply (MP_case _ _ sigma).
        + assumption.
        + apply IHM1; assumption.
        + assumption.
        + apply IHM2; assumption.
    Qed.  *)                                                            
  End FCL.
End FiniteCombinatoryLogic.

Module Type DisjointContexts(Symbols: SymbolSpecification) <: CombinatoryLogic(Symbols).
  Include CombinatoryLogic(Symbols).

  Class DisjointContexts (numberOfContexts : nat) := {
    SymbolOf: Fin.t numberOfContexts -> ConstructorSymbol -> Prop;
    SymbolsDisjoint: forall C n m, n <> m -> SymbolOf n C -> SymbolOf m C -> False;
    SymbolsFull: forall C, { n: _ | SymbolOf n C };
    SymbolsUnrelated: forall C1 C2 n m,
        n <> m -> SymbolOf n C1 -> SymbolOf m C2 -> ConstructorTaxonomy C1 C2 -> False;

    VariableOf : Fin.t numberOfContexts -> VariableSymbol -> Prop;
    VariablesDisjoint: forall alpha n m, n <> m -> VariableOf n alpha -> VariableOf m alpha -> False;
    VariablesFull: forall alpha, { n : _ | VariableOf n alpha } }.

  Section Disjoint.
    Context { numberOfContexts: nat }.
    Context { disjointProperties : DisjointContexts numberOfContexts }.
  
    Inductive TypeOf (n: Fin.t numberOfContexts): IntersectionType -> Prop :=
    | OmegaOf : TypeOf n (Ty PT_omega)
    | ConstOf : forall C sigmas,
        SymbolOf n C -> Forall (TypeOf n) sigmas ->
        TypeOf n (Ty (PT_Const C sigmas))
    | ArrowOf : forall sigma tau,
        TypeOf n sigma -> TypeOf n tau ->
        TypeOf n (Ty (PT_Arrow sigma tau))
    | InterOf: forall sigma tau,
        TypeOf n sigma -> TypeOf n tau ->
        TypeOf n (Ty (PT_Inter sigma tau)).

    Inductive TypeSchemeOf (n : Fin.t numberOfContexts): TypeScheme -> Prop :=
    | TS_OmegaOf : TypeSchemeOf n (Skeleton PT_omega)
    | TS_ConstOf : forall C sigmas,
        SymbolOf n C -> Forall (TypeSchemeOf n) sigmas ->
        TypeSchemeOf n (Skeleton (PT_Const C sigmas))
    | TS_ArrowOf : forall sigma tau,
        TypeSchemeOf n sigma -> TypeSchemeOf n tau ->
        TypeSchemeOf n (Skeleton (PT_Arrow sigma tau))
    | TS_InterOf: forall sigma tau,
        TypeSchemeOf n sigma -> TypeSchemeOf n tau ->
        TypeSchemeOf n (Skeleton (PT_Inter sigma tau))
    | TS_VarOf: forall alpha, VariableOf n alpha -> TypeSchemeOf n (Var alpha).

  

    Lemma decideTypeOf: forall (sigma: IntersectionType) (n: Fin.t numberOfContexts),
        (TypeOf n sigma) + (TypeOf n sigma -> False).
    Proof.
      intros sigma n.
      induction sigma
        as [ | C args IH | sigma tau IHsigma IHtau | sigma tau IHsigma IHtau ]
             using IntersectionType_rect';
        try solve [
              destruct IHsigma as [ sigmaPrf | sigmaDisprf ];
              destruct IHtau as [ tauPrf | tauDisprf ];
              solve [ left; apply ArrowOf || apply InterOf; assumption
                    | right;
                      intro devil;
                      inversion devil;
                      apply sigmaDisprf || apply tauDisprf;
                      assumption
                    ] 
            ].    
      - left; apply OmegaOf.
      - destruct (SymbolsFull C) as [ n' symC ].
        destruct (Fin.eq_dec n' n) as [ n_eq | n_ineq ].
        + assert (IH' : (Forall (TypeOf n) args)  + (Forall (TypeOf n) args -> False)).
          { induction args.
            - left; apply Forall_nil.
            - inversion IH as [ | ? ? ? hPrf argsPrf n_eq' [ h_eq args_eq ]].
              revert IHargs.
              dependent rewrite <- args_eq.
              intro IHargs.
              destruct hPrf. 
              + destruct (IHargs argsPrf) as [ | disprf ].
                * left.
                  apply Forall_cons; assumption.
                * right.
                  intro devil.
                  inversion devil as [ | ? ? ? hPrf' argsPrf' n_eq'' [ h_eq' args_eq' ] ].
                  dependent rewrite <- args_eq' in disprf.
                  contradiction.
              + right.
                intro devil.
                inversion devil.
                contradiction. }
          destruct IH' as [ | disprf ].
          * left.
            rewrite n_eq in symC.
            apply ConstOf; assumption.
          * right.
            intro devil.
            inversion devil as [ | ? ? ? argsPrf [ C_eq args_eq ] | | ].
            dependent rewrite <- args_eq in disprf.
            contradiction.
        + right.
          intro devil.
          inversion devil as [ | ? ? cSym | | ].
          apply (SymbolsDisjoint C n' n n_ineq); assumption.
    Qed.
    
    Lemma decideTypeSchemeOf: forall (sigma: TypeScheme) (n: Fin.t numberOfContexts),
        (TypeSchemeOf n sigma) + (TypeSchemeOf n sigma -> False).
    Proof.
      intros sigma n.
      induction sigma
        as [ alpha | | C args IH | sigma tau IHsigma IHtau | sigma tau IHsigma IHtau  ]
             using TypeScheme_rect';
        try solve [
              destruct IHsigma as [ sigmaPrf | sigmaDisprf ];
              destruct IHtau as [ tauPrf | tauDisprf ];
              solve [ left; apply TS_ArrowOf || apply TS_InterOf; assumption
                    | right;
                      intro devil;
                      inversion devil;
                      apply sigmaDisprf || apply tauDisprf;
                      assumption
                    ] 
            ].
      - destruct (VariablesFull alpha) as [ n' n'_alpha ].
        destruct (Fin.eq_dec n' n) as [ n_eq | n_ineq ].
        + left.
          apply TS_VarOf.
          rewrite <- n_eq.
          assumption.
        + right.
          intro devil.
          inversion devil.
          apply (VariablesDisjoint alpha n' n n_ineq); assumption.
      - left; apply TS_OmegaOf.
      - destruct (SymbolsFull C) as [ n' symC ].
        destruct (Fin.eq_dec n' n) as [ n_eq | n_ineq ].
        + assert (IH' : (Forall (TypeSchemeOf n) args)  + (Forall (TypeSchemeOf n) args -> False)).
          { induction args.
            - left; apply Forall_nil.
            - inversion IH as [ | ? ? ? hPrf argsPrf n_eq' [ h_eq args_eq ]].
              revert IHargs.
              dependent rewrite <- args_eq.
              intro IHargs.
              destruct hPrf. 
              + destruct (IHargs argsPrf) as [ | disprf ].
                * left.
                  apply Forall_cons; assumption.
                * right.
                  intro devil.
                  inversion devil as [ | ? ? ? hPrf' argsPrf' n_eq'' [ h_eq' args_eq' ] ].
                  dependent rewrite <- args_eq' in disprf.
                  contradiction.
              + right.
                intro devil.
                inversion devil.
                contradiction. }
          destruct IH' as [ | disprf ].
          * left.
            rewrite n_eq in symC.
            apply TS_ConstOf; assumption.
          * right.
            intro devil.
            inversion devil as [ | ? ? ? argsPrf [ C_eq args_eq ] | | | ].
            dependent rewrite <- args_eq in disprf.
            contradiction.
        + right.
          intro devil.
          inversion devil as [ | ? ? dC dArgs [ dCEq dArgsEq ] | | | ].
          apply (SymbolsDisjoint C n' n n_ineq); assumption.
    Qed.

    Lemma SymbolOfDecidable: forall C n, (SymbolOf n C) + (SymbolOf n C -> False).
    Proof.
      intros C n.
      destruct (SymbolsFull C) as [ n' symC ].
      destruct (Fin.eq_dec n' n) as [ n_eq | n_ineq ].
      - left; rewrite <- n_eq; assumption.
      - right.
        intro devil.
        apply (SymbolsDisjoint C n' n n_ineq); assumption.
    Qed.

    Fixpoint projectType (n: Fin.t numberOfContexts) (sigma: IntersectionType) :=
      match sigma with
      | Ty (PT_omega) => omega
      | Ty (PT_Const C sigmas) =>
        match (SymbolOfDecidable C n) with
        | inl _ => Ty (PT_Const C (map (projectType n) sigmas))
        | _ => omega
        end
      | Ty (PT_Inter sigma tau) =>
        Inter (projectType n sigma) (projectType n tau)
      | Ty (PT_Arrow sigma tau) =>
        Arrow (projectType n sigma) (projectType n tau)
      end.
    
    Lemma projectTypeOf: forall n sigma, TypeOf n (projectType n sigma).
    Proof.
      intros n sigma.
      induction sigma as [ | C | | ] using IntersectionType_rect'.
      - apply OmegaOf.
      - simpl.
        destruct (SymbolOfDecidable C n).
        + apply ConstOf.
          * assumption.
          * apply map_Forall.
            apply ForAll'Forall.
            assumption.
        + apply OmegaOf.
      - simpl; apply ArrowOf; assumption.
      - simpl; apply InterOf; assumption.
    Qed.

    Lemma projectType_id: forall n sigma, TypeOf n sigma -> projectType n sigma = sigma.
    Proof.
      intros n sigma.
      induction sigma
        as [ 
          | C sigmas IH
          | sigma tau IHsigma IHtau
          | sigma tau IHsigma IHtau ] using IntersectionType_rect';
        intro prf.
      - reflexivity.
      - inversion prf
          as [ | ? ? prfSymC prfTysOfsigmas [ prfCeq prfsigmaseq ] | | ].
        dependent rewrite prfsigmaseq in prfTysOfsigmas.
        clear prfCeq prfsigmaseq.
        simpl.
        destruct (SymbolOfDecidable C).
        + apply f_equal.
          apply f_equal.
          apply ForallEq_map.
          apply (Forall_ap _ (TypeOf n)).
          * apply ForAll'Forall; assumption.
          * assumption.
        + contradict prfSymC; assumption.
      - inversion prf as [ | | ? ?  TyOfnsigma TyOfntau | ].
        simpl.
        rewrite (IHsigma TyOfnsigma).
        rewrite (IHtau TyOfntau).
        reflexivity.
      - inversion prf as [ | | | ? ?  TyOfnsigma TyOfntau ].
        simpl.
        rewrite (IHsigma TyOfnsigma).
        rewrite (IHtau TyOfntau).
        reflexivity.
    Qed.

    Lemma TypeOf_omega: forall sigma m n, m <> n -> TypeOf m sigma -> TypeOf n sigma -> Organized sigma -> sigma = omega.
    Proof.
      intros sigma n m mn_ineq.
      induction sigma
        as [ | | sigma tau IHsigma IHtau | sigma1 sigma2 IHsigma1 IHsigma2 ] 
             using IntersectionType_rect';
        intros n_sigma m_sigma org_sigma.      
      - reflexivity.
      - inversion m_sigma.
        inversion n_sigma as [ | ? ? n_C | | ].
        contradict n_C.
        unfold not; intro n_C.
        apply (SymbolsDisjoint C n m mn_ineq); assumption.
      - inversion m_sigma.
        inversion n_sigma.
        inversion org_sigma as [ ? path_sigmatau | | ].
        assert (tau_omega : tau = omega).
        { apply IHtau.
          - assumption.
          - assumption.
          - inversion path_sigmatau.
            apply Organized_Path.
            assumption. }
        rewrite tau_omega in path_sigmatau.
        inversion path_sigmatau as [ | ? ? path_tau ].
        inversion path_tau.
      - inversion org_sigma as [ ? path_sigma | | ].
        + inversion path_sigma.
        + inversion n_sigma.
          inversion m_sigma.
          assert (sigma2_omega : sigma2 = omega).
          { apply IHsigma2; assumption. }
          contradiction.
    Qed.
    
    Import EqNotations.

    Lemma diag_typeOf {n: nat}:
      forall (args: t IntersectionType n) k,
        Forall (TypeOf k) args ->
        Forall (Forall (TypeOf k)) (diag omega args).
    Proof.
      intros args k prf.
      apply nth_Forall.
      intro k'.
      apply nth_Forall.
      intro k''.
      destruct (Fin.eq_dec k' k'') as [ k'_eq | k'_ineq ].
      - rewrite (diag_spec_one _ _ _ _ k'_eq).
        apply Forall_nth.
        assumption.
      - rewrite (diag_spec_zero _ _ _ _ k'_ineq).
        apply OmegaOf.
    Qed.

    Lemma intersect_typeOf {n: nat}:
      forall (args: t IntersectionType n) k,
        Forall (TypeOf k) args ->
        TypeOf k (intersect args).
    Proof.
      intros args k.
      induction args as [ | arg n args IH ].
      - intro; apply OmegaOf.
      - intro prf.
        inversion prf as [ | ? ? ? ? ? n_eq [ h_eq tl_eq ] ].
        destruct args.
        + simpl; assumption.
        + apply InterOf.
          * assumption.
          * apply IH.
            dependent rewrite <- tl_eq.
            assumption.
    Qed.

    Lemma factorize_typeOf:
      forall sigma k,
        TypeOf k sigma ->
        Forall (TypeOf k) (projT2 (factorize sigma)).
    Proof.
      intros sigma k.
      induction sigma using IntersectionType_rect'.
      - intro; apply Forall_nil.
      - intro prf.
        apply Forall_cons.
        + assumption.
        + apply Forall_nil.
      - intro prf.
        apply Forall_cons.
        + assumption.
        + apply Forall_nil.
      - intro prf.
        simpl.
        inversion prf.
        apply Forall_append; auto.
    Qed.

    Lemma intersect_many_typeOf {m: nat}:
      forall (argss: t { n : _ & t IntersectionType n } m) k,
        Forall (fun args => Forall (TypeOf k) (projT2 args)) argss ->
        TypeOf k (intersect_many argss).
    Proof.
      intros argss k.
      induction argss.
      - intro; apply OmegaOf.
      - intro prf.
        unfold intersect_many.
        apply intersect_typeOf.
        apply factorize_typeOf.
        apply intersect_typeOf.
        apply nth_Forall.
        intro k'.
        rewrite (nth_map _ _ _ _ eq_refl).
        apply intersect_typeOf.
        apply Forall_nth.
        assumption.
    Qed.

    Lemma factorize_argument_typeOf {n: nat} {C: ConstructorSymbol}:
      forall (args: t IntersectionType n) (pos : Fin.t n) (n_eq: n = constructorArity C) k,
        Forall (TypeOf k) args ->
        SymbolOf k C ->
        Forall (TypeOf k) (projT2 (factorize_argument C (rew [t IntersectionType] n_eq in args)
                                                      (rew [Fin.t] n_eq in pos))).
    Proof.
      intros args pos n_eq k prf symPrf.
      unfold factorize_argument.
      assert (argPrf : TypeOf k (nth (rew [t IntersectionType] n_eq in args)
                                     (rew [Fin.t] n_eq in pos))).
      { rewrite <- n_eq.
        simpl.
        apply Forall_nth.
        assumption. }
      assert (factorsPrf : Forall (TypeOf k) (projT2 (factorize
                                                        (nth (rew [t IntersectionType] n_eq in args)
                                                             (rew [Fin.t] n_eq in pos))))).
      { apply factorize_typeOf.
        assumption. }
      revert factorsPrf.
      destruct (factorize (nth (rew [t IntersectionType] n_eq in args)
                               (rew [Fin.t] n_eq in pos))) as [ n' [ | h ? t ] ].
      - intro.
        simpl.
        apply Forall_cons; [ | apply Forall_nil].
        apply ConstOf; [ assumption | ].
        apply nth_Forall.
        intro k'.
        destruct (Fin.eq_dec k' (rew [Fin.t] n_eq in pos)) as [ pos_eq | pos_ineq ].
        + rewrite replace_replaced; [ | assumption ].
          apply OmegaOf.
        + rewrite replace_others; [ | assumption ].
          apply Forall_nth.
          rewrite <- n_eq.
          assumption.
      - intro factorsPrf.
        inversion factorsPrf as [ | ? ? ? ? ? n'_eq [ h_eq tl_eq ] ].
        simpl.
        apply nth_Forall.
        intro k'.
        apply (Fin.caseS' k').
        + simpl.
          apply ConstOf; [ assumption | ].
          apply nth_Forall.
          intro k''.
          destruct (Fin.eq_dec k'' (rew [Fin.t] n_eq in pos)) as [ pos_eq | pos_ineq ].
          * rewrite replace_replaced; [ | assumption ].
            assumption.
          * rewrite replace_others; [ | assumption ].
            apply Forall_nth.
            rewrite <- n_eq.
            assumption.
        + simpl.
          intro k''.
          rewrite (nth_map (fun arg => Const C (replace (rew n_eq in args) (rew n_eq in pos) arg))
                           t _ k'' eq_refl).
          apply ConstOf; [ assumption | ].
          apply nth_Forall.
          intro k'''.
          destruct (Fin.eq_dec k''' (rew [Fin.t] n_eq in pos)) as [ pos_eq | pos_ineq ].
          * rewrite replace_replaced; [ | assumption ].
            apply Forall_nth.
            dependent rewrite <- tl_eq.
            assumption.
          * rewrite replace_others; [ | assumption ].
            apply Forall_nth.
            rewrite <- n_eq.
            assumption.
    Qed.   
    
    Lemma organizeConstructor'_typeOf {n : nat} (C: ConstructorSymbol) k:
      forall (args: t IntersectionType n) (n_eq: n = constructorArity C)
        (organize: IntersectionType -> IntersectionType)
        (organize_typeOf: Forall (TypeOf k) (map organize args)),
        TypeOf k (Const C (rew n_eq in args)) ->
        TypeOf k (organizeConstructor' organize args C n_eq).
    Proof.
      unfold organizeConstructor'.
      intros args n_eq organize organize_typeOf args_typeOf.
      inversion args_typeOf as [ | ? ? symPrf argsPrf [ C_eq args_eq ] | | ].
      destruct n.
      - apply ConstOf.
        + assumption.
        + dependent rewrite <- args_eq.
          assumption.
      - apply (intersect_typeOf).
        apply (factorize_typeOf).
        apply (intersect_typeOf).
        apply nth_Forall.
        intro k'.
        rewrite (nth_map _ _ _ _ eq_refl).
        apply (intersect_typeOf).
        apply nth_Forall.
        rewrite (nth_map2 _ (diag omega (map organize args)) (positions (S n)) k' k' k' eq_refl eq_refl).
        intro k''.
        simpl.
        apply (Forall_nth).
        apply (factorize_argument_typeOf).
        + apply (Forall_nth).
          apply (diag_typeOf).
          assumption.
        + assumption.
    Qed.
    

    Lemma organize_typeOf: forall sigma n, TypeOf n sigma -> TypeOf n (organize sigma).
    Proof.
      intros sigma n.
      induction sigma
        as [ | C args IHargs | sigma tau IHsigma IHtau | sigma1 sigma2 IHsigma1 IHsigma2 ]
             using IntersectionType_rect'.
      - intro. apply OmegaOf.
      - intro tyOf.
        simpl.
        apply organizeConstructor'_typeOf.
        + apply map_Forall.
          inversion tyOf as [ | ? ? symPrf argsPrf [ C_eq args_eq ] | | ].
          dependent rewrite args_eq in argsPrf.
          apply (fun IH => Forall_ap _ (TypeOf n) (fun sigma => TypeOf n (organize sigma)) IH argsPrf).
          apply ForAll'Forall.
          assumption.
        + assumption.
      - intro prf.
        inversion prf as [ | | ? ? sigmaPrf tauPrf | ].
        simpl.
        induction (organize tau) using IntersectionType_rect';
          try solve [ apply ArrowOf; [ assumption | apply IHtau; assumption ] ].
        + apply OmegaOf.
        + apply (intersect_typeOf).
          apply (nth_Forall).
          intro k'.
          rewrite (nth_map _ _ _ _ eq_refl).
          apply ArrowOf; [ assumption | ].
          apply (Forall_nth).
          generalize (IHtau tauPrf).
          intro IH.
          inversion IH.
          apply (Forall_append);
            apply (factorize_typeOf);
            assumption.
      - intro prf.
        inversion prf.
        simpl.
        apply (intersect_typeOf).
        apply (Forall_append);
          apply (factorize_typeOf);
          [ apply IHsigma1 | apply IHsigma2 ];
          assumption.
    Qed.
  End Disjoint.
    
  Module Type DisjointTypeSystem <: TypeSystem.
    Include TypeSystem.

    Section Disjoint.
      Context { numberOfContexts: nat }.
      Context { disjointProperties : DisjointContexts numberOfContexts }.
    
      Variable WF_respectful:
        forall S, WellFormed S ->
             forall sigma n, TypeSchemeOf n sigma -> TypeOf n (Apply S sigma).

      Fixpoint intersectContexts {n} (ctxts: t Context n): Context :=
        fun c =>
          match ctxts with
          | nil _ => omegaScheme
          | cons _ h _ (nil _) => h c
          | cons _ h _ ctxts => InterScheme (h c) (intersectContexts ctxts c)
          end.
      
      Section CombinedContext.
        Variable contexts: t Context numberOfContexts.
        Variable contextsWF: forall n c, TypeSchemeOf n ((nth contexts n) c).

        Definition Gamma := intersectContexts contexts.

        Definition tgt (sigma: IntersectionType): IntersectionType :=
          match sigma with
          | Ty (PT_Arrow sigma tau) => tau
          | x => x
          end.

        Definition src (sigma: IntersectionType): IntersectionType :=
          match sigma with
          | Ty (PT_Arrow sigma tau) => sigma
          | x => x
          end.

      
        Import EqNotations.
        
        Lemma Path_assumption_singular:
          forall S c (path_c: Path (Apply S (Gamma c))),
            numberOfContexts = 1.
        Proof.
          unfold Gamma.
          intros S c path_c.
          destruct (Nat.eq_dec numberOfContexts 1) as [ | n_ineq ].
          - assumption.
          - destruct numberOfContexts as [ | n ].
            + revert path_c.
              apply (fun r => case0 (fun ctxts => Path (Apply S (intersectContexts ctxts c)) -> 0 = 1) r contexts).
              intro path_c.
              simpl in path_c.
              inversion path_c.
            + destruct n.
              * reflexivity.
              * revert path_c.
                apply (caseS' contexts).
                intros ctxt contexts'.
                apply (caseS' contexts').
                clear contexts'; intros ctxt' contexts'.
                intro path_c.
                simpl in path_c.
                inversion path_c.
        Qed.

        Lemma TypeOf_singular_context:
          forall S c (singular_context: numberOfContexts = 1) (WF_S: WellFormed S),
            TypeOf (rew <- singular_context in F1) (Apply S (Gamma c)).
        Proof.
          unfold Gamma.
          intros S c singular_context WF_S.
          revert contextsWF.
          destruct numberOfContexts.
          - inversion singular_context.
          - inversion singular_context as [ n_eq ].
            destruct n.
            + unfold eq_rect_r.
              rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ (eq_sym singular_context)).
              apply (caseS' contexts).
              intros ctxt ctxts.
              apply (fun r =>
                       case0 (fun xs =>
                                (forall n c, TypeSchemeOf n (nth (cons _ _ _ xs) n c)) ->
                                TypeOf _ (Apply _ (intersectContexts (cons _ _ _ xs) _)))
                             r ctxts).
              intro contextsWF.
              simpl.
              apply (WF_respectful).
              * assumption.
              * apply (contextsWF F1 c).
            + inversion n_eq.
        Qed.
        
        Lemma TypeOf_path:
          forall M sigma,
            CL Gamma M sigma ->
            exists tau, tau <= sigma /\ Organized tau /\ Forall (fun tau' => exists n, TypeOf n tau') (projT2 (factorize tau)).
        Proof.
          intros M sigma prf.
          induction prf.
          - 
          
          
          intros M sigma prf.
          induction prf as [ | M N sigma tau Msigmatau IHM Nsigma IHN | | ? ? ? Msigma IH sigma_le ].
          - intros sigma' path_sigma'.
            exists sigma'.
            repeat split.
            + assumption.
            + assumption.
            + assert (n_eq: numberOfContexts = 1).
              { apply (Path_assumption_singular S c).
                assumption. }
              exists (rew <- n_eq in F1).
              apply (TypeOf_singular_context S c n_eq).
              assumption.
          - intro path_tau.
            destruct (IHM (Path_Arr _ _ path_tau))
              as [ sigmatau' [ sigmatau'_le [ path_sigmatau' [ n sigmatau'_n ] ] ] ].
            induction (sigmatau') using IntersectionType_rect';
              try solve [ inversion path_sigmatau' ].
            + assert (omega_tau := ST_Const_Arrow _ _ _ _ sigmatau'_le).
              contradict omega_tau.
              unfold not.
              apply Omega_path; assumption.
            + set (AF_sigmatau' := AF_complete _ _ _ sigmatau'_le).
              inversion AF_sigmatau' as [ ? ? ? tau_ge | | ? tau_omega ].
              * eexists.
                repeat split.
                { exact tau_ge. }
                { inversion path_sigmatau'; assumption. }
                { inversion sigmatau'_n; eexists; eassumption. }
              * simpl in tau_omega.
                contradict tau_omega.
                unfold not.
                apply Omega_path; assumption.
          - intro path_sigmatau; inversion path_sigmatau.
          - intro path
            destruct (ST_path _ sigma_le 
          
      
      Lemma TypeOf_arrow_omega:
        forall M sigma tau n,
          CL Gamma M (Arrow sigma tau) ->
          (TypeOf n sigma -> False) ->
          TypeOf n tau ->
          Organized tau ->
          tau = omega.
      Proof.
        intros M sigma tau n prf.
        assert (tau_eq: tau = tgt (Arrow sigma tau)); [ reflexivity | ].
        assert (sigma_eq: sigma = src (Arrow sigma tau)); [ reflexivity | ].
        rewrite sigma_eq.
        rewrite tau_eq at 2 3 4.
        clear tau_eq sigma_eq.
        induction prf.
        - intros not_n_sigma n_tau org_tau.
          clear sigma tau.
          assert (Gamma_eq: Apply S (Gamma c) = Arrow (src (Apply S (Gamma c))) (tgt (Apply S (Gamma c)))).
          { induction (Apply S (Gamma c))
                      using IntersectionType_rect';
              try solve [ contradiction ].
            reflexivity. }
          remember (src (Apply S (Gamma c))) as sigma.
          remember (tgt (Apply S (Gamma c))) as tau.
          unfold Gamma in Gamma_eq.
          destruct (intersectContexts contexts c) as [ | alpha ].
          * destruct (VariablesDecidable alpha n).
            { assert (n_sigmatau : TypeOf n (Apply S (Var alpha))).
              { apply WF_respectful.
                - assumption.
                - apply TS_VarOf.
                  assumption. }
              rewrite Gamma_eq in n_sigmatau.
              inversion n_sigmatau.
              contradiction. }
            { assert (m_sigmatau: exists m, TypeOf m (Arrow sigma tau)).
              { rewrite <- Gamma_eq.
                destruct (VariablesFull alpha) as [ m m_alpha ].
                exists m.
                apply WF_respectful.
                - assumption.
                - apply TS_VarOf.
                  assumption. }
              destruct m_sigmatau as [ m m_sigmatau ].
              inversion m_sigmatau as [ | | ? ? m_sigma m_tau | ].
              intros.
              apply (TypeOf_omega tau m n); try solve [ assumption ].
              unfold not; intro mn_eq.
              rewrite mn_eq in m_sigma.
              contradiction. }
          * admit.
        - 
              
            
      
      Lemma ContextSeparation_sound:
        forall n M tau, TypeOf n tau -> CL Gamma M tau -> CL (nth contexts n) M tau.
      Proof.
        

      

      Fixpoint applyAll {n} (M: Term) (Ms: t Term n): Term :=
        match Ms with
        | nil _ => M
        | cons _ h _ tl => applyAll (App M h) tl
        end.

      Lemma typesSound:
        forall n c {k} (Ms : t Term k) tau,
          TypeOf n tau -> CL Gamma (applyAll (Symbol c) Ms) tau -> CL (nth contexts n) (applyAll (Symbol c) Ms) tau.
      Proof.
        intros n c k.
        induction k.
        - intro Ms.
          apply (fun P H => case0 P H Ms).
          simpl.
          apply combinatorTypesSound.
        - 

      
      Lemma combinatorTypesSound:
        forall n c tau, TypeOf n tau -> CL Gamma (Symbol c) tau -> CL (nth contexts n) (Symbol c) tau.
      Proof.
        intros n c tau tauOfn prf.
        destruct (minimalCombinatorType _ _ _ prf)
          as [ k [ Ss [ WFSs leTau ] ] ].
        apply (CL_ST _ _ (intersect (map (fun S => Apply S ((nth contexts n) c)) Ss))).
        - generalize WFSs.
          clear WFSs.
          set (P := fun {k} (xs: t Substitution (S k)) =>
                      Forall WellFormed xs ->
                      CL (nth contexts n)
                         (Symbol c)
                         (intersect (map (fun S => Apply S (nth contexts n c)) xs))).
          fold (P k Ss).
          apply rectS; unfold P.
          + intros S WFSs.
            apply CL_Var.
            inversion WFSs; assumption.
          + intros S k' Ss'.
            apply (fun P H => caseS P H Ss').
            intros S' k'' Ss'' IH WFSs''.
            apply CL_II.
            * apply CL_Var.
              inversion WFSs''; assumption.
            * apply IH.
              inversion WFSs'' as [ | ? ? ? ? WFtl WFneq [ WFheq WFtleq ] ].
              dependent rewrite WFtleq in WFtl.
              assumption.
        - 
      
      Lemma combinatorTypesSound:
            forall n k c (sigmas : t IntersectionType k) tau,
              TypeOf n tau ->
              CL Gamma (Symbol c) (makeArrow sigmas tau) ->
              { sigmas': t IntersectionType k & CL (nth contexts n) (Symbol c) (makeArrow sigmas' tau) }.
      Proof.
        intros n k c sigmas.
        induction sigmas.
        - intros tau tauWF prf.
          exists (nil _).
          simpl in *.
          
          
    
    Definition WellFormedContext :=
      forall (Gamma : Context) c,
        { sigmas: t TypeScheme numberOfContexts
        | Gamma c = intersectSchemes sigmas }.

    

      

    
  End DisjointTypeSystem.  
End DisjointContexts.  
  
  

Module SomeDescriptiveName(Symbols: SymbolSpecification) <: CombinatoryLogic(Symbols).
  Include CombinatoryLogic(Symbols).



  Module Type DecidableTypeSystem <: TypeSystem.
    Include TypeSystem.

    

    Parameter CanInhabit:
      forall Gamma C tau,
        { possibleArgs : list (list IntersectionType) |
          forall M (prf: CL Gamma M tau), rootOf(M) = C ->
            exists args, List.In args possibleArgs ->
              (forall sigma,
                  Vector.In sigma (projT1 (MP_generation_iterated _ _ _ prf)) ->
                  exists tau, List.In tau args /\ sigma <= tau) /\
              (forall tau, List.In tau args ->
                 exists sigma,
                   Vector.In sigma (projT1 (MP_generation_iterated _ _ _ prf)) /\
                   sigma <= tau) }.

    (*
    Definition SubtypeStable (P: IntersectionType -> Prop) :=
      forall sigma tau, sigma <= tau -> P tau -> P sigma.

                                      
    Parameter WellFormedP:
      forall (P : IntersectionType -> Prop),
        SubtypeStable P -> (forall sigma, P sigma \/ ~(P sigma)) ->
        forall Gamma c, exists sigma,
            P sigma /\
            (CL Gamma (Symbol c) sigma) /\
            forall S, WellFormed S -> sigma <= Apply S (Gamma c).
    *)
                           
    
  

Module BoundedCombinatoryLogic(Symbols: SymbolSpecification) <: CombinatoryLogic(Symbols).
  Include CombinatoryLogic(Symbols).
  Fixpoint level (sigma: IntersectionType): nat :=
    match sigma with
    | Ty sigma' =>
      match sigma' with
      | PT_omega => 0
      | PT_Const _ sigmas => 1 + fold_left (fun s sigma => max s (level sigma)) 0 sigmas
      | PT_Arrow sigma tau => 1 + max (level sigma) (level tau)
      | PT_Inter sigma tau => max (level sigma) (level tau)
      end
    end.

  Definition Bounded (k: nat): Substitution -> Prop := fun S => forall alpha, le (level (S alpha)) k.
  Module Type KBounded.
    Parameter k: nat.    
  End KBounded.  
  Module Type BCL' :=
    KBounded <+ TypeSystem with Definition WellFormed := Bounded k.

  Module Type BCL <: BCL'.
    Include BCL'.
    Module Type SymbolsWithoutVariables <: ForbidVariablesIn(Symbols).
      Include ForbidVariablesIn(Symbols).
    End SymbolsWithoutVariables.
      
    Module Type FCL_Reduction(Symbols' : SymbolsWithoutVariables)
      <: FiniteCombinatoryLogic(Symbols').
      Include FiniteCombinatoryLogic(Symbols').
    End FCL_Reduction.
  End BCL.
End BoundedCombinatoryLogic.

