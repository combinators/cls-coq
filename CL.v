Require Import Coq.Classes.RelationClasses.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Vectors.Fin.
Require Import Coq.Vectors.Vector.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Logic.Eqdep_dec.
Require Import VectorQuantification.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Lists.ListDec.

Module Type SymbolSpecification.
  Parameter ConstructorSymbol: Set.
  Parameter constructorArity: ConstructorSymbol -> nat.
  Parameter ConstructorTaxonomy : ConstructorSymbol -> ConstructorSymbol -> Prop.
  Parameter CTPreorder : PreOrder ConstructorTaxonomy.

  Parameter VariableSymbol: Set.
  Parameter CombinatorSymbol: Set.

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
           
  Inductive TypeScheme {VariableSymbol: Set}: Set :=
  | Var: forall alpha: VariableSymbol, TypeScheme
  | Skeleton: forall skel: @PreType TypeScheme, TypeScheme.

  Fixpoint TypeScheme_rect'
           (VariableSymbol: Set)
           (P: @TypeScheme VariableSymbol -> Type)
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
                                   (TypeScheme_rect' _ P
                                                    var_case omega_case
                                                    const_case arrow_case
                                                    inter_case ty)
                                   (proof_args _ tys)
                     end) _ types)
    | Skeleton (PT_Arrow sigma tau) =>
      arrow_case _ _
                 (TypeScheme_rect' _ P var_case omega_case
                                  const_case arrow_case
                                  inter_case sigma)
                 (TypeScheme_rect' _ P var_case omega_case
                                  const_case arrow_case
                                  inter_case tau)
    | Skeleton (PT_Inter sigma tau) =>
      inter_case _ _
                 (TypeScheme_rect' _ P var_case omega_case
                                  const_case arrow_case
                                  inter_case sigma)
                 (TypeScheme_rect' _ P var_case omega_case
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

  Definition omegaScheme: @TypeScheme VariableSymbol := Skeleton PT_omega.
  Definition ConstScheme (C : ConstructorSymbol)
             (sigmas: t TypeScheme (constructorArity C)): @TypeScheme VariableSymbol :=
    Skeleton (PT_Const C sigmas).
  Definition ArrowScheme (sigma tau: TypeScheme): @TypeScheme VariableSymbol :=
    Skeleton (PT_Arrow sigma tau).
  Definition InterScheme (sigma tau: TypeScheme): @TypeScheme VariableSymbol:=
    Skeleton (PT_Inter sigma tau).

  Fixpoint unfreeze {VariableSymbol: Set} (sigma: IntersectionType): @TypeScheme VariableSymbol :=
    match sigma with
    | Ty (PT_omega) => Skeleton (PT_omega)
    | Ty (PT_Const c tys) => Skeleton (PT_Const c (map unfreeze tys))
    | Ty (PT_Arrow src tgt) => Skeleton (PT_Arrow (unfreeze src) (unfreeze tgt))
    | Ty (PT_Inter l r) => Skeleton (PT_Inter (unfreeze l) (unfreeze r))
    end.

  Fixpoint freeze (sigma: @TypeScheme False): IntersectionType :=
    match sigma with
    | Skeleton (PT_omega) => omega
    | Skeleton (PT_Const c tys) => Const c (map freeze tys)
    | Skeleton (PT_Arrow src tgt) => Arrow (freeze src) (freeze tgt)
    | Skeleton (PT_Inter l r) => Inter (freeze l) (freeze r)
    | Var alpha => False_rect _ alpha
    end.

  Lemma unfreezeFreeze: forall sigma, freeze (unfreeze sigma) = sigma.
  Proof.
    intro sigma.
    induction sigma
      as [ | c args IH | src tgt IHsrc IHtgt | l r IHl IHr ]
           using IntersectionType_rect'.
    - reflexivity.
    - simpl.
      rewrite <- map_fg.
      unfold Const.
      unfold liftPreType.
      apply f_equal.
      apply f_equal.
      revert args IH.
      generalize (constructorArity c).
      clear c.
      intros n args IH.
      induction IH as [ | ? ? ? prf prfs IH' ].
      + reflexivity.
      + simpl; rewrite prf; apply f_equal; assumption.
    - simpl; rewrite IHsrc; rewrite IHtgt; reflexivity.
    - simpl; rewrite IHl; rewrite IHr; reflexivity.
  Qed.

  Lemma freezeUnfreeze: forall sigma, unfreeze (freeze sigma) = sigma.
  Proof.
    intro sigma.
    induction sigma
      as [ | | c args IH | src tgt IHsrc IHtgt | l r IHl IHr ]
           using TypeScheme_rect'.
    - contradiction.
    - reflexivity.
    - simpl.
      rewrite <- map_fg.
      unfold Const.
      unfold liftPreType.
      apply f_equal.
      apply f_equal.
      revert args IH.
      generalize (constructorArity c).
      clear c.
      intros n args IH.
      induction IH as [ | ? ? ? prf prfs IH' ].
      + reflexivity.
      + simpl; rewrite prf; apply f_equal; assumption.
    - simpl; rewrite IHsrc; rewrite IHtgt; reflexivity.
    - simpl; rewrite IHl; rewrite IHr; reflexivity.
  Qed.

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
  Delimit Scope IntersectionTypes with intersection_types.
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
  where "sigma <= tau" := (Subtypes sigma tau) : intersection_types.
  Open Scope intersection_types.
  
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

  (*Lemma ST_organization_const {n: nat}:
    forall C C' (args args': t IntersectionType n)
      (eq: n = constructorArity C)
      (eq': n = constructorArity C'),
      (Const C (rew eq in args)) <= (Const C' (rew eq' in args')) ->
      Forall (fun tau' => Exists (fun sigma => Path sigma /\ sigma <= tau')
                              (projT2 (factorize (organize (Const C (rew eq in args))))))
             (projT2 (factorize (organize (Const C' (rew eq' in args'))))).
  Proof.*)
(*
  
  Definition InterFilter (sigma tau rho: IntersectionType): Prop :=
    Forall (fun rho_path => sigma <= rho_path \/ tau <= rho_path )
           (projT2 (factorize (organize rho))).
    
  Lemma IF_sound: forall sigma tau rho,
      InterFilter sigma tau rho -> Inter sigma tau <= rho.
  Proof.
    intros sigma tau rho IFsigmatau.
    unfold InterFilter in IFsigmatau.
    etransitivity; [ | apply ST_organize_le ].
    rewrite (factorize_organized _ (organize_organized _)).
    apply ST_intersect.
    induction IFsigmatau as [ | n rho' rhos [ sigma_le | tau_le ] _ IH ].
    - apply Forall_nil.
    - apply Forall_cons; [ | apply IH ].
      etransitivity; [ | apply sigma_le ].
      apply ST_InterMeetLeft.
    - apply Forall_cons; [ | apply IH ].
      etransitivity; [ | apply tau_le ].
      apply ST_InterMeetRight.
  Qed.

  Lemma IF_MeetLeft: forall sigma tau, InterFilter sigma tau sigma.
  Proof.
    intros sigma tau.
    unfold InterFilter.
    apply (Forall_ap _ (Subtypes (intersect (projT2 (factorize (organize sigma)))))).
    - apply Forall_tautology.
      intros; left.
      rewrite (ST_organize_ge).
      rewrite (factorize_organized _ (organize_organized _)).
      assumption.
    - apply (nth_Forall).
      apply (ST_intersect_nth).
  Qed.

  Lemma IF_MeetRight: forall sigma tau, InterFilter sigma tau tau.
  Proof.
    intros sigma tau.
    unfold InterFilter.
    apply (Forall_ap _ (Subtypes (intersect (projT2 (factorize (organize tau)))))).
    - apply Forall_tautology.
      intros; right.
      rewrite (ST_organize_ge).
      rewrite (factorize_organized _ (organize_organized _)).
      assumption.
    - apply (nth_Forall).
      apply (ST_intersect_nth).
  Qed.   
  
  Lemma IF_Refl: forall sigma tau, InterFilter sigma tau (Inter sigma tau).
  Proof.
    intros sigma tau.
    unfold InterFilter.
    simpl.
    rewrite (factorize_intersect_append _ _).
    apply Forall_append;
      rewrite <- (factorize_organized _ (organize_organized _)).
    - apply IF_MeetLeft.
    - apply IF_MeetRight.
  Qed.

  Lemma IF_Trans: forall sigma tau sigma' tau' rho,
      InterFilter sigma tau (Inter sigma' tau') ->
      InterFilter sigma' tau' rho ->
      InterFilter sigma tau rho.
  Proof.
    intros sigma tau sigma' tau' rho IFsigmatau.
    unfold InterFilter in *.
    simpl in IFsigmatau.
    rewrite (factorize_intersect_append) in IFsigmatau.
    simpl in IFsigmatau.
    generalize (append_Forall1 _ _ _ IFsigmatau).
    rewrite <- (factorize_organized _ (organize_organized _)).
    intro IF_sigma'.
    generalize (append_Forall2 _ _ _ IFsigmatau).
    rewrite <- (factorize_organized _ (organize_organized _)).
    intro IF_tau'.
    intro IFsigma'tau'.
    induction IFsigma'tau' as [ | ? ? ? hd_prf tl_prf ].
    - apply Forall_nil.
    - apply Forall_cons; [ | assumption ].
      inversion hd_prf.
      + set (sigma'_ge := IF_sound _ _ _  IF_sigma').
        
    
    remember (Inter sigma' tau') as sigma'tau' eqn:sigma'tau'_eq.
    revert sigma' tau' sigma'tau'_eq.
    induction IFsigmatau;
      intros sigma' tau' sigma'tau'_eq IFsigma'tau'.
    - 
    

  Lemma IF_complete: forall sigma tau rho,
      Inter sigma tau <= rho -> InterFilter sigma tau rho.
  Proof.
    intros sigma tau rho rho_ge.
    remember (Inter sigma tau) as lhs eqn:lhs_eq.
    revert lhs_eq.
    revert sigma tau.
    induction rho_ge;
      intros sigma' tau' lhs_eq;
      try solve [ inversion lhs_eq ].
    - inversion lhs_eq.
      apply IF_MeetLeft.
    - inversion lhs_eq.
      apply IF_MeetRight.
    - inversion lhs_eq.
      unfold InterFilter.
      simpl.
      rewrite (factorize_intersect_append).
      rewrite (factorize_intersect_append).
      rewrite <- (factorize_organized _ (organize_organized _)).
      rewrite <- (factorize_organized _ (organize_organized _)).
      apply Forall_append; apply IF_Refl.
    - admit.
    - admit.
    - admit.
    - apply Forall_nil.
    - 
 *)
  (*
  Lemma ST_either:
    forall sigma tau rho,
      Inter sigma tau <= rho -> Path rho -> sigma <= rho \/ tau <= rho.
  Proof.
    intros sigma tau rho rho_ge.
    remember (Inter sigma tau) as lhs eqn:lhs_eq.
    revert sigma tau lhs_eq.
    induction rho_ge;
      intros sigma' tau' lhs_eq;
      inversion lhs_eq.
    - intros; left; reflexivity.
    - intros; right; reflexivity.
    - intro path_rho; inversion path_rho.
    - intro path_rho.
      inversion path_rho as [ | ? ? path_rho' ].
      inversion path_rho'.
    - intro path_rho.
      inversion path_rho as [ ? ? path_args [ C_eq args_eq ] | ].
      dependent rewrite args_eq in path_args.
      destruct (Nat.eq_dec (constructorArity C) 0) as [ no_args | some_args ].
      + assert (sigmas_eq: sigmas = rew <- no_args in nil _).
        { clear ...
          revert sigmas.
          rewrite no_args.
          intro sigmas.
          unfold eq_rect_r.
          simpl.
          apply (fun r => case0 (fun xs => xs = _) r sigmas).
          reflexivity. }
        assert (taus_eq: taus = rew <- no_args in nil _).
        { clear ...
          revert taus.
          rewrite no_args.
          intro taus.
          unfold eq_rect_r.
          simpl.
          apply (fun r => case0 (fun xs => xs = _) r taus).
          reflexivity. }
        rewrite sigmas_eq.
        rewrite taus_eq.
        clear ...
        left.
        apply (ST_Ax _ _ eq_refl).
        * reflexivity.
        * unfold eq_rect_r.
          simpl.
          rewrite (rewrite_vect (fun n x => Forall2 Subtypes x (map2 Inter x x)) (eq_sym no_args)).
          apply Forall2_nil.
      + contradict path_args.
        unfold not.
        revert some_args.
        clear ...
        induction sigmas.
        * intro devil.
          contradict (devil eq_refl).
        * apply (caseS' taus).
          clear taus; intros tau' taus.
          intros _ path_args.
          simpl in path_args.
          inversion path_args as [ | ? ? path_inter | ].
          inversion path_inter.
    - intro path_inter; inversion path_inter.
    - intro path_omega; inversion path_omega.
    - 
          
    
   *)

  Inductive ArrowIdeal src tgt: IntersectionType -> Prop :=
  | AI_Omega: forall sigma, Omega tgt -> ArrowIdeal src tgt sigma
  | AI_CoContra: forall src' tgt', src <= src' -> tgt' <= tgt -> ArrowIdeal src tgt (Arrow src' tgt')
  | AI_InterLeft: forall sigma tau, ArrowIdeal src tgt sigma -> ArrowIdeal src tgt (Inter sigma tau)
  | AI_InterRight: forall sigma tau, ArrowIdeal src tgt tau -> ArrowIdeal src tgt (Inter sigma tau)
  | AI_Inter: forall sigma tau tgt1 tgt2,
      ArrowIdeal src tgt1 sigma -> ArrowIdeal src tgt2 tau -> Inter tgt1 tgt2 <= tgt ->
      ArrowIdeal src tgt (Inter sigma tau).

  Lemma AI_sound: forall src tgt sigma,
      ArrowIdeal src tgt sigma -> sigma <= Arrow src tgt.
  Proof.
    intros src tgt sigma AI_sigma.
    induction AI_sigma
      as [ |
           | ? ? ? ? IH
           | ? ? ? ? IH
           | sigmatau sigma tau tgt1 tgt2 AI_srctgt1 IH1 AI_srctgt2 IH2 IHsigmatau ].
    - transitivity omega; [ apply ST_OmegaTop | ].
      transitivity (Arrow src omega).
      + transitivity (Arrow omega omega); [ apply ST_OmegaArrow | ].
        apply ST_CoContra; [ apply ST_OmegaTop | reflexivity ].
      + apply ST_CoContra; [ reflexivity | ].
        apply Omega_sound.
        assumption.
    - apply ST_CoContra; assumption.
    - rewrite <- IH; apply ST_InterMeetLeft.
    - rewrite <- IH; apply ST_InterMeetRight.
    - transitivity (Arrow src (Inter tgt1 tgt2)).
      + transitivity (Inter (Arrow src tgt1) (Arrow src tgt2)).
        * apply ST_Both.
          { rewrite <- IH1; apply ST_InterMeetLeft. }
          { rewrite <- IH2; apply ST_InterMeetRight. }
        * apply ST_InterArrowDistrib.
      + apply ST_CoContra; [ reflexivity | assumption ].
  Qed.

  Lemma AI_weaken: forall src tgt tgt' sigma,
      tgt <= tgt' -> ArrowIdeal src tgt sigma -> ArrowIdeal src tgt' sigma.
  Proof.
    intros src tgt tgt' sigma tgt_le AI_srctgt.
    induction AI_srctgt.
    - apply AI_Omega.
      apply (Omega_complete _ _ tgt_le).
      assumption.
    - apply AI_CoContra.
      + assumption.
      + rewrite <- tgt_le; assumption.
    - apply AI_InterLeft; auto.
    - apply AI_InterRight; auto.
    - eapply AI_Inter.
      + eassumption.
      + eassumption.
      + rewrite <- tgt_le; assumption.
  Qed.

  Lemma AI_commutative:
    forall sigma tau1 tau2 rho,
      ArrowIdeal sigma (Inter tau1 tau2) rho -> ArrowIdeal sigma (Inter tau2 tau1) rho.
  Proof.
    intros.
    eapply AI_weaken; [ | eassumption ].
    apply (ST_Both); [ apply ST_InterMeetRight | apply ST_InterMeetLeft ].
  Qed.

  Lemma AI_merge:
    forall sigma tau1 tau2 rho1 rho2,
      ArrowIdeal sigma tau1 rho1 -> ArrowIdeal sigma tau2 rho2 ->
      ArrowIdeal sigma (Inter tau1 tau2) (Inter rho1 rho2).
  Proof.
    intros.
    eapply AI_weaken; [ reflexivity | ].
    eapply AI_Inter.
    - eassumption.
    - eassumption.
    - reflexivity.
  Qed.

  Lemma AI_InterOmega_left:
    forall sigma tau tau' rho, Omega tau -> ArrowIdeal sigma tau' rho -> ArrowIdeal sigma (Inter tau tau') rho.
  Proof.
    intros.
    eapply AI_weaken; [ | eassumption ].
    apply ST_Both; [ | reflexivity ].
    transitivity omega; [ apply ST_OmegaTop | ].
    apply Omega_sound; assumption.
  Qed.

  Lemma AI_InterOmega_right:
    forall sigma tau tau' rho,
      Omega tau -> ArrowIdeal sigma tau' rho -> ArrowIdeal sigma (Inter tau' tau) rho.
  Proof.
    intros.
    apply AI_commutative.
    apply AI_InterOmega_left; assumption.
  Qed.

  Lemma AI_both:
    forall tau rho1 rho2 sigma,
      ArrowIdeal sigma rho1 tau -> ArrowIdeal sigma rho2 tau -> ArrowIdeal sigma (Inter rho1 rho2) tau.
  Proof.
    intro tau.
    induction tau using IntersectionType_rect';
      intros ? ? ? AI_rho1 AI_rho2;
      inversion AI_rho1;
      inversion AI_rho2;
      try solve [ apply AI_InterOmega_left; assumption
                | apply AI_InterOmega_right; assumption ].
    - apply AI_CoContra; [ assumption | apply ST_Both; assumption ].
    - apply AI_InterLeft; auto.
    - eapply AI_merge; assumption.
    - eapply AI_weaken.
      + eapply ST_Both.
        * etransitivity; [ apply ST_InterMeetLeft | apply ST_InterMeetLeft ].
        * rewrite ST_ReassocLeft.
          etransitivity; [ apply ST_InterMeetRight | eassumption ].
      + eapply AI_merge; auto.
    - apply AI_commutative.
      eapply AI_merge; auto.
    - apply AI_InterRight; auto.
    - apply AI_commutative.
      eapply AI_weaken.
      + eapply ST_Both.
        * etransitivity; [ apply ST_ReassocRight | ].
          rewrite ST_InterMeetLeft.
          eassumption.
        * rewrite ST_InterMeetRight.
          apply ST_InterMeetRight.
      + eapply AI_merge; auto.
    - apply AI_commutative.
      eapply AI_weaken.
      + eapply ST_Both.
        * etransitivity; [ apply ST_ReassocLeft | ].
          apply ST_InterMeetLeft.
        * rewrite ST_ReassocLeft.
          etransitivity; [ apply ST_InterMeetRight | ].
          eassumption.
      + eapply AI_merge; auto.
    - eapply AI_weaken.
      + eapply ST_Both.
        * etransitivity; [ apply ST_ReassocRight | ].
          rewrite ST_InterMeetLeft.
          eassumption.
        * rewrite (ST_ReassocRight).
          apply ST_InterMeetRight.
      + eapply AI_merge; auto.
    - eapply AI_weaken.
      + eapply ST_Both.
        * etransitivity; [ apply ST_SubtypeDistrib; [ apply ST_InterMeetLeft
                                                    | apply ST_InterMeetRight ]
                         | eassumption ].
        * etransitivity; [ apply ST_SubtypeDistrib; [ apply ST_InterMeetRight
                                                    | apply ST_InterMeetLeft ]
                         | eassumption ].
      + eapply AI_merge; auto.
  Qed.
  
  Lemma AI_Trans: forall src tgt sigma tau,
      tau <= sigma -> ArrowIdeal src tgt sigma -> ArrowIdeal src tgt tau.
  Proof.
    intros src tgt sigma tau tau_le.
    revert src tgt.
    induction tau_le.
    - intros ? ? AI_C; inversion AI_C; apply AI_Omega; assumption.
    - intros; apply AI_InterLeft; assumption.
    - intros; apply AI_InterRight; assumption.
    - intros src tgt AI_Both.
      inversion AI_Both as  [ | | | | ? ? tgt1 tgt2 AI_srctgt1 AI_srctgt2 tgt_ge [ sigma_eq tau_eq ]].
      + apply AI_Omega; assumption.
      + assumption.
      + assumption.
      + eapply AI_weaken; [ eassumption | apply AI_both ]; assumption.
    - intros ? ? AI_sigmaInter.
      inversion AI_sigmaInter.
      + apply AI_Omega; assumption.
      + eapply AI_Inter.
        * apply AI_CoContra; [ assumption | reflexivity ].
        * apply AI_CoContra; [ assumption | reflexivity ].
        * assumption.
    - intros ? ? AI_C; inversion AI_C; apply AI_Omega; assumption.
    - intros ? ? AI_Both.
      inversion AI_Both.
      + apply AI_Omega; assumption.
      + apply AI_InterLeft; auto.
      + apply AI_InterRight; auto.
      + eapply AI_weaken; [ eassumption | ].
        eapply AI_Inter; [ eauto | eauto | reflexivity ].
    - intros ? ? AI_Arrow.
      inversion AI_Arrow.
      + apply AI_Omega; assumption.
      + apply AI_CoContra; etransitivity; eassumption.
    - intros ? ? AI_omega.
      inversion AI_omega.
      apply AI_Omega; assumption.
    - intros ? ? AI_omegaomega.
      inversion AI_omegaomega.
      + apply AI_Omega; assumption.
      + apply AI_Omega.
        eapply Omega_complete; [ eassumption | exact I ].
    - intros ? ? AI_rho.
      eauto.
  Qed.

  Lemma AI_Refl: forall src tgt, ArrowIdeal src tgt (Arrow src tgt).
  Proof.
    intros.
    apply AI_CoContra; reflexivity.
  Qed.   
        
  Lemma AI_complete: forall src tgt sigma,
      sigma <= Arrow src tgt -> ArrowIdeal src tgt sigma.
  Proof.
    intros src tgt sigma sigma_le.
    remember (Arrow src tgt) as rhs eqn:rhs_eq.
    revert src tgt rhs_eq.
    induction sigma_le;
      intros src tgt rhs_eq;
      try solve [ inversion rhs_eq ].
    - rewrite rhs_eq.
      apply AI_InterLeft.
      apply AI_Refl.
    - rewrite rhs_eq.
      apply AI_InterRight.
      apply AI_Refl.
    - inversion rhs_eq.
      eapply AI_Inter; [ | | reflexivity ]; apply AI_Refl.
    - inversion rhs_eq as [ [ src_eq tgt_eq ] ].
      rewrite <- src_eq.
      rewrite <- tgt_eq.
      apply AI_CoContra; assumption.
    - apply AI_Omega.
      inversion rhs_eq.
      exact I.
    - eapply AI_Trans; eauto.
  Qed.

  Inductive ConstIdeal C (args : t IntersectionType (constructorArity C)): IntersectionType -> Prop :=
  | CI_Const: forall C' (args': t IntersectionType (constructorArity C')) arity_eq,
      ConstructorTaxonomy C' C ->
      Forall2 Subtypes args' (rew <- arity_eq in args) ->
      ConstIdeal C args (Const C' args')
  | CI_InterLeft : forall sigma tau, ConstIdeal C args sigma -> ConstIdeal C args (Inter sigma tau)
  | CI_InterRight : forall sigma tau, ConstIdeal C args tau -> ConstIdeal C args (Inter sigma tau)
  | CI_Distrib: forall args1 args2 sigma tau,
      ConstIdeal C args1 sigma ->
      ConstIdeal C args2 tau ->
      Forall2 Subtypes (map2 Inter args1 args2) args ->
      ConstIdeal C args (Inter sigma tau).

  Lemma CI_sound: forall C args sigma, ConstIdeal C args sigma -> sigma <= Const C args.
  Proof.
    intros C args sigma CI_sigma.
    induction CI_sigma.
    - eapply ST_Ax; eassumption.
    - rewrite ST_InterMeetLeft; assumption.
    - rewrite ST_InterMeetRight; assumption.
    - etransitivity.
      + apply ST_Both;
          [ rewrite ST_InterMeetLeft | rewrite ST_InterMeetRight ];
          eassumption.
      + rewrite ST_InterConstDistrib.
        eapply (ST_Ax _ _ eq_refl); [ reflexivity | ].
        unfold eq_rect_r; simpl.
        assumption.
  Qed.

  Lemma CI_Refl: forall C args, ConstIdeal C args (Const C args).
  Proof.
    intros.
    eapply (CI_Const _ _ _ _ (eq_refl _)); [ reflexivity | ].
    apply nth_Forall2.
    intros; reflexivity.
  Qed.

  Lemma CI_weaken: forall C C' args args' sigma arity_eq,
      ConstIdeal C args sigma ->
      ConstructorTaxonomy C C' ->
      Forall2 Subtypes args (rew arity_eq in args') ->
      ConstIdeal C' args' sigma.
  Proof.
    intros C C' args args' sigma arity_eq CI_C.
    revert C' args' arity_eq.
    induction CI_C
      as [ ? ? ? arity_eq' | | | ? args1 args2 sigma tau CI_sigma IH_sigma CI_tau IH_tau ];
      intros C_tgt args_tgt arity_eq.
    - intros.
      eapply (CI_Const _ _ _ _ (eq_trans arity_eq' (eq_sym arity_eq))).
      + etransitivity; eassumption.
      + apply nth_Forall2.
        intro k.
        etransitivity.
        * eapply Forall2_nth; eassumption.
        * assert (rew_eq : (rew <- eq_trans arity_eq' (eq_sym arity_eq) in args_tgt) =
                  rew <- arity_eq' in rew arity_eq in args_tgt).
          { rewrite arity_eq'.
            unfold eq_rect_r.
            simpl.
            assert (eq_eq: eq_sym (eq_trans eq_refl (eq_sym arity_eq)) = arity_eq).
            { apply (UIP_dec (Nat.eq_dec)). }
            rewrite eq_eq.
            reflexivity. }
          rewrite rew_eq.
          unfold eq_rect_r.
          rewrite (nth_k (eq_sym arity_eq')).
          rewrite (nth_k (eq_sym arity_eq')).
          apply Forall2_nth.
          assumption.
    - intros; apply CI_InterLeft; eauto.
    - intros; apply CI_InterRight; eauto.
    - intros; eapply CI_Distrib.
      + eapply (IH_sigma _ (rew <- arity_eq in args1)); [ assumption | ].
        apply nth_Forall2.
        intro.
        rewrite (rew_opp_r).
        reflexivity.
      + eapply (IH_tau _ (rew <- arity_eq in args2)); [ assumption | ].
        apply nth_Forall2.
        intro.
        rewrite (rew_opp_r).
        reflexivity.
      + apply nth_Forall2.
        intro.
        assert (map2_rew_distrib : map2 Inter (rew <- arity_eq in args1) (rew <- arity_eq in args2) =
                                   rew <- arity_eq in map2 Inter args1 args2).
        { rewrite arity_eq.
          reflexivity. }
        rewrite map2_rew_distrib.
        unfold eq_rect_r.
        rewrite (nth_k (eq_sym arity_eq)).
        etransitivity; [ eapply (Forall2_nth); eassumption | ].
        etransitivity; [ eapply Forall2_nth; eassumption | ].
        rewrite (nth_k arity_eq).
        unfold eq_rect_r at 1.
        rewrite (rew_opp_r).
        reflexivity.
  Qed.

  Lemma CI_both: forall C args1 args2 sigma,
      ConstIdeal C args1 sigma -> ConstIdeal C args2 sigma -> ConstIdeal C (map2 Inter args1 args2) sigma.
  Proof.
    intros C args1 args2 sigma.    
    revert C args1 args2.
    induction sigma as [ | C args | | l r IHl IHr ] using IntersectionType_rect';
      intros C' args1 args2 CI_args1 CI_args2;
      try solve [ inversion CI_args1; inversion CI_args2 ];
      inversion CI_args1
        as [ C1 args1' arity_eq ? ? [ sigma_eq args1'_eq ]
           | ? ? ? sigma_eq
           | ? ? ? sigma_eq
           | args0 args3 ? ? ? ? sigma_eq ];
      inversion CI_args2
        as [ C2 args2' arity_eq' ? ? [ sigma_eq' args2'_eq ]
           | ? ? ? sigma_eq'
           | ? ? ? sigma_eq'
           | ? ? ? ? ? ? ? sigma_eq' ];
      try solve [ rewrite <- sigma_eq in sigma_eq'; inversion sigma_eq' ].
    - eapply CI_Const; [ eassumption | ].
      apply nth_Forall2.
      intro.
      unfold eq_rect_r in *.
      rewrite (nth_k (eq_sym arity_eq)).
      rewrite (nth_map2 _ _ _ _ _ _ eq_refl eq_refl).
      apply ST_Both;
        rewrite <- (nth_k (eq_sym arity_eq));
        apply Forall2_nth.
      + assert (args1'_eq' : args = args1').
        { apply (vect_exist_eq).
          apply (existT_fg_eq _ constructorArity).
          apply eq_sym.
          assumption. }
        rewrite args1'_eq'.
        assumption.
      + assert (args2'_eq' : args = args2').
        { apply (vect_exist_eq).
          apply (existT_fg_eq _ constructorArity).
          apply eq_sym.
          assumption. }
        rewrite args2'_eq'.
        rewrite (UIP_dec (Nat.eq_dec) _ arity_eq').
        assumption.
    - apply CI_InterLeft; auto.
    - eapply CI_Distrib; [ eassumption | eassumption | ].
      apply nth_Forall2; intro; reflexivity.
    - (* (args1 args0) args3 *)
      eapply (CI_weaken _ _ _ _ _ eq_refl); [ | reflexivity | ].
      + eapply CI_Distrib.
        * apply (IHl _ args1 args0); eassumption.
        * eassumption.
        * eapply nth_Forall2; intro; reflexivity.
      + apply nth_Forall2.
        intro.
        simpl.
        repeat rewrite (nth_map2 _ _ _ _ _ _ eq_refl eq_refl).
        rewrite ST_ReassocLeft.
        apply ST_Both; [ apply ST_InterMeetLeft | rewrite ST_InterMeetRight  ].
        rewrite <- (nth_map2 _ _ _ _ _ _ eq_refl eq_refl).
        apply Forall2_nth.
        assumption.
    - eapply CI_Distrib; [ eassumption | eassumption | ].
      apply nth_Forall2; intro.
      repeat rewrite (nth_map2 _ _ _ _ _ _ eq_refl eq_refl).
      apply ST_Both; [ apply ST_InterMeetRight | apply ST_InterMeetLeft ].
    - apply CI_InterRight; eauto.
    - (* args0 (args1 args3) *)
      eapply (CI_weaken _ _ _ _ _ eq_refl); [ | reflexivity | ].
      + eapply CI_Distrib.
        * eassumption.
        * eapply (IHr _ args1 _); eassumption.
        * eapply nth_Forall2; intro; reflexivity.
      + apply nth_Forall2.
        intro.
        simpl.
        repeat rewrite (nth_map2 _ _ _ _ _ _ eq_refl eq_refl).
        rewrite ST_ReassocRight.
        etransitivity.
        * apply ST_Both;
            [ rewrite ST_InterMeetLeft;
              apply ST_Both; [ apply ST_InterMeetRight | apply ST_InterMeetLeft ]
            | apply ST_InterMeetRight ].
        * rewrite ST_ReassocLeft.
          apply ST_Both; [ apply ST_InterMeetLeft | rewrite ST_InterMeetRight ].
          rewrite <- (nth_map2 _ _ _ _ _ _ eq_refl eq_refl).
          apply Forall2_nth.
          assumption.
    - (* (args0 args2) args3 *)
      eapply (CI_weaken _ _ _ _ _ eq_refl); [ | reflexivity | ].
      + eapply CI_Distrib.
        * eapply (IHl _ args0 _); eassumption.
        * eassumption.
        * eapply nth_Forall2; intro; reflexivity.
      + apply nth_Forall2.
        intro.
        simpl.
        repeat rewrite (nth_map2 _ _ _ _ _ _ eq_refl eq_refl).
        rewrite ST_ReassocLeft.
        etransitivity.
        * apply ST_Both;
            [ apply ST_InterMeetLeft
            | rewrite ST_InterMeetRight;
              apply ST_Both; [ apply ST_InterMeetRight | apply ST_InterMeetLeft ] ].
        * rewrite ST_ReassocRight.
          apply ST_Both; [ rewrite ST_InterMeetLeft | apply ST_InterMeetRight ].
          rewrite <- (nth_map2 _ _ _ _ _ _ eq_refl eq_refl).
          apply Forall2_nth.
          assumption.
    - (* args0 (args3 args2) *)
      eapply (CI_weaken _ _ _ _ _ eq_refl); [ | reflexivity | ].
      + eapply CI_Distrib.
        * eassumption.
        * eapply (IHr _ args3 _); eassumption.
        * eapply nth_Forall2; intro; reflexivity.
      + apply nth_Forall2.
        intro.
        simpl.
        repeat rewrite (nth_map2 _ _ _ _ _ _ eq_refl eq_refl).
        rewrite ST_ReassocRight.
        apply ST_Both; [ rewrite ST_InterMeetLeft | apply ST_InterMeetRight ].
        rewrite <- (nth_map2 _ _ _ _ _ _ eq_refl eq_refl).
        apply Forall2_nth.
        assumption.
    - (* (args0 args4) (args3 args5) *)
      eapply (CI_weaken _ _ _ _ _ eq_refl); [ | reflexivity | ].
      + eapply CI_Distrib.
        * eapply (IHl _ args0 _); eassumption.
        * eapply (IHr _ args3 _); eassumption.
        * eapply nth_Forall2; intro; reflexivity.
      + apply nth_Forall2.
        intro.
        simpl.
        repeat rewrite (nth_map2 _ _ _ _ _ _ eq_refl eq_refl).
        etransitivity.
        * apply ST_Both;
            [ apply ST_Both; [ rewrite ST_InterMeetLeft; apply ST_InterMeetLeft
                             | rewrite ST_InterMeetRight; apply ST_InterMeetLeft ]
            | apply ST_Both; [ rewrite ST_InterMeetLeft; apply ST_InterMeetRight
                             | rewrite ST_InterMeetRight; apply ST_InterMeetRight ] ].
        * apply ST_Both; [ rewrite ST_InterMeetLeft | rewrite ST_InterMeetRight ];
            rewrite <- (nth_map2 _ _ _ _ _ _ eq_refl eq_refl);
            apply Forall2_nth;
            assumption.
  Qed.
  
  Lemma CI_Trans: forall C args sigma tau, sigma <= tau -> ConstIdeal C args tau -> ConstIdeal C args sigma.
  Proof.
    intros C args sigma tau sigma_le.
    revert C args.
    induction sigma_le as [ C ? arity_eq | | | | | ? l r | |  | | | ].
    - intros ? ? CI_sigma.
      inversion CI_sigma as [ C' ? arity_eq' ? args_le [ C_eq args_eq ]  | | | ].
      + eapply CI_Const.
        * etransitivity; eassumption.
        * apply nth_Forall2; intro k.
          etransitivity.
          { eapply Forall2_nth; eassumption. }
          { generalize (existT_fg_eq (t IntersectionType) (constructorArity) _ _ _ args_eq).
            intro args_eq'.
            generalize (vect_exist_eq _ _ args_eq').
            intro args_eq''.
            rewrite <- args_eq''.
            assert (args_le' : Forall2 Subtypes (rew <- arity_eq in args') (rew <- (eq_trans arity_eq arity_eq') in args)).
            { revert args_le.
              clear ...
              rewrite arity_eq.
              unfold eq_rect_r.
              simpl.
              intro.
              assert (eq_eq : eq_trans eq_refl arity_eq' = arity_eq').
              { apply (UIP_dec (Nat.eq_dec)). }
              rewrite eq_eq.
              assumption. }
            apply Forall2_nth.
            eassumption. }
    - intros; apply CI_InterLeft; assumption.
    - intros; apply CI_InterRight; assumption.
    - intros ? ? CI_sigma.
      inversion CI_sigma (*as [ | | | ? ? ? CI_sigma' [ sigma_eq Cargs_eq ] ].*).
      + assumption.
      + assumption.
      + eapply (CI_weaken _ _ _ _ _ eq_refl); [ | reflexivity | simpl; eassumption ].
        apply CI_both; assumption.
    - intros ? ? CI_arrow; inversion CI_arrow.
    - intros ? ? CI_Both.
      inversion CI_Both as [ ? args' ? ? ? [ C_eq args_eq ] | | | ].
      eapply CI_Distrib.
      + eapply (CI_Const _ _ _ _ arity_eq).
        * assumption.
        * rewrite (rew_opp_l).
          apply nth_Forall2; intro.
          reflexivity.
      + eapply (CI_Const _ _ _ _ arity_eq).
        * assumption.
        * rewrite (rew_opp_l).
          apply nth_Forall2; intro.
          reflexivity.
      + apply nth_Forall2; intro.
        assert (rew_eq : (map2 Inter (rew arity_eq in l) (rew arity_eq in r)) =
                         rew arity_eq in map2 Inter l r).
        { rewrite <- arity_eq; simpl; reflexivity. }
        rewrite rew_eq.
        rewrite <- (nth_eq args (eq_sym arity_eq)).
        rewrite (nth_k arity_eq).
        assert (rew_eq' : map2 Inter l r = args').
        { apply (vect_exist_eq).
          apply (existT_fg_eq _ constructorArity).
          apply eq_sym.
          assumption. }
        rewrite rew_eq'.
        apply Forall2_nth.
        assumption.
    - intros C args CI_inter.
      inversion CI_inter .
      + apply CI_InterLeft; auto.
      + apply CI_InterRight; auto.
      + eapply CI_Distrib; [ eauto | eauto | assumption ].
    - intros ? ? CI_arrow; inversion CI_arrow.
    - intros ? ? CI_omega; inversion CI_omega.
    - intros ? ? CI_arrow; inversion CI_arrow.
    - eauto.
  Qed.      

  Lemma CI_complete: forall C args sigma,
      sigma <= Const C args -> ConstIdeal C args sigma.
  Proof.
    intros C args sigma sigma_le.
    remember (Const C args) as rhs eqn:rhs_eq.
    revert C args rhs_eq.
    induction sigma_le;
      intros ? ? rhs_eq; try solve [ inversion rhs_eq ].
    - inversion rhs_eq as [ [ C_eq args_eq ] ].
      eapply CI_Const; eassumption.
    - apply CI_InterLeft; rewrite rhs_eq; apply CI_Refl.
    - apply CI_InterRight; rewrite rhs_eq; apply CI_Refl.
    - inversion rhs_eq.
      eapply CI_Distrib;
        [ | | apply nth_Forall2; intro; reflexivity ];
        apply CI_Refl.
    - eapply CI_Trans; [ eassumption | eauto ].
  Qed.

  Fixpoint Ideal (sigma: IntersectionType): IntersectionType -> Prop :=
    match sigma with
    | Ty (PT_omega) => fun tau => True
    | Ty (PT_Const C args) => ConstIdeal C args
    | Ty (PT_Arrow src tgt) => ArrowIdeal src tgt
    | Ty (PT_Inter sigma tau) => fun rho => Ideal sigma rho /\ Ideal tau rho
    end.

  Lemma Ideal_sound: forall sigma tau, Ideal sigma tau -> tau <= sigma.
  Proof.
    intro sigma.
    induction sigma using IntersectionType_rect'.
    - intros; apply ST_OmegaTop.
    - intros; apply CI_sound; assumption.
    - intros; apply AI_sound; assumption.
    - intros ? I_lr; destruct I_lr; apply ST_Both; auto.
  Qed.

  Lemma Ideal_complete: forall sigma tau, tau <= sigma -> Ideal sigma tau.
  Proof.
    intro sigma.
    induction sigma as [ | | | l r ] using IntersectionType_rect'.
    - intros; exact I.
    - intro; apply CI_complete.
    - intro; apply AI_complete.
    - intros tau tau_le; split.
      + assert (tau <= l).
        { etransitivity; [ eassumption | apply ST_InterMeetLeft ]. }
        auto.
      + assert (tau <= r).
        { etransitivity; [ eassumption | apply ST_InterMeetRight ]. }
        auto.
  Qed.

  Lemma Prime_Ideal_Omega:
    forall tau1 tau2, Ideal omega (Inter tau1 tau2) -> Ideal omega tau1 \/ Ideal omega tau2.
  Proof.
    intros; left; exact I.
  Qed.

  Lemma Prime_Ideal_Path:
    forall sigma, Path sigma ->
             forall tau1 tau2, Ideal sigma (Inter tau1 tau2) ->
                          Ideal sigma tau1 \/ Ideal sigma tau2.
  Proof.
    intros sigma.
    induction sigma as [ | C args IHargs | src tgt _ IHtgt | ] using IntersectionType_rect';
      intro path_sigma; try solve [ inversion path_sigma ].
    - inversion path_sigma as [ C' args' path_args [ C_eq args_eq ] | ].
      dependent rewrite args_eq in path_args.
      clear C_eq args_eq args' C'.
      assert (args_choice:
          forall args1 args2,
            Forall2 Subtypes (map2 Inter args1 args2) args ->
            Forall2 Ideal args args1 \/ Forall2 Ideal args args2). 
      { clear path_sigma.
        revert args IHargs path_args.
        generalize (constructorArity C).
        clear C.
        intros n args IHargs path_args.
        induction IHargs as [ | arg n args prf prfs IH ].
        - intros.
          left.
          apply case0.
          apply Forall2_nil.
        - intros args1 args2.
          apply (caseS' args1); clear args1; intros arg1 args1.
          apply (caseS' args2); clear args2; intros arg2 args2.
          intro args_le.
          assert (Ideal arg (Inter arg1 arg2)).
          { inversion args_le.
            apply Ideal_complete; assumption. }          
          inversion path_args
            as [
               | ? ? ? n_eq [ arg_eq args_eq ]
               | ? ? path_args' n_eq [ arg_eq args_eq ] ].
          + assert (arg_choice: Ideal arg arg1 \/ Ideal arg arg2).
            { auto. }
            inversion arg_choice as [ choice_arg1 | choice_arg2 ];
              [ left | right ];
              solve [
                  apply Forall2_cons; [ assumption | ];
                  rewrite <- (vect_exist_eq _ _ args_eq);
                  apply nth_Forall2; intro;
                  rewrite (const_nth); exact I ].
          + dependent rewrite args_eq in path_args'.
            inversion args_le
              as [ | ? ? ? ? ? arg_le args_le' n'_eq [ hd_eq tl_eq ] [ arg_eq' args_eq' ] ].
            rewrite (vect_exist_eq _ _ args_eq') in args_le'.
            rewrite (vect_exist_eq _ _ tl_eq) in args_le'.
            assert (args_choice : Forall2 Ideal args args1 \/ Forall2 Ideal args args2).
            { auto. }
            inversion args_choice as [ choice_arg1 | choice_arg2 ];
              [ left | right ];
              solve [ apply Forall2_cons; [ exact I | assumption ] ]. }
      intros tau1 tau2 CI_tau1tau2.
      inversion CI_tau1tau2 as [ | | | ? ? ? ? CI_tau1 CI_tau2 args_le ].
      + left; assumption.
      + right; assumption.
      + destruct (args_choice _ _ args_le); [ left | right ];
          solve [
              eapply (CI_weaken _ _ _ _ _ eq_refl); [ eassumption | reflexivity | ];
              apply (nth_Forall2); intro;
              apply Ideal_sound;
              apply (Forall2_nth);
              assumption ].
    - intros tau1 tau2 AI_tau1tau2.
      inversion AI_tau1tau2 as [ | | | | ? ? ? ? AItau1 AItau2 ].
      + inversion path_sigma.
        assert False.
        { eapply Omega_path; eassumption. }
        contradiction.
      + left; assumption.
      + right; assumption.
      + inversion path_sigma.
        assert (tgt_choice: Ideal tgt tgt1 \/ Ideal tgt tgt2).
        { apply IHtgt; [ assumption | ].
          apply Ideal_complete; assumption. }
        destruct (tgt_choice);
          [ left | right ];
          solve [ eapply AI_weaken; [ | eassumption ];
                  apply Ideal_sound; assumption ].
  Qed.   
  
  Lemma ST_organization: forall sigma tau,
      sigma <= tau ->
      Forall (fun tau' => Exists (fun sigma => Path sigma /\ sigma <= tau')
                              (projT2 (factorize (organize sigma))))
             (projT2 (factorize (organize tau))).
  Proof.
    intros sigma tau sigma_le.
    assert (org_sigma_le: organize sigma <= organize tau).
    { rewrite ST_organize_le.
      rewrite <- ST_organize_ge.
      assumption. }
    clear sigma_le.
    revert org_sigma_le.
    generalize (organized_path_factors _ (organize_organized tau)).
    induction (organize tau)
      as [ | ? ? _ _ | ? ? _ _ | l r ] using IntersectionType_rect'.
    - intros; apply Forall_nil.
    - intros path_C org_sigma_le.
      apply Forall_cons; [ | apply Forall_nil].
      generalize (organized_path_factors _ (organize_organized sigma)).
      revert org_sigma_le.
      induction (organize sigma)
        as [ | | | l r ] using IntersectionType_rect'.
      + intro org_sigma_le.
        assert False.
        { eapply Omega_path.
          - inversion path_C; eassumption.
          - eapply Omega_complete; [ eassumption | exact I]. }
        contradiction.
      + intros ? path_C'.
        inversion path_C'.
        apply Exists_cons_hd; split; assumption.
      + intro.
        assert False.
        { eapply ST_Arrow_Const; eassumption. }
        contradiction.
      + intros org_sigma_le sigma_paths.
        inversion path_C as [ | ? ? ? path_C' ].
        simpl in sigma_paths.
        generalize (append_Forall1 _ _ _ sigma_paths).
        generalize (append_Forall2 _ _ _ sigma_paths).
        intros r_paths l_paths.
        destruct (Prime_Ideal_Path _ path_C' _ _ (Ideal_complete _ _ org_sigma_le))
          as [ left_choice | right_choice ].
        * generalize (Ideal_sound _ _ left_choice); intro.
          apply Exists_append1; auto.
        * generalize (Ideal_sound _ _ right_choice); intro.
          apply Exists_append2; auto.
    - intros path_Arrow org_sigma_le.
      apply Forall_cons; [ | apply Forall_nil].
      generalize (organized_path_factors _ (organize_organized sigma)).
      revert org_sigma_le.
      induction (organize sigma)
        as [ | | | l r ] using IntersectionType_rect'.
      + intro org_sigma_le.
        assert False.
        { eapply Omega_path.
          - inversion path_Arrow; eassumption.
          - eapply Omega_complete; [ eassumption | exact I]. }
        contradiction.
      + intro.
        assert False.
        { inversion path_Arrow.
          eapply Omega_path; [ eassumption | ].
          simpl.
          eapply ST_Const_Arrow; eassumption. }
        contradiction.
      + intros ? path_Arrow'.
        inversion path_Arrow'.
        apply Exists_cons_hd; split; assumption.
      + intros org_sigma_le sigma_paths.
        inversion path_Arrow as [ | ? ? ? path_Arrow' ].
        simpl in sigma_paths.
        generalize (append_Forall1 _ _ _ sigma_paths).
        generalize (append_Forall2 _ _ _ sigma_paths).
        intros r_paths l_paths.
        destruct (Prime_Ideal_Path _ path_Arrow' _ _ (Ideal_complete _ _ org_sigma_le))
          as [ left_choice | right_choice ].
        * generalize (Ideal_sound _ _ left_choice); intro.
          apply Exists_append1; auto.
        * generalize (Ideal_sound _ _ right_choice); intro.
          apply Exists_append2; auto.
    - intros paths_Inter org_sigma_le.
      simpl in paths_Inter.
      generalize (append_Forall1 _ _ _ paths_Inter).
      generalize (append_Forall2 _ _ _ paths_Inter).
      intros paths_l paths_r.
      assert (l_ge : organize sigma <= l).
      { etransitivity; [ eassumption | apply ST_InterMeetLeft ]. }
      assert (r_ge : organize sigma <= r).
      { etransitivity; [ | apply ST_InterMeetRight ]; eassumption. }
      apply Forall_append; auto.
  Qed.

  Lemma ST_path: forall sigma tau,
      sigma <= tau ->
      Path tau ->
      Exists (fun sigma => Path sigma /\ sigma <= tau) (projT2 (factorize (organize sigma))).
  Proof.
    intros sigma tau sigma_le path_tau.
    assert (org_tau_path :
              Exists (fun tau' => Path tau' /\ tau' <= tau) (projT2 (factorize (organize tau)))).
    { clear sigma sigma_le.
      generalize (ST_organize_le tau).
      generalize (organized_path_factors _ (organize_organized tau)).
      induction (organize tau)
        as [ | | | l r ] using IntersectionType_rect'.
      - intros.
        assert False.
        { eapply Omega_path; [ eassumption | ].
          eapply Omega_complete; [ eassumption | exact I ]. }
        contradiction.
      - intros paths_C ?.
        inversion paths_C as [ | ? ? ? path_C ].
        rewrite (factorize_path _ path_C).
        apply Exists_cons_hd; split; assumption.
      - intros paths_Arrow ?.
        inversion paths_Arrow as [ | ? ? ? path_Arrow ].
        rewrite (factorize_path _ path_Arrow).
        apply Exists_cons_hd; split; assumption.
      - intros paths_Inter tau_ge.
        simpl.
        simpl in paths_Inter.
        assert (paths_l : Forall Path (projT2 (factorize l))).
        { eapply append_Forall1; eassumption. }
        assert (paths_3 : Forall Path (projT2 (factorize r))).
        { eapply append_Forall2; eassumption. }        
        destruct (Prime_Ideal_Path _ path_tau _ _ (Ideal_complete _ _ tau_ge))
          as [ left_choice | right_choice ].
        + set (l_le := Ideal_sound _ _ left_choice).
          apply Exists_append1; auto.
        + set (r_le := Ideal_sound _ _ right_choice).
          apply Exists_append2; auto. }
    generalize (ST_organization _ _ sigma_le).
    induction (org_tau_path) as [ ? ? ? prf_hd | ].
    - intro prfs.
      inversion prfs as [ | ? ? ? prf _ ].
      clear prfs.
      induction prf as [ ? ? ? prf' | ? ? ? ? IH ].
      + inversion prf'.
        inversion prf_hd.
        apply Exists_cons_hd; split.
        * assumption.
        * etransitivity; eassumption.
      + apply Exists_cons_tl; assumption.
    - intro prfs.
      inversion prfs as [ | ? ? ? ? prfs' n_eq [ hd_eq tl_eq ]].
      dependent rewrite tl_eq in prfs'.
      auto.
  Qed.

  
  
  Definition Substitution: Set := VariableSymbol -> IntersectionType.
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

  Fixpoint applyAll {n : nat} (M: Term) (Ns : t Term n) { struct Ns }: Term :=
    match Ns with
    | nil _ => M
    | cons _ N _ Ns => applyAll (App M N) Ns
    end.

  Lemma applyAll_shiftin {n : nat}:
    forall M N (Ns: t Term n),
      applyAll M (shiftin N Ns) = App (applyAll M Ns) N.
  Proof.
    intros M N Ns.
    revert M N.
    induction Ns as [ | ? ? ? IH ].
    - intros; reflexivity.
    - intros M N.
      simpl.
      rewrite IH.
      reflexivity.
  Qed.
  
  Lemma applyAllSpec : forall M, applyAll (Symbol (rootOf M)) (argumentsOf M) = M.
  Proof.
    intro M.
    induction M as [ | ? IH ].
    - reflexivity.
    - simpl.
      rewrite (applyAll_shiftin).
      rewrite IH.
      reflexivity.
  Qed.
    
  Module Type TypeSystem.
    Parameter WellFormed: Substitution -> Prop.
      
    Definition Context: Type := CombinatorSymbol -> @TypeScheme VariableSymbol.

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

    Lemma CL_intersect_many {n}: forall Gamma M (xs: t IntersectionType (S n)),
        Forall (CL Gamma M) xs -> CL Gamma M (intersect xs).
    Proof.
      intros Gamma M xs.
      apply (caseS' xs); clear xs; intros x xs; revert x.
      induction xs as [ | x' n xs IH ].
      - intros x prf; inversion prf; assumption.
      - intros x prfs.
        generalize (append_Forall2 _ (cons _ x _ (nil _)) (cons _ x' _ xs) prfs).
        generalize (Forall_nth _ _ prfs F1).
        intros.
        apply CL_II; eauto.
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

    Lemma mkArrow_inj {n : nat}:
      forall xs ys x y, @mkArrow n xs x = mkArrow ys y -> xs = ys /\ x = y.
    Proof.
      intro xs.
      induction xs as [ | ? ? ? IH ].
      - intro ys.
        apply (fun r => case0 (fun ys => forall x y, (mkArrow _ _ = mkArrow ys _) -> (_ = ys) /\ x = y) r ys).
        intros; split; [ reflexivity | assumption ].
      - intros ys x y.
        apply (caseS' ys); clear ys; intros y' ys.
        intro arrow_prf.
        inversion arrow_prf as [ [ x_prf arrow_prf' ] ].
        destruct (IH ys x y arrow_prf').
        split; [ apply f_equal; assumption | assumption ].
    Qed.
       
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

    Lemma split_path_shiftout: forall sigma n prf prf',
        shiftout (fst (split_path sigma (S n) prf)) =
        fst (split_path sigma n prf').
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

    Lemma split_path_step: forall sigma n prf prf',
        snd (split_path sigma n prf) = Arrow (last (fst (split_path sigma (S n) prf')))
                                             (snd (split_path sigma (S n) prf')).
    Proof.
      intro sigma.
      induction sigma
        as [ | | sigma tau _ IHtau | ]
             using IntersectionType_rect';
        intros n prf prf';
        destruct n;
        try solve [ inversion prf' ].
      - reflexivity.
      - assert (lhs_eq: snd (split_path (Ty (PT_Arrow sigma tau)) (S n) prf) =
                        snd (split_path tau n (proj2 (Nat.succ_le_mono _ _) prf))).
        { reflexivity. }
        rewrite lhs_eq.
        assert (rhs_eq1: last (fst (split_path (Ty (PT_Arrow sigma tau)) (S (S n)) prf')) =
                         last (fst (split_path tau (S n) (proj2 (Nat.succ_le_mono _ _) prf')))).
        { reflexivity. }
        rewrite rhs_eq1.
        assert (rhs_eq2: snd (split_path (Ty (PT_Arrow sigma tau)) (S (S n)) prf') =
                         snd (split_path tau (S n) (proj2 (Nat.succ_le_mono _ _) prf'))).
        { reflexivity. }
        rewrite rhs_eq2.
        apply IHtau.
    Qed.

    Lemma ST_path_tgt_n: forall sigma tau,
        Path sigma -> Path tau ->
        sigma <= tau ->
        forall n (sigmaPrf: (n <= src_count sigma)%nat) (tauPrf: (n <= src_count tau)%nat),
          snd (split_path sigma n sigmaPrf) <= snd (split_path tau n tauPrf).
    Proof.
      intros sigma tau path_sigma.
      revert tau.
      induction path_sigma as [ | ? ? ? IH ].
      - intros tau path_tau sigma_le n n_le.
        simpl in n_le.
        destruct n.
        + intros; assumption.
        + inversion n_le.
      - intros tau' path_tau'.
        inversion path_tau' as [ | ? ? path_tau'' ].
        + intro devil.
          assert False; [ | contradiction ].
          apply (ST_Arrow_Const _ _ _ _ devil).
        + intro arrow_le.
          generalize (AI_complete _ _ _ arrow_le).
          intro AI_tau'.
          inversion AI_tau' as [ ? omega_tau'' | ? ? ? tau''_le | | | ].
          * assert False; [ | contradiction ].
            eapply Omega_path; eassumption.
          * intros n sigmaPrf tauPrf.
            destruct n.
            { assumption. }
            { apply (IH _ path_tau'' tau''_le _
                        (proj2 (Nat.succ_le_mono _ _) sigmaPrf)
                        (proj2 (Nat.succ_le_mono _ _) tauPrf)). }
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
                + inversion factor_paths as [  | ? ? ? path_factor ].
                  assert (argCountPrf' : (argumentCount (App M N) <= src_count factor')%nat).
                  { set (tgt_S_n := Path_src_count _ _ tgt_prf (Path_split_path _ _ _ path_factor')
                                                   (Path_Arr _ _ path_factor)).
                    rewrite (source_count_plus _ _ argCountPrf).
                    simpl.
                    rewrite tgt_S_n.
                    simpl.
                    rewrite <- (Nat.add_succ_comm).
                    apply (Nat.le_add_r). }
                  exists argCountPrf'; split.
                  * rewrite (split_path_shiftin _ _ _ argCountPrf).
                    apply Forall2_shiftin.
                    { set (factor'_last_eq := split_path_shiftin _ _ argCountPrf' argCountPrf).
                      simpl plus in factor'_last_eq.
                      rewrite factor'_last_eq.
                      rewrite (shiftin_last).
                      apply (CL_ST _ _ _ _ Nsigma).
                      rewrite (split_path_step _ _ _ argCountPrf') in tgt_prf.
                      set (tgt_prf' := AF_complete _ _ _ tgt_prf).
                      inversion tgt_prf' as [ | | ? omega_factor ].
                      - assumption.
                      - contradict omega_factor.
                        unfold not.
                        simpl.
                        apply Omega_path.
                        assumption. }
                    { exact args_prf. }
                  * rewrite (split_path_step _ _ _ argCountPrf') in tgt_prf.
                    set (tgt_prf' := AF_complete _ _ _ tgt_prf).
                    inversion tgt_prf' as [ | | ? omega_factor ].
                    { assumption.  }
                    { contradict omega_factor.
                      unfold not.
                      simpl.
                      apply Omega_path.
                      assumption. }
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

    Lemma CL_Path_path: forall Gamma M sigma,
        CL Gamma M sigma ->
        Path sigma ->
        exists S, WellFormed S /\
             Exists (fun path =>
                       Path path /\
                       exists argCountPrf : (argumentCount M <= src_count path)%nat,
                         Forall2 (CL Gamma) (argumentsOf M)
                                 (fst (split_path path _ argCountPrf)) /\
                         (snd (split_path path _ argCountPrf)) <= sigma
                    )
                    (projT2 (factorize (organize (Apply S (Gamma (rootOf M)))))).
    Proof.
      intros Gamma M sigma prf path_sigma.
      generalize (CL_Path _ _ _ prf).
      clear prf.
      generalize (ST_path _ _ (ST_Refl sigma) path_sigma).
      intro ex_path.
      induction ex_path as [ ? ? ? here | ? ? ? there ]; intro all_s.
      - inversion all_s as [ | ? ? ? prf prfs n_eq [ hd_eq tl_eq ] ].
        destruct prf as [ S [ WF_S ex_prf ] ].
        exists S; split; [ assumption | ].
        revert ex_prf here.
        clear ...
        intros ex_prf here.
        destruct here as [ path_x x_le ].
        induction ex_prf as [ ? ? ? here | there ].
        + inversion here as [ path_x' [ argCountPrf [ argsPrfs x_ge ] ] ].
          apply Exists_cons_hd; split.
          * assumption.
          * eexists; split; [ eassumption | ].
            rewrite <- x_le.
            assumption.
        + apply Exists_cons_tl; assumption.
      - inversion all_s as [ | ? ? ? prf prfs n_eq [ hd_eq tl_eq ] ].
        dependent rewrite tl_eq in prfs.
        auto.
    Qed.

    Lemma CL_Path_c: forall Gamma c sigma,
        CL Gamma (Symbol c) sigma ->
        Forall (fun sigma' =>
                  exists S, WellFormed S /\
                       Exists (fun path => Path path /\ path <= sigma')
                              (projT2 (factorize (organize (Apply S (Gamma c))))))
               (projT2 (factorize (organize sigma))).
    Proof.
      intros Gamma c sigma prf.
      generalize (CL_Path _ _ _ prf).
      intro path_prfs.
      match goal with
      | [ |- Forall _ ?tgt ] =>
        induction tgt as [ | path n paths IH ]
      end.
      - apply Forall_nil.
      - apply Forall_cons.
        + generalize (Forall_nth _ _ path_prfs F1).
          intro path_prf.
          destruct path_prf as [ S [ WF_S ex_prf ] ].
          eexists; split; [ eassumption | ].
          simpl in ex_prf.
          induction ex_prf as [ path' ? ? [ pathPrf [ argCountPrf [ argsPrfs tgtPrf ] ] ] | ].
          * apply Exists_cons_hd; split; assumption.
          * apply Exists_cons_tl; assumption.
        + generalize (append_Forall2 _ (cons _ path _ (nil _)) paths path_prfs).
          auto.
    Qed.

    Lemma CL_Path_c_inv: forall Gamma c sigma,
        (exists S, WellFormed S) ->
        Forall (fun sigma' =>
                  exists S, WellFormed S /\
                       Exists (fun path => Path path /\ path <= sigma')
                              (projT2 (factorize (organize (Apply S (Gamma c))))))
               (projT2 (factorize (organize sigma))) ->
        CL Gamma (Symbol c) sigma.
    Proof.
      intros Gamma c sigma ex_WF prfs.
      eapply CL_ST; [ | apply ST_organize_le ].
      rewrite (factorize_organized _ (organize_organized _)).
      match goal with
      | [ |- CL _ _ (intersect ?tgts) ] =>
        induction tgts as [ | factor n factors IH ]
      end.
      - destruct ex_WF; eapply CL_omega; eassumption.
      - assert (factor_prf : CL Gamma (Symbol c) factor).
        { generalize (Forall_nth _ _ prfs F1).
          intro ex_prf.
          simpl.
          destruct ex_prf as [ S [ WF_S ex_prfs ] ].
          eapply CL_ST; [ eapply CL_Var; eassumption | ].
          rewrite ST_organize_ge.
          rewrite (factorize_organized _ (organize_organized _)).
          induction ex_prfs as [ ? path' ? [ path_path' path'_le ] | ? x xs ? IH' ] .
          * rewrite (ST_intersect_nth _ F1); assumption.
          * rewrite <- IH'.
            rewrite (ST_intersect_append_le (cons _ x _ (nil _)) xs).
            rewrite (ST_InterMeetRight).
            reflexivity. }
        destruct factors.
        + assumption.
        + match goal with
          | [ |- CL _ _ (intersect (cons _ _ _ ?rest)) ] =>
            generalize (append_Forall2 _ (cons _ factor _ (nil _)) rest prfs)
          end.
          intro.
          apply CL_II; auto.
    Qed.          

    Lemma CL_all_paths:
      forall Gamma M sigma,
        (exists S, WellFormed S) ->
        Forall (CL Gamma M) (projT2 (factorize (organize sigma))) ->
        CL Gamma M sigma.
    Proof.
      intros Gamma M sigma ex_subst prfs.
      eapply CL_ST; [ | apply ST_organize_le ].
      rewrite (factorize_organized _ (organize_organized _)).      
      induction prfs as [ | ? ? xs ? ? IH ].
      - inversion ex_subst; eapply CL_omega; eassumption.
      - destruct xs.
        + assumption.
        + apply CL_II; [ assumption | apply IH ].
    Qed.          

    Lemma CL_ApplyPath:
      forall Gamma c n (args: t Term n) sigma argsPrf,
        Path sigma ->
        CL Gamma (Symbol c) sigma ->
        Forall2 (CL Gamma) args (fst (split_path sigma n argsPrf)) ->
        CL Gamma (applyAll (Symbol c) args) (snd (split_path sigma n argsPrf)).
    Proof.
      intros Gamma c n.
      induction n as [ | n IH ].
      - intro args; intros.
        apply (fun r => case0 (fun args => CL _ (applyAll _ args) _) r args).
        assumption.
      - intros args sigma argsPrf path_sigma cSigma argsSigmas.
        rewrite (shiftin_shiftout args).
        rewrite (applyAll_shiftin).
        eapply CL_MP.
        + assert (argsPrf' : (n <= src_count sigma)%nat).
          { etransitivity; [ apply le_S | eassumption ]; reflexivity. }
          rewrite <- (split_path_step _ _ argsPrf' argsPrf).
          apply IH; [ assumption | assumption | ].
          rewrite (split_path_shiftin _ _ _ argsPrf') in argsSigmas.
          rewrite (shiftin_shiftout args) in argsSigmas.
          generalize (Forall2_shiftout _ _ _ argsSigmas).
          intro argsSigmas'.
          rewrite <- (shiftin_shiftout) in argsSigmas'.
          rewrite <- (split_path_shiftin) in argsSigmas'.
          rewrite (split_path_shiftout _ _ _ argsPrf') in argsSigmas'.
          assumption.
        + apply Forall2_last; assumption.
    Qed.

    Lemma CL_Path_inv:
      forall Gamma M sigma,
        (exists S, WellFormed S) ->
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
               (projT2 (factorize (organize sigma))) ->
        CL Gamma M sigma.
    Proof.
      intros Gamma M sigma ex_S prfs.
      eapply CL_ST; [ | apply (ST_organize_le sigma) ].
      rewrite (factorize_organized _ (organize_organized _)).
      induction prfs as [ | n sigma' sigmas' prf prfs IH ].
      - destruct ex_S; eapply CL_omega; eassumption.
      - assert (CL Gamma M sigma').
        { destruct prf as [ S [ WF_S ex_prfs ] ].
          assert (root_prf: CL Gamma (Symbol (rootOf M))
                     (intersect (projT2 (factorize (organize (Apply S (Gamma (rootOf M)))))))).
          { rewrite <- (factorize_organized _ (organize_organized _)).
            eapply CL_ST; [ | apply ST_organize_ge ].
            apply CL_Var; assumption. }
          revert root_prf.
          induction ex_prfs
            as [ ? path ? [ path_path [ argCountPrf [ argsPrfs tgtPrf ] ] ] | ? x xs ? IH' ].
          - intro root_prf.
            eapply CL_ST; [ | eassumption ].
            rewrite <- (applyAllSpec M) at 1.
            apply CL_ApplyPath; try solve [ assumption ].
            eapply CL_ST; [ exact root_prf | ].
            rewrite (ST_intersect_nth _ F1).
            reflexivity.
          - intro root_prf.
            apply IH'.
            eapply CL_ST; [ exact root_prf | ].
            rewrite (ST_intersect_append_le (cons _ x _ (nil _)) xs).
            apply ST_InterMeetRight. }
        destruct sigmas'.
        + assumption.
        + apply CL_II; assumption.
    Qed.
    
    Section DecidableWF.
      Require Import Coq.Logic.ConstructiveEpsilon.
      Variable WF_dec: forall S, { WellFormed S } + { ~ WellFormed S }.
      Structure Countable (A: Set) : Set :=
        { toNat : A -> nat;
          fromNat : nat -> A;
          fromTo_id : forall x, fromNat (toNat x) = x }.

      Structure Finite (A : Set) : Set :=
        { cardinality : nat;
          toFin : A -> Fin.t cardinality;
          fromFin : Fin.t cardinality -> A;
          fromToFin_id : forall x, fromFin (toFin x) = x }.
      
      Context { ConstructorSymbol_countable: Countable ConstructorSymbol }.      
      Context { Variables_countable: Countable VariableSymbol }.

      (* TODO: These two are vaild and just have to be shown *)
      Axiom SubstitutionSpace_countable: `{Countable Substitution}.
      Axiom ST_dec: forall sigma tau, { sigma <= tau } + { sigma <= tau -> False }.
      
      Lemma WF_and_le_path_dec: forall sigma_pre sigma S,
          { WellFormed S /\ Apply S sigma_pre <= sigma } + { WellFormed S /\ Apply S sigma_pre <= sigma -> False }.
      Proof.
        intros sigma_pre sigma S.
        destruct (WF_dec S).
        - destruct (ST_dec (Apply S sigma_pre) sigma).
          + left; split; assumption.
          + right; intro devil; destruct devil; contradiction.
        - right; intro devil; destruct devil; contradiction.
      Qed.

      Section TypeCheckable.
        Variable Gamma : Context.
        Variable CL_Gamma_dec: forall M sigma, { CL Gamma M sigma } + { CL Gamma M sigma -> False }.

        Lemma split_path_proof_invariant: forall path n prf prf',
          (split_path path n prf) = (split_path path n prf').
        Proof.
          intro path.
          destruct path using IntersectionType_rect';
            intros n prf prf';
            simpl in prf;
            simpl in prf';
            destruct n;
            try solve [ reflexivity | inversion prf ].
          simpl.
          apply f_equal2.
          - apply f_equal.
            apply f_equal.
            auto.
          - apply f_equal.
            auto.
        Qed.
        
        Lemma S_sufficient_dec: forall M sigma S,
            { WellFormed S /\
              Exists (fun path =>
                        Path path /\
                        exists argCountPrf : (argumentCount M <= src_count path)%nat,
                          Forall2 (CL Gamma) (argumentsOf M)
                                  (fst (split_path path _ argCountPrf)) /\
                          (snd (split_path path _ argCountPrf)) <= sigma
                     )
                     (projT2 (factorize (organize (Apply S (Gamma (rootOf M)))))) } +
            { WellFormed S /\
              Exists (fun path =>
                        Path path /\
                        exists argCountPrf : (argumentCount M <= src_count path)%nat,
                          Forall2 (CL Gamma) (argumentsOf M)
                                  (fst (split_path path _ argCountPrf)) /\
                          (snd (split_path path _ argCountPrf)) <= sigma
                     )
                     (projT2 (factorize (organize (Apply S (Gamma (rootOf M)))))) -> False }.
        Proof.
          intros M sigma S.
          destruct (WF_dec S).
          - generalize (organized_path_factors _ (organize_organized (Apply S (Gamma (rootOf M))))).
            induction (projT2 (factorize (organize (Apply S (Gamma (rootOf M))))))
              as [ | path n paths IH ].
            + intro; right; intro devil; inversion devil as [ ? ex_nil ]; inversion ex_nil.
            + intro path_prfs.
              generalize (append_Forall2 _ (cons _ path _ (nil _)) paths path_prfs).
              generalize (Forall_nth _ _ path_prfs F1).
              clear path_prfs; intros path_prf path_prfs.
              assert (path_dec :
                      { Path path /\
                        exists argCountPrf,
                          Forall2 (CL Gamma) (argumentsOf M)
                                  (fst (split_path path (argumentCount M) argCountPrf)) /\
                          snd (split_path path (argumentCount M) argCountPrf) <= sigma } +
                      { (Path path /\
                         exists argCountPrf,
                           Forall2 (CL Gamma) (argumentsOf M)
                                   (fst (split_path path (argumentCount M) argCountPrf)) /\
                           snd (split_path path (argumentCount M) argCountPrf) <= sigma) -> False }).
              { destruct (le_dec (argumentCount M) (src_count path))
                  as [ argCountPrf | argCountDisprf ].
                - destruct (ST_dec (snd (split_path path (argumentCount M) argCountPrf)) sigma)
                    as [ sigma_ge | not_sigma_ge ].
                  + assert (dec_tys : forall n (Ms : t Term n) tys, 
                        { Forall2 (CL Gamma) Ms tys } +
                        { Forall2 (CL Gamma) Ms tys -> False }).
                    { revert CL_Gamma_dec.
                      clear ...
                      intros CL_Gamma_dec n Ms tys.
                      induction Ms as [ | M n Ms IH ].
                      - left.
                        apply (fun r => case0 _ r tys).
                        apply Forall2_nil.
                      - apply (caseS' tys); clear tys; intros ty tys.
                        destruct (CL_Gamma_dec M ty) as [ Mty | not_Mty ].
                        + destruct (IH tys) as [ Mstys | not_Mstys ].
                          * left; apply Forall2_cons; assumption.
                          * right; intro devil.
                            inversion devil
                              as [ | ? ? ? ? ? ? devil' n_eq [ hd_eq tl_eq ] [ hd_eq' tl_eq' ] ].
                            generalize (vect_exist_eq _ _ tl_eq).
                            generalize (vect_exist_eq _ _ tl_eq').
                            intros tys_eq terms_eq.
                            rewrite <- terms_eq in not_Mstys.
                            rewrite <- tys_eq in not_Mstys.
                            contradiction.
                        + right; intro devil; inversion devil; contradiction. }
                    destruct (dec_tys _ (argumentsOf M)
                                      (fst (split_path path (argumentCount M) argCountPrf))).
                    * left; split; [ assumption | eexists; split; eassumption ].
                    * right; intro devil;
                        inversion devil as [ ? [ argCountPrf' [ argsPrfs ? ] ] ].
                      assert (split_path_eq: (fst (split_path path (argumentCount M) argCountPrf)) =
                                             (fst (split_path path (argumentCount M) argCountPrf'))).
                      { clear ...
                        apply f_equal.
                        apply split_path_proof_invariant. }
                      rewrite <- split_path_eq in argsPrfs.
                      contradiction.
                  + right; intro devil.
                    inversion devil as [ ? [ argCountPrf' [ ? le_prf ] ] ].
                    assert (split_path_eq: (snd (split_path path (argumentCount M) argCountPrf)) =
                                           (snd (split_path path (argumentCount M) argCountPrf'))).
                    { clear ...
                      apply f_equal.
                      apply split_path_proof_invariant. }
                    rewrite <- split_path_eq in le_prf.
                    contradiction.
                - right; intro devil; inversion devil as [ ? [ ? ? ] ].
                  contradiction. }
              destruct path_dec as [ path_ok | not_path_ok ].
              * left; split; [ assumption | apply Exists_cons_hd; assumption ].
              * destruct (IH path_prfs) as [ paths_ok | not_paths_ok ].
                { destruct paths_ok.
                  left; split; [ assumption | apply Exists_cons_tl; assumption ]. }
                { right; intro devil; destruct devil as [ ? ex_prf ].
                  inversion ex_prf as [ | ? ? ? prfs n_eq [ hd_eq tl_eq ] ].
                  - contradiction.
                  - dependent rewrite tl_eq in prfs.
                    apply not_paths_ok; split; assumption. }
          - right; intro devil; inversion devil; contradiction.            
        Qed.
        
        Lemma CL_Path_compute_S:
          forall M sigma,
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
                   (projT2 (factorize (organize sigma))) ->
            ForAll' (fun sigma' =>
                       { S : _ | WellFormed S /\
                            Exists (fun path =>
                                      Path path /\
                                      exists argCountPrf : (argumentCount M <= src_count path)%nat,
                                        Forall2 (CL Gamma) (argumentsOf M)
                                                (fst (split_path path _ argCountPrf)) /\
                                        (snd (split_path path _ argCountPrf)) <= sigma'
                                   )
                                   (projT2 (factorize (organize (Apply S (Gamma (rootOf M))))))
                       }) 
                    (projT2 (factorize (organize sigma))).
        Proof.
          intros M sigma.
          induction (projT2 (factorize (organize sigma)))
            as [ | h n tl IH ].
          - intros; apply ForAll'_nil.
          - intro prfs.
            generalize (append_Forall2 _ (cons _ h _ (nil _)) tl prfs).
            generalize (Forall_nth _ _ prfs F1).
            intros h_prf tl_prfs.
            apply ForAll'_cons.
            + eapply (constructive_indefinite_ground_description).
              * apply (fromTo_id _ SubstitutionSpace_countable).
              * apply S_sufficient_dec.
              * assumption.
            + auto.
        Qed.

        Lemma CL_Path_path_compute_S:
          forall M sigma,
            Path sigma ->
            (exists S, WellFormed S /\
                 Exists (fun path =>
                           Path path /\
                           exists argCountPrf : (argumentCount M <= src_count path)%nat,
                             Forall2 (CL Gamma) (argumentsOf M)
                                   (fst (split_path path _ argCountPrf)) /\
                             (snd (split_path path _ argCountPrf)) <= sigma
                        )
                        (projT2 (factorize (organize (Apply S (Gamma (rootOf M))))))) ->
            { S : _ | WellFormed S /\
                      Exists (fun path =>
                                Path path /\
                                exists argCountPrf : (argumentCount M <= src_count path)%nat,
                                  Forall2 (CL Gamma) (argumentsOf M)
                                          (fst (split_path path _ argCountPrf)) /\
                                  (snd (split_path path _ argCountPrf)) <= sigma
                             )
                             (projT2 (factorize (organize (Apply S (Gamma (rootOf M))))))
            }.
        Proof.
          intros M sigma path_sigma ex_S.
          eapply (constructive_indefinite_ground_description).
          - apply (fromTo_id _ SubstitutionSpace_countable).
          - apply S_sufficient_dec.
          - assumption.
        Qed.
      End TypeCheckable.
     
      Section FiniteSubstitutionCheckable.
        Variable SubstitutionSpace_finite: Finite { S : Substitution | WellFormed S }.

        Definition minimalInstance (sigma_pre: TypeScheme): IntersectionType :=
          intersect
            (map
               (fun k => Apply (proj1_sig (fromFin _ SubstitutionSpace_finite k)) sigma_pre)
               (positions (cardinality _ SubstitutionSpace_finite))).
        
        
        Lemma MinimalType_sound:
          forall Gamma c, (cardinality _ SubstitutionSpace_finite > 0) ->
                     CL Gamma (Symbol c) (minimalInstance (Gamma c)).
        Proof.
          intros Gamma c.
          assert (all_prfs: forall k, CL Gamma (Symbol c)
                          (Apply (proj1_sig (fromFin _ SubstitutionSpace_finite k))
                                 (Gamma c))).
          { intro k.
            apply CL_Var; exact (proj2_sig (fromFin _ SubstitutionSpace_finite k)). }
          intro card_gt.
          unfold minimalInstance.
          revert all_prfs.
          inversion card_gt as [ prf | ? ? prf ];
            destruct SubstitutionSpace_finite as [ card to from id ];
            simpl in *;
            revert to from id;
            rewrite <- prf in *;
            intros;
            apply CL_intersect_many;
            apply nth_Forall;
            intro k;
            rewrite (nth_map _ _ _ _ eq_refl);
            auto.
        Qed.

        Lemma MinimalType_minimal: forall Gamma c sigma,
            CL Gamma (Symbol c) sigma -> (minimalInstance (Gamma c)) <= sigma.
        Proof.
          intros Gamma c sigma prf.
          remember (Symbol c) as M eqn:M_eq.
          revert c M_eq.
          induction prf as [ ? S WF_S | | | ].
          - intros c' M_eq.
            inversion M_eq.
            unfold minimalInstance.
            assert (S_eq: S = proj1_sig (fromFin _ SubstitutionSpace_finite
                                           (toFin _ SubstitutionSpace_finite (exist _ S WF_S)))).
            { rewrite fromToFin_id; reflexivity. }
            rewrite S_eq.
            rewrite (ST_intersect_nth _ (toFin _ SubstitutionSpace_finite (exist _ S WF_S))).
            rewrite (nth_map _ _ _ _ eq_refl).
            rewrite (positions_spec).
            reflexivity.
          - intros ? MN_eq; inversion MN_eq.
          - intros; apply ST_Both; auto.
          - intros; etransitivity; eauto.
        Qed.

        Definition suffixes (n: nat) (sigma: IntersectionType): list IntersectionType :=
          (fix suffixes_rec m sigma :=
             match le_dec n m with
             | left prf =>
               match le_dec m (src_count sigma) with
               | left prf' => List.cons (snd (split_path sigma _ prf'))
                                       (match m with
                                        | 0 => List.nil
                                        | S m' => suffixes_rec m' sigma
                                        end)
               | right _ => List.nil
               end
             | _ => List.nil
             end) (src_count sigma) sigma.

        Definition allPathSuffixes (n: nat) (sigma: IntersectionType): list IntersectionType :=
          (fix allPaths_rec n' sigmas :=
            match sigmas with
            | cons _ x _ xs =>
              match le_dec n (src_count x) with
              | left prf => List.cons (snd (split_path x _ prf)) (allPaths_rec _ xs)
              | right _ => allPaths_rec _ xs
              end
            | nil _ => List.nil
            end) _ (projT2 (factorize (organize sigma))).

        Lemma allPathSuffixes_0: forall (sigma: IntersectionType),
            allPathSuffixes 0 sigma = to_list (projT2 (factorize (organize sigma))).
        Proof.
          intro sigma.
          unfold allPathSuffixes.
          induction (projT2 (factorize (organize sigma))) as [ | hd n tl IH ].
          - reflexivity.
          - destruct (le_dec 0 (src_count hd)) as [ prf | disprf ].
            + simpl.
              unfold to_list.
              apply f_equal.
              assumption.
            + generalize (le_0_n (src_count hd)).
              intro; contradiction.
        Qed.
        
        Lemma allPaths_paths: forall n sigma,
            List.Forall Path (allPathSuffixes n sigma).
        Proof.
          intros n sigma.
          unfold allPathSuffixes.
          generalize (organized_path_factors _ (organize_organized sigma)).
          induction (projT2 (factorize (organize sigma))) as [ | hd ? tl IH ].
          - intros; apply List.Forall_nil.
          - intro path_prf.
            generalize (Forall_nth _ _ path_prf F1).
            intro path_hd.
            generalize (append_Forall2 _ (cons _ hd _ (nil _)) tl path_prf).
            intro paths_tl.
            destruct (le_dec n (src_count hd)).
            + apply List.Forall_cons; auto.
              apply (Path_split_path); assumption.
            + auto.
        Qed.

        
        Fixpoint powerset {A: Type} (xs: list A): list (list A) :=
            match xs with
            | List.nil => List.cons List.nil List.nil
            | List.cons x xs =>
              List.app
                (List.map (List.cons x) (powerset xs))
                (powerset xs)
            end.

        Lemma CL_MP_inv_dec_complete: forall Gamma M N tau,
            { CL Gamma (App M N) tau } + { CL Gamma (App M N) tau -> False } ->
            { exists sigma, CL Gamma M (Arrow sigma tau) /\ CL Gamma N sigma } +
            { (exists sigma, CL Gamma M (Arrow sigma tau) /\ CL Gamma N sigma) -> False }.
        Proof.
          intros Gamma M N tau MN_dec.
          destruct MN_dec.
          - left; apply MP_generation; assumption.
          - right; intro devil.
            inversion devil as [ sigma [ prfM prfN ] ].
            generalize (CL_MP _ _ _ _ _ prfM prfN).
            assumption.
        Qed.

        Lemma CL_MP_inv_dec_sound: forall Gamma M N tau,
            { exists sigma, CL Gamma M (Arrow sigma tau) /\ CL Gamma N sigma } +
            { (exists sigma, CL Gamma M (Arrow sigma tau) /\ CL Gamma N sigma) -> False } ->
            { CL Gamma (App M N) tau } + { CL Gamma (App M N) tau -> False }.
        Proof.
          intros Gamma M N tau MN_dec.
          destruct MN_dec as [ prf | ].
          - left; inversion prf as [ ? [ ? ? ] ]; eapply CL_MP; eassumption.
          - right; intro devil; generalize (MP_generation _ _ _ _ devil); contradiction.
        Qed.


        Lemma Path_suffixes_split:
          forall n (xs: t IntersectionType n) path k m,
            List.In path (allPathSuffixes m (nth xs k)) ->
            List.In path (allPathSuffixes m (intersect xs)).
        Proof.
          intros n xs path k m.
          induction k as [ | n k IH ].
          - unfold allPathSuffixes.
            apply (caseS' xs); clear xs; intros x xs.
            intro prf; simpl in prf.
            unfold allPathSuffixes.
            simpl.
            destruct xs as [ | x' n xs ].
            + assumption.
            + simpl.
              rewrite (factorize_intersect_append (projT2 (factorize (organize x))) _).
              rewrite <- (factorize_organized _ (organize_organized x)).
              induction (projT2 (factorize (organize x))) as [ | y ? ys IH ].
              * contradiction.
              * unfold List.In in prf.
                unfold List.In.
                simpl.
                destruct (le_dec m (src_count y)).
                { destruct prf.
                  - left; assumption.
                  - right. apply IH. assumption. }
                { apply IH; assumption. }
          - apply (caseS' xs); clear xs; intros x xs.
            intro prf; simpl in prf.
            unfold allPathSuffixes.
            simpl.
            destruct xs as [ | x' n xs ].
            + inversion k.
            + simpl.
              rewrite (factorize_intersect_append (projT2 (factorize (organize x))) _).
              rewrite <- (factorize_organized _ (organize_organized x)).
              generalize (factorize_organized _ (organize_organized (intersect (cons _ x' _ xs)))).
              intro eq.
              simpl in eq.
              rewrite <- eq.
              generalize (IH (cons _ x' _ xs) prf).
              clear ...
              intro prf.
              induction (projT2 (factorize (organize x))) as [ | y ? ys ].
              * simpl. unfold allPathSuffixes in prf.
                simpl in prf.
                exact prf.
              * simpl.
                destruct (le_dec m (src_count y)).
                { right.
                  assumption. }
                { assumption. }
        Qed.
          

        Lemma CL_Path_minimal_impl:
          forall Gamma M sigma
            (M_dec: forall sigma, { CL Gamma M sigma } + { CL Gamma M sigma -> False }),
            Path sigma ->
            ( exists S, WellFormed S /\
                  Exists (fun path =>
                            Path path /\
                            exists argCountPrf : (argumentCount M <= src_count path)%nat,
                              Forall2 (CL Gamma) (argumentsOf M)
                                      (fst (split_path path _ argCountPrf)) /\
                              (snd (split_path path _ argCountPrf)) <= sigma
                         )
                         (projT2 (factorize (organize (Apply S (Gamma (rootOf M))))))) ->
            exists sigma',
              sigma' <= sigma /\
              List.In sigma'
                      (filter (fun sigma' => match M_dec sigma' with
                                          | left _ => true
                                          | right _ => false end)
                              (allPathSuffixes (argumentCount M)
                                               (minimalInstance (Gamma (rootOf M))))).
        Proof.
          intros Gamma M sigma M_dec path_sigma ex_prf.
          destruct ex_prf as [ S [ WF_S ex_prf ] ] .
          assert (in_prf_compatible : forall sigma',
                     List.In sigma'
                             (filter (fun sigma' : IntersectionType =>
                                        if M_dec sigma' then true else false)
                                     (allPathSuffixes (argumentCount M)
                                                      (Apply S (Gamma (rootOf M))))) ->
                     List.In sigma'
                             (filter (fun sigma' : IntersectionType =>
                                        if M_dec sigma' then true else false)
                                     (allPathSuffixes (argumentCount M)
                                                      (minimalInstance (Gamma (rootOf M)))))).
          { intro sigma'.
            assert (S_fin : S = proj1_sig (fromFin _ SubstitutionSpace_finite
                                           (toFin _ SubstitutionSpace_finite (exist _ S WF_S)))).
            { rewrite (fromToFin_id _ SubstitutionSpace_finite).
              reflexivity. }
            rewrite S_fin.
            generalize (toFin _ SubstitutionSpace_finite (exist _ S WF_S)).
            unfold minimalInstance.
            intros k prfs.
            apply filter_In.
            split.
            - apply (Path_suffixes_split _ _ _ k).
              rewrite (nth_map _ _ _ _ eq_refl).
              rewrite (positions_spec _ k).
              eapply filter_In.
              eassumption.
            - generalize (proj1 (filter_In _ _ _) prfs).
              intros [ ? ? ]; assumption. }
          assert (replace_in_prf :
            (exists sigma' : IntersectionType,
                sigma' <= sigma /\
                List.In sigma'
                        (filter (fun sigma' => if M_dec sigma' then true else false)
                                (allPathSuffixes (argumentCount M) (Apply S (Gamma (rootOf M)))))) ->
            (exists sigma' : IntersectionType,
                sigma' <= sigma /\
                List.In sigma'
                        (filter (fun sigma' : IntersectionType => if M_dec sigma' then true else false)
                                (allPathSuffixes (argumentCount M)
                                                 (minimalInstance (Gamma (rootOf M))))))).
          { intros [ sigma' [ le_prf in_prf ] ].
            eexists; split; [ eassumption | auto ]. }
          apply replace_in_prf.
          clear replace_in_prf in_prf_compatible.
          unfold allPathSuffixes.
          assert (root_prfs :
                    Forall (CL Gamma (Symbol (rootOf M)))
                           (projT2 (factorize (organize (Apply S (Gamma (rootOf M))))))).
          { apply nth_Forall.
            intro k.
            eapply CL_ST; [ apply CL_Var; eassumption | ].
            etransitivity; [ eapply ST_organize_ge | ].
            rewrite (factorize_organized _ (organize_organized (Apply S (Gamma (rootOf M))))) at 1.
            apply ST_intersect_nth. } 
          induction ex_prf
            as [ ? path paths [ path_path [ argCountPrf [ args_prfs tgt_prf ] ] ]
               | ? path paths ? IH ].
          - eexists; split; [ eassumption | ].
            destruct (le_dec (argumentCount M) (src_count path)) as [ prf | disprf ].
            + simpl.
              destruct (M_dec (snd (split_path path (argumentCount M) prf))) as [ | devil ].
              * unfold List.In.
                rewrite <- (split_path_proof_invariant _ _ prf argCountPrf).
                left; reflexivity.
              * assert False.
                { apply devil.
                  rewrite <- (applyAllSpec M) at 1.
                  eapply CL_ApplyPath; [ eassumption | |].
                  - exact (Forall_nth _ _ root_prfs F1).
                  - rewrite (split_path_proof_invariant _ _ prf argCountPrf).
                    assumption. }
                contradiction.
            + contradiction.
          - destruct (IH (append_Forall2 _ (cons _ path _ (nil _))
                                         paths root_prfs))
              as [ sigma' [ le_prf in_prf ] ].
            eexists; split; [ eassumption | ].
            destruct (le_dec (argumentCount M) (src_count path))
              as [ argCountPrf | ].
            + simpl.
              destruct (M_dec (snd (split_path path (argumentCount M) argCountPrf))).
              * right; assumption.
              * assumption.
            + assumption.
        Qed.

        Lemma CL_Mintype_suffix_complete_org:
          forall Gamma M
            (M_dec: forall sigma, { CL Gamma M sigma } + { CL Gamma M sigma -> False }),
          forall sigma',
            CL Gamma M sigma' ->
            Forall (fun path =>
                      exists sigma'',
                        sigma'' <= path /\
                        List.In sigma''
                                (filter (fun sigma' => match M_dec sigma' with
                                                    | left _ => true
                                                    | right _ => false end)
                                               (allPathSuffixes (argumentCount M)
                                                                (minimalInstance (Gamma (rootOf M))))))
                   (projT2 (factorize (organize sigma'))).
        Proof.
          intros Gamma M M_dec sigma' M_sigma'.
          generalize (organized_path_factors _ (organize_organized sigma')).
          generalize (CL_Path _ _ _ M_sigma').
          induction (projT2 (factorize (organize sigma')))
            as [ | path n paths IH ].
          - intros; apply Forall_nil.
          - intro ex_prfs.
            generalize (Forall_nth _ _ ex_prfs F1).
            generalize (append_Forall2 _ (cons _ path _ (nil _)) paths ex_prfs).
            intros ex_prf ex_prfs'.
            intro path_prfs.
            generalize (Forall_nth _ _ path_prfs F1).
            generalize (append_Forall2 _ (cons _ path _ (nil _)) paths path_prfs).
            intros path_prfs' path_prf.
            apply Forall_cons.
            + apply CL_Path_minimal_impl; assumption.
            + auto.
        Qed.

         Lemma CL_Mintype_suffix_complete_org':
          forall Gamma M
            (M_dec: forall sigma, { CL Gamma M sigma } + { CL Gamma M sigma -> False }),
          forall sigma',
            CL Gamma M sigma' ->
            exists sigmas,
              intersect (of_list sigmas) <= sigma' /\
              List.Forall (fun sigma' =>
                             List.In sigma'
                                     (filter (fun sigma' => match M_dec sigma' with
                                                         | left _ => true
                                                         | right _ => false end)
                                             (allPathSuffixes (argumentCount M)
                                                              (minimalInstance (Gamma (rootOf M))))))
                          sigmas.
         Proof.
           intros Gamma M M_dec sigma' Msigma'.

           match goal with
           | [ |- exists sigmas, _ /\ ?inprfs ] =>
             assert (proof_organized_instead:
                 (exists sigmas,
                     intersect (of_list sigmas) <= organize sigma' /\
                     inprfs) ->
                 (exists sigmas,
                     intersect (of_list sigmas) <= sigma' /\
                     inprfs))
           end.
           { intros [ sigmas [ le_prf in_prfs ] ].
             exists sigmas; split; [ | assumption ].
             rewrite <- (ST_organize_le sigma').
             assumption. }
           apply proof_organized_instead.
           rewrite (factorize_organized _ (organize_organized sigma')).
           generalize (CL_Mintype_suffix_complete_org _ _ M_dec _ Msigma').
           induction (projT2 (factorize (organize sigma')))
             as [ | path n paths IH ].
           - intro; eexists List.nil; split; [ reflexivity | apply List.Forall_nil ].
           - intro prfs.
             generalize (append_Forall2 _ (cons _ path _ (nil _)) paths prfs).
             generalize (Forall_nth _ _ prfs F1).
             intros path_prf paths_prfs.
             destruct (IH paths_prfs)
               as [ sigmas [ sigmas_le sigmas_in_prfs ] ].
             destruct path_prf
               as [ sigma [ sigma_le sigma_in_prf ] ].
             exists (List.cons sigma sigmas); split.
             + apply ST_intersect.
               apply Forall_cons.
               * rewrite (ST_intersect_nth (of_list (List.cons sigma sigmas)) F1).
                 assumption.
               * apply ST_intersect_ge.
                 rewrite <- sigmas_le.
                 rewrite (ST_intersect_append_le (cons _ sigma _ (nil _)) (of_list sigmas)).
                 apply ST_InterMeetRight.
             + apply List.Forall_cons; assumption.
         Qed.

         Lemma powerset_empty_incl: forall {A} (xs: list A), List.In List.nil (powerset xs).
         Proof.
           intros A xs.
           induction xs as [ | x xs IH ].
           - left; reflexivity.
           - simpl.
             induction (List.map (List.cons x) (powerset xs)).
             + assumption.
             + right; assumption.
         Qed.
             
         Lemma powerset_smaller_set_incl: forall {A} (x: A) xs ys,
             List.In (List.cons x xs) (powerset ys) ->
             List.In xs (powerset ys).
         Proof.
           intros A x xs ys.
           induction ys as [ | y ys IH ].
           - intro devil; inversion devil as [ devil' | devil' ]; inversion devil'.
           - unfold powerset.
             fold (powerset ys).
             intro in_app.
             destruct (in_app_or _ _ _ in_app) as [ inleft | inright ].
             + apply in_app_iff.
               right.
               clear in_app IH.
               induction (powerset ys).
               * contradiction.
               * inversion inleft as [ eq | ].
                 { left; inversion eq; reflexivity. }
                 { right; auto. }
             + apply in_or_app; right; auto.
         Qed.

         Lemma powerset_split: forall {A} xs (y: A) ys,
             List.In xs (powerset (List.cons y ys)) ->
             List.In xs (List.map (List.cons y) (powerset ys)) \/
             List.In xs (powerset ys).
         Proof.
           intros A xs.
           induction xs as [ | x xs IH ].
           - intros; right; apply powerset_empty_incl.
           - intros y ys xxs_in.
             unfold powerset in xxs_in.
             fold (powerset ys) in xxs_in.
             apply in_app_or.
             assumption.
         Qed.



         Lemma ListIn_map_cons: forall {A} (x: A) xs ys,
             List.In ys (List.map (List.cons x) xs) -> exists ys', ys = List.cons x ys' /\ List.In ys' xs.
         Proof.
           intros A x xs.
           induction xs as [ | x' xs IH ].
           - intros ? devil; inversion devil.
           - intros ys in_prf.
             destruct in_prf as [ eq | in_rest ].
             + destruct ys as [ | y ys ].
               * inversion eq.
               * inversion eq.
                 eexists; split; [ reflexivity | left; reflexivity ].
             + destruct (IH _ in_rest) as [ ? [ ? ? ]].
               eexists; split; [ eassumption | right; eassumption ].
         Qed.

         Lemma ListIn_map_cons': forall {A} (x: A) xs ys,
             List.In xs ys -> List.In (List.cons x xs) (List.map (List.cons x) ys).
         Proof.
           intros A x xs ys.
           revert xs.
           induction ys.
           - intros ? devil; inversion devil.
           - intros xs in_prf.
             destruct in_prf as [ eq | ].
             + inversion eq.
               left; reflexivity.
             + right; auto.
         Qed.
         
        

         Lemma powerset_spec {A: Type} {A_dec : forall (x y : A), { x = y } + { x <> y }}:
           forall (x : A) xs ys,
             List.In x ys ->
             List.In xs (powerset ys) ->
             exists xs',
               List.In xs' (powerset ys) /\
               Permutation (if In_dec A_dec x xs then xs else List.cons x xs) xs'.
         Proof.
           intros x xs ys.
           revert xs.
           induction ys as [ | y ys IH ].
           - intros ? devil; inversion devil.
           - intros xs x_in xs_in.
             destruct (In_dec _ x xs) as [ x_in_xs | x_not_in_xs ].
             + simpl in xs_in.
               destruct (in_app_or _ _ _ xs_in) as [ xs_inl | xs_inr ].
               * destruct (ListIn_map_cons _ _ _ xs_inl) as [ xs' [ xs_eq xs'_in ] ].
                 exists (List.cons y xs'); split.
                 { apply in_or_app; left; apply ListIn_map_cons'; assumption. }
                 { rewrite xs_eq; reflexivity. }
               * exists xs; split.
                 { apply in_or_app; right; assumption. }
                 { reflexivity. }
             + simpl in x_in.
               destruct x_in as [ x_eq | x_not_eq ].
               * destruct (in_app_or _ _ _ xs_in) as [ xs_inl | xs_inr ].
                 { destruct (ListIn_map_cons _ _ _ xs_inl) as [ xs' [ xs_eq xs'_in ] ].
                   rewrite x_eq in xs_eq.
                   rewrite xs_eq in x_not_in_xs.
                   assert False; [ apply x_not_in_xs; left; reflexivity | contradiction ]. }
                 { exists (List.cons x xs); split.
                   - apply in_or_app.
                     left.
                     rewrite x_eq.
                     apply ListIn_map_cons'.
                     assumption.
                   - reflexivity. }
               * destruct (in_app_or _ _ _ xs_in) as [ xs_inl | xs_inr ].
                 { destruct (ListIn_map_cons _ _ _ xs_inl) as [ xs' [ xs_eq xs'_in ] ].
                   destruct (IH _ x_not_eq xs'_in) as [ xs_res [ xs_res_in xs_res_prem ] ].
                   exists (List.cons y xs_res); split.
                   - apply in_or_app.
                     left.
                     apply ListIn_map_cons'.
                     assumption.
                   - rewrite xs_eq.
                     destruct (In_dec _ x xs') as [ x_in_xs' | ].
                     + rewrite xs_eq in x_not_in_xs.
                       assert False; [ apply x_not_in_xs; right; assumption | contradiction ].
                     + rewrite (Permutation_middle (List.cons y List.nil) xs' x).
                       simpl.
                       rewrite xs_res_prem.
                       reflexivity. }
                 { generalize (IH _ x_not_eq xs_inr).
                   destruct (In_dec A_dec x xs).
                   - contradiction.
                   - intro prf.
                     destruct prf as [ ? [ ? ? ] ].
                     eexists; split; [ | eassumption ].
                     apply in_or_app.
                     right; assumption. }
         Qed.
         
         Fixpoint deduplicate {A: Type} {A_dec: forall (x y: A), {x = y} + {x <> y}} (xs: list A): list A :=
           match xs with
           | List.cons x xs =>
             if In_dec A_dec x xs
             then @deduplicate _ A_dec xs
             else List.cons x (@deduplicate _ A_dec xs)
           | List.nil => List.nil
           end.

         Lemma deduplicate_spec {A: Type} {A_dec: forall (x y: A), {x = y} + {x <> y}}: forall (x: A) xs,
             List.In x xs <-> List.In x (@deduplicate _ A_dec xs).
         Proof.
           intros x xs.
           induction xs as [ | x' xs IH ].
           - split; intro devil; inversion devil.
           - split.
             + intro prf.
               inversion prf as [ eq | in_rest ].
               * simpl.
                 destruct (In_dec A_dec x' xs) as [ in_xs | not_in_xs ].
                 { rewrite eq in in_xs; apply IH; assumption. }
                 { left; rewrite eq; reflexivity. }
               * simpl.
                 destruct (In_dec A_dec x' xs) as [ in_xs | not_in_xs ].
                 { apply IH; assumption. }
                 { right; apply IH; assumption. }
             + intro prf.
               simpl in prf.
               destruct (In_dec A_dec x' xs) as [ in_xs | not_in_xs ].
               * right; apply IH; assumption.
               * inversion prf as [ eq | in_rest ].
                 { rewrite eq; left; reflexivity. }
                 { right; apply IH; assumption. }
         Qed.
         
         Lemma powerset_permut_incl {A: Type} {A_dec: forall (x y : A), {x = y} + {x <> y}}:
           forall (xs: list A) ys,
             List.Forall (fun x' => List.In x' ys) xs ->
             exists xs',
               List.In xs' (powerset ys) /\
               Permutation (@deduplicate _ A_dec xs) xs'.
         Proof.
           intros xs.
           induction xs as [ | x xs IH ].
           - intros.
             exists List.nil; split.
             + apply powerset_empty_incl.
             + reflexivity.
           - intros ys prf.
             inversion prf as [ | ? ? x_prf xs_prf ].
             simpl.
             generalize (IH _ xs_prf).
             intro IH'.
             destruct IH' as [ xs' [ in_xs' perm_xs' ] ].
             destruct (In_dec A_dec x xs) as [ in_x_xs | not_in_x_xs ].
             + exists xs'; split.
               * assumption.
               * assumption.
             + destruct (@powerset_spec _ A_dec x xs' ys x_prf in_xs') as [ xs'' [ in_xs'' perm_xs'' ] ].
               exists xs''; split.
               * assumption.
               * assert (x_dedup : List.In x (@deduplicate _ A_dec xs) -> False).
                 { intro devil.
                   apply not_in_x_xs.
                   apply (@deduplicate_spec _ A_dec).
                   assumption. }
                 destruct (In_dec A_dec x xs') as [ in_x_xs' | ].
                 { assert False.
                   { apply x_dedup.
                     eapply Permutation_in.
                     - symmetry; eassumption.
                     - assumption. }
                   contradiction. }
                 { rewrite perm_xs'.
                   assumption. }
         Qed.

         Lemma powerset_permute_prop {A: Type} {A_dec: forall (x y : A), {x = y} + { x <> y }}:
           forall (P : list A -> Prop) xs ys,
             P (@deduplicate _ A_dec xs) ->
             (forall xs ys, Permutation (@deduplicate _ A_dec xs) ys -> P (@deduplicate _ A_dec xs) -> P ys) ->
             List.Forall (fun x => List.In x ys) xs ->
             List.Exists P (powerset ys).
         Proof.
           intros P xs ys Pxs P_stable xs_in.
           destruct (@powerset_permut_incl _ A_dec xs ys xs_in) as [ xs' [ in_xs' permut_xs' ] ].
           induction (powerset ys).
           - inversion in_xs'.
           - inversion in_xs' as [ eq | in_tl ].
             + apply List.Exists_cons_hd.
               rewrite eq.
               apply (P_stable _ _ permut_xs' Pxs).
             + apply List.Exists_cons_tl.
               auto.
         Qed.

         Lemma ListIn_In: forall {A: Type} xs (x: A), List.In x xs -> exists k, nth (of_list xs) k = x.
         Proof.
           intros A xs x.
           induction xs as [ | x' xs IH ].
           - intro devil; inversion devil.
           - intro prf.
             destruct prf as [ | in_rest ].
             + exists F1; assumption.
             + destruct (IH in_rest) as [ k prf ].
               exists (FS k); assumption.
         Qed.

         Lemma In_ListIn: forall {A: Type} xs (x: A) k, nth (of_list xs) k = x -> List.In x xs.
         Proof.
           intros A xs x.
           induction xs as [ | x' xs IH ].
           - intro devil; inversion devil.
           - intro k.
             apply (Fin.caseS' k).
             + intro; left; assumption.
             + simpl; intros; right; eapply IH; eassumption.
         Qed.

         Lemma ST_deduplicate: forall sigmas,
             intersect (of_list (@deduplicate _ IntersectionType_eq_dec sigmas)) <= intersect (of_list sigmas).
         Proof.
           intro sigmas.
           induction sigmas as [ | sigma sigmas IH ].
           - reflexivity.
           - simpl.
             destruct (In_dec IntersectionType_eq_dec sigma sigmas) as [ in_sigma_sigmas | ].
             + destruct sigmas as [ | ].
               * inversion in_sigma_sigmas.
               * apply ST_Both.
                 { destruct (ListIn_In _ _ (proj1 (@deduplicate_spec _ IntersectionType_eq_dec _ _)
                                                  in_sigma_sigmas))
                     as [ pos pos_eq ].
                   rewrite <- pos_eq.
                   apply ST_intersect_nth. }
                 { assumption. }
             + destruct sigmas as [ | sigma' sigmas ].
               * reflexivity.
               * apply ST_Both.
                 { simpl of_list.
                   match goal with
                   | [ |- intersect ?xs <= _ ] => apply (ST_intersect_nth xs F1)
                   end. }
                 { simpl of_list.                   
                   match goal with
                   | [ |- intersect (cons _ sigma _ ?xs) <= _ ] =>
                     rewrite (ST_intersect_append_le (cons _ sigma _ (nil _)) xs)
                   end.
                   rewrite ST_InterMeetRight.
                   assumption. }
         Qed.

         
         Lemma ST_permutation: forall sigmas taus,
             Permutation sigmas taus ->
             intersect (of_list sigmas) <= intersect (of_list taus).
         Proof.
           intros sigmas taus perm.
           apply ST_intersect.
           apply nth_Forall.
           intro tau_pos.
           generalize (In_ListIn _ _ _ (eq_refl (nth (of_list taus) tau_pos))).
           intro taupos_in_taus.
           generalize (Permutation_in _ (Permutation_sym perm) taupos_in_taus).
           intro taupos_in_sigmas.
           destruct (ListIn_In _ _ taupos_in_sigmas) as [ k eq ].
           rewrite <- eq.
           apply ST_intersect_nth.
         Qed.
         
         Lemma powerset_le_permute:
           forall sigma' sigmas',
           (exists sigmas,
               intersect (of_list sigmas) <= sigma' /\
               List.Forall (fun sigma' => List.In sigma' sigmas') sigmas) ->
           (exists sigma,
               sigma <= sigma' /\
               List.In sigma (List.map (fun taus => intersect (of_list taus)) (powerset sigmas'))).
         Proof.
           intros sigma' sigmas' prf.
           destruct prf as [ sigmas [ sigmas_le in_prfs ] ].
           destruct (@powerset_permut_incl _ IntersectionType_eq_dec _ _ in_prfs)
             as [ taus [ in_sigmas' perm_taus ] ].
           exists (intersect (of_list taus)); split.
           - rewrite (ST_permutation _ _ (Permutation_sym perm_taus)).
             rewrite ST_deduplicate.
             assumption.
           - apply (List.in_map (fun x => intersect (of_list x))).
             assumption.
         Qed.    
         
         Lemma CL_Mintype_suffix_complete:
           forall Gamma M
             (M_dec: forall sigma, { CL Gamma M sigma } + { CL Gamma M sigma -> False }),
           forall sigma,
             CL Gamma M sigma ->
             exists sigma',
               sigma' <= sigma /\
               List.In sigma'
                       (List.map (fun xs => intersect (of_list xs))
                                 (powerset (filter (fun sigma' => match M_dec sigma' with
                                                               | left _ => true
                                                               | right _ => false end)
                                                   (allPathSuffixes (argumentCount M)
                                                                    (minimalInstance
                                                                       (Gamma (rootOf M))))))).
         Proof.
           intros Gamma M M_dec sigma Msigma.
           apply powerset_le_permute.
           generalize (CL_Mintype_suffix_complete_org _ _ M_dec _ Msigma).
           intro prfs.
           generalize (ST_organize_le sigma).
           rewrite (factorize_organized _ (organize_organized sigma)).
           intro sigma_ge.
           match goal with
           | [ |- exists sigmas, intersect (of_list sigmas) <= sigma /\ ?rest sigmas ] =>
             assert (proof_instead :
                       (exists sigmas, intersect (of_list sigmas) <=
                                  intersect (projT2 (factorize (organize sigma))) /\
                                  rest sigmas) ->
                       (exists sigmas, intersect (of_list sigmas) <= sigma /\
                                  rest sigmas))
           end.
           { intros [ sigmas [ sigmas_le prfs' ] ].
             eexists; split; [ | eassumption ].
             rewrite sigmas_le.
             assumption. }
           apply proof_instead.
           clear proof_instead sigma_ge.           
           induction prfs as [ | n sigma' sigmas prf prfs IH ].
           - exists List.nil; split.
             + reflexivity.
             + apply List.Forall_nil.
           - destruct prf as [ tau [ tau_le tau_in ] ].
             destruct IH as [ taus [ taus_le taus_in ] ].
             exists (List.cons tau taus); split.
             + rewrite (ST_intersect_append_le (cons _ tau _ (nil _)) (of_list taus)).
               rewrite <- (ST_intersect_append_ge (cons _ sigma' _ (nil _))  sigmas).
               apply ST_SubtypeDistrib; assumption.
             + apply List.Forall_cons; assumption.
         Qed.

         Lemma CL_Mintype_suffix_sound':
          forall Gamma M
            (M_dec: forall sigma, { CL Gamma M sigma } + { CL Gamma M sigma -> False }),
          forall sigma',
            List.In sigma'
                    (filter (fun sigma' => match M_dec sigma' with | left _ => true | right _ => false end)
                            (allPathSuffixes (argumentCount M)
                                             (minimalInstance (Gamma (rootOf M))))) ->
            CL Gamma M sigma'.
         Proof.
          intros Gamma M M_dec sigma'.
          match goal with
          | [ |- List.In _ (List.filter _ ?xs) -> _ ] => induction xs as [ | hd tl IH ]
          end.
          - intro devil; inversion devil.
          - intro prf.
            unfold List.In in prf.
            simpl in prf.
            revert prf.
            destruct (M_dec hd).
            + intro prf.
              inversion prf as [ prf_hd | prf_tl ].
              * rewrite <- prf_hd; assumption.
              * auto.
            + intro; auto.
        Qed.

        Lemma powerset_hd_in: forall {A: Type} (x: A) xs ys,
            List.In (List.cons x xs) (powerset ys) ->
            List.In x ys.
        Proof.
          intros A x xs ys.
          revert xs.
          induction ys.
          - intros ? devil; inversion devil as [ devil' | devil']; inversion devil'.
          - intros xxs xxs_in.
            destruct (in_app_or _ _ _ xxs_in) as [ inl | inr ].
            + destruct (ListIn_map_cons _ _ _ inl) as [ ? [ x_eq nil_in ] ].
              inversion x_eq; left; reflexivity.
            + right; eauto.
        Qed.
                  
        Lemma powerset_spec_in: forall {A: Type} (xs ys: list A),
            List.In xs (powerset ys) -> List.Forall (fun x => List.In x ys) xs.
        Proof.
          intros A xs.
          induction xs as [ | x xs IH ].
          - intros; apply List.Forall_nil.
          - intros ys in_xs.
            destruct ys.
            + inversion in_xs as [ devil | devil ].
              * inversion devil.
              * inversion devil.
            + simpl in in_xs.
              destruct (in_app_or _ _ _ in_xs) as [ inl | inr ].
              * destruct (ListIn_map_cons _ _ _ inl) as [ ys' [ xs_eq xs_in' ] ].
                inversion xs_eq as [ [ hd_eq tl_eq ] ].
                apply List.Forall_cons.
                { left; reflexivity. }
                { rewrite tl_eq in IH.
                  apply IH.
                  apply in_or_app; right.
                  assumption. }
              * apply List.Forall_cons.
                { eapply powerset_hd_in; eassumption. }
                { apply Forall_forall.
                  intros x' x'_in_xs.
                  generalize (IH _ (powerset_smaller_set_incl _ _ _ inr)).
                  intro xs_in_ys.
                  right.
                  revert x'_in_xs xs_in_ys.
                  clear ...
                  intros x'_in_xs xs_in_ys.
                  induction xs.
                  - inversion x'_in_xs.
                  - destruct x'_in_xs as [ eq | inr ].
                    + rewrite eq in *.
                      inversion xs_in_ys.
                      assumption.
                    + inversion xs_in_ys.
                      auto. }
        Qed.
            
        Lemma CL_Mintype_suffix_sound:
           forall Gamma M
             (M_dec: forall sigma, { CL Gamma M sigma } + { CL Gamma M sigma -> False }) S,
             WellFormed S ->
             forall sigma,
               (exists sigma',
                   sigma' <= sigma /\
                   List.In sigma'
                         (List.map (fun xs => intersect (of_list xs))
                                   (powerset (filter (fun sigma' => match M_dec sigma' with
                                                                 | left _ => true
                                                                 | right _ => false end)
                                                     (allPathSuffixes (argumentCount M)
                                                                      (minimalInstance
                                                                         (Gamma (rootOf M)))))))) ->
               CL Gamma M sigma.
        Proof.
          intros Gamma M M_dec S WF_S sigma prf.
          destruct prf as [ sigma' [ sigma'_le sigma'_in_powerset ] ].
          eapply CL_ST; [ | apply sigma'_le ].
          generalize (proj1 (in_map_iff (fun xs => intersect (of_list xs)) _ _) sigma'_in_powerset).
          intros [ sigmas' [ sigmas'_eq sigmas'_in ] ].
          generalize (powerset_spec_in _ _ sigmas'_in).
          intro sigmas'_prfs.
          rewrite <- sigmas'_eq.
          destruct (sigmas') as [ | hd tl ].
          - eapply CL_omega; eassumption.
          - apply (CL_intersect_many).
            apply nth_Forall.
            intro k.
            generalize (In_ListIn _ _ _ (eq_refl (nth (of_list (List.cons hd tl)) k))).
            intro nth_in.
            apply (CL_Mintype_suffix_sound' _ _ M_dec).
            generalize (proj1 (List.Forall_forall _ _) sigmas'_prfs).
            intro sigmas'_prf.
            apply sigmas'_prf.
            assumption.
        Qed.
            
        Lemma CL_finite_dec: forall Gamma M sigma, { CL Gamma M sigma } + { CL Gamma M sigma -> False }.
        Proof.
          intros Gamma M.
          destruct (cardinality _ SubstitutionSpace_finite) eqn:card_eq.
          - intro sigma.
            right.
            intro prf.
             induction prf as [ ? S WF_S | | | ]; try solve [ contradiction ].
             generalize (toFin _ SubstitutionSpace_finite (exist _ S WF_S)).
             rewrite card_eq.
             intro k; inversion k.
          - induction M as [ c | M IHM N IHN ].
            + intro sigma.
              destruct (ST_dec (minimalInstance (Gamma c)) sigma).
              * left.
                eapply CL_ST; [ | eassumption ].
                apply MinimalType_sound.
                rewrite card_eq.
                apply (Nat.lt_0_succ).
              * right.
                intro prf.
                generalize (MinimalType_minimal _ _ _ prf).
                assumption.
            + intro sigma.
              assert (exS : { S : _ | WellFormed S }).
              { eapply (fromFin _ SubstitutionSpace_finite).
                rewrite card_eq.
                exact F1. }
              destruct exS as [ S WF_S ].
              apply CL_MP_inv_dec_sound.
              assert (M_dec:
                        {List.Exists
                           (fun sigma' => CL Gamma M (Arrow sigma' sigma))
                           (List.map (fun xs => intersect (of_list xs))
                                     (powerset (filter (fun sigma' => match IHN sigma' with
                                                                   | left _ => true
                                                                   | right _ => false end)
                                                       (allPathSuffixes (argumentCount N)
                                                                        (minimalInstance
                                                                           (Gamma (rootOf N)))))))} +
                        {List.Exists
                           (fun sigma' => CL Gamma M (Arrow sigma' sigma))
                           (List.map (fun xs => intersect (of_list xs))
                                     (powerset (filter (fun sigma' => match IHN sigma' with
                                                                   | left _ => true
                                                                   | right _ => false end)
                                                       (allPathSuffixes (argumentCount N)
                                                                        (minimalInstance
                                                                           (Gamma (rootOf N))))))) -> False}).
              { apply List.Exists_dec.
                intro x; eapply IHM. }
              destruct M_dec as [ Mprf | Mdisprf ].
              * left.
                destruct (proj1 (List.Exists_exists _ _) Mprf) as [ sigma' [ in_prf p_prf ] ].
                { exists sigma'; split.
                  - assumption.
                  - apply (CL_Mintype_suffix_sound _ _ IHN S WF_S).
                    eexists; split; [ reflexivity | eassumption ]. }
              * right.
                intro sigma_prf.
                destruct sigma_prf as [ sigma' [ Mprf Nprf ] ].
                destruct (CL_Mintype_suffix_complete _ _ IHN _ Nprf) as [ sigma'' [ sigma''_le sigma''_in ] ].
                assert (Mprf': CL Gamma M (Arrow sigma'' sigma)).
                { eapply CL_ST; [ eassumption | ].
                  apply ST_CoContra; [ assumption | reflexivity ]. }
                generalize (proj2 (List.Exists_exists _ _)
                                  (ex_intro (fun sigma' =>
                                               List.In sigma'
                                                       (List.map (fun xs => intersect (of_list xs))
                                                                 (powerset
                                                                    (filter (fun sigma' =>
                                                                               if IHN sigma' then true else false)
                                                                            (allPathSuffixes (argumentCount N)
                                                                                             (minimalInstance (Gamma (rootOf N))))))) /\
                                               CL Gamma M (Arrow sigma' sigma))
                                            sigma'' (conj sigma''_in Mprf'))).
                assumption.
        Qed.

        Definition MaximalSourceCount tau :=
          fold_left (fun s path => max s (src_count path)) 0
                    (projT2 (factorize (organize tau))).

        Lemma fold_left_append {A B: Type} {m n: nat}:
          forall (xs : t A m) (ys: t A n) (s: B) f,
            fold_left f s (append xs ys) = fold_left f (fold_left f s xs) ys.
        Proof.
          intro xs.
          induction xs.
          - intros; reflexivity.
          - intros; simpl; auto.
        Qed.

        Lemma max_count_fold {n : nat}: forall (xs: t IntersectionType n) x s,
            (x <= s)%nat -> (x <= fold_left (fun s tau => max s (src_count tau)) s xs)%nat.
        Proof.
          intro xs.
          induction xs as [ | x' n xs IH ].
          - intros; assumption.
          - intros x s x_le.
            simpl.
            eapply IH.
            rewrite x_le.
            apply (Nat.max_case_strong s (src_count x')).
            + intro; reflexivity.
            + intro; assumption.
        Qed.

        Lemma max_count_fold_cons {n : nat}: forall (xs: t IntersectionType n) x s,
            (fold_left (fun s tau => max s (src_count tau)) s xs <=
             fold_left (fun s tau => max s (src_count tau)) s (cons _ x _ xs))%nat.
        Proof.
          intro xs.
          simpl.
          induction xs as [ | x' n xs IH ];
            intros x s.
          - simpl.
            apply (Nat.max_case_strong s (src_count x)).
            + intro; reflexivity.
            + intro; assumption.
          - simpl.
            rewrite <- Nat.max_assoc.
            rewrite (Nat.max_comm (src_count x) (src_count x')).
            rewrite Nat.max_assoc.
            apply IH.
        Qed.

        Lemma max_count_fold_append {m n : nat}: forall (xs: t IntersectionType m) (ys: t IntersectionType n) s,
            (fold_left (fun s tau => max s (src_count tau)) s ys <=
             fold_left (fun s tau => max s (src_count tau)) s (append xs ys))%nat.
        Proof.
          intro xs.
          simpl.
          induction xs as [ | x m xs IH ];
            intros ys s.
          - reflexivity.
          - simpl append.
            rewrite max_count_fold_cons.
            apply IH.
        Qed.

        Lemma max_count_nth {n : nat}: forall (xs: t IntersectionType n) k s,
            (src_count (nth xs k) <= fold_left (fun s tau => max s (src_count tau)) s xs)%nat.
        Proof.
          intros xs.
          induction xs as [ | x n xs IH ]; intros k s.
          - inversion k.
          - apply (Fin.caseS' k).
            + simpl.
              apply max_count_fold.
              apply Nat.le_max_r.
            + intro k'.
              simpl.
              apply IH.
        Qed.
        
        Lemma MaximalSourceCount_intersection: forall {n} (taus: t IntersectionType n),
            Forall (fun tau => (MaximalSourceCount tau <= MaximalSourceCount (intersect taus))%nat) taus.
        Proof.
          intros n taus.
          induction taus as [ | tau n taus IH ].
          - apply Forall_nil.
          - apply Forall_cons.
            + unfold MaximalSourceCount.
              destruct taus as [ | tau' n' taus ].
              * reflexivity.
              * simpl.
                rewrite (factorize_intersect_append (projT2 (factorize (organize tau))) _).
                simpl.
                rewrite fold_left_append.
                rewrite <- (factorize_organized _ (organize_organized tau)).
                apply max_count_fold.
                reflexivity.
            + eapply Forall_ap; [ | eassumption ].
              apply nth_Forall.
              intros k prf.
              rewrite prf.
              unfold MaximalSourceCount.
              clear IH prf k.
              destruct taus as [ | tau' n taus ].
              * apply le_0_n.
              * simpl.
                rewrite (factorize_intersect_append (projT2 (factorize (organize tau))) _).
                simpl.
                generalize (factorize_organized _ (organize_organized (intersect (cons _ tau' _ taus)))).
                intro rhs_eq.
                simpl in rhs_eq.
                rewrite <- rhs_eq.
                apply max_count_fold_append.
        Qed.

        
          
        Lemma MaximalSourceCount_Maximal: forall (Gamma: Context) c S,
            WellFormed S ->
            Forall (fun path => (src_count path <= MaximalSourceCount (minimalInstance (Gamma c)))%nat)
                   (projT2 (factorize (organize (Apply S (Gamma c))))).
        Proof.
          intros Gamma c S WF_S.
          unfold minimalInstance.
          match goal with
          | [|- Forall (fun path => (_ <= MaximalSourceCount (intersect ?xs))%nat) _ ] =>
            generalize (Forall_nth _ _ (MaximalSourceCount_intersection xs))
          end.
          intro prf.
          apply nth_Forall.
          intro k.
          generalize (prf (toFin _ SubstitutionSpace_finite (exist _ S WF_S))).
          intro nth_le.
          rewrite <- nth_le.
          rewrite (nth_map _ _ _ _ eq_refl).
          rewrite (positions_spec).
          rewrite (fromToFin_id _ SubstitutionSpace_finite (exist _ S WF_S)).
          unfold MaximalSourceCount.
          apply max_count_nth.
        Qed.
        
        Lemma CL_MaximalArgumentCount: forall Gamma M tau,
            (Omega tau -> False) ->
            CL Gamma M tau -> (argumentCount M <= MaximalSourceCount (minimalInstance (Gamma (rootOf M))))%nat.
        Proof.
          intros Gamma M tau not_omega_tau prf.
          generalize (CL_Path _ _ _ prf).
          intro prf'; clear prf.
          assert (factors_not_empty : projT1 (factorize (organize tau)) = 0 -> False).
          { intro devil.
            assert (devil' : omega <= intersect (projT2 (factorize (organize tau)))).
            { revert devil.
              clear ...
              intro devil.
              destruct (factorize (organize tau)) as [ n xs ].
              simpl in devil.
              revert xs.
              rewrite devil.
              apply case0.
              reflexivity. }
            rewrite <- (factorize_organized _ (organize_organized tau)) in devil'.
            rewrite (ST_organize_le tau) in devil'.
            apply not_omega_tau.
            eapply Omega_complete; [ eassumption | exact I ]. }
          induction prf' as [ | n path paths path_prf paths_prfs IH n_eq [ path_eq paths_eq ] ].
          - contradiction (factors_not_empty eq_refl).
          - destruct n. 
            + destruct path_prf as [ S [ WF_S ex_prf ] ].
              generalize( MaximalSourceCount_Maximal Gamma (rootOf M) S WF_S).
              induction ex_prf as [ n path' paths' [ pathPrf [ argCountPrf _ ] ] | n path' paths' ].
              * rewrite argCountPrf.
                intro path_prfs; inversion path_prfs; assumption.
              * intro path_prfs.
                generalize (append_Forall2 _ (cons _ path' _ (nil _)) paths' path_prfs).
                assumption.
            + apply IH; intro devil; inversion devil.
        Qed.

        Definition allSplitPaths (n: nat) (sigma: IntersectionType): list (t IntersectionType n * IntersectionType) :=
          (fix allSplitPaths_rec m (sigmas: t IntersectionType m): list (t IntersectionType n * IntersectionType) :=
             match sigmas with
             | cons _ path _ paths =>
               match le_dec n (src_count path) with
               | left prf =>
                 List.cons (split_path path n prf) (allSplitPaths_rec _ paths)
               | right _ =>
                 allSplitPaths_rec _ paths
               end
             | nil _ => List.nil
             end) _ (projT2 (factorize (organize sigma))).

        Lemma allSplitPaths_sound:
          forall (n: nat) (sigma: IntersectionType),
            List.Forall (fun path =>
                           Exists (fun path' => mkArrow (fst path) (snd path) = path')
                                  (projT2 (factorize (organize sigma))))
                        (allSplitPaths n sigma).
        Proof.
          intros n sigma.
          unfold allSplitPaths.
          induction (projT2 (factorize (organize sigma))) as [ | path m paths IH ].
          - apply List.Forall_nil.
          - destruct (le_dec n (src_count path)).
            + apply List.Forall_cons.
              * apply Exists_cons_hd.
                apply split_path_spec.
              * induction IH.
                { apply List.Forall_nil. }
                { apply List.Forall_cons.
                  - apply Exists_cons_tl.
                    assumption.
                  - assumption. }
            + induction IH.
              * apply List.Forall_nil.
              * apply List.Forall_cons.
                { apply Exists_cons_tl; assumption. }
                { assumption. }
        Qed.

        Lemma allSplitPaths_complete:
          forall n (sigma: IntersectionType),
              Forall (fun path =>
                        (n <= src_count path)%nat ->
                        List.Exists (fun path' => mkArrow (fst path') (snd path') = path)
                                    (allSplitPaths n sigma))
                     (projT2 (factorize (organize sigma))).
        Proof.
          intros n sigma.
          unfold allSplitPaths.
          induction (projT2 (factorize (organize sigma))) as [ | path m paths IH ].
          - apply Forall_nil.
          - apply Forall_cons.
            + intro srcCountPrf.
              destruct (le_dec n (src_count path)); [ | contradiction ].
              apply List.Exists_cons_hd.
              apply split_path_spec.
            + eapply Forall_ap; [ | exact IH ].
              apply Forall_tautology.
              intros path' prf.
              intro patk'_ok.
              destruct (le_dec n (src_count path)).
              * apply List.Exists_cons_tl; auto.
              * auto.
        Qed.
                

        Definition allPossibleInhabitants (Gamma: Context) (tau: IntersectionType) (c: CombinatorSymbol) (n: nat):
          list (t IntersectionType n * IntersectionType) :=
          List.filter (fun path => if ST_dec (snd path) tau then true else false)
          (List.map (fun paths =>
                       (intersect_pointwise (of_list (List.map fst paths)),
                        intersect (of_list (List.map snd paths))))
                    (powerset (allSplitPaths n (minimalInstance (Gamma c))))).

        Lemma powerset_p: forall {A: Type} (P : A -> Prop) xs,
            List.Forall P xs ->
            List.Forall (List.Forall P) (powerset xs).
        Proof.
          intros A P xs prf.
          apply List.Forall_forall.
          intros xs' in_prf.
          apply List.Forall_forall.
          intros x x_in_xs.
          eapply (proj1 (List.Forall_forall _ _)).
          + apply prf.
          + generalize (powerset_spec_in _ _ in_prf).
            intro xs'_prfs. 
            apply (proj1 (List.Forall_forall _ _) xs'_prfs).
            assumption.
        Qed.

        Lemma powerset_map: forall {A B: Type} (f: A -> B) xs,
            powerset (List.map f xs) = List.map (List.map f) (powerset xs).
        Proof.
          intros A B f xs.
          induction xs as [ | x xs IH ].
          - reflexivity.
          - simpl List.map.
            simpl powerset.
            rewrite (List.map_app).
            rewrite IH.
            apply (f_equal (fun xs => xs ++ _)).
            rewrite (List.map_map).
            rewrite (List.map_map).
            simpl.
            reflexivity.
        Qed.            
        
        Lemma allPossibleInhabitants_sound:
          forall Gamma tau c n,
            { S : _ | WellFormed S } ->
            List.Forall (fun arrow =>
                           forall arguments,
                             Forall2 (CL Gamma) arguments (fst arrow) ->
                             CL Gamma (applyAll (Symbol c) arguments) tau)
                        (allPossibleInhabitants Gamma tau c n).
        Proof.
          intros Gamma tau c n ex_S.
          unfold allPossibleInhabitants.
          generalize (powerset_p _ _ (allSplitPaths_sound n (minimalInstance (Gamma c)))).
          induction (powerset (allSplitPaths n (minimalInstance (Gamma c)))) as [ | paths pathss IH ].
          - intro; apply List.Forall_nil.
          - intro prfs.
            inversion prfs as [ | hd tl hd_prf tl_prfs [ hd_eq tgt_eq ] ].
            clear hd_eq tgt_eq hd tl.
            simpl.
            destruct (ST_dec (intersect (of_list (List.map snd paths)))) as [ tgt_le | not_tgt_le ].
            + apply List.Forall_cons.
              * intros arguments argPrfs.
                eapply CL_ST; [ | eassumption ].
                clear tgt_le.
                destruct paths as  [ | path paths ].
                { destruct ex_S as [ S WF_S ].
                  apply (CL_omega S WF_S). }
                { apply (CL_intersect_many).
                  assert (length_eq: S (length (List.map snd paths)) = length (List.map snd (List.cons path paths))).
                  { reflexivity. }
                  rewrite <- (rewrite_vect _ length_eq).
                  simpl in length_eq.
                  rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ length_eq).
                  apply ListForall_Forall.
                  clear prfs IH tl_prfs pathss.
                  revert arguments argPrfs.
                  induction hd_prf as [ | hd tl ex_prf ex_prfs IH' ];
                    intros arguments argPrfs.
                  - apply List.Forall_nil.
                  - apply List.Forall_cons.
                    + generalize (organized_path_factors _ (organize_organized (minimalInstance (Gamma c)))).
                      assert (c_prf: CL Gamma (Symbol c)
                                 (intersect (projT2 (factorize (organize (minimalInstance (Gamma c))))))).
                      { rewrite <- (factorize_organized _ (organize_organized _)).
                        eapply CL_ST; [ | apply ST_organize_ge ].
                        apply MinimalType_sound.
                        destruct SubstitutionSpace_finite as [ card toFin fromFin toFrom_id ].
                        generalize (toFin ex_S).
                        intro k.
                        destruct card.
                        - inversion k.
                        - unfold "_ > _".
                          apply (Nat.add_pos_l 1).
                          auto. }
                      revert c_prf.
                      clear ex_prfs.
                      induction ex_prf as [ ? ex_path ex_paths ex_path_eq | ? ex_path ex_paths ? IH ].
                      * assert (ex_path_src_count : (n <= src_count ex_path)%nat).
                        { rewrite <- ex_path_eq.
                          clear ...
                          destruct hd as [ hd tgt ].
                          induction hd.
                          - apply le_0_n.
                          - apply le_n_S.
                            assumption. }
                        rewrite <- (split_path_spec ex_path _ ex_path_src_count) in ex_path_eq.
                        destruct (mkArrow_inj _ _ _ _ ex_path_eq) as [ fst_eq snd_eq ].
                        rewrite snd_eq.
                        intros c_prf path_prfs.
                        apply CL_ApplyPath.
                        { inversion path_prfs; assumption. }
                        { eapply CL_ST; [ apply c_prf | ].
                          generalize (ST_intersect_nth (cons _ ex_path _ ex_paths) F1).
                          simpl; intro; assumption. }
                        { rewrite <- fst_eq.
                          apply (nth_Forall2).
                          intro k.
                          generalize (Forall2_nth _ _ _ argPrfs k).
                          unfold fst.
                          intro argPrf.
                          rewrite intersect_pointwise_spec in argPrf.
                          eapply CL_ST; [ apply argPrf | ].
                          etransitivity; [ apply (ST_intersect_nth _ F1) | ].
                          rewrite (nth_map _ _ _ _ eq_refl).
                          reflexivity. }
                      * intros c_prf path_prfs.
                        apply IH.
                        { eapply CL_ST; [ apply c_prf | ].
                          rewrite (ST_intersect_append_le (cons _ ex_path _ (nil _)) ex_paths).
                          apply ST_InterMeetRight. }
                        { apply (append_Forall2 _ (cons _ ex_path _ (nil _)) ex_paths path_prfs). }
                    + fold (List.map snd tl).
                      apply IH'.
                      apply (nth_Forall2).
                      intro k.
                      generalize (Forall2_nth _ _ _ argPrfs k).
                      unfold fst.
                      intro argPrf.
                      rewrite intersect_pointwise_spec in argPrf.
                      rewrite intersect_pointwise_spec.
                      eapply CL_ST; [ apply argPrf | ].
                      simpl map.
                      etransitivity; [ apply (ST_intersect_append_le (cons _ (nth (let (x, _) := hd in x) k)
                                                                           _ (nil _)) _) | ].
                      apply ST_InterMeetRight.
                }
              * auto.                        
            + auto.
        Qed.

        Definition sufficient_paths Gamma M tau
                   (paths: list ((t IntersectionType (argumentCount M)) * IntersectionType)) :=
          Forall2 (CL Gamma) (argumentsOf M) (intersect_pointwise (of_list (List.map fst paths))) /\
          (intersect (of_list (List.map snd paths))) <= tau.

        Lemma split_eq: forall n (x y: (t IntersectionType n * IntersectionType)),
            { x = y } + { x <> y }.
        Proof.
          intros n x y.
          destruct (IntersectionType_eq_dec (mkArrow (fst x) (snd x)) (mkArrow (fst y) (snd y)))
            as [ eq | not_eq ].
          - left.
            destruct x; destruct y.
            simpl in eq.
            destruct (mkArrow_inj _ _ _ _ eq) as [ eq1 eq2 ].
            rewrite eq1; rewrite eq2.
            reflexivity.
          - right.
            intro devil.
            rewrite devil in not_eq.
            apply not_eq; reflexivity.
        Qed.

        Lemma exists_deduplicate {A: Type} {A_dec: forall (x y: A), { x = y } + { x <> y }}:
          forall (P : A -> Prop) xs, Exists P (of_list xs) -> Exists P (of_list (@deduplicate _ A_dec xs)).
        Proof.
          intros P xs.
          induction xs as [ | x xs IH ].
          - intro devil; inversion devil.
          - intro ex_prf.
            inversion ex_prf as [ ? ? ? prf_here | ? ? ? prf_there n_eq [ hd_eq tl_eq ] ].
            + generalize (proj1 (@deduplicate_spec _ A_dec x (List.cons x xs)) (or_introl (eq_refl x))).
              intro in_x_dedup.
              induction (deduplicate (List.cons x xs)).
              * inversion in_x_dedup.
              * destruct in_x_dedup as [ eq | in_rest ].
                { rewrite eq.
                  apply Exists_cons_hd.
                  assumption. }
                { apply Exists_cons_tl; auto. }
            + dependent rewrite tl_eq in prf_there.
              unfold deduplicate.
              destruct (In_dec A_dec x xs).
              * auto.
              * apply Exists_cons_tl; auto.
        Qed.

        Lemma exists_permute {A: Type} {A_dec: forall (x y: A), { x = y } + { x <> y }}:
          forall (P : A -> Prop) xs ys,
            Permutation xs ys ->
            Exists P (of_list xs) -> Exists P (of_list ys).
        Proof.
          intros P xs ys perm_xs_ys ex_x.
          assert (ex_x': exists x, List.In x xs /\ P x).
          { revert ex_x; clear ...
            intro ex_x.
            induction xs as [ | ? ? IH ].
            - inversion ex_x.
            - inversion ex_x as [ | ? ? ? prfs_tl n_eq [ hd_eq tl_eq ]].
              + eexists; split; [ apply (or_introl (eq_refl _)) | eassumption ].
              + dependent rewrite tl_eq in prfs_tl.
                destruct (IH prfs_tl) as [ x' [ in_prf prf ] ].
                exists x'; split; [ right; assumption | assumption ]. }
          destruct ex_x' as [ x' [ in_x' prf_x' ] ].
          generalize (Permutation_in _ perm_xs_ys in_x').
          revert prf_x'.
          clear ...
          induction ys.
          - intros ? devil; inversion devil.
          - intros x'_prf in_x'_ys.
            destruct in_x'_ys as [ here | there ].
            + rewrite here.
              apply Exists_cons_hd; assumption.
            + apply Exists_cons_tl; auto.
        Qed.

        Lemma deduplicate_map {A B: Type}
              {A_dec: forall (x y: A), { x = y } + { x <> y }}
              {B_dec: forall (x y: B), { x = y } + { x <> y }}:
          forall xs (f: A -> B),
            (forall x y, f x = f y -> x = y) -> 
            List.map f (@deduplicate _ A_dec xs) = @deduplicate _ B_dec (List.map f xs).
        Proof.
          intros xs f f_inj.
          induction xs as [ | x xs IH ].
          - reflexivity.
          - simpl List.map.
            simpl deduplicate.
            destruct (In_dec A_dec x xs) as [ in_x | not_in_x ].
            + rewrite IH.
              destruct (In_dec B_dec (f x) (List.map f xs)) as [ in_fx | not_in_fx ] .
              * reflexivity.
              * assert False; [ | contradiction ].
                apply not_in_fx.
                clear not_in_fx IH.
                induction xs.
                { inversion in_x. }
                { destruct in_x as [ here | there ].
                  - rewrite here; left; reflexivity.
                  - right; auto. }
            + destruct (In_dec B_dec (f x) (List.map f xs)) as [ in_fx | not_in_fx ] .
              * assert False; [ | contradiction ].
                apply not_in_x.
                clear not_in_x IH.
                induction xs.
                { inversion in_fx. }
                { destruct in_fx as [ here | there ].
                  - rewrite (f_inj _ _ here); left; reflexivity.
                  - right; auto. }
              * simpl; rewrite IH; reflexivity.
        Qed.                  
        
        Lemma sufficient_paths_deduplicate:
          forall Gamma M tau xs,
            sufficient_paths Gamma M tau xs ->
            sufficient_paths Gamma M tau
                             (@deduplicate _ (split_eq _) xs).
        Proof.
          intros Gamma M tau xs.
          unfold sufficient_paths.
          intro prf.
          destruct prf as [ args_inhab tgt_le ].
          split.
          - clear tgt_le.
            induction xs as [ | x xs IH ].
            + assumption.
            + assert (IH': forall k, CL Gamma (nth (argumentsOf M) k)
                                   (nth (intersect_pointwise (of_list (List.map
                                                                         fst
                                                                         (@deduplicate _ (split_eq _) xs)))) k)).
              { intro k.
                apply (fun p => Forall2_nth _ _ _ (IH p) k).
                apply nth_Forall2.
                intro k'.
                generalize (Forall2_nth _ _ _ args_inhab k'); clear args_inhab; intro arg_inhab.
                rewrite (intersect_pointwise_spec) in arg_inhab.
                rewrite (intersect_pointwise_spec).
                eapply CL_ST; [ eassumption | ].
                simpl map.
                rewrite (ST_intersect_append_le (cons _ (nth (fst x) k') _ (nil _))
                                                (map (fun xs => nth xs k') (of_list (List.map fst xs)))).
                apply ST_InterMeetRight. }
              unfold deduplicate.
              destruct (In_dec (split_eq (argumentCount M)) x xs).
              * apply nth_Forall2.
                assumption.
              * apply nth_Forall2.
                intro k.
                rewrite intersect_pointwise_spec.
                assert (CL Gamma (nth (argumentsOf M) k) (nth (fst x) k)).
                { generalize (Forall2_nth _ _ _ args_inhab k); clear args_inhab; intro arg_inhab.
                  rewrite (intersect_pointwise_spec) in arg_inhab.
                  eapply CL_ST; [ eassumption | ].
                  match goal with
                  | [ |- intersect ?xs <= _ ] =>
                    etransitivity; [ apply (ST_intersect_nth xs F1) | ]
                  end.
                  reflexivity. }
                simpl map.
                generalize (IH' k).
                rewrite intersect_pointwise_spec.
                fold (@deduplicate _ (split_eq _) xs).
                destruct (deduplicate xs).
                { intro; simpl; assumption. }
                { eapply CL_II; assumption. }
          - clear args_inhab.
            revert tgt_le.
            revert tau.
            induction xs as [ | x xs IH ]; intros tau tgt_le.
            + assumption.
            + unfold deduplicate.
              destruct (In_dec (split_eq _) x xs) as [ inprf | ].
              * apply IH.
                rewrite <- tgt_le.
                clear IH tgt_le.
                induction xs as [ | x' xs IH ]; [ inversion inprf | ].
                apply ST_Both; [ | reflexivity ].
                inversion inprf as [ here | there ].
                { rewrite here; etransitivity; [ apply (ST_intersect_nth _ F1) | reflexivity ]. }
                { etransitivity; [ apply (ST_intersect_append_le (cons _ (snd x') _ (nil _))
                                                                 (of_list (List.map snd xs))) | ].
                  etransitivity; [ apply ST_InterMeetRight; apply (IH there) | ].
                  etransitivity; [ apply (IH there) | ].
                  etransitivity; [ apply (ST_intersect_nth _ F1) | reflexivity ]. }
              * rewrite <- tgt_le.
                etransitivity; [ apply (ST_intersect_append_le (cons _ (snd x) _ (nil _)) _) | ].
                simpl List.map.
                simpl of_list.
                etransitivity; [ | apply (ST_intersect_append_ge (cons _ (snd x) _ (nil _)) _) ].
                apply ST_SubtypeDistrib; [ reflexivity | apply IH ].
                reflexivity.
        Qed.

        Lemma sufficient_paths_stable:
          forall Gamma M tau xs ys,
            Permutation (@deduplicate _ (split_eq _) xs) ys ->
            sufficient_paths Gamma M tau (@deduplicate _ (split_eq _) xs) ->
            sufficient_paths Gamma M tau ys.
        Proof.
          intros Gamma M tau xs ys perm_xs sufficient_xs.
          unfold sufficient_paths.
          destruct sufficient_xs as [ xs_inhab xs_le ].
          split.
          - apply nth_Forall2.
            intro k.
            eapply CL_ST; [ apply (Forall2_nth _ _ _ xs_inhab k) | ].
            rewrite intersect_pointwise_spec.
            rewrite intersect_pointwise_spec.
            transitivity (intersect (of_list (List.map (fun xs => nth (fst xs) k)
                                                       (@deduplicate _ (split_eq _) xs)))).
            + clear xs_inhab xs_le perm_xs.
              induction (deduplicate xs) as [ | x' xs' IH ]; [ reflexivity | ].
              etransitivity; [ apply (ST_intersect_append_le (cons _ (nth (fst x') k) _ (nil _)) _) | ].
              etransitivity; [ | apply (ST_intersect_append_ge (cons _ (nth (fst x') k) _ (nil _)) _) ].
              apply ST_SubtypeDistrib; [ reflexivity | apply IH ].
            + transitivity (intersect (of_list (List.map (fun xs => nth (fst xs) k) ys))).
              * apply (ST_permutation).
                apply (Permutation_map).
                assumption.
              * clear xs_inhab xs_le perm_xs.
                induction (ys) as [ | y' ys' IH ]; [ reflexivity | ].
                etransitivity; [ apply (ST_intersect_append_le (cons _ (nth (fst y') k) _ (nil _)) _) | ].
                etransitivity; [ | apply (ST_intersect_append_ge (cons _ (nth (fst y') k) _ (nil _)) _) ].
                apply ST_SubtypeDistrib; [ reflexivity | apply IH ].
          - rewrite <- xs_le.
            apply (ST_permutation).
            apply (Permutation_sym).
            apply (Permutation_map).
            assumption.
        Qed.
        
        Lemma allSplitPaths_inter: forall sigma tau n,
            allSplitPaths n (Inter sigma tau) = List.app (allSplitPaths n sigma) (allSplitPaths n tau).
        Proof.
          intros sigma tau n.
          unfold allSplitPaths.
          simpl.
          rewrite (factorize_intersect_append).
          rewrite <- (factorize_organized _ (organize_organized sigma)).
          rewrite <- (factorize_organized _ (organize_organized tau)).
          induction (projT2 (factorize (organize (sigma)))) as [ | path m paths IH ].
          - reflexivity.
          - simpl.
            destruct (le_dec n (src_count path)).
            + simpl.
              apply f_equal.
              exact IH.
            + exact IH.
        Qed.
        
        Lemma allPossibleInhabitants_complete:
          forall Gamma tau M,
            (Omega tau -> False) ->
            CL Gamma M tau ->
            List.Exists (fun arrow =>
                           Forall2 (CL Gamma) (argumentsOf M) (fst arrow) /\
                           (snd arrow) <= tau) (allPossibleInhabitants Gamma tau (rootOf M) (argumentCount M)).
        Proof.
          intros Gamma tau M notOmegaTau Mtau.                    
          set (xs := allSplitPaths (argumentCount M) (minimalInstance (Gamma (rootOf M)))).
          assert (sufficient_ys: exists ys,
                     sufficient_paths Gamma M tau ys /\
                     List.Forall (fun y => List.In y xs) ys).
          { generalize (CL_Path Gamma M tau Mtau).
            intro prfs.
            unfold sufficient_paths.
            assert (proof_instead: forall A (P Q Q' R: A -> Prop),
                       (forall x, Q' x -> Q x) -> (exists x, (P x /\ Q' x) /\ R x) -> exists x, (P x /\ Q x) /\ R x).
            { intros A P Q Q' R f ex.
              inversion ex as [ x [ [ p q' ] r ] ].
              eexists; split; [ split; [ | eapply f ] | ]; eassumption. }
            apply (proof_instead _ _ _ (fun xs => intersect (of_list (List.map snd xs)) <=
                                               intersect (projT2 (factorize (organize tau)))) _).
            - intros xs' xs'_le.
              rewrite <- (ST_organize_le tau).
              rewrite (factorize_organized _ (organize_organized tau)).
              assumption.
            - generalize (organized_path_factors _ (organize_organized tau)).
              induction prfs as [ | n path paths prf prfs IH ].
              + intro.
                exists List.nil; split; [ split | ].
                * simpl.
                  assert (ex_S : exists S, WellFormed S).
                  { clear notOmegaTau.
                    induction Mtau; try solve [ assumption ].
                    eexists; eassumption. }
                  apply nth_Forall2.
                  inversion ex_S as [ S WF_S ].
                  intro.
                  rewrite const_nth.
                  apply (CL_omega S WF_S).
                * reflexivity.
                * apply List.Forall_nil.
              + destruct prf as [ S [ WF_S ex_prf ] ].
                generalize (Exists_in _ _ ex_prf); clear ex_prf; intro ex_prf.
                inversion ex_prf as [ y [ [ path_y [ arg_count_y [ inhab_y y_le ] ] ] in_y ] ].
                intro path_prfs.
                inversion path_prfs as [ | ? ? ? path_path path_paths n_eq [ path_eq paths_eq ] ].
                dependent rewrite paths_eq in path_paths.
                destruct (IH path_paths) as [ ys [ [ inhab_ys ys_le ] in_ys ] ].
                exists (List.cons (split_path y _ arg_count_y) ys); split; [ split | ].
                * apply nth_Forall2; intro k.
                  rewrite (intersect_pointwise_spec).
                  generalize (Forall2_nth _ _ _ inhab_ys k); clear inhab_ys; intro inhab_ys.
                  rewrite (intersect_pointwise_spec) in inhab_ys.
                  generalize (Forall2_nth _ _ _ inhab_y k); clear inhab_y; intro inhab_y.
                  destruct ys.
                  { simpl; assumption. }
                  { apply CL_II; assumption. }
                * match goal with
                  | [|- intersect (of_list (List.map _ (List.cons ?hd ?tl))) <= _ ] =>
                      etransitivity; [ apply (ST_intersect_append_le (cons _ (snd hd) _ (nil _)) _) | ];
                        etransitivity; [ | apply (ST_intersect_append_ge (cons _ path _ (nil _)) paths) ];
                          apply ST_SubtypeDistrib; assumption
                  end.
                * apply List.Forall_cons; [ | assumption ].
                  unfold xs.
                  unfold allSplitPaths.
                  revert notOmegaTau Mtau WF_S in_y y_le path_y path_path.
                  clear ...
                  intros notOmegaTau Mtau WF_S in_y y_le path_y path_path.
                  unfold minimalInstance.
                  destruct (SubstitutionSpace_finite) as [ card toFin fromFin toFrom_id ].
                  simpl.
                  generalize (f_equal (proj1_sig (P := WellFormed)) (toFrom_id (exist WellFormed S WF_S))).
                  intro S_eq.
                  simpl in S_eq.
                  rewrite <- S_eq in in_y.
                  remember (toFin (exist WellFormed S WF_S)) as k eqn:k_eq.
                  clear k_eq toFin S_eq toFrom_id.
                  assert (in_y' :
                            List.In (split_path y (argumentCount M) arg_count_y)
                                    (allSplitPaths (argumentCount M)
                                                   (Apply (proj1_sig (fromFin k)) (Gamma (rootOf M))))).
                  { unfold allSplitPaths.
                    destruct (factorize (organize (Apply (proj1_sig (fromFin k)) (Gamma (rootOf M)))))
                      as [ n paths ].
                    simpl.
                    induction paths as [ | path' n paths IH ] .
                    - inversion in_y.
                    - inversion in_y as [ ? ? n_eq here | ? x ? there n_eq [ path'_eq paths_eq ] ].
                      + rewrite <- here.
                        destruct (le_dec (argumentCount M) (src_count y)).
                        * left; apply split_path_proof_invariant.
                        * contradiction.
                      + dependent rewrite paths_eq in there.
                        destruct (le_dec (argumentCount M) (src_count path')).
                        * right; auto.
                        * auto. }
                  clear in_y.
                  induction k as [ card' | card' k IHcard ].
                  { simpl positions.
                    simpl map.
                    destruct (positions card').
                    + simpl map.
                      simpl intersect.
                      assumption.
                    + simpl intersect.
                      match goal with
                      | [|- List.In _ (_ _ (projT2 (factorize (organize (Inter ?x ?y)))))] =>
                        fold (allSplitPaths (argumentCount M) (Inter x y))
                      end.
                      rewrite allSplitPaths_inter.
                      apply (List.in_or_app); left.
                      assumption. }
                  { generalize (IHcard (fun k => fromFin (FS k)) in_y').
                    intro inprf.
                    destruct card'.
                    - contradiction.
                    - simpl intersect.
                      match goal with
                      | [ inprf: List.In _ (_ _ (projT2 (factorize (organize ?z))))
                          |- List.In _ (_ _ (projT2 (factorize (organize (Inter ?x ?y)))))] =>
                        fold (allSplitPaths (argumentCount M) (Inter x y));
                          fold (allSplitPaths (argumentCount M) z) in inprf
                      end.
                      rewrite allSplitPaths_inter.
                      apply List.in_or_app; right.
                      simpl intersect in inprf.
                      rewrite <- (map_fg _ _ FS).
                      exact inprf. }
          }
          destruct (sufficient_ys) as [ ys [ ys_sufficient ys_in_xs ] ].
          generalize (@powerset_permute_prop
                        _ (split_eq _)
                        (sufficient_paths Gamma M tau)
                        ys xs
                        (sufficient_paths_deduplicate _ _ _ _ ys_sufficient)
                        (sufficient_paths_stable Gamma M tau)
                        ys_in_xs).
          unfold xs.
          unfold allPossibleInhabitants.
          intro ex_prf.
          induction ex_prf as [ arrow arrows here | arrow arrows there ].
          - destruct here as [ args_inhab tgt_le ].
            simpl.
            destruct (ST_dec (intersect (of_list (List.map snd arrow))) tau).
            + apply List.Exists_cons_hd; split; assumption.
            + contradiction.
          - simpl.
            destruct (ST_dec (intersect (of_list (List.map snd arrow))) tau).
            + apply List.Exists_cons_tl; assumption.
            + assumption.
        Qed.

        Definition allPossibleInhabitants_maxcount Gamma tau c :=
          (fix count n :=
             match n with
             | 0 => List.cons (existT (fun n => list (t IntersectionType n * IntersectionType))
                                     0 (allPossibleInhabitants Gamma tau c 0)) (List.nil)
             | S n =>
               List.app (count n)
                        (List.cons (existT (fun n => list (t IntersectionType n * IntersectionType))
                                           (S n) (allPossibleInhabitants Gamma tau c (S n)))
                                   (List.nil))
             end) (MaximalSourceCount (minimalInstance (Gamma c))).

        Lemma allPossibleInhabitants_maxcount_sound:
          forall Gamma tau c,
            { S : _ | WellFormed S } ->
            List.Forall (fun possible =>
                           List.Forall (fun arrow =>
                                          forall arguments,
                                            Forall2 (CL Gamma) arguments (fst arrow) ->
                                            CL Gamma (applyAll (Symbol c) arguments) tau)
                                       (projT2 possible))
                        (allPossibleInhabitants_maxcount Gamma tau c).
        Proof.
          intros Gamma tau c ex_S.
          unfold allPossibleInhabitants_maxcount.
          induction (MaximalSourceCount (minimalInstance (Gamma c))) as [ | n IH ].
          - apply List.Forall_cons; [ | apply List.Forall_nil ].
            apply allPossibleInhabitants_sound; assumption.
          - simpl.
            apply List.Forall_forall.
            intros possibilities possibilities_in.
            destruct (in_app_or _ _ _ possibilities_in) as [ inl | inr ].
            + exact (proj1 (List.Forall_forall _ _) IH _ inl). 
            + destruct inr as [ here | devil ].
              * rewrite <- here; apply allPossibleInhabitants_sound; assumption.
              * inversion devil.
        Qed.

        Lemma allPossibleInhabitants_maxcount_complete:
          forall Gamma tau M,
            (Omega tau -> False) ->
            CL Gamma M tau ->
            List.Exists (fun possible =>
                           exists argCountPrf : projT1 possible = argumentCount M,
                             List.Exists (fun arrow =>
                                            Forall2 (CL Gamma) (argumentsOf M) (rew argCountPrf in fst arrow) /\
                                            (snd arrow) <= tau) (projT2 possible))
                        (allPossibleInhabitants_maxcount Gamma tau (rootOf M)).
        Proof.
          intros Gamma tau M notOmegaTau Mtau.
          generalize (CL_MaximalArgumentCount _ _ _ notOmegaTau Mtau).
          intro prf.
          unfold allPossibleInhabitants_maxcount.
          induction prf as [ | ? ? IH ].
          - destruct M as [ c | M N ].
            + apply List.Exists_cons_hd.
              exists eq_refl.
              exact (allPossibleInhabitants_complete _ _ _ notOmegaTau Mtau).
            + apply List.Exists_exists.
              eexists; split.
              * apply (List.in_or_app); right; left; reflexivity.
              * exists eq_refl.
                exact (allPossibleInhabitants_complete _ _ _ notOmegaTau Mtau).
          - destruct (proj1 (List.Exists_exists _ _) IH)
              as [ x [ inprf prf' ] ].
            apply List.Exists_exists.
            exists x; split.
            * apply (List.in_or_app); left; assumption.
            * assumption.
        Qed.

        Definition grammarEntry (combinatorsFinite: Finite CombinatorSymbol) Gamma tau :=
          map (fun c =>
                 (fromFin _ combinatorsFinite c,
                  allPossibleInhabitants_maxcount Gamma tau (fromFin _ combinatorsFinite c)))
              (positions (cardinality _ combinatorsFinite)).


        Lemma grammarEntry_sound:
          forall combinatorsFinite Gamma tau,
            { S : _ | WellFormed S } ->
            Forall (fun entry =>
                      List.Forall (fun possible =>
                                     List.Forall (fun arrow =>
                                                    forall arguments,
                                                      Forall2 (CL Gamma) arguments (fst arrow) ->
                                                      CL Gamma (applyAll (Symbol (fst entry)) arguments) tau)
                                                 (projT2 possible))
                                  (snd entry))
                   (grammarEntry combinatorsFinite Gamma tau).
        Proof.
          intros cFinite Gamma tau ex_S.
          unfold grammarEntry.
          destruct cFinite as [ card toFin fromFin toFrom_id ].
          simpl.
          clear toFin toFrom_id.          
          induction card as [ | card' IH ].
          - apply Forall_nil.
          - apply Forall_cons.
            + apply allPossibleInhabitants_maxcount_sound; assumption.
            + generalize (IH (fun k => fromFin (FS k))).
              fold (map (fun c => (fromFin c,
                                allPossibleInhabitants_maxcount Gamma tau
                                                                (fromFin c)))
                        (map FS (positions card'))).
              rewrite <- (map_fg _ _ FS).
              intro; assumption.
        Qed.

        Lemma grammarEntry_complete:
          forall combinatorsFinite Gamma tau M,
            (Omega tau -> False) ->
            CL Gamma M tau ->
            Exists (fun entry =>
                      (fst entry = rootOf M) /\
                      List.Exists (fun possible =>
                                     exists argCountPrf : projT1 possible = argumentCount M,
                                       List.Exists (fun arrow =>
                                                      Forall2 (CL Gamma) (argumentsOf M)
                                                              (rew argCountPrf in fst arrow) /\
                                                      (snd arrow) <= tau) (projT2 possible))
                                  (snd entry))
                   (grammarEntry combinatorsFinite Gamma tau).
        Proof.
          intros cFinite Gamma tau M notOmegaTau Mtau.
          unfold grammarEntry.
          destruct cFinite as [ card toFin fromFin toFrom_id ].
          simpl.
          rewrite <- (toFrom_id (rootOf M)).
          remember (toFin (rootOf M)) as k eqn:k_eq.
          generalize (f_equal fromFin k_eq).
          intro k_eq'.
          rewrite toFrom_id in k_eq'.
          clear k_eq toFrom_id toFin.
          revert k_eq'.
          induction card as [ | card' IH ].
          - inversion k.
          - simpl positions.
            simpl map.
            apply (Fin.caseS' k).
            + intro k_eq.
              apply Exists_cons_hd; split.
              * reflexivity.
              * rewrite k_eq.
                apply (allPossibleInhabitants_maxcount_complete _ _ _ notOmegaTau Mtau).
            + intros k' k_eq.
              apply Exists_cons_tl.
              rewrite <- (map_fg _ _ FS).
              apply (IH (fun k => fromFin (FS k)) _ k_eq).
        Qed.

        Definition possibleRecursiveTargets_ofSize (Gamma: Context) c n :=
          (List.map (fun paths =>
                       intersect_pointwise (of_list (List.map fst paths)))
                    (powerset (allSplitPaths n (minimalInstance (Gamma c))))).

        Definition possibleRecursiveTargets_maxcount Gamma c :=
          (fix count n :=
             match n with
             | 0 => List.cons (existT (fun n => list (t IntersectionType n))
                                     0 (possibleRecursiveTargets_ofSize Gamma c 0))
                             List.nil
             | S n => List.cons
                       (existT (fun n => list (t IntersectionType n))
                               (S n) (possibleRecursiveTargets_ofSize Gamma c (S n)))
                       (count n)
             end) (MaximalSourceCount (minimalInstance (Gamma c))).

        Definition possibleRecursiveTargets (combinatorsFinite: Finite CombinatorSymbol) Gamma :=
          map (fun c =>
                 possibleRecursiveTargets_maxcount Gamma (fromFin _ combinatorsFinite c))
              (positions (cardinality _ combinatorsFinite)).

        Definition IsRecurisveTarget (combinatorsFinite: Finite CombinatorSymbol) Gamma tau sigma :=
          exists c arrows,
            In (c, arrows) (grammarEntry combinatorsFinite Gamma tau) /\
            List.In
              sigma
              (List.flat_map
                 (fun arrowsOfSize =>
                    List.flat_map (fun x => to_list (fst x)) (projT2 arrowsOfSize))
                 arrows).

        Definition IsPossibleRecursiveTarget (combinatorsFinite: Finite CombinatorSymbol) Gamma sigma :=
          exists arrows,
            In arrows (possibleRecursiveTargets combinatorsFinite Gamma) /\
            List.In
              sigma
              (List.flat_map
                 (fun arrowsOfSize => List.flat_map (to_list) (projT2 arrowsOfSize))
                 arrows).

        Lemma possibleInhabitants_finite:
          forall Gamma tau c n sigma,
          List.In sigma
               (flat_map (fun x : t IntersectionType n * IntersectionType => to_list (fst x))
                  (allPossibleInhabitants Gamma tau c n)) ->               
          List.In sigma (flat_map to_list (possibleRecursiveTargets_ofSize Gamma c n)).
        Proof.
          intros Gamma tau c n sigma in_prf.
          unfold allPossibleInhabitants in in_prf.
          unfold possibleRecursiveTargets.
          unfold possibleRecursiveTargets_ofSize.
          induction (powerset (allSplitPaths n (minimalInstance (Gamma c))))
            as [ | path paths IH ].
          - inversion in_prf.
          - simpl in in_prf.
            simpl.
            apply (List.in_or_app).
            destruct (ST_dec (intersect (of_list (List.map snd path))) tau).
            + simpl in in_prf.
              destruct (List.in_app_or _ _ _ in_prf) as [ inl | inr ].
              * left; assumption.
              * right; auto.
            + right; auto.
        Qed.
            

        Lemma grammarTargetsFinite:
          forall (combinatorsFinite: Finite CombinatorSymbol) Gamma tau sigma, 
            IsRecurisveTarget combinatorsFinite Gamma tau sigma ->
            IsPossibleRecursiveTarget combinatorsFinite Gamma sigma.
        Proof.
          intros cFinite Gamma tau sigma prf.
          unfold IsRecurisveTarget in prf.
          unfold IsPossibleRecursiveTarget.
          destruct cFinite as [ card toFin fromFin fromTo_id ].
          simpl.
          destruct prf as [ c [ arrows [ in_entry sigma_in ] ] ].
          exists (possibleRecursiveTargets_maxcount Gamma c); split.
          - unfold possibleRecursiveTargets.
            simpl.
            rewrite <- (fromTo_id c).
            remember (toFin c) as k eqn:k_eq.
            clear k_eq in_entry toFin fromTo_id.
            induction card as [ | card' IH ].
            + inversion k.
            + apply (Fin.caseS' k).
              * left.
              * intro k'.
                right.
                fold (map (fun c => possibleRecursiveTargets_maxcount Gamma (fromFin c))
                          (map FS (positions card'))).
                rewrite <- (map_fg _ _ FS).
                apply (IH (fun c => fromFin (FS c)) k').
          - unfold possibleRecursiveTargets_maxcount.
            unfold grammarEntry in in_entry.
            simpl in in_entry.
            assert (arrows_eq: arrows = allPossibleInhabitants_maxcount Gamma tau c).
            { destruct (In_nth _ _ in_entry) as [ k k_eq ].
              rewrite (nth_map _ _ _ _ eq_refl) in k_eq.
              rewrite (positions_spec) in k_eq.
              generalize (f_equal fst k_eq).
              intro c_eq.
              simpl in c_eq.
              rewrite <- c_eq.
              generalize (f_equal snd k_eq).
              intro arrows_eq.
              apply eq_sym; assumption. }
            rewrite arrows_eq in sigma_in.
            clear arrows_eq.
            unfold allPossibleInhabitants_maxcount in sigma_in.
            induction (MaximalSourceCount (minimalInstance (Gamma c))) as [ | n IH ].
            + simpl.
              rewrite (List.app_nil_r).
              simpl in sigma_in.
              rewrite (List.app_nil_r) in sigma_in.
              eapply (possibleInhabitants_finite); eassumption.
            + apply List.in_or_app.
              simpl in sigma_in.
              rewrite (List.flat_map_concat_map) in sigma_in.
              rewrite (List.map_app) in sigma_in.
              rewrite (List.concat_app) in sigma_in.
              destruct (List.in_app_or _ _ _ sigma_in) as [ inl | inr ].
              * right.
                apply IH.
                rewrite <- (List.flat_map_concat_map) in inl.
                assumption.
              * rewrite <- (List.flat_map_concat_map) in inr.
                simpl in inr.
                rewrite (List.app_nil_r) in inr.
                left.
                simpl.
                eapply (possibleInhabitants_finite); eassumption.
        Qed.

        Require Import Coq.Init.Wf.
        Definition TreeGrammar (combinatorsFinite: Finite CombinatorSymbol): Set :=
          list (IntersectionType *
                t (CombinatorSymbol *
                   list { n : nat & list (t IntersectionType n * IntersectionType)})
                  (cardinality CombinatorSymbol combinatorsFinite)).
        Inductive NextInhabGrammar (combinatorsFinite: Finite CombinatorSymbol) (Gamma: Context):
          TreeGrammar combinatorsFinite -> TreeGrammar combinatorsFinite -> Prop :=
        | Next:
            forall (oldGrammar: TreeGrammar combinatorsFinite) lhs rhs,
              (*(List.Forall (IsPossibleRecursiveTarget combinatorsFinite Gamma)
                           (List.map fst oldGrammar)) ->*)
              IsPossibleRecursiveTarget combinatorsFinite Gamma lhs ->
              (List.In lhs (List.map fst oldGrammar) -> False) ->
              NextInhabGrammar combinatorsFinite Gamma (List.cons (lhs, rhs) oldGrammar) oldGrammar.

        Definition initialInsert
                   (combinatorsFinite: Finite CombinatorSymbol)
                   (Gamma: Context)
                   (lhs: IntersectionType)
                   (rhs: t (CombinatorSymbol *
                            list { n : nat & list (t IntersectionType n * IntersectionType)})
                           (cardinality CombinatorSymbol combinatorsFinite))
                   (lhsOk: IsPossibleRecursiveTarget combinatorsFinite Gamma lhs):
          NextInhabGrammar combinatorsFinite Gamma (List.cons (lhs, rhs) List.nil) (List.nil) :=
          Next combinatorsFinite Gamma (List.nil) lhs rhs (*List.Forall_nil _*) lhsOk id.
(*
        Definition MaximalInhabGrammarTgts combinatorsFinite (Gamma: Context): list IntersectionType :=
          List.flat_map
            (fun tgts =>
               List.flat_map
                 (fun tgtsOfSize =>
                    List.flat_map (to_list) (projT2 tgtsOfSize))
                 tgts)
            (to_list (possibleRecursiveTargets combinatorsFinite Gamma)).

        Lemma MaximalInhabTgtsPossible:
          forall combinatorsFinite (Gamma: Context) sigma,
            IsPossibleRecursiveTarget combinatorsFinite Gamma sigma <->
            List.In sigma (MaximalInhabGrammarTgts combinatorsFinite Gamma).
        Proof.
          intros combinatorsFinite Gamma sigma.
          unfold IsPossibleRecursiveTarget.
          unfold MaximalInhabGrammarTgts.
          induction (possibleRecursiveTargets combinatorsFinite Gamma) as [ | tgt n tgts IH ]; split.
          - intro prf; inversion prf as [ arrows [ devil _ ] ]; inversion devil.
          - intro; contradiction.
          - intro prf.
            inversion prf as [ arrows [ in_arrows sigma_in ] ].
            inversion in_arrows as [ ? ? n_eq inl | ? ? ? inr n_eq [ hd_eq tl_eq ] ].
            + simpl.
              apply (List.in_or_app).
              left.
              rewrite <- inl; assumption.
            + dependent rewrite tl_eq in inr.
              generalize (proj1 IH (ex_intro _ arrows (conj inr sigma_in))).
              intro IH'.
              apply (List.in_or_app).
              right; assumption.
          - 
          
        
        Lemma NextInhabGrammar_wf':
          forall (combinatorsFinite: Finite CombinatorSymbol) (Gamma: Context),
          forall grammar, Acc (NextInhabGrammar combinatorsFinite Gamma) grammar.
        Proof.
          intros combinatorsFinite Gamma grammar.
          assert (length_finite:
                    (length (List.filter
                               (fun x =>
                                  if In_dec IntersectionType_eq_dec
                                            x (List.map fst grammar)
                                  then false else true)
                               (MaximalInhabGrammarTgts combinatorsFinite Gamma)) <=
                     length (MaximalInhabGrammarTgts combinatorsFinite Gamma))%nat).
          { admit. }
          unfold TreeGrammar in grammar.
          revert grammar length_finite.
          induction (length (MaximalInhabGrammarTgts combinatorsFinite Gamma)) as [ | n IH ].
          - intros grammar length_finite.
            apply Acc_intro.
            intros y acc_y.
            inversion acc_y.
          (* possible but not in grammar => impossible because of length_finite *)
            admit.
          - intros grammar length_finite.
            inversion length_finite as [ eq | le ].
            + apply Acc_intro.
              intros grammar' next_inhab.
              inversion next_inhab as [ ? lhs rhs possible_lhs not_in_lhs ].
              apply IH.
              clear IH length_finite next_inhab.
              induction grammar as [ | entry grammar IH ].
              * simpl in eq.
                assert (length (MaximalInhabGrammarTgts combinatorsFinite Gamma) = S n).
                { revert eq.
                  clear ...
                  revert n.
                  induction (MaximalInhabGrammarTgts combinatorsFinite Gamma) as [ | x xs IH ];
                    intros n eq.
                  - inversion eq.
                  - destruct xs.
                    + inversion eq; reflexivity.
                    + destruct n as [ | n ].
                      * inversion eq.
                      * simpl; apply f_equal.
                        apply IH.
                        inversion eq.
                        reflexivity. }
                
                induction (MaximalInhabGrammarTgts combinatorsFinite Gamma).
                { apply le_0_n. }
                { 
                admit.
              * apply IH.
              admit.
            + apply IH; assumption.
        Qed.
            

          
          apply Acc_intro.
          intros grammar' prf.
          inversion prf as [ ? tgt rhs possible_tgt not_in_tgt ].
          unfold IsPossibleRecursiveTarget in possible_tgt.
          destruct possible_tgt as [ arrows [ in_arrows_possible in_tgt_arrows ] ].
          assert (not_in_tgt' :
                    List.In
                      tgt
                      (List.filter
                         (fun x =>
                            if In_dec IntersectionType_eq_dec x
                                      (flat_map (fun arrowsOfSize =>
                                                   flat_map to_list (projT2 arrowsOfSize))
                                                arrows)
                            then true else false) (List.map fst grammar)) -> False).
          { revert not_in_tgt.
            clear ...
            intros not_in devil.
            induction grammar as [ | entry entries IH ].
            - contradiction.
            - simpl in devil.
              destruct (In_dec IntersectionType_eq_dec (fst entry)
                               (flat_map
                                  (fun arrowsOfSize => flat_map to_list (projT2 arrowsOfSize)) arrows)).
              + destruct devil as [ inl | inr ].
                * apply not_in.
                  left.                 
                  rewrite inl.
                  reflexivity.
                * apply IH.
                  { intro; apply not_in; right; assumption. }
                  { exact inr. }
              + apply IH.
                { intro; apply not_in; right; assumption. }
                { exact devil. } }
          clear in_arrows_possible not_in_tgt.
          induction arrows.
          - inversion in_tgt_arrows.
          - 

          
          induction (possibleRecursiveTargets combinatorsFinite Gamma) as [ | ptgt n ptgts IH ].
          - inversion possible_tgt as [ arrows [ devil _ ]]; inversion devil.
          - inversion possible_tgt as [ arrows [ arrows_in tgt_in_arrows ]].
            inversion arrows_in as [ ? ? n_eq [ hd_eq tl_eq ] | ? ? ? inr n_eq [ hd_eq tl_eq ] ].
            + clear IH possible_tgt n_eq hd_eq tl_eq.
              induction arrows as [ | arrow arrows IH ].
              * inversion tgt_in_arrows.
              * simpl in tgt_in_arrows.
                destruct (List.in_app_or _ _ _ tgt_in_arrows) as [ inl | inr ].
                { clear IH tgt_in_arrows.
                  destruct arrow as [ arrow_size arrow_components ].
                  induction arrow_components as [ | arrow_component arrow_components IH ].
                  - inversion inl.
                  - simpl in inl.
                    destruct (List.in_app_or _ _ _ inl) as [ inl' | inr ].
                    + clear inl IH.
                      induction arrow_component as [ | arrow_src arrow_srcs_size arrow_srcs IH ].
                      * inversion inl'.
                      * simpl in inl'.
                        inversion inl' as [ here | there ].
                        { apply Acc_intro.
                          admit.

                        }
                        { apply IH; assumption. }
                    + apply IH; assumption. }
                { apply IH; assumption. }                
            + dependent rewrite tl_eq in inr.
              apply IH.
              * exists arrows; split; assumption.
              * assumption.
              * assumption.
        Qed.
        
        Lemma NextInhabGrammar_wf:
          forall (combinatorsFinite: Finite CombinatorSymbol) (Gamma: Context),
            well_founded (NextInhabGrammar combinatorsFinite Gamma).
        Proof.
          intros cFinite Gamma.
          unfold well_founded.
          intro treeGrammar.
          apply Acc_intro.
          
        *)
              
          

            (*

          
          Forall
             (fun sigma' =>
                exists S : Substitution,
                  WellFormed S /\
                  Exists
                    (fun path =>
                       Path path /\
                       (exists argCountPrf : (argumentCount M <= src_count path)%nat,
                           Forall2 (CL Gamma) (argumentsOf M) (fst (split_path path (argumentCount M) argCountPrf)) /\
                           snd (split_path path (argumentCount M) argCountPrf) <= sigma'))
                    paths)
             (projT2 (factorize (organize tau))).

        
        Lemma sufficient_paths_deduplicate:
          forall Gamma M tau xs,
            sufficient_paths Gamma M tau _ (of_list xs) ->
            sufficient_paths Gamma M tau _ (of_list (@deduplicate _ IntersectionType_eq_dec xs)).
        Proof.
          intros Gamma M tau xs.
          unfold sufficient_paths.
          induction (projT2 (factorize (organize tau))).
          - intro; apply Forall_nil.
          - intro prfs.
            inversion prfs as [ | ? ? ? [S [ WF_S ex_prf ]] prfs_tl n_eq [ hd_eq tl_eq ] ].
            dependent rewrite tl_eq in prfs_tl.
            apply Forall_cons.
            + eexists; split; [ eassumption | ].
              apply exists_deduplicate.
              assumption.
            + auto.
        Qed.
        
        Lemma sufficient_paths_stable:
          forall Gamma M tau xs ys,
            Permutation (@deduplicate _ IntersectionType_eq_dec xs) ys ->
            sufficient_paths Gamma M tau _ (of_list (@deduplicate _ IntersectionType_eq_dec xs)) ->
            sufficient_paths Gamma M tau _ (of_list ys).
        Proof.
          intros Gamma M tau.
          unfold sufficient_paths.
          induction (projT2 (factorize (organize tau))) as [ | ? ? ? IH ].
          - intros; apply Forall_nil.
          - intros xs ys perm_xs_ys prfs.
            inversion prfs as [ | ? ? ? [S [ WF_S ex_prf ] ] prfs_tl n_eq [ hd_eq tl_eq ] ].
            dependent rewrite tl_eq in prfs_tl.
            apply Forall_cons.
            + eexists; split; [ eassumption | ].
              apply (@exists_permute _ IntersectionType_eq_dec _ (@deduplicate _ IntersectionType_eq_dec xs));
                assumption.
            + eapply IH; eassumption.
        Qed.


        Lemma MinimalInstance_omega:
          forall Gamma M tau,
            CL Gamma M tau ->
            Omega (minimalInstance (Gamma (rootOf M))) ->
            Omega tau.
        Proof.
          intros Gamma M.
          induction M as [ | M IHM N IHN ].
          - intros tau ctau omegaMinimal.
            eapply Omega_complete; [ | eassumption ].
            apply MinimalType_minimal.
            assumption.
          - intros tau MNtau omegaMinimal.
            destruct (MP_generation _ _ _ _ MNtau) as [ sigma [ Msigmatau Nsigma ] ].
            generalize (IHM _ Msigmatau omegaMinimal).
            simpl; intro; assumption.
        Qed.

        Lemma ListExists_map: forall {A B: Type} (f: A -> B) (P : B -> Prop) xs,
            List.Exists P (List.map f xs) -> List.Exists (fun x => P (f x)) xs.
        Proof.
          intros A B f P xs.
          induction xs.
          - intro devil; inversion devil.
          - intro ex_prf.
            inversion ex_prf.
            + apply List.Exists_cons_hd; assumption.
            + apply List.Exists_cons_tl; auto.
        Qed.
  
        Lemma allPossibleInhabitants_complete:
          forall Gamma tau M,
            (Omega tau -> False) ->
            CL Gamma M tau ->
            List.Exists (fun arrow =>
                      Forall2 (CL Gamma) (argumentsOf M) (fst arrow) /\
                      snd arrow <= tau)
                        (allPossibleInhabitants Gamma tau (rootOf M) (argumentCount M)).
        Proof.
          intros Gamma tau M notOmegaTau Mtau.
                    
          set (xs := List.map (fun p => mkArrow (fst p) (snd p))
                              (allSplitPaths (argumentCount M) (minimalInstance (Gamma (rootOf M))))).
          assert (sufficient_ys: exists ys,
                     sufficient_paths Gamma M tau _ (of_list ys) /\
                     List.Forall (fun y => List.In y xs) ys).
          { unfold sufficient_paths.
            generalize (CL_Path _ _ _ Mtau).
            intro prfs.
            induction prfs as [ | n path paths path_prf paths_prfs IH n_eq [ path_eq paths_eq ] ].
            - exists List.nil; split; [ apply Forall_nil | apply List.Forall_nil ].
            - destruct path_prf as [ S [ WF_S ex_prf ] ].
              generalize (allSplitPaths_complete (argumentCount M) (Apply S (Gamma (rootOf M)))).
              destruct IH as [ ys [ sufficient_ys all_in_ys ] ].
              unfold xs.
              induction ex_prf as [ ? p ps here | ? ? ? there IH' ];
                intro all_in.
              + exists (List.cons p ys); split.
                * clear all_in.
                  apply Forall_cons.
                  { eexists; split; [ eassumption | ].
                    apply Exists_cons_hd; assumption. }
                  { clear paths_prfs.
                    induction sufficient_ys as [ | ? ? ? [S' [WF_S' ex_prf']] prfys IH' ].
                    - apply Forall_nil.
                    - apply Forall_cons.
                      + exists S'; split; [ assumption | ].
                        apply Exists_cons_tl; assumption.
                      + assumption. }
                * apply List.Forall_cons.
                  { unfold allSplitPaths.
                    revert notOmegaTau Mtau all_in here WF_S.
                    clear ...
                    intros notOmegaTau Mtau all_in here WF_S.
                    inversion all_in as [ | ? ? ? prf ? n_eq [ hd_eq tl_eq ] ].
                    inversion here as [ path_p [ src_count_p _ ] ].
                    generalize (prf src_count_p).
                    unfold minimalInstance.
                    destruct (SubstitutionSpace_finite) as [ card toFin fromFin toFrom_id ].
                    simpl.
                    generalize (f_equal (proj1_sig (P := WellFormed)) (toFrom_id (exist WellFormed S WF_S))).
                    intro S_eq.
                    simpl in S_eq.
                    rewrite <- S_eq.
                    remember (toFin (exist WellFormed S WF_S)) as k eqn:k_eq.
                    clear k_eq toFin S_eq toFrom_id.
                    induction k as [ card' | card' k IHcard ].
                    - simpl positions.
                      simpl map.
                      intro ex_prf.
                      unfold allSplitPaths in ex_prf.
                      destruct (proj1 (List.Exists_exists _ _) ex_prf) as [ p' [ p'_in p'_eq ] ].
                      revert p'_eq.
                      rewrite <- (split_path_spec p _ src_count_p).
                      intro p'_eq.
                      rewrite <- p'_eq.
                      apply (List.in_map (fun p => mkArrow (fst p) (snd p))).
                      destruct (positions card').
                      + simpl map.
                        simpl intersect.
                        assumption.
                      + simpl intersect.
                        match goal with
                        | [|- List.In _ (_ _ (projT2 (factorize (organize (Inter ?x ?y)))))] =>
                          fold (allSplitPaths (argumentCount M) (Inter x y))
                        end.
                        rewrite allSplitPaths_inter.
                        apply (List.in_or_app); left.
                        assumption.
                    - intro ex_prf.
                      generalize (IHcard (fun k => fromFin (FS k)) ex_prf).
                      intro IH'.
                      simpl positions.
                      simpl map.
                      rewrite <- (map_fg _ 
                                        (fun k => Apply (proj1_sig (fromFin k)) (Gamma (rootOf M)))
                                        FS).
                      destruct (positions card').
                      + contradiction IH'.
                      + simpl intersect.
                        match goal with
                        | [|- List.In _ (List.map _ (_ _ (projT2 (factorize (organize (Inter ?x ?y))))))] =>
                          fold (allSplitPaths (argumentCount M) (Inter x y))
                        end.
                        rewrite allSplitPaths_inter.
                        rewrite (List.map_app).
                        apply (List.in_or_app); right.
                        exact IH'.                      
                  }
                  { assumption. }
              + inversion all_in as [ | ? ? ? ? prfs n_eq [ hd_eq tl_eq ] ].
                dependent rewrite tl_eq in prfs.
                auto. }
          destruct sufficient_ys as [ ys [ ys_sufficient ys_in ] ].
          generalize (@powerset_permute_prop
                        _ IntersectionType_eq_dec
                        (fun xs => sufficient_paths Gamma M tau _ (of_list xs))
                        ys xs
                        (sufficient_paths_deduplicate _ _ _ _ ys_sufficient)
                        (sufficient_paths_stable Gamma M tau)
                        ys_in).
          unfold allPossibleInhabitants.
          intro ex_prf.
          unfold xs in ex_prf.
          rewrite powerset_map  in ex_prf.
          generalize (ListExists_map _ _ _ ex_prf).
          unfold sufficient_paths.
          clear ex_prf; intro ex_prf.
          induction ex_prf as [ x xs' prf | x xs' prf prfs IH ].
          - simpl.
            assert (tgt_le : (intersect (of_list (List.map snd x))) <= tau).
            { admit. }
            destruct (ST_dec (intersect (of_list (List.map snd x))) tau); [ | contradiction ].
            apply List.Exists_cons_hd; split; [ | assumption ].
            unfold sufficient_paths in prf.
            simpl fst.
            apply nth_Forall2.
            intro k.
            rewrite intersect_pointwise_spec.
            assert (notOmegaFactors : Omega (intersect (projT2 (factorize (organize tau)))) -> False).
            { intro devil.
              apply notOmegaTau.
              eapply (Omega_complete _ _); [ | eassumption ].
              rewrite <- (factorize_organized _ (organize_organized _)).
              apply ST_organize_le. }
            induction prf as [ | ? ? ? prf' ].
            + assert False; [ apply notOmegaFactors; exact I | contradiction ].
            + 
            generalize (Forall_nth _ _ prf).
            
            
          - simpl.
            destruct (ST_dec (intersect (of_list (List.map snd x)))).
            + apply List.Exists_cons_tl; assumption.
            + assumption.
        Qed.
          
        
        Lemma CL_can_inhabit_complete: forall Gamma M tau,
            CL Gamma M tau ->
            exists (m : nat),
              (m <= MaximalSourceCount (minimalInstance (Gamma (rootOf M))))%nat /\
              exists paths,
                List.In paths (powerset (allSplitPaths m (minimalInstance (Gamma (rootOf M))))) /\
                intersect (of_list (List.map snd paths)) <= tau /\
                Forall (fun sigma => exists N, CL Gamma N sigma) (intersect_pointwise (of_list (List.map fst paths))).
        Proof.
          

        Lemma CL_finite_inhab_dec: forall Gamma tau (P : Term -> Prop),
            (forall M, { P M } + { P M -> False }) ->
            Finite CombinatorSymbol ->
            () ->
            ({ exists M, P M /\ CL Gamma M tau } + { (exists M, P M /\ CL Gamma M tau) -> False }).
        Proof.
          intros Gamma tau P P_dec P_omega_inhab c_Finite.
          destruct c_Finite as [ c_card c_to c_from c_fromTo_id ].
          assert (proof_instead:
                    (forall c,
                        {(exists M, rootOf M = c /\
                               (Omega tau \/
                                argumentCount M <= MaximalSourceCount (minimalInstance (Gamma (rootOf M))))%nat /\
                               P M /\
                               CL Gamma M tau)} +
                        {(exists M, rootOf M = c /\
                               (argumentCount M <= MaximalSourceCount (minimalInstance (Gamma (rootOf M))))%nat /\
                               P M /\
                               CL Gamma M tau) -> False}) ->
                    ({(exists M, P M /\ CL Gamma M tau)} +
                     {(exists M, P M /\ CL Gamma M tau) -> False})).
          { intro inhabc.
            assert (ex_c:
                      { Exists (fun c => (exists M, rootOf M = (c_from c) /\
                                            (argumentCount M <=
                                             MaximalSourceCount (minimalInstance (Gamma (rootOf M))))%nat /\
                                            P M /\
                                            CL Gamma M tau)) (positions c_card) } +
                      { Exists (fun c => (exists M, rootOf M = (c_from c) /\
                                            (argumentCount M <=
                                             MaximalSourceCount (minimalInstance (Gamma (rootOf M))))%nat /\
                                            P M /\
                                            CL Gamma M tau)) (positions c_card) -> False }).
            { induction (positions c_card) as [ | c n cs IH ].
              - right; intro devil; inversion devil.
              - destruct (inhabc (c_from c)) as [ prf | ].
                + left; apply Exists_cons_hd; assumption.
                + destruct IH as [ prf | disprf ].
                  * left; apply Exists_cons_tl; assumption.
                  * right; intro devil.
                    inversion devil as [ ? ? ? devil' | ? ? ? devil' n_eq [ c_eq cs_eq ] ].
                    { contradiction. }
                    { dependent rewrite cs_eq in devil'; contradiction. } }
            destruct ex_c as [ prf | disprf ].
            - left.
              induction (positions c_card).
              + inversion prf.
              + inversion prf as [ ? ? ? [ M [ _ [ _ [ PM Mtau ] ] ] ]
                                 | ? ? ? prf' n_eq [ c_eq cs_eq ] ].
                * eexists; split; eassumption.
                * dependent rewrite cs_eq in prf'; auto.
            - right.
              intro devil.
              inversion devil as [ M [ PM Mtau ] ].
              apply disprf.
              apply (nth_Exists _ _ (c_to (rootOf M))).
              eexists; repeat split; try solve [ eassumption ].
              + apply eq_sym.
                rewrite (positions_spec _ (c_to (rootOf M))).
                apply (c_fromTo_id (rootOf M)).
              + 
                eapply CL_MaximalArgumentCount.

          }
          apply proof_instead.
          intro c.
                    
          assert (c_useful:
                    { { n : _ & srcTypes: t IntersectionType n
                      | Forall (fun sigma => exists N, P N /\ CL Gamma N sigma) srcTypes /\
                        
                        
         *)
        End FiniteSubstitutionCheckable.
     
    End DecidableWF.
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

      Lemma Apply_Distrib {n} (ctxts: t Context n):
        forall S c, Apply S (intersectContexts ctxts c) = intersect (map (fun ctxt => Apply S (ctxt c)) ctxts).
      Proof.
        intros S c.
        induction ctxts as [ | ? ? ctxts IH ].
        - reflexivity.
        - destruct ctxts.
          + reflexivity.
          + simpl.
            simpl in IH.
            rewrite IH.
            reflexivity.
      Qed.
      
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

        Lemma factorize_organize_intersect:
          forall n (sigmas: t IntersectionType n),
            factorize (organize (intersect sigmas)) =
            factorize (intersect (map organize sigmas)).
        Proof.
          intros n sigmas.
          induction sigmas as [ | sigma n sigmas IH ].
          - reflexivity.
          - simpl.
            destruct sigmas.
            + reflexivity.
            + simpl.
              rewrite (factorize_intersect_append).
              simpl in IH.
              rewrite <- IH.
              rewrite <- (factorize_organized _ (organize_organized _)).
              rewrite <- (factorize_organized _ (organize_organized _)).
              reflexivity.
        Qed.

        Lemma Forall_factors_distrib {m} P:
          forall (xs : t IntersectionType m),
            (forall k, Forall P (projT2 (factorize (nth xs k)))) ->
            Forall P (projT2 (factorize (intersect xs))).
        Proof.
          intro xs.
          induction xs as [ | ? ? ? IH ].
          - intros; apply Forall_nil.
          - intro prfs.
            simpl.
            set (prf := prfs F1).
            simpl in prf.
            destruct xs.
            + assumption.
            + simpl.
              apply Forall_append; [ assumption | ].
              apply IH.
              intro k.
              apply (prfs (FS k)).
        Qed.

        Lemma Combinator_path_types:
          forall c S, WellFormed S ->
                 Forall (fun path => exists n, TypeOf n path)
                        (projT2 (factorize (organize (Apply S (Gamma c))))).
        Proof.
          intros c S WFS.
          unfold Gamma.
          rewrite Apply_Distrib.
          rewrite factorize_organize_intersect.
          apply Forall_factors_distrib.
          intro k.
          apply nth_Forall.
          intro.
          exists k.
          apply Forall_nth.
          apply factorize_typeOf.
          rewrite (nth_map _ _ _ _ eq_refl).
          apply organize_typeOf.
          rewrite (nth_map _ _ _ _ eq_refl).
          apply WF_respectful; [ assumption | ].
          apply contextsWF.
        Qed.

        Lemma ST_typeOf_path:
          forall sigma tau m n,
            (Omega tau -> False) ->
            Path sigma -> TypeOf m sigma -> TypeOf n tau -> sigma <= tau ->  m = n.
        Proof.
          intros sigma tau.
          revert sigma.
          induction tau
            as [ | | | l r ] using IntersectionType_rect';
            intros sigma m n not_omega_tau path_sigma.
          - intros; contradict (not_omega_tau I).
          - inversion path_sigma.
            + intros m_sigma n_tau sigma_le.
              destruct (Fin.eq_dec m n); [ assumption | ].
              generalize (CI_complete _ _ _ sigma_le).
              intro CI_sigma.
              inversion CI_sigma.
              inversion m_sigma.
              inversion n_tau.
              assert False.
              { eapply SymbolsUnrelated; eassumption. }
              contradiction.
            + intros m_sigma n_tau sigma_le.
              assert False.
              { eapply ST_Arrow_Const; eassumption. }
              contradiction.
          - inversion path_sigma.
            + intros m_sigma n_tau sigma_le.
              assert False.
              { apply not_omega_tau.
                simpl.
                eapply ST_Const_Arrow; eassumption. }
              contradiction.
            + intros m_sigma n_tau sigma_le.
              generalize (AI_complete _ _ _ sigma_le).
              intro AI_sigma.
              inversion AI_sigma.
              * assert False.
                { apply not_omega_tau; simpl; assumption. }
                contradiction.
              * simpl in not_omega_tau.
                inversion n_tau.
                inversion m_sigma.
                eauto.
          - intros m_sigma n_tau sigma_le.
            assert (sigma <= l).
            { etransitivity; [ eassumption | apply ST_InterMeetLeft ]. }
            assert (sigma <= r).
            { etransitivity; [ | apply ST_InterMeetRight ]; eassumption. }
            inversion n_tau.
            assert (not_omega: (Omega l -> False) \/ (Omega r -> False)).
            { destruct (Omega_dec l).
              + destruct (Omega_dec r).
                * contradict not_omega_tau.
                  unfold not; split; assumption.
                * right. assumption.
              + left; assumption. }
            inversion not_omega as [ left_choice | right_choice ]; eauto.
        Qed.

        Lemma TypeOf_disjoint:
          forall sigma m n, TypeOf m sigma -> TypeOf n sigma -> Omega sigma \/ m = n.
        Proof.
          intro sigma.
          induction sigma
            as [ | | src tgt IHsrc IHtgt | l r IHl IHr ] using IntersectionType_rect'.
          - intros; left; exact I.
          - intros m n m_sigma n_sigma.
            right.
            inversion m_sigma.
            inversion n_sigma.
            destruct (Fin.eq_dec m n) as [ | m_not_n ]; [ assumption | ].
            assert False.
            { eapply SymbolsDisjoint; eassumption. }
            contradiction.
          - intros m n m_sigma n_sigma.
            inversion m_sigma; inversion n_sigma.
            simpl; auto.
          - intros m n m_sigma n_sigma.
            inversion m_sigma; inversion n_sigma.
            assert (dec_l: Omega l \/ m = n).
            { auto. }
            assert (dec_r: Omega r \/ m = n).
            { auto. }
            destruct dec_l; destruct dec_r;
              solve [ left; split; assumption
                    | right; assumption ].
        Qed.           
            
        
        Lemma Combinator_path_typesOfn:
          forall c n S, WellFormed S ->
                   Forall (fun path => TypeOf n path -> CL (nth contexts n) (Symbol c) path)
                          (projT2 (factorize (organize (Apply S (Gamma c))))).
        Proof.
          intros c n S WFS.
          unfold Gamma.
          rewrite Apply_Distrib.
          rewrite (factorize_organize_intersect numberOfContexts).
          apply Forall_factors_distrib; intro k.
          rewrite (nth_map _ _ _ _ eq_refl).
          rewrite (nth_map _ _ _ _ eq_refl).
          apply (nth_Forall); intro k'.
          intro n_factor.          
          eapply CL_ST; [ apply CL_Var; eassumption | ].
          assert (nk_eq: n = k \/
                         Omega (nth (projT2 (factorize (organize (Apply S (nth contexts k c))))) k')).
          { assert (k_assumption : TypeOf k (Apply S (nth contexts k c))).
            { apply WF_respectful; auto. }
            generalize (Forall_nth _ _
                                   (factorize_typeOf _ _ (organize_typeOf _ _ k_assumption))
                                   k').
            intro k_factor.
            destruct (TypeOf_disjoint _ _ _ n_factor k_factor);
              [ right; assumption | left; assumption ]. }
          destruct nk_eq as [ nk_eq | c_omega ].
          + rewrite nk_eq.
            rewrite ST_organize_ge.
            rewrite (factorize_organized _ (organize_organized _)).
            apply ST_intersect_nth.
          + rewrite <- (Omega_sound _ c_omega).
            apply ST_OmegaTop.
        Qed.        
              
        Lemma split_path_typeOf_snd: forall sigma n k prf,
            TypeOf n sigma -> TypeOf n (snd (split_path sigma k prf)).
        Proof.
          intro sigma.
          induction sigma using IntersectionType_rect';
            intros n k prf n_sigma;
            try solve [
                  simpl in prf;
                  destruct k; [ assumption | inversion prf ] ].
          destruct k.
          - assumption.
          - simpl.
            inversion n_sigma.
            generalize (proj2 (Nat.succ_le_mono k (src_count sigma2)) prf).
            intro prf'.
            auto.
        Qed.

        Lemma split_path_typeOf_fst: forall sigma n k prf,
            TypeOf n sigma -> Forall (TypeOf n) (fst (split_path sigma k prf)).
        Proof.
          intro sigma.
          induction sigma using IntersectionType_rect';
            intros n k prf n_sigma;
            try solve [
                  simpl in prf;
                  destruct k; [ apply Forall_nil | inversion prf ] ].
          destruct k.
          - apply Forall_nil.
          - simpl.
            inversion n_sigma.
            apply Forall_cons; [ assumption | ].
            generalize (proj2 (Nat.succ_le_mono k (src_count sigma2)) prf).
            intro prf'.
            auto.
        Qed.


        Lemma Exist_path_unapply:
          forall S M N sigma,
            WellFormed S ->
            Exists
              (fun path : IntersectionType =>
                 Path path /\
                 (exists argCountPrf : (argumentCount (App M N) <= src_count path)%nat,
                     Forall2 (CL Gamma) (argumentsOf (App M N))
                             (fst (split_path path (argumentCount (App M N)) argCountPrf)) /\
                     snd (split_path path (argumentCount (App M N)) argCountPrf) <= sigma))
              (projT2 (factorize (organize (Apply S (Gamma (rootOf (App M N))))))) ->
            Exists 
              (fun path : IntersectionType =>
                 Path path /\
                 (exists argCountPrf : (argumentCount (App M N) <= src_count path)%nat,
                     CL Gamma M (Arrow (last (fst (split_path path (argumentCount (App M N))
                                                              argCountPrf)))
                                       (snd (split_path path (argumentCount (App M N)) argCountPrf))) /\
                     CL Gamma N (last (fst (split_path path (argumentCount (App M N)) argCountPrf))) /\
                     snd (split_path path (argumentCount (App M N)) argCountPrf) <= sigma))
              (projT2 (factorize (organize (Apply S (Gamma (rootOf (App M N))))))).
        Proof.
          intros S M N sigma WF_S ex_prf.
          assert (root_prf : CL Gamma (Symbol (rootOf (App M N)))
                     (intersect (projT2 (factorize (organize (Apply S (Gamma (rootOf (App M N))))))))).
          { rewrite <- (factorize_organized _ (organize_organized _)).
            eapply CL_ST; [ | apply ST_organize_ge ].
            apply CL_Var; assumption. }
          induction ex_prf as [ ? path ? [ path_path [ argCountPrf [ srcPrfs tgtPrf ] ] ]
                              | ? ? paths ].
          - apply Exists_cons_hd; split; [ assumption | ].
            exists argCountPrf; repeat split.
            + assert (rootPrf' : CL Gamma (Symbol (rootOf M)) path).
              { eapply CL_ST; [ apply root_prf | ].
                etransitivity; [ apply (ST_intersect_nth _ F1) | ].
                reflexivity. }
              assert (argCountPrf': (argumentCount M <= src_count path)%nat).
              { etransitivity; [ apply le_S | eassumption ]; reflexivity. }
              assert (srcPrfs' :
                        Forall2 (CL Gamma)
                                (argumentsOf M)
                                (fst (split_path path (argumentCount M) argCountPrf'))).
              { simpl argumentCount in srcPrfs.
                simpl argumentsOf in srcPrfs.
                set (params_eq := (split_path_shiftin _ _ argCountPrf argCountPrf')).
                simpl (_ + _) in params_eq.
                rewrite params_eq in srcPrfs.
                clear params_eq.
                rewrite (shiftout_shiftin (argumentsOf M) N).
                rewrite (shiftout_shiftin _
                                          (last (fst (split_path path
                                                                 (Datatypes.S (argumentCount M))
                                                                 argCountPrf)))). 
                apply (Forall2_shiftout).
                assumption. }
              generalize (CL_ApplyPath _ _ _ _ _ _
                                       path_path rootPrf'
                                       srcPrfs').
              intro Mprf.
              rewrite (applyAllSpec M) in Mprf.
              rewrite (split_path_step _ _ argCountPrf' argCountPrf) in Mprf.
              exact Mprf.
            + simpl argumentsOf in srcPrfs.
              generalize (Forall2_last _ _ _ srcPrfs).
              intro Nprf.
              rewrite (shiftin_last) in Nprf.
              exact Nprf.
            + assumption.
          - apply Exists_cons_tl.
            assert (CL Gamma (Symbol (rootOf (App M N))) (intersect paths)).
            { eapply CL_ST; [ eassumption | ].
              clear ...
              destruct paths.
              - apply ST_OmegaTop.
              - simpl; rewrite (ST_InterMeetRight); reflexivity. }
            auto.
        Qed.
          
        
        Lemma CL_ContextSeparation_sound:
          forall M sigma,
            CL Gamma M sigma ->
            forall n, TypeOf n sigma ->
                 CL (nth contexts n) M sigma.
        Proof.
          intro M.
          intros sigma prf.
          assert (existsS : exists S, WellFormed S).
          { induction prf; try solve [ assumption ].
            eexists; eassumption. }
          revert sigma prf.
          induction M as [ c | M IHM N IHN ].
          - intros sigma prf n n_sigma.
            generalize (CL_Path _ _ _ prf).
            intro path_prfs.
            apply CL_all_paths; [ assumption | ].
            generalize (factorize_typeOf _ _ (organize_typeOf _ _ n_sigma)).
            intro types_of.
            generalize (organized_path_factors _ (organize_organized sigma)).
            intro organized_xs.
            induction path_prfs as [ | ? ? ? [ S [ WF_S ex_prf ] ] ].
            + apply Forall_nil.
            + generalize (Combinator_path_typesOfn (rootOf (Symbol c)) n S WF_S).
              intro paths_inhabited.            
              inversion types_of as [ | ? ? ? type_of_hd types_of_tl n_eq [ hd_eq tl_eq ] ] .
              dependent rewrite tl_eq in types_of_tl.
              apply Forall_cons; [ | auto ].
              clear types_of_tl n_eq hd_eq tl_eq types_of.
              generalize (Combinator_path_types (rootOf (Symbol c)) S WF_S).
              intro path_types.              
              induction ex_prf
                as [ ? path ? [ path_path [ argCountPrf [ _  tgt_le ] ] ]
                   |  ].
              * eapply CL_ST; [ | exact tgt_le ].
                simpl.
                assert (n_path : TypeOf n path).
                { inversion path_types as [ | ? ? ? [ m' m'_path ] ].
                  assert (m'_eq : m' = n).
                  { eapply (ST_typeOf_path);
                      [ | | | exact type_of_hd | exact tgt_le ].
                    - inversion organized_xs.
                      apply Omega_path; assumption.
                    - apply Path_split_path; assumption.
                    - apply (split_path_typeOf_snd); assumption. }
                  rewrite <- m'_eq.
                  assumption. }
                simpl in paths_inhabited.
                inversion paths_inhabited.
                auto.
              * inversion path_types as [ | ? ? ? ? path_types' n_eq' [ hd_eq' tl_eq' ]].
                dependent rewrite tl_eq' in path_types'.
                inversion paths_inhabited as [ | ? ? ? ? paths_inhabited' n_eq'' [ hd_eq'' tl_eq'' ]].
                dependent rewrite tl_eq'' in paths_inhabited'.
                auto.
              * inversion organized_xs as [ | ? ? ? ? organized_xs' n_eq' [ hd_eq' tl_eq' ] ].
                dependent rewrite tl_eq' in organized_xs'.
                auto.              
          - intros sigma prf n n_sigma.
            generalize (CL_Path _ _ _ prf).
            intro path_prfs.
            apply CL_all_paths; [ assumption | ].
            generalize (factorize_typeOf _ _ (organize_typeOf _ _ n_sigma)).
            intro types_of.
            generalize (organized_path_factors _ (organize_organized sigma)).
            intro organized_xs.
            induction path_prfs as [ | ? ? ? [ S [ WF_S ex_prf ] ] ].
            + apply Forall_nil.
            + inversion types_of as [ | ? ? ? type_of_hd types_of_tl n_eq [ hd_eq tl_eq ] ] .
              dependent rewrite tl_eq in types_of_tl.
              apply Forall_cons; [ | auto ].
              clear types_of_tl n_eq hd_eq tl_eq types_of. 
              generalize (Exist_path_unapply _ _ _ _ WF_S ex_prf).
              intro ex_prf'.
              clear ex_prf.
              generalize (Combinator_path_types (rootOf (App M N)) S WF_S).
              intro path_types.
              induction ex_prf'
                as [ ? path ? [ path_path [ argCountPrf [ Mprf [ Nprf tgt_le ] ] ] ]
                   |  ].
              * eapply CL_ST; [ | exact tgt_le ].
                assert (n_path : TypeOf n path).
                { inversion path_types as [ | ? ? ? [ m' m'_path ] ].
                  assert (m'_eq : m' = n).
                  { eapply (ST_typeOf_path);
                      [ | | | exact type_of_hd | exact tgt_le ].
                    - inversion organized_xs.
                      apply Omega_path; assumption.
                    - apply Path_split_path; assumption.
                    - apply (split_path_typeOf_snd); assumption. }
                  rewrite <- m'_eq.
                  assumption. }
                assert (argCountPrf' : (argumentCount M <= src_count path)%nat).
                { etransitivity; [ apply le_S | eassumption ]; reflexivity. }
                eapply CL_MP.
                { apply IHM.
                  - eassumption.
                  - rewrite <- (split_path_step _ _ argCountPrf').
                    apply (split_path_typeOf_snd).
                    assumption. }
                { apply IHN.
                  - assumption.
                  - apply Forall_last.
                    apply (split_path_typeOf_fst).
                    assumption. }
              * inversion path_types as [ | ? ? ? ? path_types' n_eq' [ hd_eq' tl_eq' ] ].
                dependent rewrite tl_eq' in path_types'.
                auto.
              * inversion organized_xs as [ | ? ? ? ? org_tl n_eq' [ hd_eq' tl_eq' ] ].
                dependent rewrite tl_eq' in org_tl.
                auto.
        Qed.

        Lemma CL_ContextSeparation_complete:
          forall M sigma n, CL (nth contexts n) M sigma -> CL Gamma M sigma.
        Proof.
          intros M sigma n prf.
          induction prf.
          - eapply CL_ST; [ apply CL_Var; eassumption | ].
            unfold Gamma.
            rewrite Apply_Distrib.
            etransitivity; [ apply (ST_intersect_nth _ n) | ].
            rewrite (nth_map (fun ctxt => Apply S (ctxt c)) contexts _ n eq_refl).
            reflexivity.
          - eapply CL_MP; eassumption.
          - eapply CL_II; eassumption.
          - eapply CL_ST; eassumption.
        Qed.
          
        
      End CombinedContext.            
    End Disjoint.
  End DisjointTypeSystem.
End DisjointContexts.  
  
(* Garbage  

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

*)