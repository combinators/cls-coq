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

Delimit Scope intersection_types with it.
Open Scope intersection_types.

Class ConstructorSpecification (ConstructorSymbol: Set) :=
  { constructorArity: ConstructorSymbol -> nat;
    ConstructorTaxonomy : ConstructorSymbol -> ConstructorSymbol -> Prop;
    CTPreorder :> PreOrder ConstructorTaxonomy;
    ConstructorSymbol_eq_dec:
      forall (C1 C2: ConstructorSymbol), {C1 = C2} + {C1 <> C2};
    ConstructorTaxonomy_dec:
      forall (C1 C2: ConstructorSymbol), { ConstructorTaxonomy C1 C2 } + { ConstructorTaxonomy C1 C2 -> False }
  }.

Module Type TypeSignature.
  Parameter ConstructorSymbol: Set.
  Parameter VariableSymbol: Set.
  Parameter VariableSymbol_eq_dec:
      forall (alpha beta: VariableSymbol), {alpha = beta} + {alpha <> beta}.
  Declare Instance Symbols : ConstructorSpecification ConstructorSymbol.
End TypeSignature.

Module Type IntersectionTypes(Import TySig: TypeSignature). 
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

  Fixpoint TypeScheme_eq_dec (sigma tau : @TypeScheme VariableSymbol) {struct sigma}: {sigma = tau} + {sigma <> tau}.
  Proof.
    revert tau.
    destruct sigma as [ alpha | [ | C ts | sigma1 sigma2 | sigma1 sigma2 ] ] ;
      intros [ beta | tau ];
      try destruct tau;
      try solve [
            left; reflexivity
          | right; intro devil; inversion devil
          | destruct (TypeScheme_eq_dec sigma1 sigma)
            as [ sigma_eq | sigma_ineq ];
            [ | right; intro devil; injection devil as devil; contradiction ];
            destruct (TypeScheme_eq_dec sigma2 tau)
              as [ tau_eq | tau_ineq ];
            [ | right; intro devil; injection devil as devil; contradiction ];
            left; rewrite sigma_eq; rewrite tau_eq; reflexivity
          | destruct (VariableSymbol_eq_dec alpha beta);
            [ left; apply f_equal; assumption | right; intro devil; inversion devil; contradiction ]
          ].
    - match goal with
      | [ |- context[ Skeleton (PT_Const ?C ?ts) = Skeleton (PT_Const ?C' ?ts') ] ] =>
        destruct (ConstructorSymbol_eq_dec C C') as [ CC'_eq | CC'_not_eq ];
          [ revert ts';
            rewrite <- CC'_eq;
            intro ts';
            clear C' CC'_eq;
            destruct (Vector_eq_dec TypeScheme_eq_dec ts ts')
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
  where "sigma <= tau" := (Subtypes sigma tau) : intersection_types.
  
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

  Lemma ST_path_src_n: forall sigma tau,
      Path sigma -> Path tau ->
      sigma <= tau ->
      forall n (sigmaPrf: (n <= src_count sigma)%nat) (tauPrf: (n <= src_count tau)%nat),
        Forall2 Subtypes (fst (split_path tau n tauPrf)) (fst (split_path sigma n sigmaPrf)).
  Proof.
    intros sigma tau path_sigma.
    revert tau.
    induction path_sigma as [ | ? ? ? IH ].
    - intros tau path_tau sigma_le n n_le.
      simpl in n_le.
      destruct n.
      + intros; apply Forall2_nil.
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
          { apply Forall2_nil.  }
          { apply Forall2_cons.
            - assumption.
            - apply (IH _ path_tau'' tau''_le _
                        (proj2 (Nat.succ_le_mono _ _) sigmaPrf)
                        (proj2 (Nat.succ_le_mono _ _) tauPrf)). }
  Qed.

  (* TODO: Show me *)
  Axiom ST_dec: forall sigma tau, { sigma <= tau } + { sigma <= tau -> False }.
  
End IntersectionTypes.

