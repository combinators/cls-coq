Require Import Coq.Classes.RelationClasses.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Vectors.Fin.
Require Import Coq.Vectors.Vector.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Arith.PeanoNat.
Require Import VectorQuantification.

Module Type SymbolSpecification.
  Parameter ConstructorSymbol: Set.
  Parameter constructorArity: ConstructorSymbol -> nat.
  Parameter ConstructorTaxonomy : ConstructorSymbol -> ConstructorSymbol -> Prop.
  Parameter CTPreorder : PreOrder ConstructorTaxonomy.

  Parameter VariableSymbol: Set.
  Parameter CombinatorSymbol: Set.
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
  
  Inductive Path: IntersectionType -> Prop :=
  | Path_Const: forall C args, PathArgs args -> Path (Const C args)
  | Path_Arr: forall sigma tau, Path tau -> Path (Arrow sigma tau)
  with PathArgs: forall {n}, t IntersectionType n -> Set :=
       | PathArgs_nil: PathArgs (nil _)
       | PathArgs_cons_arg: forall n sigma, Path sigma -> PathArgs (cons _ sigma _ (const omega n))
       | PathArgs_cons_omega: forall n args, PathArgs args -> PathArgs (cons _ omega n args).

  Inductive Organized: IntersectionType -> Prop :=
  | Organized_Path: forall sigma, Path sigma -> Organized sigma
  | Organized_Cons: forall sigma tau, Path sigma -> Organized tau -> Organized (Inter sigma tau).

  Lemma arityEq: forall n m, ((S m) <= n)%nat ->  (n - (S m) + S ((S m) - 1))%nat = n.
  Proof.
    intros n m leq.
    simpl.
    rewrite (Nat.sub_0_r m).
    rewrite (Nat.sub_add).
    - reflexivity.
    - assumption.
  Qed.

  Definition fill
             (C: ConstructorSymbol)
             (pos: nat)
             (posOk: (S pos <= constructorArity C)%nat)
             (arg: IntersectionType): IntersectionType :=
    
    Ty (PT_Const C
                 (rew (arityEq _ _ posOk) in
                     (append (const omega (constructorArity C - (S pos)))
                             (cons _ arg _ (const omega ((S pos) - 1)))))).

  Definition organizeArgs
             (organize: IntersectionType -> { k : _ & t IntersectionType k})
             C
             n (args: t IntersectionType n)
             (nOk : (n <= constructorArity C)%nat): { k : _ & t IntersectionType k } :=
    (fix organizeArgs'
        n (args: t IntersectionType n)
        (nOk : (n <= constructorArity C)%nat)
        {struct args}: { k : _ & t IntersectionType k } :=
      match args with
      | cons _ arg n args =>
        fun (nOk: (S n <= constructorArity C)%nat) =>
          let orgArg := organize arg in
          let filledArg := existT _
                                  (projT1 orgArg)
                                  (map (fill C _ nOk) (projT2 orgArg)) in
          let orgRest := organizeArgs' _ args (Nat.lt_le_incl _ _ nOk) in
          existT _
                 (plus (projT1 filledArg) (projT1 orgRest))
                 (append (projT2 filledArg) (projT2 orgRest))
      | _ =>
        fun nOk => existT _ 1 (cons _ (Ty (PT_Const C (const omega _))) _ (nil _))
      end nOk) _ args nOk.
  
  Fixpoint organize (sigma: IntersectionType): { k : _ & t IntersectionType k } :=
    match sigma with
    | Ty PT_omega => existT _ 0 (nil _)
    | Ty (PT_Const C args) => organizeArgs organize C _ args (Nat.le_refl _)
    | Ty (PT_Inter sigma tau) =>
      existT _
        (plus (projT1 (organize sigma)) (projT1 (organize tau)))
        (append (projT2 (organize sigma)) (projT2 (organize tau)))
    | Ty (PT_Arrow sigma tau) =>
      existT _
             (projT1 (organize tau))
             (map (Arrow sigma) (projT2 (organize tau)))
    end.

  Lemma omegaPathArgs: forall n, PathArgs (const omega n).
  Proof.
    intro n.
    induction n.
    - apply PathArgs_nil.
    - apply PathArgs_cons_omega.
      assumption.
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

  Lemma omegaOrganize: forall tau, omega <= tau -> projT1 (organize tau) = 0.
  Proof.
    intro tau.
    induction tau
      as [ | | sigma' tau' IHsigma' IHtau' | sigma' tau' IHsigma' IHtau' ]
           using IntersectionType_rect'; intro omegaTau.
    - reflexivity.
    - contradict (Omega_complete _ _ omegaTau I).
    - apply IHtau'.
      apply Omega_sound.
      cut (Omega (Arrow sigma' tau')).
      + apply id.
      + apply (Omega_complete omega).
        * assumption.
        * simpl; trivial.
    - destruct (Omega_complete _ _ omegaTau I)
        as [ omegaSigma' omegaTau' ].
      simpl.
      rewrite (IHsigma' (Omega_sound _ omegaSigma')).
      rewrite (IHtau' (Omega_sound _ omegaTau')).
      reflexivity.
  Qed.

  Lemma pathPathArgs:
    forall n m sigma, Path sigma -> PathArgs (append (const omega n) (cons _ sigma _ (const omega m))).
  Proof.
    intro n.
    induction n; intros m sigma pathSigma.
    - apply PathArgs_cons_arg.
      assumption.
    - apply PathArgs_cons_omega.
      auto.
  Qed.
    
  Lemma fillPath:
    forall C {n} (args: t IntersectionType n) {pos} (posOk: (S pos <= constructorArity C)%nat),
      Forall Path args -> Forall Path (map (fill C _ posOk) args).
  Proof.
    intros C n args.
    induction args; intros pos posOk argsPaths.
    - apply Forall_nil.
    - inversion argsPaths
        as [ | n' arg args' argPrf argsPrf nEq [ argEq argsEq ] ].
      dependent rewrite argsEq in argsPrf.
      clear argsEq argEq nEq n' arg args'.
      apply Forall_cons.
      + apply Path_Const.
        clear IHargs.
        rewrite <- (arityEq (constructorArity C) pos posOk).
        simpl.
        apply pathPathArgs.
        assumption.
      + fold (map (fill C _ posOk) args).
        apply IHargs.
        assumption.
  Qed.

  Lemma organizeArgsPaths:
    forall C {n} (args: t IntersectionType n)
      (nOk: (n <= constructorArity C)%nat),
      ForAll'
        (fun tau => Forall Path (projT2 (organize tau)))
        args -> Forall Path (projT2 (organizeArgs organize C _ args nOk)).
  Proof.
    intros C n args.
    induction args as [ | arg n args IH ]; intros nOk argsOrg.
    - apply Forall_cons.
      + apply Path_Const.
        apply omegaPathArgs.
      + apply Forall_nil.
    - inversion argsOrg
        as [ | arg' n' args' argOrg argsOrg' nEq [ argEq argsEq ] ].
      dependent rewrite argsEq in argsOrg'.
      clear nEq argEq argsEq n' arg' args' argsOrg.
      apply Forall_append.
      + apply fillPath; assumption.
      + apply IH; assumption.
  Qed.

  Lemma mapArrowPath:
    forall sigma {n} (taus: t IntersectionType n),
      Forall Path taus -> Forall Path (map (Arrow sigma) taus).
  Proof.
    intros n sigma taus.
    induction taus; intro paths.
    - apply Forall_nil.
    - inversion paths as [ | ? ? ? pathh pathtl nEq [ hEq tlEq ] ].
      dependent rewrite tlEq in pathtl.
      clear nEq hEq tlEq.
      apply Forall_cons.
      * apply Path_Arr; assumption.
      * auto.
  Qed.
    
  Lemma organizeOrganized: forall tau, Forall Path (projT2 (organize tau)).
  Proof.
    intro tau.
    induction tau using IntersectionType_rect'.
    - apply Forall_nil.
    - apply organizeArgsPaths; assumption.
    - apply mapArrowPath; assumption.
    - apply Forall_append; assumption.
  Qed.

  Lemma ST_constOmega:
    forall {n} (sigmas: t IntersectionType n),
      Forall2 Subtypes sigmas (const omega n).
  Proof.
    intros n sigmas.
    induction sigmas.
    - apply Forall2_nil.
    - apply Forall2_cons.
      + apply ST_OmegaTop.
      + assumption.
  Qed.

  (*
  Lemma fillArgsConsts:
    forall C {n} (args: t IntersectionType n) {m} mOk,
      Forall (fun tau => exists args', tau = Const C args') (map (fill C m mOk) args).
  Proof.
    intros C n args.
    induction args; intros m mOk.
    - apply Forall_nil.
    - apply Forall_cons.
      + eexists; reflexivity.
      + fold (map (fill C m mOk) args); auto.
  Qed.

  Lemma organizeArgsConsts:
    forall C {n} (args: t IntersectionType n) nOk, Forall (fun tau => exists args', tau = Const C args') (projT2 (organizeArgs organize C _ args nOk)).
  Proof.
    intros C n args.
    induction args; intro nOk.
    - apply Forall_cons.
      + exists (const omega _); reflexivity.
      + apply Forall_nil.
    - apply Forall_append.
      + apply fillArgsConsts.
      + auto.
  Qed.

  Lemma ST_organizeArgs:
    forall C {n} (args: t IntersectionType n) nOk, Forall (fun tau => 
   *)

  Definition IsConst (sigma: IntersectionType): Prop :=
    match sigma with
    | Ty (PT_Const C args) => True
    | _ => False
    end.

  Definition getC (sigma: IntersectionType) (ok: IsConst sigma): ConstructorSymbol :=
    match sigma with
    | Ty (PT_Const C args) => fun ok => C
    | x => fun (ok : IsConst x) => False_rec _ ok
    end ok.

  Definition getArgs (sigma: IntersectionType) (ok: IsConst sigma): { k : _ & t IntersectionType k } :=
    match sigma with
    | Ty (PT_Const C args) => fun ok => existT _ (constructorArity C) args
    | x => fun (ok : IsConst x) => False_rec _ ok
    end ok.

  Lemma getArgsCount: forall sigma (ok: IsConst sigma),
      projT1 (getArgs sigma ok) = (constructorArity (getC sigma ok)).
  Proof.
    intro sigma.
    induction sigma using IntersectionType_rect';
      intro ok; try solve [ contradiction ].
    reflexivity.
  Defined.
    
  Lemma constSpec: forall sigma (ok : IsConst sigma),
      sigma = Ty (PT_Const (getC sigma ok) (rew (getArgsCount sigma ok) in projT2 (getArgs sigma ok))).
  Proof.
    intro sigma.
    induction sigma using IntersectionType_rect';
      intro ok; try solve [ contradiction ].
    reflexivity.
  Defined.

  Lemma ST_Const_Split:
    forall C (args: t IntersectionType (constructorArity C)) sigma,
      (exists (ok: IsConst sigma) (cEq: C = getC sigma ok),
        (Forall2 Subtypes
                 args
                 (rew <- (f_equal constructorArity cEq) in
                     rew (getArgsCount sigma ok) in projT2 (getArgs sigma ok)))) ->
      (Ty (PT_Const C args)) <= sigma.
  Proof.
    intros C args sigma [ ok [ cEq prfs ] ].
    rewrite (constSpec _ ok).
    apply (ST_Ax _ _ (f_equal constructorArity cEq)).
    - rewrite <- cEq.
      reflexivity.
    - assumption.
  Qed.


  Lemma foo:
    forall C {n} (args: t IntersectionType (S n)) (nOk: (S n <= constructorArity C)%nat),
      Forall (fun tau => Ty (PT_Const C
                                   (rew (Nat.sub_add _ _ nOk) in
                                       (append (const omega (constructorArity C - (S n)))
                                               args))) <= tau)
             (projT2 (organizeArgs organize C _ args nOk)).
  Proof.
    intros C n args.
    induction args; intro nOk.
    - apply Forall_cons.
      + eapply ST_Ax.
        * reflexivity.
        * 
  
  Lemma organize_le: forall tau, tau <= intersect (projT2 (organize tau)).
  Proof.
    intro tau.
    induction tau
      as [ | C args IH | | ] using IntersectionType_rect'.
    - reflexivity.
    - apply ST_intersect.
      simpl.
      eapply Forall_ap; [ | apply ForAll'Forall; exact IH ].
      
      
      apply
        (Forall_ap _
                   (fun sigma =>
                      exists (ok : IsConst sigma) (cEq: C = (getC sigma ok)),
                        Forall2 Subtypes
                                args
                                (rew <- (f_equal constructorArity cEq) in
                                    rew (getArgsCount sigma ok) in projT2 (getArgs sigma ok)))).
      + apply Forall_tautology.
        apply ST_Const_Split.
      + simpl.
        
      apply (Forall_depAp _ _ (ST_Const_Split )).
      
      apply nth_Forall.
      intro k.
      simpl.
      inversion k.
      + 
      apply ST_Ax.
         
    
  
  
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

    Inductive CL (Gamma : Context): Term -> IntersectionType -> Type :=
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
        CL Gamma (App M N) tau -> { sigma: _ & CL Gamma M (Arrow sigma tau) * CL Gamma N sigma }.
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

    Lemma ForAll2'_tail: forall {n: nat} {A B: Type} (P : A -> B -> Type) (xs: t A (S n)) (ys: t B (S n)) (prfs: ForAll2' P xs ys), ForAll2' P (tl xs) (tl ys).
    Proof.
      intros n A B P xs ys prfs.
      inversion prfs as [ | ? ? ? ? ? ? ? ? n_eq m_eq xs_eq ys_eq ].
      revert xs_eq.
      revert ys_eq.
      apply (caseS' xs
                    (fun xs =>
                       (existT _ (S n) (cons _ y _ ys0) = existT _ (S n) ys) ->
                       (existT _ (S n) (cons _ x _ xs0) = existT _ (S n) xs) ->
                       ForAll2' P (tl xs) (tl ys))).
      intros x' xs'.
      apply (caseS' ys
                    (fun ys =>
                       (existT _ (S n) (cons _ y _ ys0) = existT _ (S n) ys) ->
                       (existT _ (S n) (cons _ x _ xs0) = existT _ (S n) (cons _ x' _ xs')) ->
                       ForAll2' P (tl (cons _ x' _ xs')) (tl ys))).
      intros y' ys'.
      intros ys_eq xs_eq.
      injection xs_eq as x_eq xs'_eq.
      injection ys_eq as y_eq ys'_eq.
      simpl.
      set (G := fun n xs' => ForAll2' (n := n) P xs' ys').
      fold (G n xs').
      dependent rewrite <- xs'_eq.
      unfold G.
      set (G' := fun n ys' => ForAll2' (m := n) P xs0 ys').
      fold (G' n ys').
      dependent rewrite <- ys'_eq.
      unfold G'.
      assumption.
    Qed.
        

    Lemma ForAll2'_shiftin: forall {n : nat} {A B: Type} (P : A -> B -> Type) (xs: t A n) (ys: t B n) (prfs: ForAll2' P xs ys) (x: A) (y: B) (prf: P x y), ForAll2' P (shiftin x xs) (shiftin y ys).
    Proof.
      intro n.
      induction n; intros A B P xs ys prfs x y prf.
      - apply (case0 (fun xs => ForAll2' P (shiftin x xs) (shiftin y ys))).
        apply (case0 (fun ys => ForAll2' P (shiftin x (nil _)) (shiftin y ys))).
        apply ForAll2'_cons.
        + assumption.
        + apply ForAll2'_nil.
      - generalize prfs.
        clear prfs.
        apply (caseS' _ (fun xs => ForAll2' P xs ys -> ForAll2' P (shiftin x xs) (shiftin y ys))).
        intros x' xs'.
        apply (caseS' _ (fun ys => ForAll2' P (cons _ x' _ xs') ys -> ForAll2' P (shiftin x (cons _ x' _ xs')) (shiftin y ys))).
        intros y' ys' prfs.
        simpl.
        apply ForAll2'_cons.
        + inversion prfs; assumption.
        + apply IHn.
          * exact (ForAll2'_tail _ _ _ prfs).
          * inversion prfs; assumption.
    Qed.                       

    Lemma MP_generation_iterated: forall Gamma M tau,
        CL Gamma M tau -> { sigmas : t IntersectionType (argumentCount M) &
                           CL Gamma (Symbol (rootOf M)) (makeArrow sigmas tau) *
                           ForAll2' (CL Gamma) (argumentsOf M) sigmas }.
    Proof.
      intros Gamma M.
      induction M as [ | M' IHM' N IHN ].
      - intros tau prf.
        exists (nil _).
        split.
        + exact prf.
        + apply ForAll2'_nil.
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
    Qed.
            
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

    Lemma II_Admissible:
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
      - destruct (MP_generation _ _ _ _ prf) as [ sigma [ M1_prf M2_prf ] ].
        apply (MP_case _ _ sigma).
        + assumption.
        + apply IHM1; assumption.
        + assumption.
        + apply IHM2; assumption.
    Qed.                                                              
  End FCL.
End FiniteCombinatoryLogic.

Module Type DisjointContexts(Symbols: SymbolSpecification) <: CombinatoryLogic(Symbols).
  Include CombinatoryLogic(Symbols).

  Parameter numberOfContexts: nat.
  Parameter SymbolOf: Fin.t numberOfContexts -> ConstructorSymbol -> Prop.

  Parameter SymbolOfDecidable: forall C n, SymbolOf n C + (SymbolOf n C -> False).
  Parameter SymbolsDisjoint: forall C n m, n <> m -> SymbolOf n C -> SymbolOf m C -> False.
  Parameter SymbolsFull: forall C, exists n, SymbolOf n C.
  Parameter SymbolsUnrelated: forall C1 C2 n m,
      n <> m -> SymbolOf n C1 -> SymbolOf m C2 -> ConstructorTaxonomy C1 C2 -> False.

  Parameter VariableOf : Fin.t numberOfContexts -> VariableSymbol -> Prop.
  Parameter VariablesDecidable: forall alpha n, VariableOf n alpha \/ (VariableOf n alpha -> False).
  Parameter VariablesDisjoint: forall alpha n m, n <> m -> VariableOf n alpha -> VariableOf m alpha -> False.
  Parameter VariablesFull: forall alpha, exists n, VariableOf n alpha.

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
      (TypeOf n sigma) \/ (TypeOf n sigma -> False).
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
    - destruct (SymbolOfDecidable C n) as [ prf | disprf ].
      + destruct (decideForall _ _ _ IH) as [ prfs | disprfs ].
        * left; apply ConstOf; assumption.
        * right.
          intro devil.
          inversion devil as [ | ? ? dC dArgs [ dCEq dArgsEq ] | |  ].
          dependent rewrite dArgsEq in dArgs.
          apply disprfs; assumption.
      + right.
        intro devil.
        inversion devil as [ | ? ? dC dArgs [ dCEq dArgsEq ] | | ].
        apply disprf; assumption.
  Qed.

   Lemma decideTypeSchemeOf: forall (sigma: TypeScheme) (n: Fin.t numberOfContexts),
      (TypeSchemeOf n sigma) \/ (TypeSchemeOf n sigma -> False).
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
    - destruct (VariablesDecidable alpha n) as [ prf | disprf ].
      + left; apply TS_VarOf; assumption.
      + right.
        intro devil.
        inversion devil as [ | | | | dalpha dVarOf ].
        apply (disprf dVarOf).
    - left; apply TS_OmegaOf.
    - destruct (SymbolOfDecidable C n) as [ prf | disprf ].
      + destruct (decideForall _ _ _ IH) as [ prfs | disprfs ].
        * left; apply TS_ConstOf; assumption.
        * right.
          intro devil.
          inversion devil as [ | ? ? dC dArgs [ dCEq dArgsEq ] | | | ].
          dependent rewrite dArgsEq in dArgs.
          apply disprfs; assumption.
      + right.
        intro devil.
        inversion devil as [ | ? ? dC dArgs [ dCEq dArgsEq ] | | | ].
        apply disprf; assumption.
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

  
  Module Type DisjointTypeSystem <: TypeSystem.
    Include TypeSystem.
    Parameter WF_respectful:
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
      Variable constextsWF: forall n c, TypeSchemeOf n ((nth contexts n) c).

      Definition Gamma := intersectContexts contexts.

      Lemma foo: forall n c tau 
      
      Axiom combinatorTypesSound:
        forall n c tau, TypeOf n tau -> CL Gamma (Symbol c) tau -> CL (nth contexts n) (Symbol c) tau.

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

