Require Import CombinatoryLogic.

Class DisjointContexts (numberOfContexts : nat) :=
  { SymbolOf: Fin.t numberOfContexts -> ConstructorSymbol -> Prop;
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
    
    Section DisjointTypeSystem.
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
                simpl plus in params_eq.
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
        
        