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

Require Import CombinatoryTerm.
Require Import IntersectionTypes.

Module Type TypeAndTermSignature := TypeSignature <+ TermSignature.
                             
Module Type WellFormedPredicate
       (Signature: TypeSignature)
       (Import Types: IntersectionTypes.IntersectionTypes Signature). 
  Parameter WellFormed: Substitution -> Prop.
End WellFormedPredicate.

Module Type CombinatoryLogic
       (Import TypesAndTermsSig: TypeAndTermSignature)
       (Import Types: IntersectionTypes.IntersectionTypes(TypesAndTermsSig))
       (Import Terms: CombinatoryTerm.Terms(TypesAndTermsSig))
       (Import WF: WellFormedPredicate(TypesAndTermsSig)(Types)). 
      
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
                    unfold argumentCount.
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
End CombinatoryLogic.
    

(*
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
*)

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

