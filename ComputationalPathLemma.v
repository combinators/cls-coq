Require Import Coq.Logic.ConstructiveEpsilon.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Vectors.Fin.
Require Import Coq.Vectors.Vector.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Lists.ListDec.

Require Import VectorQuantification.
Require Import CombinatoryLogic.
Require Import IntersectionTypes.
Require Import CombinatoryTerm.
Require Import Cantor.

Import EqNotations.
Open Scope intersection_types.

Module Type CountableTypeSignature <: TypeSignature.
  Include TypeSignature.
  Declare Instance ConstructorSymbol_countable: Countable ConstructorSymbol.
  Declare Instance Variables_finite: Finite VariableSymbol.
End CountableTypeSignature.

Module Type DecidableWellFormedPredicate
       (Signature: TypeSignature)
       (Import Types: IntersectionTypes.IntersectionTypes Signature) <: WellFormedPredicate(Signature)(Types).
  Include WellFormedPredicate(Signature)(Types).  
  Parameter WF_dec: forall S, { WellFormed S } + { ~ WellFormed S }.  
End DecidableWellFormedPredicate.

Module Type CountableTypeAndTermSignature := CountableTypeSignature <+ TermSignature.

Module Type ComputationalPathLemma
       (Import TypesAndTermsSig: CountableTypeAndTermSignature)
       (Import Types: IntersectionTypes.IntersectionTypes(TypesAndTermsSig))
       (Import Terms: CombinatoryTerm.Terms(TypesAndTermsSig))
       (Import WF: DecidableWellFormedPredicate(TypesAndTermsSig)(Types))
       (Import CL: CombinatoryLogic(TypesAndTermsSig)(Types)(Terms)(WF)).
  (* TODO: Show me *)
  Axiom SubstitutionSpace_countable: `{Countable Substitution}. 
  
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
          * apply (fromTo_id).
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
      - apply (fromTo_id).
      - apply S_sufficient_dec.
      - assumption.
    Qed.
  End TypeCheckable.
End ComputationalPathLemma.