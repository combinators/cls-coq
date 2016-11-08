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
Require Import ConstructiveExtensionalEpsilon.
Require Import Cantor.

Import EqNotations.
Open Scope intersection_types.

Module Type CountableTypeSignature <: TypeSignature.
  Include TypeSignature.
  Declare Instance ConstructorSymbol_countable: Countable ConstructorSymbol.
  Declare Instance Variables_finite: Finite VariableSymbol.
End CountableTypeSignature.

Module Type CountableTypes
       (Import Signature: CountableTypeSignature)
       (Import Types: IntersectionTypes.IntersectionTypes Signature).

  Definition vectToNat {A: Set} (toNat: A -> nat) {n: nat} (xs: t A n): nat :=
    (fix vectToNat_rec (n: nat) (xs: t A n): nat :=
       match xs with
       | nil _ => 0
       | cons _ x n xs => cantor_pair (toNat x) (vectToNat_rec _ xs)
       end) _ xs.
  
  Fixpoint typeToNat_rec (tau: IntersectionType): nat :=
    match tau with
    | Ty (PT_omega) => cantor_sum (inl 0)
    | Ty (PT_Const C args) =>
      cantor_sum (* omega + ... *)
        (inr (cantor_sum (* const + ... *)
                (inl (cantor_pair (toNat C) (vectToNat typeToNat_rec args)))))
    | Ty (PT_Arrow sigma tau) =>
      cantor_sum (* omega + ... *)
        (inr (cantor_sum (* const + ... *)
                (inr (cantor_sum (* arrow + inter *)
                        (inl (cantor_pair (typeToNat_rec sigma) (typeToNat_rec tau)))))))
    | Ty (PT_Inter sigma tau) =>
      cantor_sum (* omega + ... *)
        (inr (cantor_sum (* const + ... *)
                (inr (cantor_sum (* arrow + inter *)
                        (inr (cantor_pair (typeToNat_rec sigma) (typeToNat_rec tau)))))))
    end.

  Fixpoint fuelForType (tau: IntersectionType): nat :=
    match tau with
    | Ty (PT_omega) => 1
    | Ty (PT_Const C args) => 1 + (fold_right (Nat.max) (map fuelForType args) 0)
    | Ty (PT_Arrow sigma tau) => 1 + (Nat.max (fuelForType sigma) (fuelForType tau))
    | Ty (PT_Inter sigma tau) => 1 + (Nat.max (fuelForType sigma) (fuelForType tau))
    end.

  Definition typeToNat (tau: IntersectionType): nat :=
    cantor_pair (fuelForType tau) (typeToNat_rec tau).
  
  Definition vectFromNat {A: Set} (fromNat: nat -> A) (m: nat) (n: nat): t A m :=
    (fix vectFromNat_rec m n: t A m :=
       match m with
       | 0 => nil _
       | S m => cons _ (fromNat (fst (cantor_pair_inv n))) _
                    (vectFromNat_rec m (snd (cantor_pair_inv n)))
       end) m n.

  Fixpoint natToType_rec (fuel n: nat): IntersectionType :=
    match fuel with
    | 0 => omega
    | S fuel =>
      match cantor_sum_inv n with
      | inl _ => omega
      | inr n =>
        match cantor_sum_inv n with
        | inl n =>
          Const (fromNat (fst (cantor_pair_inv n)))
                (vectFromNat (natToType_rec fuel) _ (snd (cantor_pair_inv n)))
        | inr n =>
          match cantor_sum_inv n with
          | inl n =>
            Arrow (natToType_rec fuel (fst (cantor_pair_inv n)))
                  (natToType_rec fuel (snd (cantor_pair_inv n)))
          | inr n =>
            Inter (natToType_rec fuel (fst (cantor_pair_inv n)))
                  (natToType_rec fuel (snd (cantor_pair_inv n)))
          end
        end
      end
    end.
  
  Definition natToType (n: nat): IntersectionType :=
     natToType_rec (fst (cantor_pair_inv n)) (snd (cantor_pair_inv n)).

  Lemma omega_inj: forall fuel, natToType_rec fuel (typeToNat_rec omega) = omega.
  Proof.
    intro fuel.
    destruct fuel; reflexivity.
  Qed.

  Lemma arrow_inj:
    forall sigma tau
      (IH_sigma: forall fuel, fuel >= fuelForType sigma -> natToType_rec fuel (typeToNat_rec sigma) = sigma)
      (IH_tau: forall fuel, fuel >= fuelForType tau -> natToType_rec fuel (typeToNat_rec tau) = tau)
      fuel,
      fuel >= S (Nat.max (fuelForType sigma) (fuelForType tau)) ->
      natToType_rec fuel (typeToNat_rec (Arrow sigma tau)) = Arrow sigma tau.
  Proof.
    intros sigma tau IH_sigma IH_tau fuel max_prf.
    destruct fuel.
    - inversion max_prf.
    - unfold typeToNat_rec.
      unfold Arrow.
      unfold liftPreType.
      unfold natToType_rec.
      rewrite cantor_sum_inj.
      rewrite cantor_sum_inj.
      rewrite cantor_sum_inj.
      rewrite <- cantor_pair_inj.
      generalize (IH_sigma fuel (Nat.le_trans _ _ _  (Nat.le_max_l _ _)
                                              (proj2 (Nat.succ_le_mono _ _) max_prf))).
      generalize (IH_tau fuel (Nat.le_trans _ _ _  (Nat.le_max_r _ _)
                                            (proj2 (Nat.succ_le_mono _ _) max_prf))).
      intros tau_eq sigma_eq.
      fold (typeToNat_rec sigma).
      fold (typeToNat_rec tau).
      fold (natToType_rec fuel (fst (typeToNat_rec sigma, typeToNat_rec tau))).
      fold (natToType_rec fuel (snd (typeToNat_rec sigma, typeToNat_rec tau))).
      unfold fst.
      unfold snd.
      rewrite sigma_eq.
      rewrite tau_eq.
      reflexivity.
  Qed.

  Lemma inter_inj:
    forall sigma tau
      (IH_sigma: forall fuel, fuel >= fuelForType sigma -> natToType_rec fuel (typeToNat_rec sigma) = sigma)
      (IH_tau: forall fuel, fuel >= fuelForType tau -> natToType_rec fuel (typeToNat_rec tau) = tau)
      fuel,
      fuel >= S (Nat.max (fuelForType sigma) (fuelForType tau)) ->
      natToType_rec fuel (typeToNat_rec (Inter sigma tau)) = Inter sigma tau.
  Proof.
    intros sigma tau IH_sigma IH_tau fuel max_prf.
    destruct fuel.
    - inversion max_prf.
    - unfold typeToNat_rec.
      unfold Inter.
      unfold liftPreType.
      unfold natToType_rec.
      rewrite cantor_sum_inj.
      rewrite cantor_sum_inj.
      rewrite cantor_sum_inj.
      rewrite <- cantor_pair_inj.
      generalize (IH_sigma fuel (Nat.le_trans _ _ _  (Nat.le_max_l _ _)
                                              (proj2 (Nat.succ_le_mono _ _) max_prf))).
      generalize (IH_tau fuel (Nat.le_trans _ _ _  (Nat.le_max_r _ _)
                                            (proj2 (Nat.succ_le_mono _ _) max_prf))).
      intros tau_eq sigma_eq.
      fold (typeToNat_rec sigma).
      fold (typeToNat_rec tau).
      fold (natToType_rec fuel (fst (typeToNat_rec sigma, typeToNat_rec tau))).
      fold (natToType_rec fuel (snd (typeToNat_rec sigma, typeToNat_rec tau))).
      unfold fst.
      unfold snd.
      rewrite sigma_eq.
      rewrite tau_eq.
      reflexivity.
  Qed.

  Lemma vect_inj:
    forall (A: Set) n (xs: t A n) (fromNat: nat -> A) (toNat: A -> nat)
      (IH: Forall (fun x => fromNat (toNat x) = x) xs),
      vectFromNat fromNat n (vectToNat toNat xs) = xs.
  Proof.
    intros A n xs fromNat toNat prfs.
    induction prfs as [ | n x xs prf prfs IH ].
    - reflexivity.
    - unfold vectToNat.
      unfold vectFromNat.
      rewrite <- cantor_pair_inj.
      unfold fst.
      unfold snd.
      rewrite prf.
      apply f_equal.
      apply IH.
  Qed.

  Lemma ctor_inj:
    forall C (args: t IntersectionType (constructorArity C))
      (IH: ForAll' (fun arg => forall fuel, fuel >= fuelForType arg -> natToType_rec fuel (typeToNat_rec arg) = arg) args)
      fuel,
      fuel >= 1 + (fold_right (Nat.max) (map fuelForType args) 0) ->
      natToType_rec fuel (typeToNat_rec (Const C args)) = Const C args.
  Proof.
    intros C args IH fuel max_prf.
    destruct fuel.
    - inversion max_prf.
    - assert (args_inj: Forall (fun arg => natToType_rec fuel (typeToNat_rec arg) = arg) args).
      { apply nth_Forall.
        generalize (proj2 (Nat.succ_le_mono _ _) max_prf); clear max_prf; intro max_prf.
        intro k.
        apply (Forall_nth _ _ (ForAll'Forall _ _ IH) k fuel).
        clear IH.
        eapply (Nat.le_trans); [ | apply max_prf].
        rewrite <- (nth_map fuelForType _ _ _ eq_refl).
        simpl.
        clear max_prf.
        generalize 0.
        induction k as [ | arity k IH ].
        - intro s.
          apply (caseS' args); clear args; intros arg args.
          simpl.
          apply Nat.le_max_l.
        - intro s.
          apply (caseS' args); clear args; intros arg args.
          simpl.
          rewrite (IH args s).
          apply Nat.le_max_r. }
      unfold typeToNat_rec.
      unfold Const.
      unfold liftPreType.
      unfold natToType_rec.
      rewrite cantor_sum_inj.
      rewrite cantor_sum_inj.
      rewrite <- cantor_pair_inj.
      unfold fst.
      rewrite fromTo_id.
      unfold snd.
      fold (typeToNat_rec).
      generalize (vect_inj _ _ _ _ _ args_inj).
      intro args_eq.
      unfold natToType_rec in args_eq.
      rewrite <- args_eq at 2.
      unfold Const.
      unfold liftPreType.
      reflexivity.
  Qed.

  Lemma natType_rec_inj:
    forall tau fuel, fuel >= fuelForType tau -> natToType_rec fuel (typeToNat_rec tau) = tau.
  Proof.
    intro tau.
    induction tau using IntersectionType_rect'.
    - intros; apply omega_inj.
    - intros; apply ctor_inj; assumption.
    - intros; apply arrow_inj; assumption.
    - intros; apply inter_inj; assumption.
  Qed.

  Lemma natType_inj:
    forall tau, natToType (typeToNat tau) = tau.
  Proof.
    intro tau.
    unfold typeToNat.
    unfold natToType.
    rewrite <- cantor_pair_inj.
    simpl fst.
    simpl snd.
    apply natType_rec_inj.
    unfold ge.
    reflexivity.
  Qed.

  Instance TypesCountable : `{Countable IntersectionType} :=
    {| toNat := typeToNat;
       fromNat := natToType;
       fromTo_id := natType_inj |}.
  
End CountableTypes.

Module Type DecidableWellFormedPredicate
       (Signature: TypeSignature)
       (Import Types: IntersectionTypes.IntersectionTypes Signature) <: WellFormedPredicate(Signature)(Types).
  Include WellFormedPredicate(Signature)(Types).  
  Parameter WF_dec: forall S, { WellFormed S } + { ~ WellFormed S }.
  Parameter WF_ext: forall S S', (forall alpha, S alpha = S' alpha) -> WellFormed S -> WellFormed S'.
End DecidableWellFormedPredicate.

Module Type CountableTypeAndTermSignature := CountableTypeSignature <+ TermSignature.

Module Type ComputationalPathLemma
       (Import TypesAndTermsSig: CountableTypeAndTermSignature)
       (Import Types: IntersectionTypes.IntersectionTypes(TypesAndTermsSig))
       (Import Terms: CombinatoryTerm.Terms(TypesAndTermsSig))
       (Import TypesCountable: CountableTypes(TypesAndTermsSig)(Types))
       (Import WF: DecidableWellFormedPredicate(TypesAndTermsSig)(Types))
       (Import CL: CombinatoryLogic(TypesAndTermsSig)(Types)(Terms)(WF)).

  Definition SubstToNat (S: Substitution): nat :=
    cantor_fin_fun _ (fun alpha => toNat (S (fromFin alpha))).

  Definition natToSubst (n: nat): Substitution :=
    fun alpha => fromNat (cantor_fin_fun_inv _ n (toFin alpha)).

  Lemma natSubst_inj: forall S alpha, natToSubst (SubstToNat S) alpha = S alpha.
  Proof.
    intros S alpha.
    unfold natToSubst.
    unfold SubstToNat.
    rewrite <- cantor_fin_fun_ext_inj.
    rewrite fromTo_id.
    rewrite fromToFin_id.
    reflexivity.
  Qed.
  
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
        + eapply (constructive_extensional_indefinite_ground_description).
          * apply natSubst_inj.
          * apply S_sufficient_dec.
          * intros S S' S_eq wf_exists.
            destruct wf_exists as [ WF exprf ].
            split.
            { eapply WF_ext; eassumption. }
            { rewrite <- (Apply_ext _ _ S_eq).
              assumption. }
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
      eapply (constructive_extensional_indefinite_ground_description).
      - apply natSubst_inj.
      - apply S_sufficient_dec.
      - intros S S' S_eq wf_exists.
        destruct wf_exists as [ WF exprf ].
        split.
        + eapply WF_ext; eassumption.
        + rewrite <- (Apply_ext _ _ S_eq).
          assumption.
      - assumption.
    Qed.
  End TypeCheckable.
End ComputationalPathLemma.