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

Module Type FiniteWellFormedPredicate
       (Signature: TypeSignature)
       (Import Types: IntersectionTypes.IntersectionTypes Signature) <: WellFormedPredicate(Signature)(Types).
  Include WellFormedPredicate(Signature)(Types).
  Declare Instance SubstitutionSpace_finite: Finite { S : Substitution | WellFormed S }.
End FiniteWellFormedPredicate.

Module Type CombinatoryLogicWithFiniteSubstitutionSpace
       (Import TypesAndTermsSig: TypeAndTermSignature)
       (Import Types: IntersectionTypes.IntersectionTypes(TypesAndTermsSig))
       (Import Terms: CombinatoryTerm.Terms(TypesAndTermsSig))
       (Import WF: FiniteWellFormedPredicate(TypesAndTermsSig)(Types))
       (Import CL: CombinatoryLogic(TypesAndTermsSig)(Types)(Terms)(WF)).  
  Definition minimalInstance (sigma_pre: TypeScheme): IntersectionType :=
    intersect
      (map
         (fun k => Apply (proj1_sig (fromFin k)) sigma_pre) (positions cardinality)).
  
  Lemma MinimalType_sound:
    forall Gamma c, (cardinality > 0) ->
               CL Gamma (Symbol c) (minimalInstance (Gamma c)).
  Proof.
    intros Gamma c.
    assert (all_prfs: forall k, CL Gamma (Symbol c)
                              (Apply (proj1_sig (fromFin k))
                                     (Gamma c))).
    { intro k.
      apply CL_Var; exact (proj2_sig (fromFin k)). }
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
      assert (S_eq: S = proj1_sig (fromFin (toFin (exist _ S WF_S)))).
      { rewrite fromToFin_id; reflexivity. }
      rewrite S_eq.
      rewrite (ST_intersect_nth _ (toFin (exist _ S WF_S))).
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
      assert (S_fin : S = proj1_sig (fromFin (toFin (exist _ S WF_S)))).
      { rewrite (fromToFin_id).
        reflexivity. }
      rewrite S_fin.
      generalize (toFin (exist _ S WF_S)).
      unfold minimalInstance.
      intros k prfs.
      apply filter_In.
      split.
      - apply (Path_suffixes_split _ _ _ k).
        rewrite (nth_map _ _ _ _ eq_refl).
        rewrite (positions_spec).
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
    destruct (Nat.eq_dec cardinality 0) as [ card_eq | card_ineq ].
    - intro sigma.
      right.
      intro prf.
      induction prf as [ ? S WF_S | | | ]; try solve [ contradiction ].
      generalize (toFin (exist _ S WF_S)).
      destruct cardinality.
      + intro k; inversion k.
      + inversion card_eq.
    - induction M as [ c | M IHM N IHN ].
      + intro sigma.
        destruct (ST_dec (minimalInstance (Gamma c)) sigma).
        * left.
          eapply CL_ST; [ | eassumption ].
          apply MinimalType_sound.
          destruct cardinality; [ contradict (card_ineq eq_refl) | ].
          apply (Nat.lt_0_succ).
        * right.
          intro prf.
          generalize (MinimalType_minimal _ _ _ prf).
          assumption.
      + intro sigma.
        assert (exS : { S : _ | WellFormed S }).
        { eapply (fromFin).
          destruct cardinality; [ contradict (card_ineq eq_refl) | ].
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
    generalize (prf (toFin (exist _ S WF_S))).
    intro nth_le.
    rewrite <- nth_le.
    rewrite (nth_map _ _ _ _ eq_refl).
    rewrite (positions_spec).
    rewrite (fromToFin_id (exist _ S WF_S)).
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
           (fromFin c,
            allPossibleInhabitants_maxcount Gamma tau (fromFin c)))
        (positions cardinality).


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
           possibleRecursiveTargets_maxcount Gamma (fromFin c))
        (positions cardinality).


  Definition MaximalInhabGrammarTgts combinatorsFinite (Gamma: Context): list IntersectionType :=
    List.flat_map
      (fun tgts =>
         List.flat_map
           (fun tgtsOfSize =>
              List.flat_map (to_list) (projT2 tgtsOfSize))
           tgts)
      (to_list (possibleRecursiveTargets combinatorsFinite Gamma)).

  Definition IsRecursiveTarget (combinatorsFinite: Finite CombinatorSymbol) Gamma tau sigma :=
    exists c arrows,
      In (c, arrows) (grammarEntry combinatorsFinite Gamma tau) /\
      List.In
        sigma
        (List.flat_map
           (fun arrowsOfSize =>
              List.flat_map (fun x => to_list (fst x)) (projT2 arrowsOfSize))
           arrows).
  
  Lemma grammarTargetsFinite:
    forall (combinatorsFinite: Finite CombinatorSymbol) Gamma tau sigma, 
      IsRecursiveTarget combinatorsFinite Gamma tau sigma ->
      List.In sigma (MaximalInhabGrammarTgts combinatorsFinite Gamma).
  Proof.
    intros combinatorsFinite Gamma tau sigma.
    unfold IsRecursiveTarget.
    unfold MaximalInhabGrammarTgts.
    unfold grammarEntry.
    unfold possibleRecursiveTargets.
    unfold allPossibleInhabitants_maxcount.
    unfold possibleRecursiveTargets_maxcount.
    unfold allPossibleInhabitants.
    unfold possibleRecursiveTargets_ofSize.
    induction (positions cardinality) as [ | k n ks IH ].
    - simpl.
      intro prf.
      inversion prf as [ c [ arrows [ devil _ ] ] ].
      inversion devil.
    - intro prf.
      inversion prf as [ c [ arrows [ inprf insigma ] ] ].
      simpl.
      apply List.in_or_app.
      simpl in inprf.
      inversion inprf as [ ? ? n_eq [ c_eq here ] | ? ? ? there n_eq [ c_eq tl_eq ] ].
      + left.
        rewrite here in insigma.
        revert insigma.
        clear ...
        induction (MaximalSourceCount (minimalInstance (Gamma (fromFin k)))) as [ | n IH ].
        * simpl.
          rewrite List.app_nil_r.
          rewrite List.app_nil_r.
          induction (powerset (allSplitPaths 0 (minimalInstance (Gamma (fromFin k))))) as [ | hd tl IH ].
          { intro; contradiction. }
          { intro inprf.
            simpl in inprf.
            apply List.in_or_app.
            destruct (ST_dec (intersect (of_list (List.map snd hd))) tau).
            - simpl in inprf.
              destruct (List.in_app_or _ _ _ inprf) as [ inl | inr ].
              + left; assumption.
              + right; apply IH; assumption.
            - right; apply IH; assumption. }                
        * simpl.
          intro inprf.
          rewrite (List.flat_map_concat_map) in inprf.
          rewrite (List.map_app) in inprf.
          rewrite (List.concat_app) in inprf.
          rewrite <- (List.flat_map_concat_map) in inprf.
          rewrite <- (List.flat_map_concat_map) in inprf.
          apply List.in_or_app.
          destruct (List.in_app_or _ _ _ inprf) as [ inl | inr ].
          { right; apply IH; assumption. }
          { left.
            simpl in inr.
            rewrite List.app_nil_r in inr.
            revert inr.
            clear ...
            induction (powerset (allSplitPaths (S n) (minimalInstance (Gamma (fromFin k))))) as [ | hd tl IH ].
            - intro devil; inversion devil.
            - intro inprf.
              simpl in inprf.
              apply List.in_or_app.
              destruct (ST_dec (intersect (of_list (List.map snd hd))) tau).
              + simpl in inprf.
                destruct (List.in_app_or _ _ _ inprf) as [ inl | inr ].
                * left; assumption.
                * right; apply IH; assumption.
              + right; apply IH; assumption. }
      + right; apply IH.
        exists c. exists arrows.
        dependent rewrite tl_eq in there.
        split; assumption.
  Qed.

  
  Require Import Coq.Init.Wf.
  Definition TreeGrammar (combinatorsFinite: Finite CombinatorSymbol): Set :=
    list (IntersectionType *
          t (CombinatorSymbol *
             list { n : nat & list (t IntersectionType n * IntersectionType)})
            cardinality).
  Inductive NextInhabGrammar (combinatorsFinite: Finite CombinatorSymbol) (Gamma: Context):
    TreeGrammar combinatorsFinite -> TreeGrammar combinatorsFinite -> Prop :=
  | Next:
      forall (oldGrammar: TreeGrammar combinatorsFinite) lhs rhs,
        List.In lhs (MaximalInhabGrammarTgts combinatorsFinite Gamma) ->
        (List.In lhs (List.map fst oldGrammar) -> False) ->
        NextInhabGrammar combinatorsFinite Gamma (List.cons (lhs, rhs) oldGrammar) oldGrammar.

  Lemma ListLen_impl:
    forall {A: Type} (xs: list A) (p1 p2: A -> bool),
      (forall x, p1 x = true -> p2 x = true) ->
      (List.length (List.filter p1 xs) <= List.length (List.filter p2 xs))%nat.
  Proof.
    intros A xs p1 p2 p_impl.
    induction xs as [ | x xs IH ].
    - reflexivity.
    - simpl.
      generalize (p_impl x).
      destruct (p1 x).
      + intro prf; rewrite (prf eq_refl).
        simpl.
        rewrite <- Nat.succ_le_mono.
        assumption.
      + intro prf; clear prf.
        destruct (p2 x).
        * simpl.
          rewrite IH.
          apply le_S.
          reflexivity.
        * assumption.
  Qed.

  Lemma ListLen_ineq:
    forall {A: Type} (xs: list A) (p1 p2: A -> bool) (x: A),
      List.In x xs -> p1 x = true -> p2 x = false ->
      (forall y, p2 y = true -> p1 y = true) ->
      List.length (List.filter p1 xs) > List.length (List.filter p2 xs).
  Proof.
    intros A xs p1 p2.
    induction xs as [ | x xs IH ]; intros y in_xxs p1_y not_p2_y p2_impl.
    - inversion in_xxs.
    - destruct in_xxs as [ here | there ].
      + rewrite here.
        simpl.
        rewrite p1_y.
        rewrite not_p2_y.
        simpl.
        unfold "_ > _".
        unfold "_ < _".
        rewrite <- Nat.succ_le_mono.
        apply ListLen_impl.
        assumption.
      + simpl.
        generalize (p2_impl x).
        destruct (p2 x).
        * intro prf; rewrite (prf eq_refl).
          simpl.
          unfold "_ > _".
          rewrite <- Nat.succ_lt_mono.
          apply (IH y); auto.
        * intro prf.
          destruct (p1 x).
          { apply le_S.
            eapply IH; eauto. }
          { eapply IH; eauto. }
  Qed.

  Lemma ListFilter_le:
    forall {A: Type} (xs: list A) (p: A -> bool), (List.length (List.filter p xs) <= List.length xs)%nat.
  Proof.
    intros A xs p.
    induction xs.
    - reflexivity.
    - simpl.
      destruct (p a).
      + simpl.
        rewrite <- (Nat.succ_le_mono).
        assumption.
      + apply le_S.
        assumption.
  Qed.

  Lemma NextInhabGrammar_wf:
    forall (combinatorsFinite: Finite CombinatorSymbol) (Gamma: Context),
      well_founded (NextInhabGrammar combinatorsFinite Gamma).
  Proof.
    unfold well_founded.
    intros combinatorsFinite Gamma grammar.
    unfold TreeGrammar in grammar.    
    assert (length_le:
              (List.length (List.filter
                              (fun x =>
                                 if In_dec IntersectionType_eq_dec
                                           x (List.map fst grammar)
                                 then false else true)
                              (MaximalInhabGrammarTgts combinatorsFinite Gamma)) <=
               List.length (MaximalInhabGrammarTgts combinatorsFinite Gamma))%nat).
    { apply ListFilter_le. }
    revert grammar length_le.
    induction (length (MaximalInhabGrammarTgts combinatorsFinite Gamma)) as [ | n IH ].
    - intros grammar length_le.
      apply Acc_intro.
      intros next_grammar prf.
      inversion prf as [ ? lhs rhs in_max_lhs not_in_old_lhs next_eq old_eq ]; clear prf.
      inversion length_le as [ length_eq | ]; clear length_le.
      induction (MaximalInhabGrammarTgts combinatorsFinite Gamma) as [ | x xs IH ].
      + inversion in_max_lhs.
      + destruct in_max_lhs as [ here | there ].
        * simpl in length_eq.
          rewrite here in length_eq.
          destruct (In_dec IntersectionType_eq_dec lhs (List.map fst grammar)) as [ devil | ].
          { contradiction. }
          { inversion length_eq. }
        * apply IH; [ assumption | ].
          simpl in length_eq.
          destruct (In_dec IntersectionType_eq_dec x (List.map fst grammar)).
          { assumption. }
          { inversion length_eq. }
    - intros grammar length_le.
      inversion length_le as [ length_eq | ].
      + apply Acc_intro.
        intros next_grammar' next_next.
        inversion next_next as [ ? lhs' rhs' in_max_lhs' not_in_old_lhs' next_eq' old_eq' ].
        apply IH.
        revert in_max_lhs' not_in_old_lhs' length_eq.
        clear ...
        revert n.
        induction (MaximalInhabGrammarTgts combinatorsFinite Gamma) as [ | x xs IH ].
        * intros ? devil; inversion devil.
        * intros n in_xxs not_in_grammar length_eq.
          assert (incl_impl:
              forall x, (if In_dec IntersectionType_eq_dec x (List.map fst ((lhs', rhs') :: grammar))
                    then false else true) = true ->
                   (if In_dec IntersectionType_eq_dec x (List.map fst grammar) then false else true) = true).
          { clear ...
            intros x prf.
            destruct (In_dec IntersectionType_eq_dec x (List.map fst ((lhs', rhs') :: grammar))) as [ | disprf ].
            - inversion prf.
            - destruct (In_dec IntersectionType_eq_dec x (List.map fst grammar)).
              + assert False; [ apply disprf | contradiction ].
                right; assumption.
              + reflexivity. }
          match goal with
          | [ length_eq: ?l1 = _ |- (?l2 <= _)%nat ] =>
            assert (length_gt: l1 > l2)
          end.
          { apply (ListLen_ineq _ _ _ lhs'); auto.
            - destruct (In_dec IntersectionType_eq_dec lhs' (List.map fst grammar));
                [ contradiction | reflexivity ].
            - destruct (In_dec IntersectionType_eq_dec lhs' (List.map fst (List.cons (lhs', rhs') grammar)))
                as [ | devil ]; [ reflexivity | ].
              assert False; [ apply devil; left; reflexivity | contradiction ]. }
          rewrite length_eq in length_gt.
          unfold "_ > _" in length_gt.
          unfold "_ < _" in length_gt.
          rewrite <- (Nat.succ_le_mono) in length_gt.
          assumption.
      + auto.
  Qed.
  Require Import Coq.Wellfounded.Transitive_Closure.
  Require Import Coq.Relations.Relation_Operators.
  Definition NextInhabGrammarTrans (combinatorsFinite: Finite CombinatorSymbol) (Gamma: Context) := 
    clos_trans _ (NextInhabGrammar combinatorsFinite Gamma).
  Lemma NextInhabGrammarTrans_wf: forall (combinatorsFinite: Finite CombinatorSymbol) (Gamma: Context),
      well_founded (NextInhabGrammarTrans combinatorsFinite Gamma).
  Proof.
    intros; apply wf_clos_trans; apply NextInhabGrammar_wf; assumption.
  Qed.

  Definition recursiveTargets
             {n : nat}
             (entry: t (CombinatorSymbol *
                        list { n : nat & list (t IntersectionType n * IntersectionType)})
                       n): list IntersectionType :=
    (fix recursiveTargets_rec n rules :=
       match rules with
       | nil _ => List.nil
       | cons _ rule _ rules =>
         List.app (List.flat_map
                     (fun arrowsOfSize =>
                        List.flat_map (fun x => to_list (fst x)) (projT2 arrowsOfSize))
                     (snd rule))
                  (recursiveTargets_rec _ rules)
       end) _ entry.

  Lemma ListForall_app:
    forall {A: Type} (xs ys: list A) (P: A -> Prop),
      List.Forall P xs -> List.Forall P ys -> List.Forall P (xs ++ ys).
  Proof.
    intros A xs ys P all_xs all_ys.
    apply List.Forall_forall.
    intros x x_in.
    destruct (List.in_app_or _ _ _ x_in) as [ inl | inr ].
    - apply (proj1 (List.Forall_forall _ _) all_xs).
      assumption.
    - apply (proj1 (List.Forall_forall _ _) all_ys).
      assumption.
  Qed.   
  
  Lemma recursiveTargets_sound:
    forall (combinatorsFinite: Finite CombinatorSymbol) (Gamma: Context)
      (tau: IntersectionType),
      List.Forall (IsRecursiveTarget combinatorsFinite Gamma tau)
                  (recursiveTargets (grammarEntry combinatorsFinite Gamma tau)).
  Proof.
    intros combinatorsFinite Gamma tau.
    unfold recursiveTargets.
    unfold IsRecursiveTarget.
    unfold grammarEntry.
    destruct combinatorsFinite as [ card toFin fromFin toFrom_id ].
    simpl.
    clear toFin toFrom_id.
    induction (positions card) as [ | hd n tl IH ].
    - apply List.Forall_nil.
    - simpl.
      rewrite List.flat_map_concat_map.
      apply ListForall_app.
      + apply List.Forall_forall.
        intros tgt prf.
        rewrite <- List.flat_map_concat_map in prf.
        eexists; eexists; split.
        * left; reflexivity.
        * assumption.
      + induction IH as [ | ? ? prf prfs IH' ].
        * apply List.Forall_nil.
        * apply List.Forall_cons.
          { destruct prf as [ c [ arrows [ in_c_arrows in_tgt ] ] ].
            eexists; eexists; split.
            - right; eassumption.
            - assumption. }
          { assumption. }
  Qed.

  Lemma recursiveTargets_complete:
    forall (combinatorsFinite: Finite CombinatorSymbol) (Gamma: Context)
      (tau: IntersectionType) (tgt: IntersectionType),
      IsRecursiveTarget combinatorsFinite Gamma tau tgt ->
      List.In tgt (recursiveTargets (grammarEntry combinatorsFinite Gamma tau)).
  Proof.
    intros combinatorsFinite Gamma tau tgt.
    unfold IsRecursiveTarget.
    unfold recursiveTargets.
    unfold grammarEntry.
    destruct  combinatorsFinite as [ card toFin fromFin toFrom_id ].
    simpl.
    clear toFin toFrom_id.
    induction (positions card) as [ | hd n tl IH ].
    - intro prf; destruct prf as [ ? [ ? [ devil ] ] ].
      inversion devil.
    - intro prf.
      destruct prf as [ c [ arrows [ in_c_arrows in_tgt ] ] ].
      simpl.
      apply List.in_or_app.
      inversion in_c_arrows as [ ? ? n_eq [ c_eq arrows_eq ] | ? ? ? there n_eq [ hd_eq tl_eq ] ].
      + left.
        rewrite <- arrows_eq.
        assumption.
      + right.
        dependent rewrite tl_eq in there.
        apply IH.
        eexists; eexists; split.
        * eassumption.
        * assumption.
  Qed.     

  Definition inhabit_step
             (combinatorsFinite: Finite CombinatorSymbol) (Gamma: Context)
             (grammar : TreeGrammar combinatorsFinite)
             (inhabit_rec:
                forall grammar',
                  NextInhabGrammarTrans combinatorsFinite Gamma grammar' grammar ->
                  List.Forall (fun entry => snd entry = grammarEntry combinatorsFinite Gamma (fst entry))
                              grammar' ->
                  { g: TreeGrammar combinatorsFinite
                  | (forall g', NextInhabGrammar combinatorsFinite Gamma g' g ->
                           NextInhabGrammarTrans combinatorsFinite Gamma g' grammar') /\
                    (List.Forall (fun entry => snd entry = grammarEntry combinatorsFinite Gamma (fst entry))
                                 g)
                  }
             )
             (grammar_sane: List.Forall (fun entry => snd entry = grammarEntry combinatorsFinite Gamma (fst entry))
                                        grammar):
    { g: TreeGrammar combinatorsFinite
    | (forall g', NextInhabGrammar combinatorsFinite Gamma g' g ->
             NextInhabGrammarTrans combinatorsFinite Gamma g' grammar) /\
      (List.Forall (fun entry => snd entry = grammarEntry combinatorsFinite Gamma (fst entry)) g)
    }.
  Proof.
    destruct grammar as [ | entry entries ].
    - exists List.nil; split.
      + intros ? next; apply t_step; exact next.
      + apply List.Forall_nil.
    - assert (entry_sane: snd entry = grammarEntry combinatorsFinite Gamma (fst entry)).
      { inversion grammar_sane; assumption. }
      generalize (recursiveTargets_sound combinatorsFinite Gamma (fst entry)).
      intro tgts_sound.
      rewrite <- entry_sane in tgts_sound.
      induction (recursiveTargets (snd entry)) as [ | tgt tgts IH ].
      + exists (List.cons entry entries); split.
        * intros ? prf; apply t_step; exact prf.
        * assumption.
      + assert (tgts_sound': List.Forall (IsRecursiveTarget combinatorsFinite Gamma (fst entry)) tgts).
        { inversion tgts_sound as [ | ? ? tgt_sound tgts_sound' [ tgt_eq tgts_eq ] ].
          assumption. }
        destruct (IH tgts_sound') as [ next_grammar [ mk_next_acc next_grammar_sound ] ].
        destruct (In_dec IntersectionType_eq_dec tgt (List.map fst next_grammar)) as [ | fresh_tgt ].
        * eexists; split; eassumption.
        * set (next_next_grammar :=
                 List.cons (tgt, grammarEntry combinatorsFinite Gamma tgt) next_grammar).
          assert (rec_result :
                    { g: TreeGrammar combinatorsFinite
                    | (forall g', NextInhabGrammar combinatorsFinite Gamma g' g ->
                             NextInhabGrammarTrans combinatorsFinite Gamma g' next_next_grammar) /\
                      (List.Forall (fun entry => snd entry = grammarEntry combinatorsFinite Gamma (fst entry))
                                   g)
                 }).
          { apply inhabit_rec.
            - apply mk_next_acc.
              apply Next.
              + inversion tgts_sound as [ | ? ? tgt_sound ].
                eapply grammarTargetsFinite.
                eassumption.
              + exact fresh_tgt.
            - apply List.Forall_cons.
              + simpl; reflexivity.
              + exact next_grammar_sound. }
          destruct rec_result as [ g [ mk_next_next_acc next_next_sound ] ].
          exists g; split.
          { intros g' g'g.
            generalize (mk_next_next_acc g' g'g).
            intro g'_next_next.
            unfold next_next_grammar in g'_next_next.
            eapply (t_trans); [ exact  g'_next_next | ].
            apply mk_next_acc.
            apply Next.
            - eapply grammarTargetsFinite.
              inversion tgts_sound; eassumption.
            - assumption. }
          { assumption. }
  Defined.
      
  Definition inhabit (combinatorsFinite: Finite CombinatorSymbol) (Gamma: Context) (tau: IntersectionType):
    { g: TreeGrammar combinatorsFinite |
      (List.Forall (fun entry => snd entry = grammarEntry combinatorsFinite Gamma (fst entry)) g) } :=
    let first_entry :=
        (tau, grammarEntry combinatorsFinite Gamma tau) in
    let start :=
        (List.cons first_entry List.nil) in
    let start_eq :=
        eq_refl : snd first_entry = grammarEntry combinatorsFinite Gamma (fst first_entry) in
    let result :=
        Fix (NextInhabGrammarTrans_wf combinatorsFinite Gamma)
            (fun grammar =>
               List.Forall (fun entry => snd entry = grammarEntry combinatorsFinite Gamma (fst entry))
                           grammar ->
               { g: TreeGrammar combinatorsFinite
               | (forall g', NextInhabGrammar combinatorsFinite Gamma g' g ->
                        NextInhabGrammarTrans combinatorsFinite Gamma g' grammar) /\
                 (List.Forall (fun entry => snd entry = grammarEntry combinatorsFinite Gamma (fst entry)) g)
               }
            )
            (inhabit_step combinatorsFinite Gamma)
            start            
            (List.Forall_cons _ start_eq (List.Forall_nil _)) in
    exist _ (proj1_sig result) (proj2 (proj2_sig result)).
(*
  Inductive WordOf (combinatorsFinite: Finite CombinatorSymbol) (grammar: TreeGrammar combinatorsFinite):
    IntersectionType -> Term -> Prop :=
  | 
    












    

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
            cardinality).
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
                     cardinality)
             (lhsOk: IsPossibleRecursiveTarget combinatorsFinite Gamma lhs):
    NextInhabGrammar combinatorsFinite Gamma (List.cons (lhs, rhs) List.nil) (List.nil) :=
    Next combinatorsFinite Gamma (List.nil) lhs rhs (*List.Forall_nil _*) lhsOk id.


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
End CombinatoryLogicWithFiniteSubstitutionSpace.