Require Import Coq.Vectors.Vector.
Require Import VectorQuantification.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Wf_nat.

Require Import CombinatoryLogic.
Require Import ComputationalPathLemma.
Require Import IntersectionTypes.
Require Import CombinatoryTerm.
Require Import SigmaAlgebra.
Require Import Cantor.
Require Import VectorQuantification.
Require Import FunctionSpace.

Import EqNotations.

Module Type SignatureWithCLSig := SignatureSpec <+ CountableTypeAndTermSignature.
                                     
Module Type CompatibleCLSignature <: SignatureWithCLSig.
  Include SignatureSpec.
  Parameter ConstructorSymbol: Type.
  Definition VariableSymbol: Set := Var.
  Definition CombinatorSymbol: Type := Operation.
  Definition VariableSymbol_eq_dec := Var_eq_dec.
  Declare Instance Symbols : ConstructorSpecification ConstructorSymbol.
  Declare Instance ConstructorSymbol_countable: Countable ConstructorSymbol.
  Declare Instance Variables_finite: Finite VariableSymbol.
  Parameter ClosedSortsInhabited: Sort EmptySet.
  Parameter OpenSortsInhabited: Sort Var.
  Parameter BlackBox : ConstructorSymbol.
  Parameter BlackBoxArity: constructorArity BlackBox = 1.
End CompatibleCLSignature.  

Module Type SortEmbedding(Import SigSpec: CompatibleCLSignature)(Import Types: IntersectionTypes(SigSpec)).
  Class Embedding (A: Set) :=
    { embed: Sort A -> TypeScheme (VariableSymbol := A);
      unembed: TypeScheme (VariableSymbol := A) -> Sort A; }.

  Definition embedSubst `{Embedding EmptySet}: (SigSpec.Var -> Sort EmptySet) -> (SigSpec.Var -> IntersectionType) :=
    fun S alpha => freeze (embed (S alpha)).
  Definition unembedSubst `{Embedding EmptySet}: (SigSpec.Var -> IntersectionType) -> (SigSpec.Var -> Sort EmptySet) :=
    fun S alpha => unembed (unfreeze (S alpha)).

  Class InjectiveEmbedding (A: Set) :=
    { Embed :> Embedding A;
      unembedEmbed: forall (s: Sort A), unembed (embed s) = s }.

  Lemma embedUnembed:
    forall {A: Set} `{InjectiveEmbedding A} (ty: TypeScheme (VariableSymbol := A)),
    (forall (sigma tau: TypeScheme (VariableSymbol := A)), { sigma = tau } + { sigma <> tau }) ->
    (exists s, ty = embed s) ->
    embed (unembed ty) = ty.
  Proof.
    intros A inj ty eq_dec ex_prf.
    destruct (eq_dec (embed (unembed ty)) ty) as [ | devil ].
    - assumption.
    - assert False; [ | contradiction ].
      inversion ex_prf as [ s ty_eq ].
      rewrite ty_eq in devil.
      rewrite unembedEmbed in devil.
      apply devil; reflexivity.
  Qed.

  Lemma embedUnembedClosed:
    forall `{InjectiveEmbedding EmptySet} (ty: TypeScheme (VariableSymbol := EmptySet)),
    (exists s, ty = embed s) ->
    embed (unembed ty) = ty.
  Proof.
    intros.
    apply embedUnembed; [ | assumption ].
    intros sigma tau.
    destruct (IntersectionType_eq_dec (freeze sigma) (freeze tau)) as [ eq | not_eq ].
    - generalize (f_equal (@unfreeze EmptySet)  eq).
      rewrite freezeUnfreeze.
      rewrite freezeUnfreeze.
      intro; left; assumption.
    - right; intro eq.
      generalize (f_equal freeze eq).
      assumption.
  Qed.

  Lemma embedUnembedOpen:
    forall `{InjectiveEmbedding VariableSymbol} (ty: TypeScheme (VariableSymbol := VariableSymbol)),
    (exists s, ty = embed s) ->
    embed (unembed ty) = ty.
  Proof.
    intros.
    apply embedUnembed; [ exact TypeScheme_eq_dec | assumption ].
  Qed.

  Class ProperEmbedding :=
    { EmbedClosed :> InjectiveEmbedding EmptySet;
      EmbedOpen :> InjectiveEmbedding SigSpec.Var;
      
      embed_respectful: forall (s s': Sort EmptySet), subsorts s s' -> freeze (embed s) <= freeze (embed s');
      unembed_respectful:
        forall (sigma tau: IntersectionType),
            (exists s, sigma = freeze (embed s)) -> (exists s, tau = freeze (embed s)) ->
            sigma <= tau -> subsorts (unembed (unfreeze sigma)) (unembed (unfreeze tau));
      embed_Path: forall s, Path (freeze (embed s));
      embedApply: forall S s, freeze (embed (applySubst S s)) = Apply (embedSubst S) (embed s);
      unembedApply: forall S tau,
          (exists s, tau = embed s) ->
          (forall alpha, exists s, S alpha = freeze (embed s)) ->
          Apply S tau = freeze (embed (applySubst (unembedSubst S) (unembed tau))) }.
  
  Lemma unembed_embedSubst `{ProperEmbedding}: forall S alpha,
      unembedSubst (embedSubst S) alpha = S alpha.
  Proof.
    intros S alpha.
    unfold embedSubst.
    unfold unembedSubst.
    rewrite (freezeUnfreeze).
    rewrite unembedEmbed.
    reflexivity.
  Qed.
  Lemma embed_unembedSubst `{ProperEmbedding}: forall S alpha,
      (exists s, unfreeze (VariableSymbol := EmptySet) (S alpha) = embed s) ->
      embedSubst (unembedSubst S) alpha = S alpha.
  Proof.
    intros S alpha fromSort.
    unfold embedSubst.
    unfold unembedSubst.
    rewrite (embedUnembedClosed _ fromSort).
    rewrite unfreezeFreeze.
    reflexivity.
  Qed.
End SortEmbedding.

Module Type WithProperEmbedding(SigSpec: CompatibleCLSignature)(Types: IntersectionTypes(SigSpec)).
  Declare Module Embedding: SortEmbedding(SigSpec)(Types).
  Export Embedding.
  Declare Instance ProperlyEmbedded: ProperEmbedding.
End WithProperEmbedding.

Module Type ProperWellFormedPredicate
       (Import SigSpec: CompatibleCLSignature)
       (Import Types: IntersectionTypes(SigSpec))
       (Import ProperEmbedding: WithProperEmbedding(SigSpec)(Types))
<: WellFormedPredicate(SigSpec)(Types).
  Include WellFormedPredicate(SigSpec)(Types).
  Parameter WF_embed: forall (S: SigSpec.WellFormed), { S' : WellFormed | forall x, take S' x = embedSubst (take S) x }.
  Parameter WF_unembed: forall (S: WellFormed), { S' : SigSpec.WellFormed | forall x, take S' x = unembedSubst (take S) x }.
  Parameter WF_closed: forall (S: WellFormed), forall alpha, exists s, take S alpha = freeze (embed s).
End ProperWellFormedPredicate.


Module Type EmbedWellFormedSpace
       (Import SigSpec: CompatibleCLSignature)
       (Import Types: IntersectionTypes(SigSpec))
       (Import ProperEmbedding: WithProperEmbedding(SigSpec)(Types)) <:
  ProperWellFormedPredicate(SigSpec)(Types)(ProperEmbedding).
  Definition WellFormed: Type := SigSpec.WellFormed.
  Lemma WF_extensional: forall S S', (forall x, embedSubst (take S) x = embedSubst (take S') x) -> S = S'.
  Proof.
    intros S S' prf.
    apply extensional.
    intro x.
    rewrite <- (unembed_embedSubst (take S)).
    rewrite <- (unembed_embedSubst (take S')).
    unfold embedSubst in *.
    unfold unembedSubst.
    rewrite (prf x).
    reflexivity.
  Qed.
    
  Instance WellFormedSpace: FunctionSpace WellFormed VariableSymbol IntersectionType :=
    {| take S x := embedSubst (take S) x;
       extensional := WF_extensional |}.

  Definition WF_embed: forall (S: SigSpec.WellFormed), { S' : WellFormed | forall x, take S' x = embedSubst (take S) x } :=
    fun S => exist _ S (fun x => eq_refl).
  Lemma WF_unembed: forall (S: WellFormed), { S' : SigSpec.WellFormed | forall x, take S' x = unembedSubst (take S) x }.
  Proof.
    intro S.
    exists S.
    intro x.
    unfold take at 2.
    simpl.
    unfold unembedSubst.
    unfold embedSubst.
    rewrite freezeUnfreeze.
    rewrite unembedEmbed.
    reflexivity.
  Defined.

  Lemma WF_closed: forall (S: WellFormed), forall alpha, exists s, take S alpha = freeze (embed s).
  Proof.
    intros S alpha.
    exists (take S alpha).
    reflexivity.
  Qed.    
End EmbedWellFormedSpace.

Module Type CountableProperWellFormedPredicate
         (SigSpec: CompatibleCLSignature)
         (Types: IntersectionTypes(SigSpec))
         (ProperEmbedding: WithProperEmbedding(SigSpec)(Types))
<: CountableWellFormedPredicate(SigSpec)(Types)
<: ProperWellFormedPredicate(SigSpec)(Types)(ProperEmbedding).
  Include ProperWellFormedPredicate(SigSpec)(Types)(ProperEmbedding).
  Declare Instance SubstitutionSpace_countable: Countable WellFormed.
End CountableProperWellFormedPredicate.
  
Module Type CombinatoryLogicAlgebra
       (Import SigSpec: CompatibleCLSignature)
       (Import Types: IntersectionTypes(SigSpec))
       (Import Terms: Terms(SigSpec))
       (Import ProperEmbedding: WithProperEmbedding(SigSpec)(Types))
       (Import TypesCountable: CountableTypes(SigSpec)(Types))
       (Import WF: CountableProperWellFormedPredicate(SigSpec)(Types)(ProperEmbedding))
       (Import CL: CombinatoryLogic(SigSpec)(Types)(Terms)(WF))
       (Import CPL: ComputationalPathLemma(SigSpec)(Types)(Terms)(TypesCountable)(WF)(CL))
       (Import Alg: Algebraic(SigSpec)).
  
  Definition blackBoxEmbedOpen (s: Sort SigSpec.Var): TypeScheme (VariableSymbol := SigSpec.Var) :=
    ConstScheme BlackBox (rew <- BlackBoxArity in cons _ (embed s) _ (nil _)).

  Definition blackBoxEmbed (s: Sort EmptySet): IntersectionType :=
    freeze (Skeleton (PT_Const BlackBox (rew <- BlackBoxArity in cons _ (embed s) _ (nil _)))).

  Definition Gamma (c: Operation) :=
    (fix Gamma_rec n dom :=
       match dom with
       | nil _ => blackBoxEmbedOpen (range c)
       | cons _ param _ params =>
         ArrowScheme (blackBoxEmbedOpen param) (Gamma_rec _ params)
       end) _ (domain c).
  
  Lemma Gamma_paths:
    forall (c: Operation) (S: SigSpec.Var -> Sort EmptySet),
      Path (Apply (embedSubst S) (Gamma c)).
  Proof.
    intros c S.
    unfold Gamma.
    induction (domain c).
    - unfold blackBoxEmbedOpen.
      apply Path_Const.
      simpl.
      rewrite BlackBoxArity.
      simpl.
      apply PathArgs_cons_arg.
      fold (Apply).
      rewrite <- embedApply.
      apply embed_Path.
    - apply Path_Arr.
      assumption.
  Qed.

  Lemma source_count_eq : forall S op, src_count (Apply (embedSubst S) (Gamma op)) = arity op.
  Proof.
    intros S op.
    unfold Gamma.
    generalize (arity op) (domain op).
    intros arity domain.
    induction domain as [ | ? ? ? IH ].
    - reflexivity.
    - simpl.
      rewrite IH.
      reflexivity.
  Qed. 

  Definition Carrier s := { M : Term | CL Gamma M (blackBoxEmbed s) }.

  Definition ProjectTerms: forall S n (args: t (Sort SigSpec.Var) n),
      F_args Carrier S args -> t Term n :=
    fun S n args f => 
      map (fun k => proj1_sig ((F_args_nth _ _ _ f) k)) (positions n).

  Lemma blackBoxEmbed_nth:
    forall op S k (src_count_eq: src_count (Apply (embedSubst S) (Gamma op)) = arity op),
      blackBoxEmbed (applySubst S (nth (domain op) (rew <- eq_sym src_count_eq in k))) =
      nth
        (fst
           (split_path (Apply (embedSubst S) (Gamma op)) (src_count (Apply (embedSubst S) (Gamma op)))
                       (le_n (src_count (Apply (embedSubst S) (Gamma op)))))) k.
  Proof.
    intros op S k src_count_eq.
    generalize (le_n (src_count (Apply (embedSubst S) (Gamma op)))).
    revert k.
    generalize src_count_eq.
    match goal with
    | [ |- ?tgt ] =>
      apply (fun x =>
               rew <- [fun n =>
                        forall (src_count_eq: n = arity op)
                          (k: Fin.t n)
                          (prf: (n <= src_count (Apply (embedSubst S) (Gamma op)))%nat),
                          blackBoxEmbed (applySubst S (nth (domain op) (rew <- [Fin.t] eq_sym src_count_eq in k))) =
                          nth (fst (split_path (Apply (embedSubst S) (Gamma op)) n prf)) k]
                   (src_count_eq) in x)
    end.
    clear src_count_eq.
    intros src_count_eq k prf.
    unfold eq_rect_r.
    rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ (eq_sym _)).
    clear src_count_eq.
    apply (Forall2_nth (fun x y => blackBoxEmbed (applySubst S x) = y)
                       (domain op)
                       (fst (split_path (Apply (embedSubst S) (Gamma op)) (arity op) prf))).
    clear k.
    revert prf.
    unfold Gamma.
    induction (domain op) as [ | ? ? ? IH ].
    - intros; apply Forall2_nil.
    - intro prf. 
      apply Forall2_cons.
      + unfold blackBoxEmbed.
        unfold blackBoxEmbedOpen.
        simpl.
        apply f_equal.
        rewrite BlackBoxArity.
        simpl.
        rewrite embedApply.
        reflexivity.
      + apply IH.
  Qed.
  
  Definition CL_Algebra: SigmaAlgebra Carrier.
  Proof.
    unfold SigmaAlgebra.
    intros s Fs.
    destruct Fs as [ op S args tgt_le ].
    assert (opty : CL Gamma (Symbol op) (Apply (embedSubst (take S)) (Gamma op))).
    { rewrite <- (Apply_ext (take (proj1_sig (WF_embed S))) (embedSubst (take S))).
      - apply CL_Var.
      - destruct (WF_embed S).
        assumption. }
    generalize (source_count_eq (take S) op).
    intro source_count_eq.
    assert (args' :
              { Ns: t Term (src_count (Apply (embedSubst (take S)) (Gamma op)))
              | Forall2 (CL Gamma) Ns (fst (split_path (Apply (embedSubst (take S)) (Gamma op))
                                                       (src_count (Apply (embedSubst (take S)) (Gamma op)))
                                                       (le_n _))) }).
    { exists (rew <- source_count_eq in ProjectTerms _ _ _ args).
      apply nth_Forall2.
      unfold eq_rect_r.
      intro k.
      assert (rew_ext:
                (rew [fun n => t Term n] eq_sym source_count_eq in (ProjectTerms (take S) (arity op) (domain op) args)) =
                rew [t Term] eq_sym source_count_eq in (ProjectTerms (take S) (arity op) (domain op) args)).
      { rewrite <- (eq_sym source_count_eq).
        simpl.
        reflexivity. }
      rewrite rew_ext.
      rewrite (nth_k (eq_sym source_count_eq) (ProjectTerms (take S) (arity op) (domain op) args) k).
      unfold ProjectTerms.
      rewrite (nth_map _ _ _ _ eq_refl).
      rewrite (positions_spec).
      destruct (F_args_nth _ _ _ args (rew <- [Fin.t] eq_sym source_count_eq in k)) as [ M proof ].        
      simpl.
      rewrite <- (blackBoxEmbed_nth _ _ _ source_count_eq).
      assumption. }
    clear args.
    assert (tgt_le':
              snd (split_path (Apply (embedSubst (take S)) (Gamma op))
                              (src_count (Apply (embedSubst (take S)) (Gamma op)))
                              (le_n _)) <= blackBoxEmbed s).
    { unfold blackBoxEmbed.
      simpl freeze.
      unfold Gamma.
      clear args'.
      generalize (domain op).
      rewrite <- source_count_eq.
      clear source_count_eq.
      intro domain.
      induction domain as [ | ? ? ? IH ].
      - simpl.
        apply (ST_Ax _ _ eq_refl); [ reflexivity | ].
        rewrite BlackBoxArity.
        apply Forall2_cons; [ | apply Forall2_nil ].
        rewrite <- embedApply.
        apply embed_respectful.
        assumption.
      - simpl.
        match goal with
        | [ |- (snd (split_path _ _ ?prfSx) <= _)] =>
          rewrite (split_path_proof_invariant _ _ _ prfSx) in IH
        end.
        exact IH. }
    eexists.
    eapply CL_ST; [ | apply tgt_le' ].
    eapply CL_ApplyPath.
    - apply Gamma_paths. 
    - eassumption.
    - exact (proj2_sig args').
  Defined.

  Lemma unembedApply_c: forall S c,
      (forall alpha, exists s, S alpha = freeze (embed s)) ->
      Apply (embedSubst (unembedSubst S)) (Gamma c) =
      Apply S (Gamma c).
  Proof.
    intros S c S_valid.
    unfold Gamma.
    induction (domain c) as [ | ? ? ? IH ].
    - unfold blackBoxEmbedOpen.
      simpl Apply.
      apply f_equal.
      rewrite BlackBoxArity.
      simpl.
      match goal with
      |[|- cons _ ?lhs _ _ = cons _ ?rhs _ _] =>
       assert (s_eq: lhs = rhs)
      end.
      { match goal with
        |[|- _ = Apply S ?erc ] =>
         assert (ex_s: exists s, erc = embed s); [ eexists; reflexivity | ];
           rewrite (unembedApply S _ ex_s S_valid)
        end.
        rewrite <- embedApply.
        rewrite unembedEmbed.
        reflexivity. }
      rewrite s_eq.
      reflexivity.
    - simpl.
      apply (f_equal2); [ | exact IH ].
      apply f_equal.
      rewrite BlackBoxArity.
      simpl.
      match goal with
      |[|- cons _ ?lhs _ _ = cons _ ?rhs _ _] =>
       assert (s_eq: lhs = rhs)
      end.
      { match goal with
        |[|- _ = Apply S ?erc ] =>
         assert (ex_s: exists s, erc = embed s); [ eexists; reflexivity | ];
           rewrite (unembedApply S _ ex_s S_valid)
        end.
        rewrite <- embedApply.
        rewrite unembedEmbed.
        reflexivity. }
      rewrite s_eq.
      reflexivity.
  Qed.

  Lemma blackBoxEmbed_Path:
    forall s, Path (blackBoxEmbed s).
  Proof.
    intro s.
    unfold blackBoxEmbed.
    apply Path_Const.
    simpl.
    rewrite BlackBoxArity.
    simpl.
    apply PathArgs_cons_arg.
    fold freeze.
    apply embed_Path.
  Qed.

  Lemma fully_applied:
    forall M s,
      CL Gamma M (blackBoxEmbed s) ->
      argumentCount M = arity (rootOf M).
  Proof.
    intros M s prf.
    generalize (CL_Path_path _ _ _ prf (blackBoxEmbed_Path s)).
    intro ex_subst.
    destruct ex_subst as [ S ex_path ].
    unfold CombinatorSymbol.
    rewrite <- (source_count_eq (unembedSubst (take S)) (rootOf M)).
    rewrite (unembedApply_c _ _ (WF_closed _ )).
    generalize (ST_organize_ge (Apply (take S) (Gamma (rootOf M)))).
    rewrite (factorize_organized _ (organize_organized _)).
    induction ex_path as [ ? ? ? here | ? x xs ].
    - destruct here as [ path_x [ argCountPrf [ _ tgt_le ] ] ].
      intro x_ge.
      rewrite (ST_intersect_nth _ Fin.F1) in x_ge.
      simpl in x_ge.
      generalize (Gamma_paths (rootOf M) (unembedSubst (take S))).
      rewrite (unembedApply_c _ _ (WF_closed _ )).
      intro path_c.
      generalize (Path_src_count _ _ x_ge path_c path_x).
      intro src_count_eq'.
      rewrite src_count_eq'.
      inversion argCountPrf as [ | n argCountPrf' src_count_eq'' ].
      + reflexivity.
      + assert (argCountPrf'' : (Datatypes.S (argumentCount M) <= Datatypes.S n)%nat).
        { rewrite <- Nat.succ_le_mono.
          assumption. }
        rewrite src_count_eq'' in argCountPrf''.
        generalize (split_path_step _ _ argCountPrf argCountPrf'').
        intro split_path_eq.
        rewrite split_path_eq in tgt_le.
        unfold blackBoxEmbed in tgt_le.
        assert False; [ | contradiction ].
        apply (ST_Arrow_Const _ _ _ _ tgt_le).
    - rewrite (ST_intersect_append_le (cons _ x _ (nil _)) xs).
      rewrite (ST_InterMeetRight).
      intro; auto.
  Qed.

  Definition mkF_args {n : nat}
             (terms: t Term n)
             S (argSorts : t (Sort SigSpec.Var) n)
             (prfs: forall k, CL Gamma (nth terms k) (blackBoxEmbed (applySubst S (nth argSorts k)))):
    F_args Carrier S argSorts.
  Proof.
    apply nth_F_args.
    intro k.
    exists (nth terms k).
    apply prfs.
  Defined.

  Lemma mkF_args_eq:
    forall n terms S argSorts prfs, ProjectTerms S n argSorts (mkF_args terms S argSorts prfs) = terms.
  Proof.
    intros n terms S argSorts prfs.
    induction n as [ | n IH ].
    - unfold mkF_args.
      unfold ProjectTerms.
      simpl.
      apply (fun r => case0 (fun xs => _ = xs) r terms).
      reflexivity.
    - revert prfs.
      apply (caseS' terms); clear terms; intros term terms.
      apply (caseS' argSorts); clear argSorts; intros argSort argSorts.
      intro prfs.
      unfold mkF_args.
      unfold ProjectTerms.
      simpl.
      apply f_equal.
      rewrite <- (map_fg _ _ Fin.FS).
      generalize (IH terms argSorts (fun k => prfs (Fin.FS k))).
      simpl.
      unfold ProjectTerms.
      unfold mkF_args.
      intro; assumption.
  Qed.
    
  Definition CL_CoAlgebra:     
      (forall M sigma, {CL Gamma M sigma} + {CL Gamma M sigma -> False}) ->
      SigmaCoAlgebra Carrier.
  Proof.
    intros CL_dec.
    unfold SigmaCoAlgebra.
    intros s prf.
    destruct prf as [ M prf ].
    generalize (blackBoxEmbed_Path s); intro path_s.
    generalize (CL_Path_path _ _ _ prf path_s).
    intro ex_subst.
    generalize (CL_Path_path_compute_S _ CL_dec _ _ path_s ex_subst).
    clear ex_subst; intro ex_subst.
    generalize (fully_applied _ _ prf).
    intro fully_applied.
    apply (mkF _ _ (rootOf M) (proj1_sig (WF_unembed (proj1_sig ex_subst))));
      destruct ex_subst as [ S ex_path ].
    - generalize (ST_organize_ge (Apply (take S) (Gamma (rootOf M)))).
      simpl.
      intro root_le.
      rewrite (factorize_organized _ (organize_organized (Apply (take S) (Gamma (rootOf M))))) in root_le.
      apply (mkF_args (rew fully_applied in argumentsOf M) (take (proj1_sig (WF_unembed S))) (domain (rootOf M))).
      intro k.
      induction ex_path as [ ? x ? here | ? x xs ? IH ].
      + destruct here as [ path_x [ argCountPrf [ args_inhab tgt_le ] ] ].
        eapply CL_ST.
        * rewrite nth_k.
          apply (Forall2_nth _ _ _ args_inhab (rew <- fully_applied in k)).
        * generalize (Gamma_paths (rootOf M) (unembedSubst (take S))).
          rewrite (unembedApply_c _ _ (WF_closed _)).
          intro path_c.
          rewrite (ST_intersect_nth _ Fin.F1) in root_le.
          assert (argCountPrf' : (argumentCount M <= src_count (Apply (take S) (Gamma (rootOf M))))%nat).
          { generalize (Path_src_count _ _ root_le path_c path_x).
            intro count_eq.
            rewrite count_eq.
            assumption. }
          generalize (Forall2_nth _ _ _ (ST_path_src_n _ _ path_c path_x root_le _ argCountPrf' argCountPrf)
                     (rew <- fully_applied in k)).
          intro arg_le.
          rewrite arg_le.
          unfold Gamma.
          clear arg_le.
          rewrite <- (nth_eq (domain (rootOf M)) (eq_sym fully_applied) k).
          unfold eq_rect_r.
          assert (k'_eq: (rew [fun y => Fin.t y] eq_sym fully_applied in k) =
                         (rew [Fin.t] eq_sym fully_applied in k)).
          { reflexivity. }
          rewrite k'_eq.
          clear k'_eq.
          generalize (rew eq_sym fully_applied in k).
          intro k'.
          revert fully_applied k' argCountPrf'.
          clear ...
          intro fully_applied.
          rewrite fully_applied.
          unfold eq_rect_r.
          simpl.
          clear fully_applied.
          unfold Gamma.
          intro k.
          fold CombinatorSymbol.
          induction (domain (rootOf M)) as [ | ? ? ? IH ].
          { inversion k. }
          { intros argCountPrf.
            apply (Fin.caseS' k).
            - simpl.
              unfold blackBoxEmbed.
              simpl.
              apply (ST_Ax _ _ eq_refl); [ reflexivity | ].
              rewrite BlackBoxArity.
              simpl.              
              rewrite unembedApply; [ | eexists; reflexivity | apply WF_closed; assumption ].
              unfold eq_rect_r.
              simpl.
              rewrite unembedEmbed.
              apply Forall2_cons; [ | apply Forall2_nil ].
              match goal with
              |[|- freeze (embed (applySubst ?S _)) <= freeze (embed (applySubst ?S' _)) ] =>
               rewrite (applySubst_ext S' S (proj2_sig (WF_unembed _)))
              end.
              reflexivity.
            - intro k'.
              apply (IH k' (proj2 (Nat.succ_le_mono _ _) argCountPrf)). }
      + rewrite (ST_intersect_append_le (cons _ x _ (nil _)) xs) in root_le.
        rewrite (ST_InterMeetRight) in root_le.
        auto.
    - assert (source_count_le : (arity (rootOf M) <= src_count (Apply (take S) (Gamma (rootOf M))))%nat).
      { generalize (source_count_eq (unembedSubst (take S)) (rootOf M)).
        intro source_count_eq.
        rewrite (unembedApply_c _ _ (WF_closed _ )) in source_count_eq.
        unfold CombinatorSymbol.
        rewrite <- source_count_eq.
        reflexivity. }
      assert (split_path_eq:
                snd (split_path (Apply (take S) (Gamma (rootOf M))) _ source_count_le) =
                blackBoxEmbed (applySubst (unembedSubst (take S)) (range (rootOf M)))).
      { clear ...
        revert source_count_le.
        generalize (rootOf M).
        clear M.
        intros c.
        unfold Gamma.
        unfold blackBoxEmbed.
        fold CombinatorSymbol.
        induction (domain c) as [ | ? ? ? IH ].
        - intros; simpl.
          apply f_equal.
          rewrite BlackBoxArity.
          simpl.
          rewrite unembedApply; [ | eexists; reflexivity | apply WF_closed; assumption ].
          rewrite unembedEmbed.
          reflexivity.
        - simpl.
          intro source_count_le.
          fold src_count.
          generalize (proj2 (PeanoNat.Nat.succ_le_mono _ _) source_count_le).
          intro source_count_le'.
          generalize (IH source_count_le').
          intro IH'.
          exact IH'. }
      assert (path_tgt_le:
                snd (split_path (Apply (take S) (Gamma (rootOf M))) _ source_count_le) <=
                blackBoxEmbed s).
      { generalize (ST_organize_ge (Apply (take S) (Gamma (rootOf M)))).
        rewrite (factorize_organized _ (organize_organized _)).
        induction ex_path as [ ? ? ? here | ? x xs there IH ].
        - intro x_ge.
          rewrite (ST_intersect_nth _ Fin.F1) in x_ge.
          simpl in x_ge.
          destruct here as [ path_x [ argCountPrf [ inhab_args x_tgt_le ] ] ].
          rewrite <- x_tgt_le.
          generalize (Gamma_paths (rootOf M) (unembedSubst (take S))).
          rewrite (unembedApply_c _ _ (WF_closed _)).
          intro path_c.
          clear split_path_eq inhab_args x_tgt_le.
          revert fully_applied source_count_le path_c path_x x_ge argCountPrf.
          clear ...
          intros fully_applied source_count_le path_c path_x x_ge.
          rewrite fully_applied.
          intro argCountPrf.            
          apply (ST_path_tgt_n _ _ path_c path_x x_ge _ _ argCountPrf).
        - intro xs_ge.
          rewrite (ST_intersect_append_le (cons _ x _ (nil _)) xs) in xs_ge.
          rewrite (ST_InterMeetRight _ _) in xs_ge.
          exact (IH xs_ge). }
      rewrite split_path_eq in path_tgt_le.
      unfold blackBoxEmbed in path_tgt_le.
      simpl in path_tgt_le.
      generalize (CI_complete _ _ _ path_tgt_le).
      intro path_tgt_ci.
      inversion path_tgt_ci as [ ? ? arity_eq ? args_st [ hd_eq tl_eq ] | | | ].
      unfold eq_rect_r in args_st.
      rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ (eq_sym arity_eq)) in args_st.
      rewrite (vect_exist_eq _ _
                             (existT_fg_eq (fun x => t IntersectionType x) constructorArity _ _ _ tl_eq))
        in args_st.
      rewrite BlackBoxArity in args_st.
      simpl in args_st.
      inversion args_st as [ | ? ? ? ? ? arg_st ].
      generalize (unembed_respectful _ _
                                     (ex_intro _ _ eq_refl)
                                     (ex_intro _ _ eq_refl)
                                     arg_st).
      intro arg_subsorts.
      rewrite freezeUnfreeze in arg_subsorts.
      rewrite freezeUnfreeze in arg_subsorts.
      rewrite unembedEmbed in arg_subsorts.
      rewrite unembedEmbed in arg_subsorts.
      simpl.
      rewrite (applySubst_ext _ _ (proj2_sig (WF_unembed S))).
      exact arg_subsorts.
  Defined.

  Definition carrier_eq: forall s s', Carrier s -> Carrier s' -> Prop :=
    fun s1 s2 c1 c2 => proj1_sig c1 = proj1_sig c2.

  Lemma carrier_eq_refl: forall s c, carrier_eq s s c c.
  Proof.
    intros; reflexivity.
  Qed.
  Lemma carrier_eq_sym: forall s s' c1 c2, carrier_eq s s' c1 c2 -> carrier_eq s' s c2 c1.
  Proof.
    intros; apply eq_sym; assumption.
  Qed.
  Lemma carrier_eq_trans: forall s s' s'' c1 c2 c3,
      carrier_eq s s' c1 c2 -> carrier_eq s' s'' c2 c3 -> carrier_eq s s'' c1 c3.
  Proof.
    intros; eapply eq_trans; eassumption.
  Qed.

  Lemma CL_Algebra_op:
    forall s f, rootOf (proj1_sig (CL_Algebra s f)) = op _ _ f.
  Proof.
    intros s f.
    unfold CL_Algebra.
    destruct f as [ op wf args tgt_le ].
    simpl.
    rewrite (applyAllRoot).
    reflexivity.
  Qed.
  
  Lemma CL_Algebra_argCount:
    forall s f, argumentCount (proj1_sig (CL_Algebra s f)) =
           (arity (op _ _ f)).
  Proof.
    intros s f.
    unfold CL_Algebra.
    destruct f as [ op wf args tgt_le ].
    simpl.
    rewrite (applyAllArgumentCount).
    simpl.
    rewrite (source_count_eq).
    reflexivity.
  Defined.

  Lemma CL_Algebra_args:
    forall s f, argumentsOf (proj1_sig (CL_Algebra s f)) =
           rew <- (CL_Algebra_argCount s f) in ProjectTerms _ _ _ (args _ _ f).
  Proof.
    intros s f.
    destruct f as [ op wf args tgt_le ].       
    simpl.
    rewrite (applyAllArguments).
    simpl.
    match goal with
      [|- (rew <- [t Term] ?prf1 in rew <- [t Term] ?prf2 in _) =
         (rew <- [t Term] ?prf3 in _) ] =>
      generalize prf2 prf1 prf3
    end.
    intro prf1.
    rewrite prf1.
    unfold eq_rect_r.
    simpl.
    intros prf2 prf3.
    rewrite (UIP_dec (Nat.eq_dec) prf2 prf3).
    reflexivity.
  Qed.

  Lemma CL_CoAlgebra_op:
    forall (CL_dec: forall M sigma, {CL Gamma M sigma} + {CL Gamma M sigma -> False}),
    forall s c, op _ _ (CL_CoAlgebra CL_dec s c) = rootOf (proj1_sig c).
  Proof.
    intros CL_dec s c.
    destruct c as [ M prf ].
    reflexivity.
  Qed.

  Lemma CL_CoAlgebra_arity:
    forall (CL_dec: forall M sigma, {CL Gamma M sigma} + {CL Gamma M sigma -> False}),
    forall s c,
      arity (op _ _ (CL_CoAlgebra CL_dec s c)) =
      argumentCount (proj1_sig c).
  Proof.
    intros CL_dec s c.
    rewrite (CL_CoAlgebra_op).
    destruct c as [ M prf ].
    simpl.
    exact (eq_sym (fully_applied M s prf)).
  Qed.
               
  Lemma CL_CoAlgebra_args:
    forall (CL_dec: forall M sigma, {CL Gamma M sigma} + {CL Gamma M sigma -> False}),
    forall s c, rew CL_CoAlgebra_arity CL_dec s c in ProjectTerms _ _ _ (args _ _ (CL_CoAlgebra CL_dec s c)) =
           argumentsOf (proj1_sig c).
  Proof.
    intros CL_dec s c.
    destruct c as [ M prf ].
    simpl.
    destruct (CL_Path_path_compute_S Gamma CL_dec M (blackBoxEmbed s) (blackBoxEmbed_Path s)
                                     (CL_Path_path Gamma M (blackBoxEmbed s) prf (blackBoxEmbed_Path s)))
      as [ S ex_prf ].
    rewrite mkF_args_eq.
    generalize (fully_applied M s prf).
    generalize (CL_CoAlgebra_arity CL_dec s (exist _ M prf)).
    simpl.
    intros eq1 eq2.
    generalize (argumentsOf M).
    clear ...
    revert eq1 eq2.
    intro eq1.
    rewrite <- eq1.
    simpl.
    intro eq2.
    intro xs.
    rewrite (UIP_dec (Nat.eq_dec) eq2 eq_refl).
    simpl.
    reflexivity.
  Qed.

  Lemma CL_AlgebraCoAlgebra_inv:
    forall (CL_dec: forall M sigma, {CL Gamma M sigma} + {CL Gamma M sigma -> False}),
      forall s f, F_eq _ carrier_eq s s f
                  (CL_CoAlgebra CL_dec s (CL_Algebra s f)).
  Proof.
    intros CL_dec s f.
    assert (op_eq:
              op Carrier s f =
              op Carrier s (CL_CoAlgebra CL_dec s (CL_Algebra s f))).
    { destruct f as [ op WF_subst args tgt_le ].
      rewrite (CL_CoAlgebra_op CL_dec).
      rewrite <- CL_Algebra_op.
      reflexivity. }
    assert (arity_eq:
              arity (op Carrier s f) =
              arity (op Carrier s (CL_CoAlgebra CL_dec s (CL_Algebra s f)))).
    { rewrite op_eq.
      reflexivity. }    
    assert (args_eq:
      (rew arity_eq in ProjectTerms _ _ _ (args Carrier s f)) =
      ProjectTerms _ _ _ (args Carrier s
                               (CL_CoAlgebra CL_dec s (CL_Algebra s f)))).
    { generalize (CL_CoAlgebra_args CL_dec s (CL_Algebra s f)).
      intro args_prf.
      rewrite (CL_Algebra_args) in args_prf.
      revert args_prf arity_eq.
      generalize (CL_CoAlgebra_arity CL_dec s (CL_Algebra s f)).
      generalize (CL_Algebra_argCount s f).
      generalize (ProjectTerms (take (subst Carrier s f)) (arity (op Carrier s f))
                               (domain (op Carrier s f)) (args Carrier s f)).
      match goal with
      | [|- _ -> _ -> _ -> rew _ in ?xs = _ -> _ ] =>
        generalize xs
      end.
      rewrite op_eq.
      intros xs ys eq1 eq2 xsys_eq arity_eq.
      assert (xsys_eq': xs = ys).
      { revert xsys_eq.
        clear ...
        unfold eq_rect_r.
        rewrite (UIP_dec (Nat.eq_dec) eq2 (eq_sym eq1)).
        rewrite <- (eq_sym eq1).
        simpl.
        intro; assumption. }
      rewrite xsys_eq'.
      rewrite (UIP_dec (Nat.eq_dec) arity_eq eq_refl).
      reflexivity. }
    split.
    - assumption.
    - revert args_eq.
      generalize (args Carrier s (CL_CoAlgebra CL_dec s (CL_Algebra s f))).
      revert op_eq arity_eq.
      generalize (op Carrier s (CL_CoAlgebra CL_dec s (CL_Algebra s f))).
      intros o op_eq.
      rewrite <- op_eq.
      intro arity_eq.
      rewrite (UIP_dec (Nat.eq_dec) arity_eq eq_refl).
      simpl.
      clear arity_eq op_eq.
      generalize (args Carrier s f).
      generalize (domain (op Carrier s f)).
      intro dom.
      induction dom as [ | param n params IH ].
      + intros; trivial.
      + intros args args' terms_eq.
        split.
        * unfold carrier_eq.
          unfold ProjectTerms in terms_eq.
          simpl in terms_eq.
          inversion terms_eq as [ term_eq ].
          reflexivity.
        * apply IH.
          unfold ProjectTerms.
          unfold ProjectTerms in terms_eq.
          simpl map in terms_eq.
          rewrite <- (map_fg _ _ Fin.FS) in terms_eq.
          rewrite <- (map_fg _ _ Fin.FS) in terms_eq.
          inversion terms_eq as [ [ hd_eq tl_eq' ] ].
          exact (vect_exist_eq _ _ tl_eq').
  Qed.
  
  Lemma CL_CoAlgebraAlgebra_inv:
    forall (CL_dec: forall M sigma, {CL Gamma M sigma} + {CL Gamma M sigma -> False}),
    forall s c, proj1_sig (CL_Algebra s (CL_CoAlgebra CL_dec s c)) = proj1_sig c.
  Proof.
    intros CL_dec s c.
    match goal with
    |[|- ?M' = _ ] => rewrite <- (applyAllSpec M')
    end.
    rewrite CL_Algebra_op.
    rewrite CL_CoAlgebra_op.
    rewrite CL_Algebra_args.
    rewrite <- (applyAllSpec (proj1_sig c)).
    rewrite <- (CL_CoAlgebra_args CL_dec s c).
    rewrite applyAllRoot.
    simpl.
    unfold eq_rect_r.
    match goal with
    |[|- applyAll _ (rew ?eq1 in ?xs) = applyAll _ (rew ?eq2 in _) ] =>
     generalize eq1 eq2 xs
    end.
    rewrite CL_Algebra_argCount.
    intro eq1.
    rewrite eq1.
    simpl.
    intro eq2.
    rewrite <- eq2.
    simpl.
    intro; reflexivity.
  Qed.

  
  Lemma CL_CoAlgebra_smaller_nth (CL_dec: forall M sigma, {CL Gamma M sigma} + {CL Gamma M sigma -> False}):
    forall s c k,
      sizeOf (nth (ProjectTerms _ _ _ (args _ s (CL_CoAlgebra CL_dec s c))) k) <
      sizeOf (proj1_sig c).
  Proof.
    intros s c k.
    assert (args_eq: (rew <- CL_CoAlgebra_arity CL_dec s c in argumentsOf (proj1_sig c)) =
            ProjectTerms _ _ _ (args _ s (CL_CoAlgebra CL_dec s c))).
    { generalize (CL_CoAlgebra_args CL_dec s c).
      intro prf.
      rewrite <- prf.
      rewrite rew_opp_l.
      reflexivity. }
    rewrite <- args_eq.
    apply argumentsOf_size.
    unfold eq_rect_r.
    rewrite nth_k.
    apply nth_In.
  Qed.
  
  Lemma CL_CoAlgebra_smaller (CL_dec : forall M sigma, {CL Gamma M sigma} + {CL Gamma M sigma -> False}):
    forall (s : Sort EmptySet) (c : Carrier s),
      argsDec Carrier Term (ltof Term sizeOf) (fun _ c => proj1_sig c) s c
              (take (subst Carrier s (CL_CoAlgebra CL_dec s c)))
              (domain (op Carrier s (CL_CoAlgebra CL_dec s c)))
              (args Carrier s (CL_CoAlgebra CL_dec s c)).
  Proof.
    intros s c.
    generalize (CL_CoAlgebra_smaller_nth CL_dec s c).
    destruct (CL_CoAlgebra CL_dec s c) as [ op S args subsorts ].
    simpl.
    revert args.
    generalize (domain op).
    generalize (arity op).
    intros n dom.
    induction dom as [ | param n params IH ].
    - intros; simpl; trivial.
    - intros args size_prf.
      split.
      + exact (size_prf Fin.F1).
      + apply IH.
        intro k.
        generalize (size_prf (Fin.FS k)).
        simpl.
        rewrite <- (map_fg _ _ (Fin.FS)).
        intro; assumption.        
  Qed.

  (* Also called f_Pi *)
  Definition CL_Algebra_morphism (CL_dec: forall M sigma, {CL Gamma M sigma} + {CL Gamma M sigma -> False}):
             forall Carrier', SigmaAlgebra Carrier' -> forall s, Carrier s -> Carrier' s :=
    fun D => fun h => fun s => fun c =>
      canonical_morphism Carrier D
                         (CL_CoAlgebra CL_dec) h
                         Term _ (well_founded_ltof _ sizeOf) (fun _ c => proj1_sig c)
                         (CL_CoAlgebra_smaller CL_dec) s c.
  
  Lemma F_eq_compat_alg: forall s s' f f',
      F_eq _ carrier_eq s s' f f' ->
      carrier_eq s s' (CL_Algebra s f) (CL_Algebra s' f').
  Proof.
    intros s s' f f'.   
    destruct f as [ x S args subsort ].
    destruct f' as [ x' S' args' subsort' ].
    intro f_eq.
    unfold carrier_eq.
    match goal with
    |[|- ?x = ?y] =>
     rewrite <- (applyAllSpec x);
       rewrite <- (applyAllSpec y)
    end.
    rewrite (CL_Algebra_op).
    rewrite (CL_Algebra_op).
    rewrite (CL_Algebra_args).
    rewrite (CL_Algebra_args).
    simpl.
    match goal with
    |[|- applyAll _ (rew <- ?p in _) = applyAll _ (rew <- ?p' in _) ] =>
     rewrite p; rewrite p'
    end.
    unfold eq_rect_r.
    simpl.
    destruct f_eq as [ op_eq args_eq ].
    simpl in op_eq.
    revert args S' args' subsort subsort' args_eq.
    rewrite <- op_eq.
    clear x' op_eq.
    intros args S' args' subsort subsort' args_eq.
    apply f_equal2; [ reflexivity | ].
    revert S S' args args' subsort subsort' args_eq.
    simpl.
    generalize (domain x).
    generalize (arity x).
    intros n dom S S' args args' _ _.
    revert args'.
    induction dom as [ | hd n tl IH ].
    - unfold ProjectTerms; intros; reflexivity.
    - intros args' args_eq.
      destruct args as [ arg args ].
      destruct args' as [ arg' args' ].
      destruct args_eq as [ arg_eq args_eq ].
      unfold carrier_eq in arg_eq.
      unfold ProjectTerms.
      simpl.
      simpl in arg_eq.
      rewrite <- arg_eq.
      apply f_equal.
      rewrite <- map_fg.
      rewrite <- map_fg.
      simpl.
      simpl in args_eq.
      fold (ProjectTerms (take S) n tl args).
      fold (ProjectTerms (take S') n tl args').
      apply IH.
      assumption.
  Qed.

  Lemma F_eq_compat_coalg  (CL_dec: forall M sigma, {CL Gamma M sigma} + {CL Gamma M sigma -> False}):
    forall s s' c c', carrier_eq s s' c c' -> F_eq _ carrier_eq s s' (CL_CoAlgebra CL_dec s c) (CL_CoAlgebra CL_dec s' c').
  Proof.
    intros s s' c c'.
    unfold F_eq.
    intro c_eq.
    split.
    - rewrite CL_CoAlgebra_op.
      rewrite CL_CoAlgebra_op.
      rewrite c_eq.
      reflexivity.
    - assert (op_eq: op Carrier s (CL_CoAlgebra CL_dec s c) = op Carrier s' (CL_CoAlgebra CL_dec s' c')).
      { rewrite CL_CoAlgebra_op.
        rewrite CL_CoAlgebra_op.
        unfold carrier_eq in c_eq.
        rewrite c_eq.
        reflexivity. }
      assert (arity_eq: arity (op Carrier s (CL_CoAlgebra CL_dec s c)) =
                        arity (op Carrier s' (CL_CoAlgebra CL_dec s' c'))).
      { rewrite op_eq; reflexivity. }
      assert (args_eq: ProjectTerms (take (subst Carrier s (CL_CoAlgebra CL_dec s c))) _
                                    (domain (op Carrier s (CL_CoAlgebra CL_dec s c)))
                                    (args Carrier s (CL_CoAlgebra CL_dec s c)) =
                       rew <- arity_eq in
                       ProjectTerms (take (subst Carrier s' (CL_CoAlgebra CL_dec s' c'))) _
                                    (domain (op Carrier s' (CL_CoAlgebra CL_dec s' c')))
                                    (args Carrier s' (CL_CoAlgebra CL_dec s' c'))).
      { match goal with
        |[|- ?lhs = _ ] =>
         assert (lhs_eq: lhs = rew <- (CL_CoAlgebra_arity CL_dec s c) in argumentsOf (proj1_sig c))
        end.
        { rewrite <- (CL_CoAlgebra_args CL_dec s c).
          rewrite rew_opp_l.
          reflexivity. }
        match goal with
        |[|- _ = rew <- _ in ?rhs ] =>
         assert (rhs_eq: rhs = rew <- (CL_CoAlgebra_arity CL_dec s' c') in argumentsOf (proj1_sig c'))
        end.
        { rewrite <- (CL_CoAlgebra_args CL_dec s' c').
          rewrite rew_opp_l.
          reflexivity. }
        rewrite lhs_eq.
        rewrite rhs_eq.
        generalize (CL_CoAlgebra_arity CL_dec s c).
        generalize (CL_CoAlgebra_arity CL_dec s' c').
        revert arity_eq.
        rewrite c_eq.
        intro arity_eq.
        rewrite arity_eq.
        intro eq1.
        rewrite eq1.
        intro eq2.
        rewrite (UIP_dec (Nat.eq_dec) eq2 eq_refl).
        reflexivity. }
      revert c_eq op_eq arity_eq args_eq.
      generalize (CL_CoAlgebra CL_dec s c).
      generalize (CL_CoAlgebra CL_dec s' c').
      intros f' f.
      destruct f as [ op S args ].
      destruct f' as [ op' S' args' ].
      simpl.
      intros c_eq op_eq.
      generalize args'; clear args'.
      generalize args; clear args.
      rewrite <- op_eq.
      intros args args' arity_eq.
      rewrite (UIP_dec (Nat.eq_dec) arity_eq eq_refl).
      unfold eq_rect_r.
      simpl.
      clear ...
      revert args args'.
      generalize (domain op).
      generalize (arity op).
      intros n dom.
      induction dom as [ | hd n tl IH ].
      + intros; reflexivity.
      + intros args args' args_eq.
        unfold carrier_eq.
        unfold ProjectTerms in args_eq.
        simpl in args_eq.
        inversion args_eq as [ [ hd_eq tl_eq ] ].
        split.       
        * reflexivity.
        * apply IH.
          rewrite <- map_fg in tl_eq.
          rewrite <- map_fg in tl_eq.
          exact (vect_exist_eq _ _ tl_eq).
  Qed.

  Section Uniqueness.
    Variable Carrier': Sort EmptySet -> Type.
    Variable algebra: SigmaAlgebra Carrier'.
    Variable carrier'_eq: forall s s', Carrier' s -> Carrier' s' -> Prop.

    Hypothesis carrier'_eq_trans:
      forall s s' s'' x y z, carrier'_eq s s' x y -> carrier'_eq s' s'' y z -> carrier'_eq s s'' x z.
    Hypothesis alg_compat: forall s s' f f',
        F_eq Carrier' carrier'_eq s s' f f' -> carrier'_eq s s' (algebra s f) (algebra s' f').

    Hypothesis (CL_dec: forall M sigma, {CL Gamma M sigma} + {CL Gamma M sigma -> False}).

    Definition unique_mor := CL_Algebra_morphism CL_dec Carrier' algebra.      
    
    Lemma CL_Algebra_morphism_alg_mor:
      forall s s' f f',
        F_eq Carrier carrier_eq s s' f f' ->
        carrier'_eq s s' (unique_mor s (CL_Algebra s f))
                    (algebra s' (F_mor Carrier Carrier' unique_mor s' f')).
    Proof.
      apply canonical_morphism_alg_mor; try solve [ assumption ].
      - exact carrier_eq_trans.
      - exact (F_eq_compat_coalg CL_dec).
      - intros.
        apply F_eq_sym; [ exact carrier_eq_sym | ].
        apply (CL_AlgebraCoAlgebra_inv CL_dec).
    Qed.

    Lemma CL_Algebra_morphism_unique:
      forall (morphism: forall s, Carrier s -> Carrier' s)
        (morphism_compat:
           forall s s' c c', carrier_eq s s' c c' -> carrier'_eq s s' (morphism s c) (morphism s' c'))
        (morphism_alg_homo:
           forall s s' f f',
             F_eq Carrier carrier_eq s s' f f' ->
             carrier'_eq s s' (morphism s (CL_Algebra s f)) (algebra s' (F_mor Carrier Carrier' morphism s' f')))
        s c,
        carrier'_eq s s (morphism s c) (unique_mor s c).
    Proof.
      apply canonical_morphism_unique.
      - exact carrier_eq_refl.
      - exact carrier'_eq_trans.
      - exact alg_compat.
      - intros s c.
        apply carrier_eq_sym.
        exact (CL_CoAlgebraAlgebra_inv CL_dec s c).
    Qed.

    Lemma CL_Algebra_morphism_sound:
      forall s c, AlgebraicallyGenerated Carrier' algebra s (unique_mor s c).
    Proof.
      apply canonical_morphism_sound.
    Qed.

    Lemma CL_Algebra_morphism_complete:
      forall s c,
        AlgebraicallyGenerated Carrier' algebra s c ->
        exists c', carrier'_eq s s c (unique_mor s c').
    Proof.
      intros.
      apply (canonical_morphism_complete _ _ (CL_CoAlgebra CL_dec) algebra
                                         _ _ _ _ (CL_CoAlgebra_smaller CL_dec)
                                         CL_Algebra carrier_eq carrier'_eq).
      - exact carrier'_eq_trans.
      - exact alg_compat.
      - apply F_eq_compat_coalg.
      - intros.
        apply (F_eq_sym _ _ carrier_eq_sym).
        apply (CL_AlgebraCoAlgebra_inv).
      - exact carrier_eq_sym.
      - assumption.
    Qed.
      
  End Uniqueness.   
 
End CombinatoryLogicAlgebra.
