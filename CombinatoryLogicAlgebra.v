Require Import Coq.Vectors.Vector.
Require Import VectorQuantification.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.PeanoNat.

Require Import CombinatoryLogic.
Require Import ComputationalPathLemma.
Require Import IntersectionTypes.
Require Import SigmaAlgebra.
Require Import Cantor.

Import EqNotations.

Module Type SignatureWithCLSig := SignatureSpec <+ CountableTypeAndTermSignature.
                                     
Module Type CompatibleCLSignature <: SignatureWithCLSig.
  Include SignatureSpec.
  Parameter ConstructorSymbol: Set.
  Definition VariableSymbol: Set := Var.
  Definition CombinatorSymbol: Set := Operation.
  Definition VariableSymbol_eq_dec := Var_eq_dec.
  Declare Instance Symbols : ConstructorSpecification ConstructorSymbol.
  Declare Instance ConstructorSymbol_countable: Countable ConstructorSymbol.
  Declare Instance Variables_finite: Finite VariableSymbol.
  Parameter ClosedSortsInhabited: Sort EmptySet.
  Parameter OpenSortsInhabited: Sort Var.
End CompatibleCLSignature.
  
Module Type ProtectedSymbols(SigSpec: CompatibleCLSignature) <: CompatibleCLSignature.
  Definition Sort: Set -> Set := SigSpec.Sort.
  Definition Var: Set := SigSpec.Var.
  Definition Operation: Set := SigSpec.Operation.
  Definition WellFormed := SigSpec.WellFormed.
  Instance SigSpec: SignatureSpecification Sort Var Operation := SigSpec.SigSpec.

  Definition BlackBox := unit.
  Definition blackBox := @inl unit SigSpec.ConstructorSymbol tt.

  Definition ConstructorSymbol := (BlackBox + SigSpec.ConstructorSymbol)%type.
  Definition VariableSymbol: Set := Var.
  Definition VariableSymbol_eq_dec := Var_eq_dec.
  Definition CombinatorSymbol: Set := Operation.

  Module Impl.
    Definition constructorArity (symbol: ConstructorSymbol): nat :=
      match symbol with
      | inl _ => 1
      | inr sym => constructorArity sym
      end.
    Hint Unfold constructorArity.

    Definition ConstructorTaxonomy (c1 c2 : ConstructorSymbol): Prop :=
      match c1 with
      | inl _ =>
        match c2 with
        | inl _ => True
        | _ => False
        end
      | inr c1' =>
        match c2 with
        | inr c2' => ConstructorTaxonomy c1' c2'
      | _ => False
        end
      end.
    Lemma CTPreorder : PreOrder ConstructorTaxonomy.
    Proof.
      split.
      - unfold Reflexive.
        intro x.
        destruct x.
        + exact I.
        + apply CTPreorder.
      - unfold Transitive.
        intros x y z ctxy ctyz.
        destruct x;
          destruct y;
          try solve [ inversion ctxy ];
          destruct z;
          try solve [ inversion ctyz ];
          solve [ exact I | eapply CTPreorder; eassumption ].
    Qed.
    Lemma ConstructorSymbol_eq_dec (c1 c2: ConstructorSymbol): {c1 = c2} + {c1 <> c2}.
    Proof.
      destruct c1 as [ box1 | c1 ]; destruct c2 as [ box2 | c2 ];
        try solve [ right; intro devil; inversion devil ].
      - destruct box1; destruct box2; left; reflexivity.
      - destruct (ConstructorSymbol_eq_dec c1 c2).
        + left; apply f_equal; assumption.
        + right; intro devil; inversion devil; contradiction.
    Qed.
    Lemma ConstructorTaxonomy_dec (c1 c2: ConstructorSymbol):
      { ConstructorTaxonomy c1 c2 } + { ConstructorTaxonomy c1 c2 -> False }.
    Proof.
      destruct c1; destruct c2;
        try solve [ left; exact I | right; intro devil; inversion devil ].
      apply ConstructorTaxonomy_dec.
    Qed.

    Definition toNat (x: ConstructorSymbol) :=
      cantor_sum (match x with
                  | inl _ => inl 1
                  | inr x => inr (@toNat _ SigSpec.ConstructorSymbol_countable x)
                  end).
    Definition fromNat (x: nat): ConstructorSymbol :=
      match cantor_sum_inv x with
      | inl _ => inl tt
      | inr x => inr (@fromNat _ SigSpec.ConstructorSymbol_countable x)
      end.
    Lemma fromTo_id: forall (x: ConstructorSymbol), fromNat (toNat x) = x.
    Proof.
      intro x.
      unfold fromNat.
      unfold toNat.
      rewrite cantor_sum_inj.
      destruct x as [ []  | ].
      - reflexivity.
      - rewrite (@fromTo_id _ SigSpec.ConstructorSymbol_countable).
        reflexivity.
    Qed.
  End Impl.
  
  Instance Symbols : ConstructorSpecification ConstructorSymbol :=
    {| constructorArity := Impl.constructorArity;
       ConstructorTaxonomy := Impl.ConstructorTaxonomy;
       CTPreorder := Impl.CTPreorder;
       ConstructorSymbol_eq_dec := Impl.ConstructorSymbol_eq_dec;
       ConstructorTaxonomy_dec := Impl.ConstructorTaxonomy_dec |}.

  Instance Variables_finite: Finite VariableSymbol := SigSpec.Variables_finite.  
  Instance ConstructorSymbol_countable: Countable ConstructorSymbol :=
    {| toNat := Impl.toNat; 
       fromNat := Impl.fromNat;
       fromTo_id := Impl.fromTo_id |}.
  Definition ClosedSortsInhabited := SigSpec.ClosedSortsInhabited.
  Definition OpenSortsInhabited := SigSpec.OpenSortsInhabited.
End ProtectedSymbols.

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

Module LiftProperEmbedding
       (SigSpec: CompatibleCLSignature)
       (Types: IntersectionTypes(SigSpec))
       (UnprotectedEmbedding: WithProperEmbedding(SigSpec)(Types)).
  Module ProtectedSigSpec: ProtectedSymbols(SigSpec).
    Include ProtectedSymbols(SigSpec).
  End ProtectedSigSpec.
  Module ProtectedTypes: IntersectionTypes(ProtectedSigSpec).
    Include IntersectionTypes.IntersectionTypes(ProtectedSigSpec).
  End ProtectedTypes.
  
  Module LiftedEmbedding: WithProperEmbedding(ProtectedSigSpec)(ProtectedTypes).
    Module Embedding: SortEmbedding(ProtectedSigSpec)(ProtectedTypes).
      Include SortEmbedding(ProtectedSigSpec)(ProtectedTypes).
    End Embedding.
    Export Embedding.
    Module EmbeddingImpl.
      Import ProtectedSigSpec.
      Import ProtectedTypes.
      Fixpoint liftScheme {A: Set}
                 (scheme: Types.TypeScheme (VariableSymbol := A)): TypeScheme (VariableSymbol := A) :=
        match scheme with
        | Types.Var alpha => Var alpha
        | Types.Skeleton (Types.PT_omega) => Skeleton (PT_omega)
        | Types.Skeleton (Types.PT_Const C args) =>
          Skeleton (PT_Const (inr C) (map liftScheme args))
        | Types.Skeleton (Types.PT_Arrow sigma tau) =>
          Skeleton (PT_Arrow (liftScheme sigma) (liftScheme tau))
        | Types.Skeleton (Types.PT_Inter sigma tau) =>
          Skeleton (PT_Inter (liftScheme sigma) (liftScheme tau))
        end.
      
      Fixpoint unliftScheme {A: Set}
               (scheme: TypeScheme (VariableSymbol := A)): option (Types.TypeScheme (VariableSymbol := A)) :=
        match scheme with
        | Var alpha => Some (Types.Var alpha)
        | Skeleton (PT_omega) => Some (Types.Skeleton (Types.PT_omega))
        | Skeleton (PT_Const (inr C) args)  =>
          match (fix unliftArgs n (args: t TypeScheme n): option (t Types.TypeScheme n) :=
                   match args with
                   | cons _ arg _ args =>
                     match unliftScheme arg with
                     | Some arg =>
                       match unliftArgs _ args with
                       | Some args => Some (cons _ arg _ args)
                       | None => None
                       end
                     | None => None
                     end
                   | nil _ => Some (nil _)
                   end) _ args with
          | Some args => Some (Types.Skeleton (Types.PT_Const C args))
          | None => None
          end
        | Skeleton (PT_Const (inl _) _) => None
        | Skeleton (PT_Arrow sigma tau) =>
          match unliftScheme sigma with
          | Some sigma =>
            match unliftScheme tau with
            | Some tau => Some (Types.Skeleton (Types.PT_Arrow sigma tau))
            | None => None
            end
          | None => None
          end
        | Skeleton (PT_Inter sigma tau) =>
          match unliftScheme sigma with
          | Some sigma =>
            match unliftScheme tau with
            | Some tau => Some (Types.Skeleton (Types.PT_Inter sigma tau))
            | None => None
            end
          | None => None
          end
        end.
      
      Lemma unliftLift: forall {A: Set} (scheme: Types.TypeScheme (VariableSymbol := A)),
          unliftScheme (liftScheme scheme) = Some scheme.
      Proof.
        intros A scheme.
        induction scheme
          as [ | | C args IH | ? ? IHsigma IHtau | ? ? IHsigma IHtau ]
               using Types.TypeScheme_rect';
          try solve [ reflexivity | simpl; rewrite IHsigma; rewrite IHtau; reflexivity ].
        simpl.
        match goal with
        | [|- match ?rec with | Some _ => _ | _ => _ end = _] =>
          assert (unliftArgs_eq: rec = Some args)
        end.
        { revert IH.
          generalize args.
          generalize (constructorArity C).
          clear args C.
          intros n args prfs.
          induction prfs as [ | ? ? ? prf prfs IH ].
          - reflexivity.
          - simpl.
            rewrite prf.
            rewrite IH.
            reflexivity. }
        rewrite unliftArgs_eq.
        reflexivity.
      Qed.

      Definition liftEmbed {A: Set} `{UnprotectedEmbedding.Embedding.Embedding A} (s: Sort A):
        TypeScheme (VariableSymbol := A) :=
        liftScheme (UnprotectedEmbedding.Embedding.embed s).
      Definition  liftUnembed {A: Set} `{UnprotectedEmbedding.Embedding.Embedding A}
                  (fallback: Sort A) (ty: TypeScheme (VariableSymbol := A)): Sort A :=
        match unliftScheme ty with
        | Some ty => UnprotectedEmbedding.Embedding.unembed ty
        | None => fallback
        end.

      Instance ClosedEmbedding: Embedding EmptySet  :=
        {| embed := liftEmbed; unembed := liftUnembed ClosedSortsInhabited |}.
      Instance OpenEmbedding: Embedding VariableSymbol :=
        {| embed := liftEmbed; unembed := liftUnembed OpenSortsInhabited |}.

      Lemma liftEmbedUnembedClosed `{UnprotectedEmbedding.Embedding.InjectiveEmbedding EmptySet}:
        forall (s: Sort EmptySet), liftUnembed ClosedSortsInhabited (liftEmbed s) = s.
      Proof.
        intros s.
        unfold liftEmbed.
        unfold liftUnembed.
        rewrite unliftLift.
        rewrite UnprotectedEmbedding.Embedding.unembedEmbed.
        reflexivity.
      Qed.

      Lemma liftEmbedUnembedOpen `{UnprotectedEmbedding.Embedding.InjectiveEmbedding VariableSymbol}:
        forall (s: Sort VariableSymbol), liftUnembed OpenSortsInhabited (liftEmbed s) = s.
      Proof.
        intros s.
        unfold liftEmbed.
        unfold liftUnembed.
        rewrite unliftLift.
        rewrite UnprotectedEmbedding.Embedding.unembedEmbed.
        reflexivity.
      Qed.

      Instance ClosedInjectiveEmbedding: InjectiveEmbedding EmptySet :=
        {| Embed := ClosedEmbedding; unembedEmbed := liftEmbedUnembedClosed |}.
      Instance OpenInjectiveEmbedding: InjectiveEmbedding VariableSymbol :=
        {| Embed := OpenEmbedding; unembedEmbed := liftEmbedUnembedOpen |}.       
      
      Fixpoint liftType (sigma: Types.IntersectionType): IntersectionType :=
        match sigma with
        | Types.Ty (Types.PT_omega) => Ty (PT_omega)
        | Types.Ty (Types.PT_Const C args) =>
          Ty (PT_Const (inr C) (map liftType args))
        | Types.Ty (Types.PT_Arrow sigma tau) =>
          Ty (PT_Arrow (liftType sigma) (liftType tau))
        | Types.Ty (Types.PT_Inter sigma tau) =>
          Ty (PT_Inter (liftType sigma) (liftType tau))
        end.      
      Lemma liftFreeze: forall scheme, freeze (liftScheme scheme) = liftType (Types.freeze scheme).
      Proof.
        intro scheme.
        induction scheme
          as [ | | C args IH | ? ? IHsigma IHtau | ? ? IHsigma IHtau ] 
            using Types.TypeScheme_rect'.
        - contradiction.
        - reflexivity.
        - simpl.
          unfold Const.
          unfold liftPreType.
          apply f_equal.
          apply f_equal.
          rewrite <- (map_fg).
          revert args IH.
          simpl.
          generalize (constructorArity C).
          intros n args IH.
          induction IH as [ | ? ? ? prf prfs IH' ].
          + reflexivity.
          + simpl.
            rewrite prf.
            apply f_equal.
            assumption.
        - simpl; rewrite IHsigma; rewrite IHtau; reflexivity.
        - simpl; rewrite IHsigma; rewrite IHtau; reflexivity.
      Qed.

      Definition forall_args {A B: Type} (P: A -> B -> Prop) n (sigmas: t A n) (taus: t B n)
               (prf: Forall2 P sigmas taus)
               (P': A -> B -> Prop)
               (f : forall sigma tau, P sigma tau -> P' sigma tau):
        Forall2 P' sigmas taus :=
        (fix forall_args_rec n (sigmas : t A n) (taus: t B n)
            (prf: Forall2 P sigmas taus): Forall2 P' sigmas taus :=
           match prf in @Forall2 _ _ _ n' sigmas' taus' return (@Forall2 _ _ P' n' sigmas' taus') with
           | Forall2_nil _ => Forall2_nil _
           | Forall2_cons _ sigma tau sigmas taus prf prfs =>
             Forall2_cons _ _ _ _ _ (f sigma tau prf) (forall_args_rec _ _ _ prfs)
           end) _ _ _ prf.

      Lemma liftTypeDistrib:
        forall n (sigmas taus: t Types.IntersectionType n),
          map liftType (map2 Types.Inter sigmas taus) =
          map2 Inter (map liftType sigmas) (map liftType taus).
      Proof.
        intros n sigmas.
        induction sigmas.
        - apply case0.
          reflexivity.
        - intro taus.
          apply (caseS' taus); clear taus; intros tau taus.
          simpl.
          apply f_equal.
          auto.
      Qed.

      Fixpoint liftTypeRespectful sigma tau (prf: Types.Subtypes sigma tau) {struct prf}:
        liftType sigma <= liftType tau.
      Proof.
        destruct prf as [ ? ? arity_eq ? ? ? args_le | | | | | | | | | | ].
        - eapply ST_Ax.
          + assumption.
          + apply nth_Forall2.
            intro k.
            assert (prfs_rec: Forall2 (fun sigma tau => Subtypes (liftType sigma)
                                                    (liftType tau))
                            sigmas (rew <- [t Types.IntersectionType] arity_eq in taus)).
            { exact (forall_args _ _ _ _ args_le _ liftTypeRespectful). }
            generalize (Forall2_nth _ _ _ prfs_rec k).
            intro prf.
            unfold eq_rect_r.
            rewrite (nth_map _ _ _ _ eq_refl).
            rewrite (nth_k).
            rewrite (nth_map _ _ _ _ eq_refl).
            unfold eq_rect_r in prf.
            rewrite nth_k in prf.
            fold liftType.
            exact prf.
        - apply ST_InterMeetLeft.
        - apply ST_InterMeetRight.
        - apply ST_InterIdem.
        - apply ST_InterArrowDistrib.
        - simpl.
          rewrite liftTypeDistrib.
          apply ST_InterConstDistrib.
        - apply ST_SubtypeDistrib; auto.
        - apply ST_CoContra; auto.
        - apply ST_OmegaTop.
        - apply ST_OmegaArrow.
        - eapply ST_Trans; eauto.
      Qed.

      Fixpoint unliftType (sigma: IntersectionType): option (Types.IntersectionType) :=
        match sigma with
        | Ty (PT_omega) => Some (Types.Ty (Types.PT_omega))
        | Ty (PT_Const (inr C) args)  =>
          match (fix unliftArgs n (args: t IntersectionType n): option (t Types.IntersectionType n) :=
                   match args with
                   | cons _ arg _ args =>
                     match unliftType arg with
                     | Some arg =>
                       match unliftArgs _ args with
                       | Some args => Some (cons _ arg _ args)
                       | None => None
                       end
                     | None => None
                     end
                   | nil _ => Some (nil _)
                   end) _ args with
          | Some args => Some (Types.Ty (Types.PT_Const C args))
          | None => None
          end
        | Ty (PT_Const (inl _) _) => None
        | Ty (PT_Arrow sigma tau) =>
          match unliftType sigma with
          | Some sigma =>
            match unliftType tau with
            | Some tau => Some (Types.Ty (Types.PT_Arrow sigma tau))
            | None => None
            end
          | None => None
          end
        | Ty (PT_Inter sigma tau) =>
          match unliftType sigma with
          | Some sigma =>
            match unliftType tau with
            | Some tau => Some (Types.Ty (Types.PT_Inter sigma tau))
            | None => None
            end
          | None => None
          end
        end.
      
      Lemma unliftLiftType: forall sigma, unliftType (liftType sigma) = Some sigma.
      Proof.
        intro sigma.
        induction sigma
          as [ | C args IH | ? ? IHsigma IHtau | ? ? IHsigma IHtau ]
               using Types.IntersectionType_rect';
          try solve [ reflexivity | simpl; rewrite IHsigma; rewrite IHtau; reflexivity ].
        simpl.
        match goal with
        | [|- match ?rec with | Some _ => _ | _ => _ end = _] =>
          assert (unliftArgs_eq: rec = Some args)
        end.
        { revert IH.
          generalize args.
          generalize (constructorArity C).
          clear args C.
          intros n args prfs.
          induction prfs as [ | ? ? ? prf prfs IH ].
          - reflexivity.
          - simpl.
            rewrite prf.
            rewrite IH.
            reflexivity. }
        rewrite unliftArgs_eq.
        reflexivity.
      Qed.

      Definition unliftType' sigma: Types.IntersectionType :=
        match unliftType sigma with
        | Some sigma => sigma
        | None => Types.omega
        end.
      Lemma unliftLiftType': forall sigma, unliftType' (liftType sigma) = sigma.
      Proof.
        intro sigma.
        unfold unliftType'.
        rewrite unliftLiftType.
        reflexivity.
      Qed.

      Lemma liftType_inj: forall sigma tau, liftType sigma = liftType tau -> sigma = tau.
      Proof.
        intro sigma.
        induction sigma
          as [ | C1 args1 IH1 | sigma1 tau1 IHsigma1 IHtau1 | sigma1 tau1 IHsigma1 IHtau1 ]
               using Types.IntersectionType_rect';
          induction tau
          as [ | C2 args2 IH2 | sigma2 tau2 IHsigma2 IHtau2 | sigma2 tau2 IHsigma2 IHtau2 ]
               using Types.IntersectionType_rect';
          intro eq; simpl in eq; inversion eq as [ eq' ].
        - reflexivity.
        - clear IH2.
          revert args2 eq.
          rewrite <- eq'.
          intros args2 eq.
          apply f_equal.
          apply f_equal.
          assert (args_eq: map liftType args1 = map liftType args2).
          { generalize (f_equal (
                       fun (x: IntersectionType) =>
                         match x with
                         | Ty (PT_Const C xs) => existT (t IntersectionType) (constructorArity C) xs
                         | _ => existT (t IntersectionType) 0 (nil _)
                         end) eq).
            intro ex_eq.
            apply (vect_exist_eq _ _ ex_eq). }
          clear eq.
          induction IH1 as [ | ? ? ? prf prfs IH1' ]. 
          + apply case0; reflexivity.
          + revert args_eq.
            apply (caseS' args2); clear args2; intros arg2 args2.
            intro args_eq.
            inversion args_eq as [ [ arg2_eq args2_eq ] ] .
            rewrite (prf _ arg2_eq).
            apply f_equal.
            apply IH1'.
            apply (vect_exist_eq _ _ args2_eq).
        - assert (sigma_eq: sigma1 = sigma2); [ auto | rewrite sigma_eq ].
          assert (tau_eq: tau1 = tau2); [ auto | rewrite tau_eq ].
          reflexivity.
        - assert (sigma_eq: sigma1 = sigma2); [ auto | rewrite sigma_eq ].
          assert (tau_eq: tau1 = tau2); [ auto | rewrite tau_eq ].
          reflexivity.
      Qed.
      
      Definition forall_args_map {A B: Type} (P: B -> B -> Prop) n (sigmas taus: t A n) (f: A -> B)
               (prf: Forall2 P (map f sigmas) (map f taus))
               (P': A -> A -> Prop)
               (g : forall sigma tau, P (f sigma) (f tau) -> P' sigma tau):
        Forall2 P' sigmas taus :=
        (fix forall_args_map_rec n (sigmas taus : t A n)
            (prf: Forall2 P (map f sigmas) (map f taus)) {struct prf}: Forall2 P' sigmas taus :=
           match prf in @Forall2 _ _ _ n' sigmas' taus'
                 return forall xs, map f xs = sigmas' -> forall ys, map f ys = taus' -> (@Forall2 _ _ P' n' xs ys) with
           | Forall2_nil _ =>
             fun xs _ ys _ =>
               case0 (fun ys => Forall2 P' xs ys) (case0 (fun xs => Forall2 P' xs (nil _)) (Forall2_nil _) xs) ys
           | Forall2_cons _ sigma tau sigmas taus prf prfs =>
             fun xs =>
               caseS'
                 xs _
                 (fun x xs =>
                    fun (xs_eq : map f (cons _ x _ xs) = cons _ sigma _ sigmas) ys =>
                      caseS'
                        ys _
                        (fun y ys =>
                           fun (ys_eq : map f (cons _ y _ ys) = cons _ tau _ taus) =>
                             let xs_eq' : cons _ (f x) _ (map f xs) = cons _ sigma _ sigmas := xs_eq in
                             let ys_eq' : cons _ (f y) _ (map f ys) = cons _ tau _ taus := ys_eq in
                             let x_eq : f x = sigma := f_equal hd xs_eq' in
                             let y_eq : f y = tau := f_equal hd ys_eq' in
                             let xs'_eq : map f xs = sigmas := f_equal tl xs_eq' in
                             let ys'_eq : map f ys = taus := f_equal tl ys_eq' in
                             Forall2_cons _ _ _ _ _ (g x y (rew <- [fun x => P x (f y)] x_eq in
                                                               rew <- [fun y => P sigma y] y_eq in prf))
                                          (forall_args_map_rec _ xs ys
                                                               (rew <- [fun ys => Forall2 P (map f xs) ys] ys'_eq in
                                                                   rew <- [fun xs => Forall2 P xs taus] xs'_eq in
                                                                   prfs))))
           end sigmas eq_refl taus eq_refl) _ _ _ prf.
      
      Fixpoint unliftTypeRespectful' sigma tau (prf: liftType sigma <= liftType tau) {struct prf}:
        Types.Subtypes sigma tau.
      Proof.
        rewrite <- (unliftLiftType' sigma).
        rewrite <- (unliftLiftType' tau).
        remember (liftType sigma) as sigma' eqn:sigma_eq.
        remember (liftType tau) as tau' eqn:tau_eq.
        destruct prf as [ C1 C2 arity_eq tax sigmas taus args_le | | | | | | | | | | ].
        - unfold unliftType'.
          rewrite sigma_eq.
          rewrite tau_eq.
          rewrite unliftLiftType.
          rewrite unliftLiftType.
          destruct sigma
            as [ | C1' sigmas' _ | | ]
                   using Types.IntersectionType_rect'; inversion sigma_eq as [ [ C1_eq args1_eq ] ].
          destruct tau
            as [ | C2' taus' _ | | ]
                 using Types.IntersectionType_rect'; inversion tau_eq as [ [ C2_eq args2_eq ] ].
          revert args_le.
          generalize arity_eq; clear arity_eq.
          clear sigma_eq tau_eq.
          revert sigmas taus args1_eq args2_eq.
          rewrite C1_eq.
          rewrite C2_eq.
          intros sigmas taus args1_eq args2_eq arity_eq args_le.
          eapply (Types.ST_Ax C1' C2' arity_eq).
          + simpl.
            rewrite C1_eq in tax.
            rewrite C2_eq in tax.
            assumption.
          + apply nth_Forall2.
            intro k.
            rewrite (vect_exist_eq _ _ (existT_fg_eq (t IntersectionType)
                                                     constructorArity _ _ _ args1_eq)) in args_le.
            rewrite (vect_exist_eq _ _ (existT_fg_eq (t IntersectionType)
                                                     constructorArity _ _ _ args2_eq)) in args_le.
            unfold eq_rect_r in args_le.
            rewrite map_rew in args_le.
            assert (prfs_rec: Forall2 (fun sigma tau => Types.Subtypes sigma tau)
                                      sigmas' (rew <- [t Types.IntersectionType] arity_eq in taus')).
            { exact (forall_args_map _ _ _ _ liftType args_le _ unliftTypeRespectful'). }
            generalize (Forall2_nth _ _ _ prfs_rec k).
            trivial.
        - unfold unliftType'.
          rewrite sigma_eq.
          rewrite tau_eq.
          rewrite unliftLiftType.
          rewrite unliftLiftType.
          rewrite tau_eq in sigma_eq.
          destruct sigma using Types.IntersectionType_rect'; inversion sigma_eq as [ sigma_eq' ].
          rewrite (liftType_inj _ _ sigma_eq').
          apply Types.ST_InterMeetLeft.
        - unfold unliftType'.
          rewrite sigma_eq.
          rewrite tau_eq.
          rewrite unliftLiftType.
          rewrite unliftLiftType.
          rewrite tau_eq in sigma_eq.
          destruct sigma using Types.IntersectionType_rect'; inversion sigma_eq as [ [ sigma_eq' tau_eq' ] ].
          rewrite (liftType_inj _ _ tau_eq').
          apply Types.ST_InterMeetRight.
        - unfold unliftType'.
          simpl.
          rewrite sigma_eq.
          rewrite unliftLiftType.
          apply Types.ST_InterIdem.
        - unfold unliftType'.
          rewrite sigma_eq.
          rewrite tau_eq.
          rewrite unliftLiftType.
          rewrite unliftLiftType.
          destruct sigma
            as [ | | | sigma1 sigma2 _ _ ]
                 using Types.IntersectionType_rect'; inversion sigma_eq as [ [sigma1_eq sigma2_eq] ].
          destruct sigma1
            as [ | | sigma1' tau1 _ _ | ]
                 using Types.IntersectionType_rect'; inversion sigma1_eq as [ [sigma1'_eq tau1_eq] ].
          destruct sigma2
            as [ | | sigma2' tau2 _ _ | ]
                 using Types.IntersectionType_rect'; inversion sigma2_eq as [ [sigma2'_eq tau2_eq] ].
          destruct tau
            as [ | | sigma3' tau3 _ _ | ]
                 using Types.IntersectionType_rect'; inversion tau_eq as [ [sigma3'_eq tau3_eq] ].
          destruct tau3
            as [ | | | tau31 tau32 _ _ ]
                 using Types.IntersectionType_rect'; inversion tau3_eq as [ [tau31_eq tau32_eq] ].
          rewrite (liftType_inj _ _ (eq_trans (eq_sym sigma2'_eq) sigma1'_eq)).
          rewrite (liftType_inj _ _ (eq_trans (eq_sym sigma3'_eq) sigma1'_eq)).
          rewrite (liftType_inj _ _ (eq_trans (eq_sym tau31_eq) tau1_eq)).
          rewrite (liftType_inj _ _ (eq_trans (eq_sym tau32_eq) tau2_eq)).
          apply Types.ST_InterArrowDistrib.
        - unfold unliftType'.
          rewrite sigma_eq.
          rewrite tau_eq.
          rewrite unliftLiftType.
          rewrite unliftLiftType.
          destruct sigma
            as [ | | | sigma1 sigma2 _ _ ]
                 using Types.IntersectionType_rect'; inversion sigma_eq as [ [sigma1_eq sigma2_eq] ].
          destruct sigma1
            as [ | C1 args1 _ | | ]
                 using Types.IntersectionType_rect'; inversion sigma1_eq as [ [C1_eq args1_eq] ].
          destruct sigma2
            as [ | C2 args2 _ | | ]
                 using Types.IntersectionType_rect'; inversion sigma2_eq as [ [C2_eq args2_eq] ].
          destruct tau
            as [ | C3 args3 _ | | ]
                 using Types.IntersectionType_rect'; inversion tau_eq as [ [C3_eq args3_eq] ].          
          clear sigma_eq tau_eq sigma1_eq sigma2_eq.
          revert sigmas taus args1 args2 args3 args1_eq args2_eq args3_eq.
          destruct C as [ | C ];
            inversion C1_eq as [ C1_eq' ];
            inversion C2_eq as [ C2_eq' ];
            inversion C3_eq as [ C3_eq' ].
          rewrite (eq_trans (eq_sym C2_eq') C1_eq').
          rewrite (eq_trans (eq_sym C3_eq') C1_eq').
          intros sigmas taus args1 args2 args3 args1_eq args2_eq args3_eq.
          
          
          inversion  C1_eq.
          inversion C2_eq.
          revert C2_eq C3_eq.
          rewrite C1_eq.
          intro C2_eq.
          
          
          rewrite liftTypeDistrib.
          apply ST_InterConstDistrib.
        - apply ST_SubtypeDistrib; auto.
        - apply ST_CoContra; auto.
        - apply ST_OmegaTop.
        - apply ST_OmegaArrow.
        - eapply ST_Trans; eauto.
      Qed.

      Lemma liftRespectful: forall (s s': Sort EmptySet), subsorts s s' -> freeze (embed s) <= freeze (embed s').
      Proof.
        intros s s' subsorts.
        unfold embed.
        unfold ClosedEmbedding.
        unfold liftEmbed.
        rewrite liftFreeze.
        rewrite liftFreeze.
        apply liftTypeRespectful.
        apply UnprotectedEmbedding.Embedding.embed_respectful.
        assumption.
      Qed.
       *)
      Lemma unliftRespectful:
        forall (sigma tau: IntersectionType),
            (exists s, sigma = freeze (embed s)) -> (exists s, tau = freeze (embed s)) ->
            sigma <= tau -> subsorts (unembed (unfreeze sigma)) (unembed (unfreeze tau)).
      Proof.
        intros sigma tau ex_sigma ex_tau sigma_le.
        destruct ex_sigma as [ s sigma_eq ].
        destruct ex_tau as [ s' tau_eq ].
        unfold unembed.
        unfold ClosedEmbedding.
        unfold liftUnembed.
        rewrite sigma_eq.
        rewrite tau_eq.
        rewrite freezeUnfreeze.
        rewrite freezeUnfreeze.
        unfold embed.
        unfold ClosedEmbedding.
        unfold liftEmbed.
        rewrite unliftLift.
        rewrite unliftLift.
        rewrite sigma_eq in sigma_le.
        rewrite tau_eq in sigma_le.
        unfold embed in sigma_le.
        unfold ClosedEmbedding in sigma_le.
        unfold liftEmbed in sigma_le.
        rewrite liftFreeze in sigma_le.
        rewrite liftFreeze in sigma_le.
        rewrite <- (Types.freezeUnfreeze (UnprotectedEmbedding.Embedding.embed s)).
        rewrite <- (Types.freezeUnfreeze (UnprotectedEmbedding.Embedding.embed s')). 
        apply UnprotectedEmbedding.Embedding.unembed_respectful.
        - exists s; reflexivity.
        - exists s'; reflexivity.
        - 

        
    End EmbeddingImpl.
    Instance ProperlyEmbedded: ProperEmbedding.
  End LiftedEmbedding.
End LiftProperEmbedding.

Module CombinatoryLogicAlgebra
       (Import SigSpec: CompatibleCLSignature)
       (Import Logic: CombinatoryLogicSignature(SigSpec))
       (Import ProperEmbedding: WithProperEmbedding(SigSpec)(Logic)).
  Context {UnprotectedConstructorSymbol: Set}.
  Context `{Signature: `{SignatureSpecification}}.
  Context `{ContextSymbols: `{SymbolSpecification UnprotectedConstructorSymbol Operation}}.
  Import ProtectedSymbols.
  Context `{Embedding: `{ProperEmbedding (ContextSymbols := ProtectedSymbolSpecificationInstance)}}.

  Implicit Types ConstructorSymbol : (unit + UnprotectedConstructorSymbol).
  Implicit Types VariableSymbol := Var.
  
  Definition blackBoxEmbedOpen (s: Sort Var): TypeScheme (VariableSymbol := Var) :=
    ConstScheme blackBox (cons _ (embed s) _ (nil _)).

  Definition blackBoxEmbed (s: Sort EmptySet): IntersectionType (ConstructorSymbol := unit + ConstructorSymbol) :=
    freeze (ConstructorSymbol := unit + ConstructorSymbol)  (Skeleton  (ConstructorSymbol := unit + ConstructorSymbol) (PT_Const (ConstructorSymbol := unit + ConstructorSymbol) blackBox (cons _ (embed s) _ (nil _)))).

    Definition Gamma (c: Operation) :=
      (fix Gamma_rec n dom :=
         match dom with
         | nil _ => blackBoxEmbedOpen (range c)
         | cons _ param _ params =>
           ArrowScheme (blackBoxEmbedOpen param) (Gamma_rec _ params)
         end) _ (domain c).

    Lemma Gamma_paths:
      forall (c: Operation) (S: Var -> Sort EmptySet),
        Path (Apply (embedSubst S) (Gamma c)).
    Proof.
      intros c S.
      unfold Gamma.
      induction (domain c).
      - unfold blackBoxEmbedOpen.
        apply Path_Const.
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

    Definition ProjectTerms: forall S n (args: t (Sort Signature.Var) n),
        F_args Sort Carrier S args -> t Term n :=
      fun S n args f => 
        map (fun k => proj1_sig ((F_args_nth _ _ _ _ f) k)) (positions n).

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
          rewrite embedApply.
          reflexivity.
        + apply IH.
    Qed.
    
    Definition CL_Algebra:
      forall (WellFormed : (Signature.Var -> Sort EmptySet) -> Prop),
        (forall S, WellFormed S -> TypeSystem.WellFormed (embedSubst S)) ->
        SigmaAlgebra Sort Signature.Var subsorts WellFormed Carrier.
    Proof.
      unfold SigmaAlgebra.
      intros WF WF_transport s Fs.
      destruct Fs as [ op S WF_S args tgt_le ].
      assert (opty : CL Gamma (Symbol op) (Apply (embedSubst S) (Gamma op))).
      { apply CL_Var.
        apply WF_transport; assumption. }
      generalize (source_count_eq S op).
      intro source_count_eq.
      assert (args' :
        { Ns: t Term (src_count (Apply (embedSubst S) (Gamma op)))
        | Forall2 (CL Gamma) Ns (fst (split_path (Apply (embedSubst S) (Gamma op))
                                                 (src_count (Apply (embedSubst S) (Gamma op)))
                                                 (le_n _))) }).
      { exists (rew <- source_count_eq in ProjectTerms _ _ _ args).
        apply nth_Forall2.
        unfold eq_rect_r.
        intro k.
        assert (rew_ext:
            (rew [fun n => t Term n] eq_sym source_count_eq in (ProjectTerms S (arity op) (domain op) args)) =
            rew [t Term] eq_sym source_count_eq in (ProjectTerms S (arity op) (domain op) args)).
        { rewrite <- (eq_sym source_count_eq).
          simpl.
          reflexivity. }
        rewrite rew_ext.
        rewrite (nth_k (eq_sym source_count_eq) (ProjectTerms S (arity op) (domain op) args) k).
        unfold ProjectTerms.
        rewrite (nth_map _ _ _ _ eq_refl).
        rewrite (positions_spec).
        destruct (F_args_nth _ _ _ _ args (rew <- [Fin.t] eq_sym source_count_eq in k)) as [ M proof ].        
        simpl.
        rewrite <- (blackBoxEmbed_nth _ _ _ source_count_eq).
        assumption. }
      clear args.
      assert (tgt_le':
          snd (split_path (Apply (embedSubst S) (Gamma op))
                          (src_count (Apply (embedSubst S) (Gamma op)))
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
        Apply (embedSubst (unembedSubst S)) (Gamma c) =
        Apply S (Gamma c).
    Proof.
      intros S c.
      unfold Gamma.
      induction (domain c) as [ | ? ? ? IH ].
      - unfold blackBoxEmbedOpen.
        simpl Apply.
        apply f_equal.
        match goal with
        |[|- cons _ ?lhs _ _ = cons _ ?rhs _ _] =>
         assert (s_eq: lhs = rhs)
        end.
        { match goal with
          |[|- _ = Apply S ?erc ] =>
           assert (ex_s: exists s, erc = embed s); [ eexists; reflexivity | ];
             rewrite (unembedApply S _ ex_s)
          end.
          rewrite <- embedApply.
          rewrite unembedEmbed.
          reflexivity. }
        rewrite s_eq.
        reflexivity.
      - simpl.
        apply (f_equal2); [ | exact IH ].
        apply f_equal.
        match goal with
        |[|- cons _ ?lhs _ _ = cons _ ?rhs _ _] =>
         assert (s_eq: lhs = rhs)
        end.
        { match goal with
          |[|- _ = Apply S ?erc ] =>
           assert (ex_s: exists s, erc = embed s); [ eexists; reflexivity | ];
             rewrite (unembedApply S _ ex_s)
          end.
          rewrite <- embedApply.
          rewrite unembedEmbed.
          reflexivity. }
        rewrite s_eq.
        reflexivity.
    Qed.

    Definition CL_CoAlgebra:
      forall (WellFormed : (Signature.Var -> Sort EmptySet) -> Prop),
        (forall S, TypeSystem.WellFormed S -> WellFormed (unembedSubst S)) ->
        (forall S, { TypeSystem.WellFormed S } + { TypeSystem.WellFormed S -> False }) ->
        (forall M sigma, {CL Gamma M sigma} + {CL Gamma M sigma -> False}) ->
        SigmaCoAlgebra Sort Signature.Var subsorts WellFormed Carrier.
     Proof.
       intros WF WF_transport WF_dec CL_dec.
       unfold SigmaCoAlgebra.
       intros s prf.
       destruct prf as [ M prf ].
       assert (path_s : Path (blackBoxEmbed s)).
       { unfold blackBoxEmbed.
         apply Path_Const.
         simpl.
         apply PathArgs_cons_arg.
         fold freeze.
         apply embed_Path. }
       generalize (CL_Path_path _ _ _ prf path_s).
       intro ex_subst.
       generalize (CL_Path_path_compute_S WF_dec _ CL_dec _ _ path_s ex_subst).
       clear ex_subst; intro ex_subst.
       assert (fully_applied: argumentCount M = arity (rootOf M)).
       { destruct ex_subst as [ S [ WF_S ex_path ] ].
         rewrite <- (source_count_eq (unembedSubst S) (rootOf M)).
         rewrite unembedApply_c.
         generalize (ST_organize_ge (Apply S (Gamma (rootOf M)))).
         rewrite (factorize_organized _ (organize_organized _)).
         induction ex_path as [ ? ? ? here | ? x xs ].
         - destruct here as [ path_x [ argCountPrf [ _ tgt_le ] ] ].
           intro x_ge.
           rewrite (ST_intersect_nth _ Fin.F1) in x_ge.
           simpl in x_ge.
           generalize (Gamma_paths (rootOf M) (unembedSubst S)).
           rewrite unembedApply_c.
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
           intro; auto. }
       apply (mkF _ _ _ _ _ _ (rootOf M) (unembedSubst (proj1_sig ex_subst)));
         destruct ex_subst as [ S [ WF_S ex_path ] ].
       - apply WF_transport; assumption.
       - generalize (ST_organize_ge (Apply S (Gamma (rootOf M)))).
         simpl.
         rewrite (factorize_organized _ (organize_organized (Apply S (Gamma (rootOf M))))).
         intro root_le.
         apply nth_F_args.
         intro k.
         set (k' := rew <- fully_applied in k).
         exists (nth (argumentsOf M) k').
         induction ex_path as [ ? x ? here | ? x xs ? IH ].
         + destruct here as [ path_x [ argCountPrf [ args_inhab tgt_le ] ] ].
           eapply CL_ST.
           * apply (Forall2_nth _ _ _ args_inhab k').
           * generalize (Gamma_paths (rootOf M) (unembedSubst S)).
             rewrite unembedApply_c.
             intro path_c.
             rewrite (ST_intersect_nth _ Fin.F1) in root_le.
             assert (argCountPrf' : (argumentCount M <= src_count (Apply S (Gamma (rootOf M))))%nat).
             { generalize (Path_src_count _ _ root_le path_c path_x).
               intro count_eq.
               rewrite count_eq.
               assumption. }               
             generalize (Forall2_nth _ _ _ (ST_path_src_n _ _ path_c path_x root_le _ argCountPrf' argCountPrf) k').
             intro arg_le.
             rewrite arg_le.
             unfold Gamma.
             clear arg_le.
             revert fully_applied k' argCountPrf'.
             clear ...
             intro fully_applied.
             rewrite fully_applied.
             unfold eq_rect_r.
             simpl.
             clear fully_applied.
             unfold Gamma.
             induction (domain (rootOf M)) as [ | ? ? ? IH ].
             { inversion k. }
             { intro argCountPrf.
               apply (Fin.caseS' k).
               - simpl.
                 unfold blackBoxEmbed.
                 simpl.
                 rewrite unembedApply; [ | eexists; reflexivity ].
                 apply (ST_Ax _ _ eq_refl); [ reflexivity | ].
                 unfold eq_rect_r.
                 simpl.
                 rewrite unembedEmbed.
                 apply Forall2_cons; [ | apply Forall2_nil ].
                 reflexivity.
               - intro k'.
                 apply (IH k' (proj2 (Nat.succ_le_mono _ _) argCountPrf)). }
         + rewrite (ST_intersect_append_le (cons _ x _ (nil _)) xs) in root_le.
           rewrite (ST_InterMeetRight) in root_le.
           auto.
       - assert (source_count_le : (arity (rootOf M) <= src_count (Apply S (Gamma (rootOf M))))%nat).
         { generalize (source_count_eq (unembedSubst S) (rootOf M)).
           intro source_count_eq.
           rewrite unembedApply_c in source_count_eq.
           rewrite <- source_count_eq.
           reflexivity. }
         assert (split_path_eq:
           snd (split_path (Apply S (Gamma (rootOf M))) _ source_count_le) =
           blackBoxEmbed (applySubst (unembedSubst S) (range (rootOf M)))).
         { clear ...
           revert source_count_le.
           generalize (rootOf M).
           clear M.
           intros c.
           unfold Gamma.
           unfold blackBoxEmbed.
           induction (domain c) as [ | ? ? ? IH ].
           - intros; simpl.
             rewrite unembedApply; [ | eexists; reflexivity ].
             rewrite unembedEmbed.
             reflexivity.
           - simpl.
             intro source_count_le.
             generalize (proj2 (PeanoNat.Nat.succ_le_mono _ _) source_count_le).
             intro source_count_le'.
             generalize (IH source_count_le').
             intro IH'.
             exact IH'. }
         assert (path_tgt_le:
           snd (split_path (Apply S (Gamma (rootOf M))) _ source_count_le) <=
           blackBoxEmbed s).
         { generalize (ST_organize_ge (Apply S (Gamma (rootOf M)))).
           rewrite (factorize_organized _ (organize_organized _)).
           induction ex_path as [ ? ? ? here | ? x xs there IH ].
           - intro x_ge.
             rewrite (ST_intersect_nth _ Fin.F1) in x_ge.
             simpl in x_ge.
             destruct here as [ path_x [ argCountPrf [ inhab_args x_tgt_le ] ] ].
             rewrite <- x_tgt_le.
             generalize (Gamma_paths (rootOf M) (unembedSubst S)).
             rewrite unembedApply_c.
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
       forall (WellFormed : (Signature.Var -> Sort EmptySet) -> Prop)
         (WF_transport: forall S, WellFormed S -> TypeSystem.WellFormed (embedSubst S)),
       forall s f, rootOf (proj1_sig (CL_Algebra WellFormed WF_transport s f)) = op _ _ _ _ _ _ f.
     Proof.
       intros WF WF_transport s f.
       unfold CL_Algebra.
       destruct f as [ op subst wf args tgt_le ].
       simpl.
       rewrite (applyAllRoot).
       reflexivity.
     Qed.
     
     Lemma CL_Algebra_argCount:
       forall (WellFormed : (Signature.Var -> Sort EmptySet) -> Prop)
         (WF_transport: forall S, WellFormed S -> TypeSystem.WellFormed (embedSubst S)),
       forall s f, argumentCount (proj1_sig (CL_Algebra WellFormed WF_transport s f)) =
              (arity (op _ _ _ _ _ _ f)).
     Proof.
       intros WF WF_transport s f.
       unfold CL_Algebra.
       destruct f as [ op subst wf args tgt_le ].
       simpl.
       rewrite (applyAllArgumentCount).
       simpl.
       rewrite (source_count_eq).
       reflexivity.
     Defined.

     Lemma CL_Algebra_args:
       forall (WellFormed : (Signature.Var -> Sort EmptySet) -> Prop)
         (WF_transport: forall S, WellFormed S -> TypeSystem.WellFormed (embedSubst S)),
       forall s f, argumentsOf (proj1_sig (CL_Algebra WellFormed WF_transport s f)) =
              rew <- (CL_Algebra_argCount WellFormed WF_transport s f) in ProjectTerms _ _ _ (args _ _ _ _ _ _ f).
     Proof.
       intros WF WF_transport s f.
       destruct f as [ op subst wf args tgt_le ].       
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
       forall (WellFormed : (Signature.Var -> Sort EmptySet) -> Prop)
         (WF_transport: forall S, TypeSystem.WellFormed S -> WellFormed (unembedSubst S))
         (WF_dec: forall S, { TypeSystem.WellFormed S } + { TypeSystem.WellFormed S -> False })
         (CL_dec: forall M sigma, {CL Gamma M sigma} + {CL Gamma M sigma -> False}),
       forall s c, op _ _ _ _ _ _ (CL_CoAlgebra WellFormed WF_transport WF_dec CL_dec s c) = rootOf (proj1_sig c).
     Proof.
       intros WF WF_transport WF_dec CL_dec s c.
       destruct c as [ M prf ].
       reflexivity.
     Qed.
(*
     Lemma CL_CoAlgebra_arity:
       forall (WellFormed : (Signature.Var -> Sort EmptySet) -> Prop)
         (WF_transport: forall S, TypeSystem.WellFormed S -> WellFormed (unembedSubst S))
         (WF_dec: forall S, { TypeSystem.WellFormed S } + { TypeSystem.WellFormed S -> False })
         (CL_dec: forall M sigma, {CL Gamma M sigma} + {CL Gamma M sigma -> False}),
       forall s c,
         arity (op _ _ _ _ _ _ (CL_CoAlgebra WellFormed WF_transport WF_dec CL_dec s c)) =
         argumentCount (proj1_sig c).
     Proof.
       rewrite (sour

     Lemma CL_CoAlgebra_args:
       forall (WellFormed : (Signature.Var -> Sort EmptySet) -> Prop)
         (WF_transport: forall S, TypeSystem.WellFormed S -> WellFormed (unembedSubst S))
         (WF_dec: forall S, { TypeSystem.WellFormed S } + { TypeSystem.WellFormed S -> False })
         (CL_dec: forall M sigma, {CL Gamma M sigma} + {CL Gamma M sigma -> False}),
       forall s c, ProjectTerms _ _ _
                           (args _ _ _ _ _ _
                                 (CL_CoAlgebra WellFormed WF_transport WF_dec CL_dec s c)) =
              argumentsOf (proj1_sig c).
     Proof.
     argumentsOf (proj1_sig (CL_Algebra WellFormed WF_transport s f)) =
              rew <- (CL_Algebra_argCount WellFormed WF_transport s f) in ProjectTerms _ _ _ (args _ _ _ _ _ _ f).
     

     Lemma CL_AlgebraCoAlgebra_inv:
       forall (WellFormed : (Signature.Var -> Sort EmptySet) -> Prop)
         (WF_transport1: forall S, WellFormed S -> TypeSystem.WellFormed (embedSubst S))
         (WF_transport2: forall S, TypeSystem.WellFormed S -> WellFormed (unembedSubst S))
         (WF_dec: forall S, { TypeSystem.WellFormed S } + { TypeSystem.WellFormed S -> False })
         (CL_dec: forall M sigma, {CL Gamma M sigma} + {CL Gamma M sigma -> False}),
       forall s f, F_eq _ _ _ WellFormed _ carrier_eq s f
                (CL_CoAlgebra WellFormed WF_transport2 WF_dec CL_dec s
                              (CL_Algebra WellFormed WF_transport1 s f)).
     Proof.
       intros WellFormed WF_transport1 WF_transport2 WF_dec CL_dec s f.
       destruct f as [ op subst WF_subst args tgt_le ].
       split.
       - revert args.
         simpl Top.op at 1.
         simpl CL_Algebra at 1.
         set (coalg := fun x => Top.op Sort Signature.Var subsorts WellFormed Carrier s
                                    (CL_CoAlgebra WellFormed WF_transport2 WF_dec CL_dec s x)).
         simpl Top.op in coalg.
         match goal with
         | [|- _ = Top.op Sort Signature.Var subsorts WellFormed Carrier s (CL_CoAlgebra _ _ _ _ _ ?x) ] =>
           set (alg := x)
         end.
         simpl in alg.
         revert alg.
         induction (arity).
         + simpl in alg.
     *)
  End Algebra.
End CLAlgebra.*)