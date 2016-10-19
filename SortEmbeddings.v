Require Import Coq.Classes.RelationClasses.
Require Import Coq.Vectors.Vector.

Require Import SigmaAlgebra.
Require Import CombinatoryLogic.
Require Import IntersectionTypes.
Require Import CombinatoryLogicAlgebra.

Module Type ConstantSortCLSignature <: CompatibleCLSignature.
  Include SignatureSpec with Definition Var := EmptySet.
  Definition ConstructorSymbol := Sort EmptySet.
  Definition VariableSymbol := Var.
  Definition CombinatorSymbol := Operation.
  Definition VariableSymbol_eq_dec := Var_eq_dec.
  Instance Symbols: ConstructorSpecification ConstructorSymbol :=
    {| constructorArity := fun _ => 0;
       ConstructorTaxonomy := subsorts;
       CTPreorder := subsorts_pre;
       ConstructorSymbol_eq_dec := Sort_eq_dec;
       ConstructorTaxonomy_dec := subsorts_dec |}.

  Parameter SortsInhabited: Sort EmptySet.
  Parameter applySubst_eq: forall S s, applySubst S s = s.
End ConstantSortCLSignature.

Module Type ProperConstantEmbedding
       (Import SigSpec: ConstantSortCLSignature)
       (Import Logic: CombinatoryLogicSignature(SigSpec)) <: WithProperEmbedding(SigSpec)(Logic).
  Module Embedding : SortEmbedding(SigSpec)(Logic).
    Include SortEmbedding(SigSpec)(Logic).
  End Embedding.

  Import Embedding.

  Module Proper.
    Definition embedS (s: Sort EmptySet) := ConstScheme s (nil _).
    Definition unembedS (ts: TypeScheme (VariableSymbol := EmptySet)): Sort EmptySet :=
      match ts with
      | Skeleton (PT_Const C _) => C
      | _ => SortsInhabited
      end.

    Instance ClosedEmbedding : Embedding EmptySet :=
      {| embed := embedS; unembed := unembedS |}.

    Lemma injectivity: forall (s: Sort EmptySet), unembed (embed s) = s.
    Proof.
      intro; reflexivity.
    Qed.

    Instance ClosedInjectiveEmbedding: InjectiveEmbedding EmptySet :=
      {| Embed := ClosedEmbedding; unembedEmbed := injectivity |}.

    Lemma embed_respectful: forall s s', subsorts s s' -> freeze (embed s) <= freeze (embed s').
    Proof.
      intros s s' s_le.
      apply (ST_Ax s s' eq_refl); [ assumption | apply Forall2_nil ].
    Qed.

    Lemma unembed_respectful: forall (sigma tau: IntersectionType),
        (exists s, sigma = freeze (embed s)) -> (exists s, tau = freeze (embed s)) ->
        sigma <= tau -> subsorts (unembed (unfreeze sigma)) (unembed (unfreeze tau)).
    Proof.
      intros sigma tau ex_l ex_r.
      destruct ex_l as [ s sigma_eq ].
      destruct ex_r as [ s' tau_eq ].
      rewrite sigma_eq.
      rewrite tau_eq.
      rewrite freezeUnfreeze.
      rewrite freezeUnfreeze.
      intro sigma_le.
      simpl in sigma_le.
      generalize (CI_complete _ _ _ sigma_le).
      intro sigma_le'.
      inversion sigma_le'.
      rewrite injectivity.
      rewrite injectivity.
      assumption.
    Qed.

    Lemma embed_Path: forall s, Path (freeze (embed s)).
    Proof.
      intros.
      apply Path_Const.
      apply PathArgs_nil.
    Qed.

    Lemma embedApply: forall S s, freeze (embed (applySubst S s)) = Apply (embedSubst S) (embed s).
    Proof.
      intros S s.
      simpl.
      rewrite applySubst_eq.
      reflexivity.
    Qed.

    Lemma unembedApply: forall S tau,
        (exists s, tau = embed s) ->
        Apply S tau = freeze (embed (applySubst (unembedSubst S) (unembed tau))).
    Proof.
      intros S tau ex_prf.
      simpl.
      rewrite applySubst_eq.
      destruct ex_prf as [ s tau_eq ].
      simpl embed in tau_eq.
      unfold embedS in tau_eq.
      rewrite tau_eq.
      simpl.
      reflexivity.
    Qed.
  End Proper.
  Instance ProperlyEmbedded: ProperEmbedding :=
    {| EmbedClosed := Proper.ClosedInjectiveEmbedding;
       EmbedOpen := Proper.ClosedInjectiveEmbedding;
       embed_respectful := Proper.embed_respectful;
       unembed_respectful := Proper.unembed_respectful;
       embed_Path := Proper.embed_Path;
       embedApply := Proper.embedApply;
       unembedApply := Proper.unembedApply |}.       
End ProperConstantEmbedding.

(*
Module ConstantSortSymbolSpecification(Signature: ConstantSortSignature): SignatureSymbolSpecification(Signature).
  Module Type Spec <: SignatureSymbolSpecification(Signature).
    Definition ConstructorSymbol := Signature.Sort EmptySet.
    Definition constructorArity: ConstructorSymbol -> nat := fun _ => 0.
    Definition ConstructorTaxonomy : ConstructorSymbol -> ConstructorSymbol -> Prop := Signature.subsorts.
    Definition CTPreorder : PreOrder ConstructorTaxonomy := Signature.subsorts_pre.
    Definition ConstructorSymbol_eq_dec:
      forall (C1 C2: ConstructorSymbol), {C1 = C2} + {C1 <> C2} := Signature.Sort_eq_dec.
  
    Definition ConstructorTaxonomy_dec:
      forall (C1 C2: ConstructorSymbol), { ConstructorTaxonomy C1 C2 } + { ConstructorTaxonomy C1 C2 -> False } :=
      Signature.subsorts_dec.
    Definition VariableSymbol := Signature.Var.
    Definition CombinatorSymbol: Set := Operation.
  End Spec.
    
  Include SignatureSymbolSpecification(Signature) <+ Spec.
*)