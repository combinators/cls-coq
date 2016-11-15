Require Import Coq.Classes.RelationClasses.
Require Import Coq.Vectors.Vector.

Require Import SigmaAlgebra.
Require Import CombinatoryLogic.
Require Import IntersectionTypes.
Require Import CombinatoryLogicAlgebra.
Require Import FiniteSubstitutionSpace.
Require Import ComputationalPathLemma.
Require Import VarianceLabeledTree.
Require Import Cantor.

Module Type FiniteCountableSignatureSpec <: SignatureSpec.
  Include SignatureSpec.
  Declare Instance ClosedSortsCountable: Countable (Sort EmptySet).
  Declare Instance Vars_finite: Finite Var.
  Parameter OpenSortsInhabited: Sort Var.
End FiniteCountableSignatureSpec.

Module Type SortConstructorCLSignature(SigSpec: FiniteCountableSignatureSpec) <: CompatibleCLSignature.
  Definition Sort: Set -> Set := SigSpec.Sort.
  Definition Var: Set := SigSpec.Var.
  Definition Operation: Set := SigSpec.Operation.
  Definition WellFormed: (Var -> Sort EmptySet) -> Prop := SigSpec.WellFormed.
  Instance SigSpec: SignatureSpecification Sort Var Operation := SigSpec.SigSpec.
  
  Definition ConstructorSymbol := (unit + Sort EmptySet)%type.
  Definition VariableSymbol := Var.
  Definition CombinatorSymbol := Operation.
  Definition VariableSymbol_eq_dec := Var_eq_dec.
  Module ConstructorDefs.
    Definition ConstructorTaxonomy: ConstructorSymbol -> ConstructorSymbol -> Prop :=
      fun c1 c2 =>
        match c1 with
        | inr c1 =>
          match c2 with
          | inr c2 => subsorts c1 c2
          | _ => False
          end
        | inl tt =>
          match c2 with
          | inl tt => True
          | inr _ => False
          end
        end.
    Lemma ConstructorTaxonomy_reflexive: Reflexive ConstructorTaxonomy.
    Proof.
      intro x.
      destruct x as [ [ ] | s ].
      - simpl; trivial.
      - simpl.
        generalize (subsorts_pre).
        intro presub.
        reflexivity.
    Qed.

    Lemma ConstructorTaxonomy_transitive: Transitive ConstructorTaxonomy.
    Proof.
      intros x y z.
      destruct x as [ [] | x ]; destruct y as [ [] | y ]; destruct z as [ [] | z ];
        intros xy yz;
        try solve [ contradiction | trivial ].
      generalize (subsorts_pre); intro presub.
      simpl.
      transitivity y; assumption.
    Qed.

    Lemma ConstructorTaxonomy_eq_dec: forall (c1 c2: ConstructorSymbol), { c1 = c2 } + { c1 <> c2 }.
    Proof.
      intros c1 c2.
      destruct c1 as [ [] | c1 ]; destruct c2 as [ [] | c2 ];
        try solve [ left; reflexivity | right; intro devil; inversion devil ].
      generalize (SigSpec).
      intro sigspec.
      destruct (Sort_eq_dec c1 c2);
        [ left; apply f_equal; assumption
        | right; intro devil; inversion devil; contradiction ].
    Qed.

    Lemma ConstructorTaxonomy_dec: forall c1 c2, { ConstructorTaxonomy c1 c2 } + { ConstructorTaxonomy c1 c2 -> False }.
    Proof.
      intros c1 c2.
      destruct c1 as [ [] | ]; destruct c2 as [ [] | ];
        try solve [ left; reflexivity | right; intro; assumption ].
      apply subsorts_dec.
    Qed.

    Definition constructorSymbolToNat (c: ConstructorSymbol): nat :=
      match c with
      | inl tt => cantor_sum (inl 0)
      | inr c => cantor_sum (inr (toNat c))
      end.
    Definition natToConstructorSymbol (n: nat): ConstructorSymbol :=
      match cantor_sum_inv n with
      | inl _ => inl tt
      | inr n => inr (fromNat n)
      end.
    Lemma fromToConstructorSymbol_id: forall c, natToConstructorSymbol (constructorSymbolToNat c) = c.
    Proof.
      intro c.
      destruct c as [ [] | c ].
      - reflexivity.
      - unfold constructorSymbolToNat.
        unfold natToConstructorSymbol.
        rewrite cantor_sum_inj.
        rewrite fromTo_id.
        reflexivity.
    Qed.
  End ConstructorDefs.
    
  Definition Symbols: ConstructorSpecification ConstructorSymbol :=
    {| constructorArity := fun c => match c with | inl _ => 1 | inr _ => 0 end;
       ConstructorTaxonomy := ConstructorDefs.ConstructorTaxonomy;        
       CTPreorder :=
         {| PreOrder_Reflexive := ConstructorDefs.ConstructorTaxonomy_reflexive;
            PreOrder_Transitive := ConstructorDefs.ConstructorTaxonomy_transitive |};
       ConstructorSymbol_eq_dec := ConstructorDefs.ConstructorTaxonomy_eq_dec;
       ConstructorTaxonomy_dec := ConstructorDefs.ConstructorTaxonomy_dec |}.
  Instance ConstructorSymbol_countable: Countable ConstructorSymbol :=
    {| toNat := ConstructorDefs.constructorSymbolToNat;
       fromNat := ConstructorDefs.natToConstructorSymbol;
       fromTo_id := ConstructorDefs.fromToConstructorSymbol_id |}.
  Instance Variables_finite: Finite VariableSymbol := SigSpec.Vars_finite.
  Definition ClosedSortsInhabited: Sort EmptySet := fromNat 0.
  Definition OpenSortsInhabited: Sort Var := SigSpec.OpenSortsInhabited.
  Definition BlackBox : ConstructorSymbol := inl tt.
  Lemma BlackBoxArity: @constructorArity _ Symbols BlackBox = 1.
  Proof.
    reflexivity.
  Qed.
End SortConstructorCLSignature.

Module Type CountableClosedSortSignatureSpec.
  Include SignatureSpec with Definition Var := EmptySet.
  Declare Instance ClosedSortsCountable: Countable (Sort EmptySet).
  Parameter applySubst_eq: forall S s, applySubst S s = s.
End CountableClosedSortSignatureSpec.

Module Type FiniteCountableFromCountableClosedSortSignatureSpec
       (SigSpec: CountableClosedSortSignatureSpec) <: FiniteCountableSignatureSpec.
  Definition Sort: Set -> Set := SigSpec.Sort.
  Definition Var: Set := SigSpec.Var.
  Definition Operation: Set := SigSpec.Operation.
  Definition WellFormed: (Var -> Sort EmptySet) -> Prop := SigSpec.WellFormed.
  Instance SigSpec: SignatureSpecification Sort Var Operation := SigSpec.SigSpec.
  Instance ClosedSortsCountable: Countable (Sort EmptySet) := SigSpec.ClosedSortsCountable.
  Instance Vars_finite: Finite Var :=
    {| cardinality := 0;
       toFin := fun devil => False_rect _ devil;
       fromFin := fun devil =>
                    match devil in Fin.t n return 0 = n -> EmptySet with
                    | Fin.F1 =>
                      fun devil' =>
                        match devil' in _ = n return match n with | 0 => True | _ => False end with
                        | eq_refl => I
                        end  
                    | Fin.FS _ =>
                      fun devil' =>
                        match devil' in _ = n return match n with | 0 => True | _ => False end with
                        | eq_refl => I
                        end
                    end eq_refl;
       fromToFin_id := fun devil => False_rect _ devil |}.
  Definition OpenSortsInhabited: Sort Var := fromNat 0.
End FiniteCountableFromCountableClosedSortSignatureSpec.

Module Type MakeClosedSortCLSignature(SigSpec: CountableClosedSortSignatureSpec).
  Declare Module SigSpec' : FiniteCountableFromCountableClosedSortSignatureSpec(SigSpec).
  Declare Module Signature : SortConstructorCLSignature(SigSpec').
End MakeClosedSortCLSignature.


Module Type ProperConstantEmbedding
       (Import SigSpec: CountableClosedSortSignatureSpec)
       (Import MakeSignature: MakeClosedSortCLSignature(SigSpec))
       (Import Types: IntersectionTypes(MakeSignature.Signature))
<: WithProperEmbedding(MakeSignature.Signature)(Types).
  
  Module Embedding : SortEmbedding(Signature)(Types).
    Include SortEmbedding(Signature)(Types).
  End Embedding.

  Import Embedding.

  Module Proper.
    Import Signature.
    Definition embedS (s: Sort EmptySet) := ConstScheme (inr s) (nil _).
    Definition unembedS (ts: TypeScheme (VariableSymbol := EmptySet)): Sort EmptySet :=
      match ts with
      | Skeleton (PT_Const (inr C) _) => C
      | _ => OpenSortsInhabited
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
      apply (ST_Ax (inr s) (inr s') eq_refl); [ assumption | apply Forall2_nil ].
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

Module Type ConstantFiniteWellFormedPredicate
       (Import SigSpec: CountableClosedSortSignatureSpec)
       (Import MakeSignature: MakeClosedSortCLSignature(SigSpec))
       (Import Types: IntersectionTypes(MakeSignature.Signature))
<: FiniteWellFormedPredicate(MakeSignature.Signature)(Types)
<: DecidableWellFormedPredicate(MakeSignature.Signature)(Types).
  Definition WellFormed: Substitution -> Prop := fun S => forall alpha, S alpha = omega.
  Definition SubstitutionSpace : Set := unit.
  Definition SubstitutionSpace_sound: SubstitutionSpace -> { S : Substitution | WellFormed S } :=
    fun _ => exist _ (fun _ => omega) (fun alpha => eq_refl).
  Definition SubstitutionSpace_complete: { S : Substitution | WellFormed S } -> SubstitutionSpace :=
    fun _ => tt.
  Lemma SubstitutionSpace_eq:
    forall WFS alpha, proj1_sig (SubstitutionSpace_sound (SubstitutionSpace_complete WFS)) alpha =
                 proj1_sig WFS alpha.
  Proof.
    intros WFS alpha; simpl.
    rewrite (proj2_sig WFS alpha).
    reflexivity.
  Qed.
  Instance SubstitutionSpace_finite: Finite SubstitutionSpace :=
    {| cardinality := 1;
       toFin := fun _ => Fin.F1;
       fromFin := fun _ => tt;
       fromToFin_id := fun x => match x with | tt => eq_refl end |}.
  Lemma WF_dec: forall S, { WellFormed S } + { ~ WellFormed S }.
  Proof.
    intro S; left; intro alpha.
    contradiction.
  Qed.

  Lemma WF_ext: forall S S', (forall alpha, S alpha = S' alpha) -> WellFormed S -> WellFormed S'.
  Proof.
    intros S S' S_eq WF_S.
    intro alpha.
    rewrite <- (S_eq alpha).
    apply WF_S.
  Qed.
   
End ConstantFiniteWellFormedPredicate.                  



(* Trees *)
Module Type TreeSpec.
  Parameter Label: Set.
  Parameter Var: Set.
  Parameter LOrder: Label -> Label -> Prop.

  Declare Instance Info: LabelInfo Label.
  Declare Instance LOrder_pre: PreOrder LOrder.

  Parameter Operation: Set.
  Parameter WellFormed: (Var -> VLTree Label EmptySet) -> Prop.
  Declare Instance Sigma: Signature (VLTree Label) Var Operation.

  Parameter Var_eq_dec:  forall (alpha beta: Var), { alpha = beta } + { alpha <> beta }.
  Parameter Label_eq_dec: forall (l1 l2: Label), { l1 = l2 } + { l1 <> l2 }.  
End TreeSpec.
(* TODO:

Module Type TreeSignatureSpec(Import Trees: TreeSpec) <: FiniteCountableSignatureSpec.
  Definition Sort: Set -> Set := VLTree Label.
  Definition Var: Set := Trees.Var.
  Definition Operation: Set := Trees.Operation.
  Definition WellFormed: (Var -> Sort EmptySet) -> Prop := Trees.WellFormed.
  Instance SigSpec: SignatureSpecification Sort Var Operation := SigSpec.SigSpec.
  
  Declare Instance SigSpec: SignatureSpecification Sort Var Operation.
End SignatureSpec.


Module Type TreeSortCLSignature(SigSpec: FiniteCountableSignatureSpec) <: CompatibleCLSignature.
  Definition Sort: Set -> Set := SigSpec.Sort.
  Definition Var: Set := SigSpec.Var.
  Definition Operation: Set := SigSpec.Operation.
  Definition WellFormed: (Var -> Sort EmptySet) -> Prop := SigSpec.WellFormed.
  Instance SigSpec: SignatureSpecification Sort Var Operation := SigSpec.SigSpec.
  
  Definition ConstructorSymbol := (unit + Sort EmptySet)%type.
  Definition VariableSymbol := Var.
  Definition CombinatorSymbol := Operation.
  Definition VariableSymbol_eq_dec := Var_eq_dec.
  Module ConstructorDefs.
    Definition ConstructorTaxonomy: ConstructorSymbol -> ConstructorSymbol -> Prop :=
      fun c1 c2 =>
        match c1 with
        | inr c1 =>
          match c2 with
          | inr c2 => subsorts c1 c2
          | _ => False
          end
        | inl tt =>
          match c2 with
          | inl tt => True
          | inr _ => False
          end
        end.
    Lemma ConstructorTaxonomy_reflexive: Reflexive ConstructorTaxonomy.
    Proof.
      intro x.
      destruct x as [ [ ] | s ].
      - simpl; trivial.
      - simpl.
        generalize (subsorts_pre).
        intro presub.
        reflexivity.
    Qed.

    Lemma ConstructorTaxonomy_transitive: Transitive ConstructorTaxonomy.
    Proof.
      intros x y z.
      destruct x as [ [] | x ]; destruct y as [ [] | y ]; destruct z as [ [] | z ];
        intros xy yz;
        try solve [ contradiction | trivial ].
      generalize (subsorts_pre); intro presub.
      simpl.
      transitivity y; assumption.
    Qed.

    Lemma ConstructorTaxonomy_eq_dec: forall (c1 c2: ConstructorSymbol), { c1 = c2 } + { c1 <> c2 }.
    Proof.
      intros c1 c2.
      destruct c1 as [ [] | c1 ]; destruct c2 as [ [] | c2 ];
        try solve [ left; reflexivity | right; intro devil; inversion devil ].
      generalize (SigSpec).
      intro sigspec.
      destruct (Sort_eq_dec c1 c2);
        [ left; apply f_equal; assumption
        | right; intro devil; inversion devil; contradiction ].
    Qed.

    Lemma ConstructorTaxonomy_dec: forall c1 c2, { ConstructorTaxonomy c1 c2 } + { ConstructorTaxonomy c1 c2 -> False }.
    Proof.
      intros c1 c2.
      destruct c1 as [ [] | ]; destruct c2 as [ [] | ];
        try solve [ left; reflexivity | right; intro; assumption ].
      apply subsorts_dec.
    Qed.

    Definition constructorSymbolToNat (c: ConstructorSymbol): nat :=
      match c with
      | inl tt => cantor_sum (inl 0)
      | inr c => cantor_sum (inr (toNat c))
      end.
    Definition natToConstructorSymbol (n: nat): ConstructorSymbol :=
      match cantor_sum_inv n with
      | inl _ => inl tt
      | inr n => inr (fromNat n)
      end.
    Lemma fromToConstructorSymbol_id: forall c, natToConstructorSymbol (constructorSymbolToNat c) = c.
    Proof.
      intro c.
      destruct c as [ [] | c ].
      - reflexivity.
      - unfold constructorSymbolToNat.
        unfold natToConstructorSymbol.
        rewrite cantor_sum_inj.
        rewrite fromTo_id.
        reflexivity.
    Qed.
  End ConstructorDefs.
    
  Definition Symbols: ConstructorSpecification ConstructorSymbol :=
    {| constructorArity := fun c => match c with | inl _ => 1 | inr _ => 0 end;
       ConstructorTaxonomy := ConstructorDefs.ConstructorTaxonomy;        
       CTPreorder :=
         {| PreOrder_Reflexive := ConstructorDefs.ConstructorTaxonomy_reflexive;
            PreOrder_Transitive := ConstructorDefs.ConstructorTaxonomy_transitive |};
       ConstructorSymbol_eq_dec := ConstructorDefs.ConstructorTaxonomy_eq_dec;
       ConstructorTaxonomy_dec := ConstructorDefs.ConstructorTaxonomy_dec |}.
  Instance ConstructorSymbol_countable: Countable ConstructorSymbol :=
    {| toNat := ConstructorDefs.constructorSymbolToNat;
       fromNat := ConstructorDefs.natToConstructorSymbol;
       fromTo_id := ConstructorDefs.fromToConstructorSymbol_id |}.
  Instance Variables_finite: Finite VariableSymbol := SigSpec.Vars_finite.
  Definition ClosedSortsInhabited: Sort EmptySet := fromNat 0.
  Definition OpenSortsInhabited: Sort Var := SigSpec.OpenSortsInhabited.
  Definition BlackBox : ConstructorSymbol := inl tt.
  Lemma BlackBoxArity: @constructorArity _ Symbols BlackBox = 1.
  Proof.
    reflexivity.
  Qed.
End SortConstructorCLSignature.

Module Type CountableClosedSortSignatureSpec.
  Include SignatureSpec with Definition Var := EmptySet.
  Declare Instance ClosedSortsCountable: Countable (Sort EmptySet).
  Parameter applySubst_eq: forall S s, applySubst S s = s.
End CountableClosedSortSignatureSpec.

Module Type FiniteCountableFromCountableClosedSortSignatureSpec
       (SigSpec: CountableClosedSortSignatureSpec) <: FiniteCountableSignatureSpec.
  Definition Sort: Set -> Set := SigSpec.Sort.
  Definition Var: Set := SigSpec.Var.
  Definition Operation: Set := SigSpec.Operation.
  Definition WellFormed: (Var -> Sort EmptySet) -> Prop := SigSpec.WellFormed.
  Instance SigSpec: SignatureSpecification Sort Var Operation := SigSpec.SigSpec.
  Instance ClosedSortsCountable: Countable (Sort EmptySet) := SigSpec.ClosedSortsCountable.
  Instance Vars_finite: Finite Var :=
    {| cardinality := 0;
       toFin := fun devil => False_rect _ devil;
       fromFin := fun devil =>
                    match devil in Fin.t n return 0 = n -> EmptySet with
                    | Fin.F1 =>
                      fun devil' =>
                        match devil' in _ = n return match n with | 0 => True | _ => False end with
                        | eq_refl => I
                        end  
                    | Fin.FS _ =>
                      fun devil' =>
                        match devil' in _ = n return match n with | 0 => True | _ => False end with
                        | eq_refl => I
                        end
                    end eq_refl;
       fromToFin_id := fun devil => False_rect _ devil |}.
  Definition OpenSortsInhabited: Sort Var := fromNat 0.
End FiniteCountableFromCountableClosedSortSignatureSpec.

Module Type MakeClosedSortCLSignature(SigSpec: CountableClosedSortSignatureSpec).
  Declare Module SigSpec' : FiniteCountableFromCountableClosedSortSignatureSpec(SigSpec).
  Declare Module Signature : SortConstructorCLSignature(SigSpec').
End MakeClosedSortCLSignature.


Module Type ProperConstantEmbedding
       (Import SigSpec: CountableClosedSortSignatureSpec)
       (Import MakeSignature: MakeClosedSortCLSignature(SigSpec))
       (Import Types: IntersectionTypes(MakeSignature.Signature))
<: WithProperEmbedding(MakeSignature.Signature)(Types).
  
  Module Embedding : SortEmbedding(Signature)(Types).
    Include SortEmbedding(Signature)(Types).
  End Embedding.

  Import Embedding.

  Module Proper.
    Import Signature.
    Definition embedS (s: Sort EmptySet) := ConstScheme (inr s) (nil _).
    Definition unembedS (ts: TypeScheme (VariableSymbol := EmptySet)): Sort EmptySet :=
      match ts with
      | Skeleton (PT_Const (inr C) _) => C
      | _ => OpenSortsInhabited
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
      apply (ST_Ax (inr s) (inr s') eq_refl); [ assumption | apply Forall2_nil ].
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

Module Type ConstantFiniteWellFormedPredicate
       (Import SigSpec: CountableClosedSortSignatureSpec)
       (Import MakeSignature: MakeClosedSortCLSignature(SigSpec))
       (Import Types: IntersectionTypes(MakeSignature.Signature))
<: FiniteWellFormedPredicate(MakeSignature.Signature)(Types)
<: DecidableWellFormedPredicate(MakeSignature.Signature)(Types).
  Definition WellFormed: Substitution -> Prop := fun S => forall alpha, S alpha = omega.
  Definition SubstitutionSpace : Set := unit.
  Definition SubstitutionSpace_sound: SubstitutionSpace -> { S : Substitution | WellFormed S } :=
    fun _ => exist _ (fun _ => omega) (fun alpha => eq_refl).
  Definition SubstitutionSpace_complete: { S : Substitution | WellFormed S } -> SubstitutionSpace :=
    fun _ => tt.
  Lemma SubstitutionSpace_eq:
    forall WFS alpha, proj1_sig (SubstitutionSpace_sound (SubstitutionSpace_complete WFS)) alpha =
                 proj1_sig WFS alpha.
  Proof.
    intros WFS alpha; simpl.
    rewrite (proj2_sig WFS alpha).
    reflexivity.
  Qed.
  Instance SubstitutionSpace_finite: Finite SubstitutionSpace :=
    {| cardinality := 1;
       toFin := fun _ => Fin.F1;
       fromFin := fun _ => tt;
       fromToFin_id := fun x => match x with | tt => eq_refl end |}.
  Lemma WF_dec: forall S, { WellFormed S } + { ~ WellFormed S }.
  Proof.
    intro S; left; intro alpha.
    contradiction.
  Qed.

  Lemma WF_ext: forall S S', (forall alpha, S alpha = S' alpha) -> WellFormed S -> WellFormed S'.
  Proof.
    intros S S' S_eq WF_S.
    intro alpha.
    rewrite <- (S_eq alpha).
    apply WF_S.
  Qed.
   
End ConstantFiniteWellFormedPredicate.                  
*)