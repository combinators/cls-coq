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
Require Import VectorQuantification.

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
  Parameter LOrder_dec: forall (l1 l2: Label), { LOrder l1 l2 } + { LOrder l1 l2 -> False }.

  Declare Instance Vars_finite: Finite Var.
  Declare Instance Labels_countable: Countable Label.
  Parameter GroundLabel: { l : Label | labelArity l = 0 }.
End TreeSpec.


Module Type TreeSignatureSpec(Import Trees: TreeSpec) <: FiniteCountableSignatureSpec.
  Definition Sort: Set -> Set := VLTree Label.
  Definition Var: Set := Trees.Var.
  Definition Operation: Set := Trees.Operation.
  Definition WellFormed: (Var -> Sort EmptySet) -> Prop := Trees.WellFormed.
  Instance TreeSubst: CanSubst (VLTree Label) :=
    {| applySubst := fun _ f t => substitute f t |}.
  Definition TreeSubsorts: Sort EmptySet -> Sort EmptySet -> Prop :=
    VLTreeOrder Trees.Label LOrder.
  Instance SigSpec: SignatureSpecification Sort Var Operation :=
    {| subsorts := VLTreeOrder Trees.Label LOrder;
       SigmaAlgebra.Sigma := Trees.Sigma;
       subsorts_pre := VLOrderPre _ LOrder;
       SigmaAlgebra.Var_eq_dec := Trees.Var_eq_dec;
       Sort_eq_dec := Tree_eq_dec _ _ Label_eq_dec (fun x => False_rect _ x);
       subsorts_dec := VLTreeOrder_dec _ LOrder LOrder_dec;
       SortSubst := TreeSubst |}.
  Instance ClosedSortsCountable: Countable (Sort EmptySet) :=
    {| toNat := VLTreeToNat _ toNat;
       fromNat := natToVLTree _ fromNat (proj1_sig GroundLabel) (proj2_sig GroundLabel);
       fromTo_id := natVLTree_inj toNat fromNat (proj1_sig GroundLabel) (proj2_sig GroundLabel) fromTo_id |}.       
  Instance Vars_finite: Finite Var := Trees.Vars_finite.
  Definition OpenSortsInhabited: Sort Var :=
    substitute (fun devil => False_rect _ devil) (fromNat 0).
End TreeSignatureSpec.

Module Type TreeSortCLSignature
       (Trees: TreeSpec)
       (SigSpec: TreeSignatureSpec(Trees)) <: CompatibleCLSignature.
  Definition Sort: Set -> Set := SigSpec.Sort.
  Definition Var: Set := SigSpec.Var.
  Definition Operation: Set := SigSpec.Operation.
  Definition WellFormed: (Var -> Sort EmptySet) -> Prop := SigSpec.WellFormed.
  Instance SigSpec: SignatureSpecification Sort Var Operation := SigSpec.SigSpec.

  Inductive CtorSym : Set := BB | Dot | Label: Trees.Label -> CtorSym.
  
  Definition ConstructorSymbol := CtorSym.
  Definition VariableSymbol := Var.
  Definition CombinatorSymbol := Operation.
  Definition VariableSymbol_eq_dec := Var_eq_dec.
  Module ConstructorDefs.
    Definition ConstructorTaxonomy: ConstructorSymbol -> ConstructorSymbol -> Prop :=
      fun c1 c2 =>
        match c1 with
        | Label c1 =>
          match c2 with
          | Label c2 => Trees.LOrder c1 c2
          | _ => False
          end
        | BB =>
          match c2 with
          | BB => True
          | _ => False
          end
        | Dot =>
          match c2 with
          | Dot => True
          | _ => False
          end
        end.
    Lemma ConstructorTaxonomy_reflexive: Reflexive ConstructorTaxonomy.
    Proof.
      intro x.
      destruct x as [ | | s ]; try solve [ simpl; trivial ].
      simpl.
      generalize (Trees.LOrder_pre).
      intro presub.
      reflexivity.
    Qed.

    Lemma ConstructorTaxonomy_transitive: Transitive ConstructorTaxonomy.
    Proof.
      intros x y z.
      destruct x as [ | | x ]; destruct y as [ | | y ]; destruct z as [ | | z ];
        intros xy yz;
        try solve [ contradiction | trivial ].
      generalize (Trees.LOrder_pre); intro presub.
      simpl.
      transitivity y; assumption.
    Qed.

    Lemma ConstructorTaxonomy_eq_dec: forall (c1 c2: ConstructorSymbol), { c1 = c2 } + { c1 <> c2 }.
    Proof.
      intros c1 c2.
      destruct c1 as [ | | c1 ]; destruct c2 as [ | | c2 ];
        try solve [ left; reflexivity | right; intro devil; inversion devil ].
      generalize (SigSpec).
      intro sigspec.
      destruct (Trees.Label_eq_dec c1 c2);
        [ left; apply f_equal; assumption
        | right; intro devil; inversion devil; contradiction ].
    Qed.

    Lemma ConstructorTaxonomy_dec: forall c1 c2, { ConstructorTaxonomy c1 c2 } + { ConstructorTaxonomy c1 c2 -> False }.
    Proof.
      intros c1 c2.
      destruct c1 as [ | | ]; destruct c2 as [ | | ];
        try solve [ left; reflexivity | right; intro; assumption ].
      apply Trees.LOrder_dec.
    Qed.

    Definition constructorSymbolToNat (c: ConstructorSymbol): nat :=
      match c with
      | BB => cantor_sum (inl 0)
      | Dot => cantor_sum (inr (cantor_sum (inl 0)))
      | Label l => cantor_sum (inr (cantor_sum (inr (toNat l))))
      end.
    Definition natToConstructorSymbol (n: nat): ConstructorSymbol :=
      match cantor_sum_inv n with
      | inl _ => BB
      | inr n =>
        match cantor_sum_inv n with
        | inl _ => Dot
        | inr n => Label (fromNat n)
        end
      end.
    Lemma fromToConstructorSymbol_id: forall c, natToConstructorSymbol (constructorSymbolToNat c) = c.
    Proof.
      intro c.
      destruct c as [ | | l ].
      - reflexivity.
      - unfold constructorSymbolToNat.
        unfold natToConstructorSymbol.
        rewrite (cantor_sum_inj (inr (cantor_sum (inl 0)))).
        rewrite cantor_sum_inj.
        reflexivity.
      - unfold constructorSymbolToNat.
        unfold natToConstructorSymbol.
        rewrite cantor_sum_inj.
        rewrite cantor_sum_inj.
        rewrite fromTo_id.
        reflexivity.
    Qed.
  End ConstructorDefs.
    
  Definition Symbols: ConstructorSpecification ConstructorSymbol :=
    {| constructorArity := fun c => match c with | BB => 1 | Dot => 0 | Label l => labelArity l end;
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
  Definition BlackBox : ConstructorSymbol := BB.
  Lemma BlackBoxArity: @constructorArity _ Symbols BlackBox = 1.
  Proof.
    reflexivity.
  Qed.
End TreeSortCLSignature.

Module Type MakeTreeSortCLSignature(Trees: TreeSpec).
  Declare Module SigSpec: TreeSignatureSpec(Trees).
  Declare Module Signature: TreeSortCLSignature(Trees)(SigSpec).
End MakeTreeSortCLSignature.

(* In progress

Module Type ProperTreeSortEmbedding
       (Import Trees: TreeSpec)
       (Import MakeSignature: MakeTreeSortCLSignature(Trees))
       (Import Types: IntersectionTypes(MakeSignature.Signature))
<: WithProperEmbedding(MakeSignature.Signature)(Types).
  
  Module Embedding : SortEmbedding(Signature)(Types).
    Include SortEmbedding(Signature)(Types).
  End Embedding.

  Import Embedding.

  Module Proper.
    Import Signature.

    Definition ClosedArrowScheme (src tgt: @TypeScheme EmptySet): @TypeScheme EmptySet :=
      Skeleton (PT_Arrow src tgt).

    Definition ClosedConstScheme
               (c: ConstructorSymbol)
               (xs: t (@TypeScheme EmptySet) (constructorArity c)): @TypeScheme EmptySet :=
      Skeleton (PT_Const c xs).      
    
    Fixpoint closedEmbedS_variance (s: Sort EmptySet) (v: Variance) {struct s}: @TypeScheme EmptySet :=
      match s with
      | Node _ _ l xs =>
        match v with
        | Co =>
          ClosedArrowScheme (ClosedArrowScheme
                               (ClosedConstScheme (Label l)
                                                  (map2 (fun x v => closedEmbedS_variance x (successorVariance l v))
                                                        xs
                                                        (positions (labelArity l))))
                               (ClosedConstScheme Dot (nil _)))
                            (ClosedConstScheme Dot (nil _))
        | Contra =>
          ClosedArrowScheme (ClosedArrowScheme
                               (ClosedConstScheme Dot (nil _))
                               (ClosedConstScheme (Label l)
                                                  (map2 (fun x v => closedEmbedS_variance x (successorVariance l v))
                                                        xs
                                                        (positions (labelArity l)))))
                            (ClosedConstScheme Dot (nil _))
        | In =>
          ClosedArrowScheme (ClosedArrowScheme
                               (ClosedConstScheme (Label l)
                                                  (map2 (fun x v => closedEmbedS_variance x (successorVariance l v))
                                                        xs
                                                        (positions (labelArity l))))
                               (ClosedConstScheme (Label l)
                                                  (map2 (fun x v => closedEmbedS_variance x (successorVariance l v))
                                                        xs
                                                        (positions (labelArity l)))))
                            (ClosedConstScheme Dot (nil _))
        end
      | Hole _ _ alpha => False_rect _ alpha
      end.
    
    Fixpoint openEmbedS_variance (s: Sort Var) (v: Variance) {struct s}: TypeScheme :=
      match s with
      | Node _ _ l xs =>
        match v with
        | Co =>
          ArrowScheme (ArrowScheme
                         (ConstScheme (Label l)
                                      (map2 (fun x v => openEmbedS_variance x (successorVariance l v))
                                            xs
                                            (positions (labelArity l))))
                         (ConstScheme Dot (nil _)))
                      (ConstScheme Dot (nil _))
        | Contra =>
          ArrowScheme (ArrowScheme
                         (ConstScheme Dot (nil _))
                         (ConstScheme (Label l)
                                      (map2 (fun x v => openEmbedS_variance x (successorVariance l v))
                                            xs
                                            (positions (labelArity l)))))
                      (ConstScheme Dot (nil _))
        | In =>
          ArrowScheme (ArrowScheme
                         (ConstScheme (Label l)
                                      (map2 (fun x v => openEmbedS_variance x (successorVariance l v))
                                            xs
                                            (positions (labelArity l))))
                         (ConstScheme (Label l)
                                      (map2 (fun x v => openEmbedS_variance x (successorVariance l v))
                                            xs
                                            (positions (labelArity l)))))
                      (ConstScheme Dot (nil _))
        end
      | Hole _ _ alpha => Types.Var alpha
      end.
    
    Definition closedEmbedS (s: Sort EmptySet) := closedEmbedS_variance s Co.
    Definition openEmbedS (s: Sort Var) := openEmbedS_variance s Co.
    
    Fixpoint closedUnembedS (ts: TypeScheme (VariableSymbol := EmptySet)): Sort EmptySet :=
      match ts with
      | Skeleton (PT_Arrow (Skeleton (PT_Arrow (Skeleton (PT_Const (Label l) xs)) _)) _) =>
        Node _ _ l (map closedUnembedS xs)
      | Skeleton (PT_Arrow (Skeleton (PT_Arrow _ (Skeleton (PT_Const (Label l) xs)))) _) =>
        Node _ _ l (map closedUnembedS xs)
      | _ => ClosedSortsInhabited
      end.
    
    Fixpoint openUnembedS (ts: TypeScheme (VariableSymbol := Var)): Sort Var :=
      match ts with
      | Skeleton (PT_Arrow (Skeleton (PT_Arrow (Skeleton (PT_Const (Label l) xs)) _)) _) =>
        Node _ _ l (map openUnembedS xs)
      | Skeleton (PT_Arrow (Skeleton (PT_Arrow _ (Skeleton (PT_Const (Label l) xs)))) _) =>
        Node _ _ l (map openUnembedS xs)
      | Types.Var alpha => Hole _ _ alpha
      | _ => OpenSortsInhabited
      end.

    Instance ClosedEmbedding : Embedding EmptySet :=
      {| embed := closedEmbedS; unembed := closedUnembedS |}.
    Instance OpenEmbedding : Embedding Var :=
      {| embed := openEmbedS; unembed := openUnembedS |}.

    Lemma openInjectivity: forall (s: Sort Var), unembed (embed s) = s.
    Proof.
      intro s.
      unfold embed.
      unfold unembed.
      simpl.
      unfold openEmbedS.
      generalize (Co).
      induction s as [ alpha | l successors IH ] using VLTree_rect'.
      - intro v; simpl; destruct v; reflexivity.
      - intro v.
        assert (successors_eq:
                  map openUnembedS
                      (map2 (fun x v => openEmbedS_variance x (successorVariance l v))
                            successors (positions (labelArity l))) = successors).
        { revert successors IH.
          generalize (successorVariance l).
          generalize (labelArity l).
          intros arity succVar successors IH'.
          generalize (Forall_nth _ _ (ForAll'Forall _ _ IH')).
          intro IH; clear IH'.
          rewrite (map_map2_fg).
          induction successors as [ | successor n successors IH' ].
          - reflexivity.
          - simpl.
            rewrite (IH Fin.F1 _).
            simpl.
            apply f_equal.
            rewrite <- (IH' (fun k => succVar (Fin.FS k)) (fun k => IH (Fin.FS k))) at 2.
            rewrite <- (map_id successors (fun x => x) (fun x => eq_refl)).
            rewrite <- (map_id (positions n) (fun x => x) (fun x => eq_refl)) at 2.
            rewrite map2_map_fg.
            rewrite map2_map_fg.
            reflexivity. }
        destruct v; simpl; rewrite successors_eq; reflexivity.
    Qed.

    Lemma closedInjectivity: forall (s: Sort EmptySet), unembed (embed s) = s.
    Proof.
      intro s.
      unfold embed.
      unfold unembed.
      simpl.
      unfold closedEmbedS.
      generalize (Co).
      induction s as [ | l successors IH ] using VLTree_rect'.
      - contradiction.
      - intro v.
        assert (successors_eq:
                  map closedUnembedS
                      (map2 (fun x v => closedEmbedS_variance x (successorVariance l v))
                            successors (positions (labelArity l))) = successors).
        { revert successors IH.
          generalize (successorVariance l).
          generalize (labelArity l).
          intros arity succVar successors IH'.
          generalize (Forall_nth _ _ (ForAll'Forall _ _ IH')).
          intro IH; clear IH'.
          rewrite (map_map2_fg).
          induction successors as [ | successor n successors IH' ].
          - reflexivity.
          - simpl.
            rewrite (IH Fin.F1 _).
            simpl.
            apply f_equal.
            rewrite <- (IH' (fun k => succVar (Fin.FS k)) (fun k => IH (Fin.FS k))) at 2.
            rewrite <- (map_id successors (fun x => x) (fun x => eq_refl)).
            rewrite <- (map_id (positions n) (fun x => x) (fun x => eq_refl)) at 2.
            rewrite map2_map_fg.
            rewrite map2_map_fg.
            reflexivity. }
        destruct v; simpl; rewrite successors_eq; reflexivity.
    Qed.
    
    Instance ClosedInjectiveEmbedding: InjectiveEmbedding EmptySet :=
      {| Embed := ClosedEmbedding; unembedEmbed := closedInjectivity |}.
    Instance OpenInjectiveEmbedding: InjectiveEmbedding Var :=
      {| Embed := OpenEmbedding; unembedEmbed := openInjectivity |}.
    (*Lemma embed_respectful: forall s s', subsorts s s' -> freeze (embed s) <= freeze (embed s').
    Proof.
      intro s.
      induction s as [ | l successors IH ] using VLTree_rect'; [ contradiction | ].
      intros s' s_le.
      destruct s'; [ | contradiction ].
      simpl.
      apply ST_CoContra; [ | reflexivity ].
      
      inversion s_le.
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
    Qed.*)

    Lemma embed_Path: forall s, Path (freeze (embed s)).
    Proof.
      intros.
      destruct s; [ | contradiction ].
      simpl.
      apply Path_Arr.
      apply Path_Const.
      apply PathArgs_nil.
    Qed.

    (*Lemma applyEq:
      forall S s v,
        freeze (closedEmbedS (substitute S s)) = Apply (embedSubst S) (openEmbedS s) ->
        freeze (closedEmbedS_variance (substitute S s) v) =
        Apply (embedSubst S) (openEmbedS_variance s v).
    Proof.
      intros S s.
      induction s as [ alpha | l successors IH ] using VLTree_rect'.
      - unfold embedSubst.
        intro v.
        simpl.
        destruct v.
        + simpl.
          unfold closedEmbedS.
          intro; reflexivity.
        + simpl.
          unfold closedEmbedS.*)

    Lemma embedApply_Var: forall S alpha, freeze (embed (applySubst S (Hole _ _ alpha))) =
                                     Apply (embedSubst S) (embed (Hole _ _ alpha)).
    Proof.
      intros S alpha; reflexivity.
    Qed.

    Require Import Coq.Arith.Wf_nat.

    Lemma embedApply: forall S s, freeze (embed (applySubst S s)) =
                                     Apply (embedSubst S) (embed s).
    Proof.
      intros S s.
      unfold embed.
      unfold embedSubst.
      unfold ClosedEmbedding.
      unfold OpenEmbedding.
      unfold embed.
      unfold closedEmbedS.
      unfold openEmbedS.
      generalize Co.      
      apply (fun IH => Fix (well_founded_ltof _ (VLTree_size _ _))
                        (fun s => forall v, freeze (closedEmbedS_variance (applySubst S s) v) =
                                    Apply _ (openEmbedS_variance s v)) IH s).
      clear s; intro s.
      destruct s as [ l successors | ].
      - intros IH v.
        destruct v.
        + simpl.
          apply f_equal2; [ | reflexivity ].
          apply f_equal2; [ | reflexivity ].
          apply f_equal.
          rewrite map_map2_fg.
          rewrite map_map2_fg.
          rewrite <- (map_id (positions (labelArity l)) (fun x => x) (fun x => eq_refl)) at 1.
          rewrite map2_map_fg.
          revert successors IH.
          generalize (successorVariance l).
          unfold ltof.
          unfold constructorArity.
          simpl.
          generalize (labelArity l).
          intros arity succVar successors successorPrfs.
          generalize Co.
          induction successorPrfs as [ | n successor successors prf prfs IH ].
          * reflexivity.
          * intro v.
            simpl.
            rewrite <- (map_id successors (fun x => x) (fun x => eq_refl)).
            rewrite map2_map_fg.
            rewrite map2_map_fg.
            rewrite (IH (fun k => succVar (Fin.FS k)) v).
            apply (f_equal (fun x => cons _ x _ _)).
            destruct successor.
            
      
      assert (notHole: forall alpha, Node _ _ l xs <> Hole _ _ alpha).
      { intros alpha devil; inversion devil. }     
      unfold embed.
      unfold embedSubst.
      unfold ClosedEmbedding.
      unfold OpenEmbedding.
      unfold embed.
      unfold closedEmbedS.
      unfold openEmbedS.
      generalize Co.      
      induction (Node _ _ l xs) as [ alpha | l' successors IH ] using VLTree_rect'.
      - destruct (notHole alpha eq_refl).
      - clear l xs notHole.
        simpl.
        intro v.
        destruct v.
        + simpl.
          apply f_equal2; [ | reflexivity ].
          apply f_equal2; [ | reflexivity ].
          apply f_equal.
          rewrite map_map2_fg.
          rewrite map_map2_fg.
          rewrite <- (map_id (positions (labelArity l')) (fun x => x) (fun x => eq_refl)) at 1.
          rewrite map2_map_fg.
          generalize (ForAll'Forall _ _ IH).
          clear IH.
          revert successors.
          generalize (successorVariance l').
          unfold constructorArity.
          simpl.
          generalize (labelArity l').
          intros arity succVar successors successorPrfs.
          generalize Co.
          induction successorPrfs as [ | n successor successors prf prfs IH ].
          * reflexivity.
          * intro v.
            simpl.
            rewrite <- (map_id successors (fun x => x) (fun x => eq_refl)).
            rewrite map2_map_fg.
            rewrite map2_map_fg.
            rewrite (IH (fun k => succVar (Fin.FS k)) v).
            apply (f_equal (fun x => cons _ x _ _)).
            destruct successor.
            { rewrite prf.
              - reflexivity.
                reflexivity.
              reflexivity.
            reflexivity.
        

        intro v.
        destruct v.
        + simpl.
          apply f_equal2; [ | reflexivity ].
          apply f_equal2; [ | reflexivity ].
          apply f_equal.
          rewrite map_map2_fg.
          rewrite map_map2_fg.
          rewrite <- (map_id (positions (labelArity l)) (fun x => x) (fun x => eq_refl)) at 1.
          rewrite map2_map_fg.
          generalize (ForAll'Forall _ _ IH).
          clear IH.
          revert successors.
          generalize (successorVariance l).
          unfold constructorArity.
          simpl.
          generalize (labelArity l).
          intros arity succVar successors successorPrfs.
          induction successorPrfs as [ | n successor successors prf prfs IH ].
          * reflexivity.
          * simpl.
            rewrite <- (map_id successors (fun x => x) (fun x => eq_refl)).
            rewrite map2_map_fg.
            rewrite map2_map_fg.
            rewrite (IH (fun k => succVar (Fin.FS k))).
            apply (f_equal (fun x => cons _ x _ _)).
            rewrite prf.
            reflexivity.
      + 
        
      
      
            
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

*)