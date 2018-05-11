Require Import Coq.Classes.RelationClasses.
Require Import Coq.Vectors.Vector.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Eqdep_dec.

Require Import SigmaAlgebra.
Require Import CombinatoryLogic.
Require Import IntersectionTypes.
Require Import CombinatoryLogicAlgebra.
Require Import FiniteSubstitutionSpace.
Require Import ComputationalPathLemma.
Require Import VarianceLabeledTree.
Require Import Cantor.
Require Import VectorQuantification.
Require Import FunctionSpace.

Module Type SortConstructorCLSignature(SigSpec: FiniteVarsCountableSortSignatureSpec) <: CompatibleCLSignature.
  Definition Sort: Set -> Type := SigSpec.Sort.
  Definition Var: Set := SigSpec.Var.
  Definition Operation: Type := SigSpec.Operation.
  Definition WellFormed: Type := SigSpec.WellFormed.
  Instance SigSpec: SignatureSpecification Sort Var Operation := SigSpec.SigSpec.
  Instance WellFormedSpace: FunctionSpace WellFormed Var (Sort EmptySet) := SigSpec.WellFormedSpace.
  
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
       (SigSpec: CountableClosedSortSignatureSpec) <: FiniteVarsCountableSortSignatureSpec.
  Definition Sort: Set -> Type := SigSpec.Sort.
  Definition Var: Set := SigSpec.Var.
  Definition Operation: Type := SigSpec.Operation.
  Definition WellFormed: Type := SigSpec.WellFormed.
  Instance SigSpec: SignatureSpecification Sort Var Operation := SigSpec.SigSpec.
  Instance WellFormedSpace: FunctionSpace WellFormed Var (Sort EmptySet) := SigSpec.WellFormedSpace.
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
       fromToFin_id := fun devil => False_rect _ devil;
       toFromFin_id := fun devil => Fin.case0 _ devil |}.
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
       unembedApply := (fun S tau prf _ => Proper.unembedApply S tau prf) |}.
End ProperConstantEmbedding.

Module Type ConstantFiniteWellFormedPredicate
       (Import SigSpec: CountableClosedSortSignatureSpec)
       (Import MakeSignature: MakeClosedSortCLSignature(SigSpec))
       (Import Types: IntersectionTypes(MakeSignature.Signature))
<: FiniteWellFormedPredicate(MakeSignature.Signature)(Types)
<: CountableWellFormedPredicate(MakeSignature.Signature)(Types).
  Definition WellFormed: Type := unit.
  Instance WellFormedSpace: FunctionSpace WellFormed SigSpec.Var IntersectionType := ConstantSpace _ _ omega.
  Instance SubstitutionSpace_finite: Finite WellFormed :=
    {| cardinality := 1;
       toFin := fun _ => Fin.F1;
       fromFin := fun _ => tt;
       fromToFin_id := fun x => match x with | tt => eq_refl end;
       toFromFin_id := fun x => match x as x' in Fin.t (S n) return n = 0 ->  Fin.F1 = x' with
                             | Fin.F1 => fun devil => eq_refl
                             | Fin.FS x => fun devil => Fin.case0 (fun _ => Fin.F1 = Fin.FS x) (eq_rect _ _ x _ devil)
                             end eq_refl |}.
  Instance SubstitutionSpace_nonEmpty : NonEmptyFinite WellFormed :=
    {| IsFinite := SubstitutionSpace_finite;
       cardinality_nonempty :=
         fun devil => eq_rect cardinality (fun (x: nat) => match x with | 1 => True | _ => False end) I _ devil |}.
  Instance SubstitutionSpace_countable: Countable WellFormed :=
    @CountableFromFinite WellFormed SubstitutionSpace_nonEmpty.
End ConstantFiniteWellFormedPredicate.                  

(* Trees *)
Module Type TreeSpec.
  Parameter Label: Set.
  Parameter Var: Set.
  Parameter LOrder: Label -> Label -> Prop.

  Declare Instance Info: LabelInfo Label.
  Declare Instance LOrder_pre: PreOrder LOrder.
  
  Parameter Operation: Set.
  Parameter WellFormed: Type.
  Declare Instance Sigma: Signature (VLTree Label) Var Operation.
  Declare Instance WellFormedSpace: FunctionSpace WellFormed Var (VLTree Label EmptySet).

  Parameter Var_eq_dec:  forall (alpha beta: Var), { alpha = beta } + { alpha <> beta }.
  Parameter Label_eq_dec: forall (l1 l2: Label), { l1 = l2 } + { l1 <> l2 }.
  Parameter LOrder_dec: forall (l1 l2: Label), { LOrder l1 l2 } + { LOrder l1 l2 -> False }.

  Declare Instance Vars_finite: Finite Var.
  Declare Instance Labels_countable: Countable Label.
  Parameter GroundLabel: { l : Label | labelArity l = 0 }.
End TreeSpec.


Module Type TreeSignatureSpec(Import Trees: TreeSpec) <: FiniteVarsCountableSortSignatureSpec.
  Definition Sort: Set -> Set := VLTree Label.
  Definition Var: Set := Trees.Var.
  Definition Operation: Set := Trees.Operation.
  Definition WellFormed: Type := Trees.WellFormed.
  Instance WellFormedSpace: FunctionSpace WellFormed Var (VLTree Label EmptySet) := Trees.WellFormedSpace.
  Instance TreeSubst: CanSubst (VLTree Label) :=
    {| applySubst := fun _ f t => substitute f t;
       applySubst_ext := fun Var => @substitute_ext _ Var EmptySet Info |}.
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
  Definition WellFormed: Type := SigSpec.WellFormed.
  Instance SigSpec: SignatureSpecification Sort Var Operation := SigSpec.SigSpec.
  Instance WellFormedSpace: FunctionSpace WellFormed Var (VLTree Trees.Label EmptySet) := Trees.WellFormedSpace.

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

    Fixpoint closedEmbedS (s: Sort EmptySet) {struct s}: @TypeScheme EmptySet :=
      match s with
      | Node _ _ l xs =>
        ClosedArrowScheme
          (ClosedArrowScheme
             (ClosedConstScheme
                (Label l)
                (map2 (fun x v =>
                         match successorVariance l v with
                         | Co =>
                           ClosedArrowScheme
                             (ClosedArrowScheme
                                (closedEmbedS x)
                                (ClosedConstScheme Dot (nil _)))
                             (ClosedConstScheme Dot (nil _))
                         | Contra =>
                           ClosedArrowScheme
                             (ClosedArrowScheme
                                (ClosedConstScheme Dot (nil _))
                                (closedEmbedS x))
                             (ClosedConstScheme Dot (nil _))
                         | In =>
                           ClosedArrowScheme
                             (ClosedArrowScheme
                                (closedEmbedS x)
                                (closedEmbedS x))
                             (ClosedConstScheme Dot (nil _))
                         end)
                      xs
                      (positions (labelArity l))))
             (ClosedConstScheme Dot (nil _)))
          (ClosedConstScheme Dot (nil _))
      | Hole _ _ alpha => False_rect _ alpha
      end.

    Fixpoint openEmbedS (s: Sort Var) {struct s}: @TypeScheme VariableSymbol :=
      match s with
      | Node _ _ l xs =>
        ArrowScheme
          (ArrowScheme
             (ConstScheme
                (Label l)
                (map2 (fun x v =>
                         match successorVariance l v with
                         | Co =>
                           ArrowScheme
                             (ArrowScheme
                                (openEmbedS x)
                                (ConstScheme Dot (nil _)))
                             (ConstScheme Dot (nil _))
                         | Contra =>
                           ArrowScheme
                             (ArrowScheme
                                (ConstScheme Dot (nil _))
                                (openEmbedS x))
                             (ConstScheme Dot (nil _))
                         | In =>
                           ArrowScheme
                             (ArrowScheme
                                (openEmbedS x)
                                (openEmbedS x))
                             (ConstScheme Dot (nil _))
                         end)
                      xs
                      (positions (labelArity l))))
             (ConstScheme Dot (nil _)))
          (ConstScheme Dot (nil _))
      | Hole _ _ alpha => Types.Var alpha
      end.
    
    Fixpoint closedUnembedS (ts: TypeScheme (VariableSymbol := EmptySet)): Sort EmptySet :=
      match ts with
      | Skeleton (PT_Arrow (Skeleton (PT_Arrow (Skeleton (PT_Const (Label l) xs)) _)) _) =>
        Node _ _ l
             (map
                (fun x =>
                   match x with
                   | Skeleton (PT_Arrow
                                 (Skeleton (PT_Arrow x' (Skeleton (PT_Const Dot (nil _)))))
                                 _) => closedUnembedS x'
                   | Skeleton (PT_Arrow (Skeleton (PT_Arrow _ x')) _) => closedUnembedS x'
                   | _ => ClosedSortsInhabited
                   end) xs)
      | _ => ClosedSortsInhabited
      end.

    Fixpoint openUnembedS (ts: TypeScheme (VariableSymbol := Var)): Sort Var :=
      match ts with
      | Skeleton (PT_Arrow (Skeleton (PT_Arrow (Skeleton (PT_Const (Label l) xs)) _)) _) =>
        Node _ _ l
             (map
                (fun x =>
                   match x with
                   | Skeleton (PT_Arrow
                                 (Skeleton (PT_Arrow x' (Skeleton (PT_Const Dot (nil _)))))
                                 _) => openUnembedS x'
                   | Skeleton (PT_Arrow (Skeleton (PT_Arrow _ x')) _) => openUnembedS x'
                   | _ => OpenSortsInhabited
                   end) xs)
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
      induction s as [ alpha | l successors IH ] using VLTree_rect'.
      - simpl; reflexivity.
      - simpl.
        apply f_equal.
        revert successors IH.
        fold openEmbedS.
        generalize (successorVariance l).
        generalize (labelArity l).
        intros n succVar successors IH.
        generalize (ForAll'Forall _ _ IH).
        clear IH; intro IH.
        induction IH as [ | n x xs prf prfs IH ].
        + reflexivity.
        + simpl.
          apply (f_equal2 (fun x xs => cons _ x _ xs)).
          * destruct (succVar Fin.F1);
              simpl; rewrite prf; try solve [ reflexivity ];
              unfold openEmbedS;
              destruct x; reflexivity. 
          * rewrite <- (map_id xs (fun x => x) (fun x => eq_refl)) at 1.
            rewrite (map2_map_fg).
            apply (IH (fun pos => succVar (Fin.FS pos))).            
    Qed.

    Lemma closedInjectivity: forall (s: Sort EmptySet), unembed (embed s) = s.
    Proof.
      intro s.
      unfold embed.
      unfold unembed.
      simpl.
      unfold openEmbedS.
      induction s as [ alpha | l successors IH ] using VLTree_rect'.
      - contradiction.
      - simpl.
        apply f_equal.
        revert successors IH.
        fold openEmbedS.
        generalize (successorVariance l).
        generalize (labelArity l).
        intros n succVar successors IH.
        generalize (ForAll'Forall _ _ IH).
        clear IH; intro IH.
        induction IH as [ | n x xs prf prfs IH ].
        + reflexivity.
        + simpl.
          apply (f_equal2 (fun x xs => cons _ x _ xs)).
          * destruct (succVar Fin.F1);
              simpl; rewrite prf; try solve [ reflexivity ];
              unfold openEmbedS;
              destruct x; try solve [ reflexivity ];
                solve [ contradiction ].
          * rewrite <- (map_id xs (fun x => x) (fun x => eq_refl)) at 1.
            rewrite (map2_map_fg).
            apply (IH (fun pos => succVar (Fin.FS pos))).            
    Qed.
    
    Instance ClosedInjectiveEmbedding: InjectiveEmbedding EmptySet :=
      {| Embed := ClosedEmbedding; unembedEmbed := closedInjectivity |}.
    Instance OpenInjectiveEmbedding: InjectiveEmbedding Var :=
      {| Embed := OpenEmbedding; unembedEmbed := openInjectivity |}.
      
    
    Lemma embed_respectful: forall s s', subsorts s s' -> freeze (embed s) <= freeze (embed s').
    Proof.
      intros s s'.
      apply (fun tgt =>
               @Fix_F_2 _ _ (fun x y => max (VLTree_size _ _ (fst x)) (VLTree_size _ _ (snd x)) <
                                     max (VLTree_size _ _ (fst y)) (VLTree_size _ _ (snd y)))
                        (fun s s' => subsorts s s' -> freeze (embed s) <= freeze (embed s'))
                        tgt s s' (WF_VLTree_size_max _ (s, s'))).
      clear s s'.
      intros s s' IH.
      destruct s as [ l successors | ]; [ | contradiction ].
      destruct s' as [ l' successors' | ]; [ | contradiction ].
      intros s_le.
      simpl.
      apply ST_CoContra; [ | reflexivity ].
      apply ST_CoContra; [ | reflexivity ].
      inversion s_le
        as [ ? ? arity_eq variance_eq ? ? l_le forest_order [ l_eq successors_eq ] [ l'_eq successors'_eq  ] ].
      unfold eq_rect_r in forest_order.
      rewrite (vect_exist_eq _ _
                             (existT_fg_eq (t (VLTree Trees.Label False))
                                           (labelArity) _ _ _ successors_eq))
        in forest_order.
      rewrite (vect_exist_eq _ _
                             (existT_fg_eq (t (VLTree Trees.Label False))
                                           (labelArity) _ _ _ successors'_eq))
        in forest_order.
      apply (ST_Ax (Label l) (Label l') arity_eq); [ assumption | ].
      apply nth_Forall2.
      intro k.
      rewrite map_map2_fg.
      rewrite map_map2_fg.
      rewrite (nth_map2 _ _ _ _ _ k eq_refl eq_refl).
      unfold eq_rect_r.
      rewrite nth_k.
      rewrite (nth_map2 _ _ _ _ _ _ eq_refl eq_refl).
      rewrite positions_spec.
      rewrite positions_spec.
      assert (k_eq: eq_rect _ _ k (labelArity l') arity_eq =
                    eq_rect_r Fin.t k (eq_sym arity_eq)).
      { unfold eq_rect_r.
        apply f_equal.
        apply (UIP_dec (Nat.eq_dec)). }
      revert k_eq.
      unfold constructorArity.
      simpl.
      intro k_eq.
      rewrite <- k_eq.
      rewrite <- variance_eq.
      assert (successor_le:
          match successorVariance l k with
          | Co =>
            freeze (closedEmbedS (nth successors k)) <=
            freeze (closedEmbedS (nth successors'
                                      (eq_rect (labelArity l) Fin.t k (labelArity l') arity_eq)))
          | Contra =>
            freeze (closedEmbedS (nth successors'
                                      (eq_rect (labelArity l) Fin.t k (labelArity l') arity_eq))) <=
            freeze (closedEmbedS (nth successors k))
          | In => 
            freeze (closedEmbedS (nth successors k)) <=
            freeze (closedEmbedS (nth successors'
                                      (eq_rect (labelArity l) Fin.t k (labelArity l') arity_eq))) /\
            freeze (closedEmbedS (nth successors'
                                      (eq_rect (labelArity l) Fin.t k (labelArity l') arity_eq))) <=
            freeze (closedEmbedS (nth successors k))
          end).
      { rewrite k_eq.
        rewrite <- nth_k.
        clear k_eq.
        revert k forest_order IH.
        unfold constructorArity.
        simpl.
        clear ...
        generalize (successorVariance l).
        revert successors'.
        rewrite (eq_sym arity_eq).
        simpl.
        intros successors' succVar k forest_order IH.
        clear arity_eq.
        assert (forest_order_k:
                    match succVar k with
                    | Co => VLTreeOrder _ LOrder (nth successors k) (nth successors' k)
                    | Contra => VLTreeOrder _ LOrder (nth successors' k) (nth successors k)
                    | In => VLTreeOrder _ LOrder (nth successors k) (nth successors' k) /\
                           VLTreeOrder _ LOrder (nth successors' k) (nth successors k)
                    end).
        { revert forest_order.
          clear ...
          rewrite <- (positions_spec _ k) at 1.
          rewrite <- (nth_map succVar (positions (labelArity l)) k k eq_refl).
          intro forest_order.
          induction forest_order as [ | t1 t2 n variances ts1 ts2 prf prfs IH
                                      | t1 t2 n variances ts1 ts2 prf prfs IH
                                      | t1 t2 n variances ts1 ts2 prf prf' prfs IH ];
            try solve [ inversion k ];
            apply (Fin.caseS' k);
            try solve [ assumption | split; assumption ];
            intro k';
            apply (IH (fun k => succVar (Fin.FS k)) k'). }
        generalize (Forall_nth _ _ (VLTree_size_lt _ _ l successors) k).
        intro successors_k_lt.
        generalize (Forall_nth _ _ (VLTree_size_lt _ _ l successors') k).
        intro successors'_k_lt.
        destruct (succVar k); [ | | split; destruct forest_order_k ];
          apply IH; try solve [ assumption ];
            unfold "_ < _";
            apply (proj1 (Nat.succ_le_mono _ _));
            solve
              [ apply (Nat.max_le_compat _ _);
                [ apply (proj2 (Nat.succ_le_mono _ _) successors_k_lt)
                | apply (proj2 (Nat.succ_le_mono _ _) successors'_k_lt) ]
              | rewrite (Nat.max_comm _ _);
                  apply (Nat.max_le_compat _ _);
                  [ apply (proj2 (Nat.succ_le_mono _ _) successors_k_lt)
                  | apply (proj2 (Nat.succ_le_mono _ _) successors'_k_lt) ] ]. }
      destruct (successorVariance l k);
         simpl;
         apply ST_CoContra;
         try solve [ reflexivity ];
         apply ST_CoContra;
         solve
           [ reflexivity
           | assumption
           | destruct successor_le; assumption ].
    Qed.

    Lemma embed_Path: forall s, Path (freeze (embed s)).
    Proof.
      intros.
      destruct s; [ | contradiction ].
      simpl.
      apply Path_Arr.
      apply Path_Const.
      apply PathArgs_nil.
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
      generalize (unembedEmbed s').
      generalize (unembedEmbed s).
      simpl.
      intros s_eq s'_eq.
      rewrite s_eq.
      rewrite s'_eq.
      revert sigma_le.
      apply (fun tgt =>
               @Fix_F_2 _ _ (fun x y => max (VLTree_size _ _ (fst x)) (VLTree_size _ _ (snd x)) <
                                     max (VLTree_size _ _ (fst y)) (VLTree_size _ _ (snd y)))
                        (fun s s' => freeze (embed s) <= freeze (embed s') -> VLTreeOrder _ LOrder s s')
                        tgt s s' (WF_VLTree_size_max _ (s, s'))).
      clear ...
      intros s s' IH.
      destruct s as [ l successors | ]; [ | contradiction ].
      destruct s' as [ l' successors' | ]; [ | contradiction ].
      intro ss'_le.
      simpl in ss'_le.
      generalize (AI_complete _ _ _ ss'_le).
      clear ss'_le.
      intro ss'_ideal.
      inversion ss'_ideal
        as [ | ? ? src_le tgt_le | | | ];
        [ contradiction | ].
      generalize (AI_complete _ _ _ src_le).
      revert IH.
      clear ...
      intros IH src_ideal.
      inversion src_ideal
        as [ | ? ? src_le tgt_le | | | ];
        [ contradiction | ].
      generalize (CI_complete _ _ _ src_le).
      revert IH.
      clear ...
      intros IH src_ideal.
      inversion src_ideal as [ ? ? arity_eq lorder successors_le [ l_eq successors_eq ] | | | ].
      clear l_eq.
      rewrite (vect_exist_eq _ _ (existT_fg_eq (t IntersectionType)
                                               (fun C => match C with
                                                      | BB => 1
                                                      | Dot => 0
                                                      | Label l => labelArity l end)
                                               _ _ _ successors_eq)) in successors_le.
      clear successors_eq.
      assert (varianceEq:
          forall k : Fin.t (labelArity l),
            successorVariance l k =
            successorVariance l' (eq_rect (labelArity l) Fin.t k (labelArity l') arity_eq)).
      { intro k.
        generalize (Forall2_nth _ _ _ successors_le k).
        clear ...
        simpl in arity_eq.
        generalize (successorVariance l').
        generalize (successorVariance l).
        revert successors k.
        simpl.
        rewrite arity_eq.
        unfold eq_rect_r.
        simpl.
        clear ...
        intros successors k succVar succVar'.
        induction k as [ | n k IH ].
        - apply (caseS' successors); clear successors; intros successor successors.
          apply (caseS' successors'); clear successors'; intros successor' successors'.
          simpl.
          destruct (succVar Fin.F1);
            destruct (succVar' Fin.F1);
            try solve [ intro; reflexivity ];
            simpl;
            intro subtypes;
            generalize (AI_complete _ _ _ subtypes);
            clear subtypes;
            intro ideal;
            inversion ideal as [ | ? ? src_le tgt_le | | | ];
            try solve [ contradiction ];
            generalize (AI_complete _ _ _ src_le);
            clear src_le tgt_le; intro src_ideal;
            inversion src_ideal as [ | ? ? src_le tgt_le | | | ];
            try solve [ contradiction ];
            destruct successor;
            try solve
                [ contradiction
                | simpl in src_le;
                  generalize (ST_Arrow_Const _ _ _ _ src_le);
                  intro; contradiction ];
            destruct successor';
            try solve
                [ contradiction
                | simpl in tgt_le;
                  generalize (ST_Arrow_Const _ _ _ _ tgt_le);
                  intro; contradiction
                | simpl in src_le;
                  generalize (ST_Const_Arrow _ _ _ _ src_le);
                  intro; contradiction
                | simpl in tgt_le;
                  generalize (ST_Const_Arrow _ _ _ _ tgt_le);
                  intro; contradiction ].
        - apply (caseS' successors); clear successors; intros successor successors.
          apply (caseS' successors'); clear successors'; intros successor' successors'.
          intro subtypes.  
          apply (IH successors' successors
                    (fun k => succVar (Fin.FS k)) (fun k => succVar' (Fin.FS k))).
          repeat rewrite (nth_map _ _ _ k eq_refl).          
          repeat rewrite (nth_map2 _ _ _ _ _ k eq_refl eq_refl).
          repeat rewrite (nth_map _ _ _ (Fin.FS k) eq_refl) in subtypes.
          repeat rewrite (nth_map2 _ _ _ _ _ (Fin.FS k) eq_refl eq_refl) in subtypes.
          rewrite positions_spec in subtypes.
          rewrite positions_spec.
          simpl in subtypes.
          exact subtypes. }
      apply (NodesOrdered _ _ l l' arity_eq); try solve [ assumption ].
      revert successors_le IH varianceEq.
      clear ...
      generalize (successorVariance l).
      generalize (successorVariance l').
      simpl in arity_eq.
      revert successors.
      simpl.
      rewrite arity_eq.
      clear ...
      unfold eq_rect_r.
      simpl.
      intros successors succVar' succVar subtypes IH varianceEq.
      assert (kth_order:
          forall k,
            match succVar k with
            | Co => VLTreeOrder _ LOrder (nth successors k) (nth successors' k)
            | Contra => VLTreeOrder _ LOrder (nth successors' k) (nth successors k)
            | In => VLTreeOrder _ LOrder (nth successors k) (nth successors' k) /\
                   VLTreeOrder _ LOrder (nth successors' k) (nth successors k)
            end).
      { intro k.
        generalize (Forall2_nth _ _ _ subtypes k).
        clear subtypes.
        repeat rewrite (nth_map _ _ _ k eq_refl).
        repeat rewrite (nth_map2 _ _ _ _ _ k eq_refl eq_refl).
        rewrite <- varianceEq.
        rewrite positions_spec.
        destruct (succVar k).
        - intro subtypes.
          simpl in subtypes.
          apply IH.
          + generalize (Forall_nth _ _ (VLTree_size_lt _ _ l' successors') k).
            generalize (Forall_nth _ _ (VLTree_size_lt _ _ l' successors) k).
            simpl.
            unfold "_ < _".
            repeat rewrite <- Nat.succ_le_mono.
            intros successors_k_lt successors'_k_lt.
            apply (Nat.max_le_compat _ _).
            * apply successors_k_lt.
            * apply successors'_k_lt.
          + generalize (AI_complete _ _ _ subtypes).
            clear subtypes; intro ideal.
            inversion ideal as [ | ? ? src_le tgt_le | | | ]; [ contradiction | ].
            generalize (AI_complete _ _ _ src_le).
            clear src_le; intro src_ideal.
            inversion src_ideal; solve [ contradiction | assumption ].
        - intro subtypes.
          simpl in subtypes.
          apply IH.
          + generalize (Forall_nth _ _ (VLTree_size_lt _ _ l' successors') k).
            generalize (Forall_nth _ _ (VLTree_size_lt _ _ l' successors) k).
            simpl.
            unfold "_ < _".
            repeat rewrite <- Nat.succ_le_mono.
            intros successors_k_lt successors'_k_lt.
            rewrite (Nat.max_comm _ _).
            apply (Nat.max_le_compat _ _).
            * apply successors_k_lt.
            * apply successors'_k_lt.
          + generalize (AI_complete _ _ _ subtypes).
            clear subtypes; intro ideal.
            inversion ideal as [ | ? ? src_le tgt_le | | | ]; [ contradiction | ].
            generalize (AI_complete _ _ _ src_le).
            clear src_le; intro src_ideal.
            clear tgt_le.
            inversion src_ideal as [ ? tgt_omega | ? ? src_le tgt_le | | | ].
            * revert tgt_omega.
              match goal with
              | [ |- Omega (freeze (closedEmbedS ?x)) -> _ ] =>
                destruct x; simpl; intro; contradiction
              end.
            * assumption.
        - intro subtypes.
          simpl in subtypes.
          split; apply IH.
          + generalize (Forall_nth _ _ (VLTree_size_lt _ _ l' successors') k).
            generalize (Forall_nth _ _ (VLTree_size_lt _ _ l' successors) k).
            simpl.
            unfold "_ < _".
            repeat rewrite <- Nat.succ_le_mono.
            intros successors_k_lt successors'_k_lt.
            apply (Nat.max_le_compat _ _).
            * apply successors_k_lt.
            * apply successors'_k_lt.
          + generalize (AI_complete _ _ _ subtypes).
            clear subtypes; intro ideal.
            inversion ideal as [ | ? ? src_le tgt_le | | | ]; [ contradiction | ].
            generalize (AI_complete _ _ _ src_le).
            clear src_le tgt_le; intro src_ideal.
            inversion src_ideal as [ ? tgt_omega | ? ? src_le tgt_le | | | ].
            * revert tgt_omega.
              match goal with
              | [ |- Omega (freeze (closedEmbedS ?x)) -> _ ] =>
                destruct x; simpl; intro; contradiction
              end.
            * assumption.
          + generalize (Forall_nth _ _ (VLTree_size_lt _ _ l' successors') k).
            generalize (Forall_nth _ _ (VLTree_size_lt _ _ l' successors) k).
            simpl.
            unfold "_ < _".
            repeat rewrite <- Nat.succ_le_mono.
            intros successors_k_lt successors'_k_lt.
            rewrite (Nat.max_comm _ _).
            apply (Nat.max_le_compat _ _).
            * apply successors_k_lt.
            * apply successors'_k_lt.
          + generalize (AI_complete _ _ _ subtypes).
            clear subtypes; intro ideal.
            inversion ideal as [ | ? ? src_le tgt_le | | | ]; [ contradiction | ].
            generalize (AI_complete _ _ _ src_le).
            clear src_le; intro src_ideal.
            clear tgt_le.
            inversion src_ideal as [ ? tgt_omega | ? ? src_le tgt_le | | | ].
            * revert tgt_omega.
              match goal with
              | [ |- Omega (freeze (closedEmbedS ?x)) -> _ ] =>
                destruct x; simpl; intro; contradiction
              end.
            * assumption. }
      revert kth_order.
      clear ...
      revert successors succVar.
      induction successors' as [ | successor' n successors' IH' ];
        intros successors succVar kth_order.
      + simpl.
        apply (fun r => case0 (fun xs => VLForestOrder _ _ _ xs _) r successors).
        apply VLForestOrder_empty.
      + revert kth_order.
        apply (caseS' successors); clear successors; intros successor successors.
        intro kth_order.
        generalize (kth_order Fin.F1).
        intro hd_order.
        generalize (IH' successors (fun k => succVar (Fin.FS k)) (fun k => kth_order (Fin.FS k))).
        intro IH.
        simpl.
        rewrite (map_fg _ succVar Fin.FS) in IH.
        destruct (succVar (Fin.F1)).
        * apply VLForestOrder_cons_co; assumption.
        * apply VLForestOrder_cons_contra; assumption.
        * destruct hd_order.
          apply VLForestOrder_cons_in; assumption.
    Qed.

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
      induction s as [ | l successors IH ] using VLTree_rect'.
      - reflexivity.
      - simpl.
        repeat apply f_equal2; try solve [ reflexivity ].
        apply f_equal.
        generalize (ForAll'Forall _ _ IH); clear IH.
        fold closedEmbedS.
        fold openEmbedS.
        generalize (successorVariance l).
        revert successors.
        simpl.
        generalize (labelArity l).
        intros n succsessors succVar IH.
        induction IH as [ | n successor successors prf prfs IH ].
        + reflexivity.
        + simpl.
          apply (f_equal2 (fun x xs => cons _ x _ xs)).
          * destruct (succVar Fin.F1);
              simpl; repeat apply f_equal2; solve [ reflexivity | exact prf ].
          * rewrite <- (map_id successors (fun x => x) (fun x => eq_refl)) at 2.
            rewrite <- (map_id (map (substitute S) successors) (fun x => x) (fun x => eq_refl)).
            rewrite map2_map_fg.
            rewrite map2_map_fg.
            apply (IH (fun k => succVar (Fin.FS k))).
    Qed.

    Lemma unembedApply: forall S tau,
        (exists s, tau = embed s) ->
        (forall alpha, exists s, S alpha = freeze (embed s)) ->
        Apply S tau = freeze (embed (applySubst (unembedSubst S) (unembed tau))).
    Proof.
      intros S tau ex_prf ex_prfS.
      simpl.
      destruct ex_prf as [ s tau_eq ].
      rewrite tau_eq.
      clear tau_eq.
      unfold embed.
      simpl.
      unfold unembedSubst.
      simpl.
      rewrite openInjectivity.
      induction s as [ alpha | l successors IH ] using VLTree_rect'.
      - simpl.
        generalize (embedUnembedClosed).
        destruct (ex_prfS alpha) as [ s subst_eq ].
        rewrite subst_eq.
        rewrite freezeUnfreeze.
        unfold embed.
        unfold unembed.
        simpl.
        intro embedUnembedClosed.
        rewrite (embedUnembedClosed _ (ex_intro _ s eq_refl)).
        reflexivity.
      - simpl.
        repeat apply f_equal2; try solve [ reflexivity ].
        apply f_equal.
        clear ex_prfS.
        generalize (ForAll'Forall _ _ IH).
        clear IH.
        revert successors.
        generalize (successorVariance l).
        simpl.
        generalize (labelArity l).
        intros n succVar successors IH.
        induction IH as [ | n successor successors prf prfs IH ].
        + reflexivity.
        + simpl.
          apply (f_equal2 (fun x xs => cons _ x n xs)).
          * destruct (succVar Fin.F1);
              simpl;
              repeat apply f_equal2; solve [ reflexivity | assumption ].
          * rewrite <- (map_id successors (fun x => x) (fun x => eq_refl)) at 1.
            match goal with
            |[|- _ = map _ (map2 _ ?xs _)] =>
             rewrite <- (map_id xs (fun x => x) (fun x => eq_refl))
            end.
            rewrite map2_map_fg.
            rewrite map2_map_fg.
            apply (IH (fun k => succVar (Fin.FS k))).
    Qed.
  End Proper.
  Instance ProperlyEmbedded: ProperEmbedding :=
    {| EmbedClosed := Proper.ClosedInjectiveEmbedding;
       EmbedOpen := Proper.OpenInjectiveEmbedding;
       embed_respectful := Proper.embed_respectful;
       unembed_respectful := Proper.unembed_respectful;
       embed_Path := Proper.embed_Path;
       embedApply := Proper.embedApply;
       unembedApply := Proper.unembedApply |}.       
End ProperTreeSortEmbedding.
