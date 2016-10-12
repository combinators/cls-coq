Require Import Coq.Vectors.Vector.
Require Import Coq.Classes.RelationClasses.

(*
Class Monad (F : Set -> Set): Type :=
  mkMonad { fmap {A B: Set}: (A -> B) -> F A -> F B;
            pure {A: Set}: A -> F A;
            join {A : Set}: F (F A) -> F A;
            fmap_id {A : Set}: forall (x: F A), fmap id x = x;
            fmap_fg {A B C : Set}: forall (f: B -> C) (g: A -> B) (x: F A), fmap (fun x => f (g x)) x = fmap f (fmap g x);
            join_join {A: Set}: forall (x: F (F (F A))), join (join x) = join (fmap join x);
            pure_join {A: Set}: forall (x: F A), join (pure x) = join (fmap pure x) }.
 *)


Class Signature (Sort: Set -> Set) (Var: Set): Type :=
  { Operation: Set;
    arity: Operation -> nat;
    domain: forall o: Operation, t (Sort Var) (arity o);
    range: forall o: Operation, Sort Var
  }.

Definition EmptySet: Set := False.

Class CanSubst (F: Set -> Set): Type :=
  { applySubst: forall {A: Set}, (A -> F EmptySet) -> F A -> F EmptySet }.

Section Algebraic.
  Variable Sort: Set -> Set.
  Variable Var: Set.
  Variable subsorts: Sort EmptySet -> Sort EmptySet -> Prop.
 
  Context `{Sigma: `{Signature Sort Var}, subsorts_pre: `{PreOrder subsorts}, SortSubst: `{CanSubst Sort} }.
  Variable WellFormed: (Var -> Sort EmptySet) -> Prop.
  
  Section WithCarrier.
    Variable Carrier: Sort EmptySet -> Type.
    
    Fixpoint F_args {n : nat} {Var: Set} (S : Var -> Sort EmptySet)
             (argSorts : t (Sort Var) n) {struct argSorts}: Type :=
      match argSorts with
      | nil _ => unit
      | cons _ x _ xs => Carrier (applySubst S x) * F_args S xs
      end.

    Structure F (s : Sort EmptySet): Type :=
      mkF { op: Operation;
            subst: Var -> Sort EmptySet;
            wf_subst: WellFormed subst;
            args: F_args subst (domain op);
            subsort: subsorts (applySubst subst (range op)) s }.
    
    Definition SigmaAlgebra: Type := forall (s: Sort EmptySet), F s -> Carrier s.  
    Definition SigmaCoAlgebra: Type := forall (s: Sort EmptySet), Carrier s -> F s.
  End WithCarrier.
  
  Definition fmap_args
             C C' {Var : Set} (S: Var -> Sort EmptySet) {n} (argSorts: t (Sort Var) n)
             (f: forall s, C s -> C' s):
    F_args C S argSorts -> F_args C' S argSorts :=
    (fix fmap_args_rec n (argSorts: t (Sort Var) n): F_args C S argSorts -> F_args C' S argSorts := 
       match argSorts as argSorts' return
             F_args C S argSorts' -> F_args C' S argSorts'
       with
       | nil _ => fun x => x
       | cons _ x _ xs => fun args => (f (applySubst S x) (fst args), fmap_args_rec _ xs (snd args))
       end) _ argSorts.

  Proposition F_hom C C' (f : forall s, C s -> C' s): forall s, F C s -> F C' s.
  Proof.
    intros s x.
    destruct x.
    eapply mkF.
    - eassumption.
    - eapply fmap_args; eassumption.
    - eassumption.
  Qed.
End Algebraic.

Module Type SignatureSpecification.
  Parameter Sort: Set -> Set.
  Parameter Var: Set.
  Parameter subsorts: Sort EmptySet -> Sort EmptySet -> Prop.
  Parameter Sigma: `{Signature Sort Var}.
  Axiom subsorts_pre: `{PreOrder subsorts}.
  Axiom SortSubst: `{CanSubst Sort}.
End SignatureSpecification.


Require Import CL.
Module Type SignatureSymbolSpecification(Signature: SignatureSpecification) <: SymbolSpecification.
  Parameter ConstructorSymbol: Set.
  Parameter constructorArity: ConstructorSymbol -> nat.
  Parameter ConstructorTaxonomy : ConstructorSymbol -> ConstructorSymbol -> Prop.
  Parameter CTPreorder : PreOrder ConstructorTaxonomy.
  
  Parameter ConstructorSymbol_eq_dec:
    forall (C1 C2: ConstructorSymbol), {C1 = C2} + {C1 <> C2}.
  
  Parameter ConstructorTaxonomy_dec:
    forall (C1 C2: ConstructorSymbol), { ConstructorTaxonomy C1 C2 } + { ConstructorTaxonomy C1 C2 -> False }.

  Definition VariableSymbol: Set := Signature.Var.
  Definition CombinatorSymbol: Set := Operation.
End SignatureSymbolSpecification.

Module Type ProtectedCLSymbols
       (Signature: SignatureSpecification)
       (ContextSymbols: SignatureSymbolSpecification(Signature)) <: SignatureSymbolSpecification(Signature).
  Definition BlackBox := unit.
  Definition blackBox := @inl unit ContextSymbols.ConstructorSymbol tt.
  Definition ConstructorSymbol := (BlackBox + ContextSymbols.ConstructorSymbol)%type.
  Definition constructorArity (symbol: ConstructorSymbol): nat :=
    match symbol with
    | inl _ => 1
    | inr sym => ContextSymbols.constructorArity sym
    end.
  Definition ConstructorTaxonomy (c1 c2 : ConstructorSymbol): Prop :=
    match c1 with
    | inl _ =>
      match c2 with
      | inl _ => True
      | _ => False
      end
    | inr c1' =>
      match c2 with
      | inr c2' => ContextSymbols.ConstructorTaxonomy c1' c2'
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
      + apply ContextSymbols.CTPreorder.
    - unfold Transitive.
      intros x y z ctxy ctyz.
      destruct x;
        destruct y;
        try solve [ inversion ctxy ];
        destruct z;
        try solve [ inversion ctyz ];
        solve [ exact I | eapply ContextSymbols.CTPreorder; eassumption ].
  Qed.
  Definition VariableSymbol: Set := ContextSymbols.VariableSymbol.
  Lemma ConstructorSymbol_eq_dec (c1 c2: ConstructorSymbol): {c1 = c2} + {c1 <> c2}.
  Proof.
    destruct c1 as [ box1 | c1 ]; destruct c2 as [ box2 | c2 ];
      try solve [ right; intro devil; inversion devil ].
    - destruct box1; destruct box2; left; reflexivity.
    - destruct (ContextSymbols.ConstructorSymbol_eq_dec c1 c2).
      + left; apply f_equal; assumption.
      + right; intro devil; inversion devil; contradiction.
  Qed.
  Lemma ConstructorTaxonomy_dec (c1 c2: ConstructorSymbol):
    { ConstructorTaxonomy c1 c2 } + { ConstructorTaxonomy c1 c2 -> False }.
  Proof.
    destruct c1; destruct c2;
      try solve [ left; exact I | right; intro devil; inversion devil ].
    apply ContextSymbols.ConstructorTaxonomy_dec.
  Qed.
  Definition CombinatorSymbol := ContextSymbols.CombinatorSymbol.
End ProtectedCLSymbols.

Module MkCombinatoryLogicForSignature
       (Signature: SignatureSpecification)
       (ContextSymbols: SignatureSymbolSpecification(Signature)).
  Module ProtectedContextSymbols : ProtectedCLSymbols(Signature)(ContextSymbols).
    Include ProtectedCLSymbols(Signature)(ContextSymbols).
  End ProtectedContextSymbols.
  Module Type CLFromSignature <: CombinatoryLogic(ProtectedContextSymbols).
    Export Signature.
    Export ProtectedContextSymbols.
    Include CombinatoryLogic(ProtectedContextSymbols).
  End CLFromSignature.
End MkCombinatoryLogicForSignature.

Module Type SortEmbedding
       (Signature: SignatureSpecification)
       (ContextSymbols: SignatureSymbolSpecification(Signature)).
  Module Mk := MkCombinatoryLogicForSignature(Signature)(ContextSymbols).
  Module CL : Mk.CLFromSignature.
    Include Mk.CLFromSignature.
  End CL.

  Export CL.
  Parameter embed: forall {A: Set}, Sort A -> @TypeScheme A.
  Parameter unembed: forall {A: Set}, @TypeScheme A -> Sort A.
  Axiom unembedEmbed: forall {A: Set} (s: Sort A), unembed (embed s) = s.
  Axiom embedUnembed: forall {A: Set} (ty: @TypeScheme A), (exists s, ty = embed s) -> embed (unembed ty) = ty.
  Axiom embed_respectful: forall (s s': Sort EmptySet), subsorts s s' -> freeze (embed s) <= freeze (embed s').
  Axiom unembed_respectful: forall (sigma tau: IntersectionType),
      sigma <= tau -> subsorts (unembed (unfreeze sigma)) (unembed (unfreeze tau)). 
  
  Definition embedSubst: (Signature.Var -> Sort EmptySet) -> (VariableSymbol -> IntersectionType) :=
    fun S alpha => freeze (embed (S alpha)).
  Definition unembedSubst: (VariableSymbol -> IntersectionType) -> (Signature.Var -> Sort EmptySet) :=
    fun S alpha => unembed (unfreeze (S alpha)).

  Axiom embedApply: forall S s, freeze (embed (applySubst S s)) = Apply (embedSubst S) (embed s).
  Axiom unembedApply: forall S tau,
      (exists s, @unfreeze EmptySet tau = embed s) ->
      unembed (unfreeze (Apply S (unfreeze tau))) = applySubst (unembedSubst S) (unembed (unfreeze tau)).
  
  Lemma unembed_embedSubst: forall S alpha,
      unembedSubst (embedSubst S) alpha = S alpha.
  Proof.
    intros S alpha.
    unfold embedSubst.
    unfold unembedSubst.
    rewrite (freezeUnfreeze).
    rewrite unembedEmbed.
    reflexivity.
  Qed.
  Lemma embed_unembedSubst: forall S alpha,
      (exists s, @unfreeze EmptySet (S alpha) = embed s) ->
      embedSubst (unembedSubst S) alpha = S alpha.
  Proof.
    intros S alpha fromSort.
    unfold embedSubst.
    unfold unembedSubst.
    rewrite (embedUnembed _ fromSort).
    rewrite unfreezeFreeze.
    reflexivity.
  Qed.

  Module Type SignatureSystem <: TypeSystem.
    Include TypeSystem.
  End SignatureSystem.
End SortEmbedding.

Module Type CLAlgebra
       (Signature: SignatureSpecification)
       (ContextSymbols: SignatureSymbolSpecification(Signature))
       (Embedding: SortEmbedding(Signature)(ContextSymbols)).
  Export Embedding.
  
  Module Type Algebra(TypeSystem: SignatureSystem).
    Export TypeSystem.

    Definition blackBoxEmbedOpen (s: Sort VariableSymbol): @TypeScheme VariableSymbol :=
      ConstScheme blackBox (cons _ (embed s) _ (nil _)).

    Definition blackBoxEmbed (s: Sort EmptySet): IntersectionType :=
      freeze (Skeleton (PT_Const blackBox (cons _ (embed s) _ (nil _)))).

    Definition Gamma (c: CombinatorSymbol) :=
      (fix Gamma_rec n dom :=
         match dom with
         | nil _ => blackBoxEmbedOpen (range c)
         | cons _ param _ params =>
           ArrowScheme (blackBoxEmbedOpen param) (Gamma_rec _ params)
         end) _ (domain c).

    Definition CL_Algebra:
      forall (WellFormed : (Signature.Var -> Sort EmptySet) -> Prop),
        (forall S, WellFormed S -> TypeSystem.WellFormed (embedSubst S)) ->
        (forall S, WellFormed S -> forall tau, Path (Apply (embedSubst S) tau)) ->
        SigmaAlgebra Sort Signature.Var subsorts WellFormed
                     (fun s => { M : Term | CL Gamma M (blackBoxEmbed s) }).
    Proof.
      unfold SigmaAlgebra.
      intros WF WF_transport WF_Path s Fs.
      destruct Fs as [ op S WF_S args tgt_le ].
      assert (opty : CL Gamma (Symbol op) (Apply (embedSubst S) (Gamma op))).
      { apply CL_Var.
        apply WF_transport; assumption. }
      assert (source_count_eq : src_count (Apply (embedSubst S) (Gamma op)) = arity op).
      { unfold Gamma.
        clear args.
        generalize (arity op) (domain op).
        intros arity domain.
        induction domain as [ | ? ? ? IH ].
        - reflexivity.
        - simpl.
          rewrite IH.
          reflexivity. }
      assert (args' :
        { Ns: t Term (src_count (Apply (embedSubst S) (Gamma op)))
        | Forall2 (CL Gamma) Ns (fst (split_path (Apply (embedSubst S) (Gamma op))
                                                 (src_count (Apply (embedSubst S) (Gamma op)))
                                                 (le_n _))) }).
      { unfold Gamma.
        unfold Gamma in args.
        revert args.
        generalize (domain op).        
        rewrite <- source_count_eq.
        clear source_count_eq.
        intros domain args.
        induction domain as [ | domain_fst n domain IH ].
        - exists (nil _); apply Forall2_nil.
        - simpl.
          destruct args as [ [term proof] args ].
          destruct (IH args) as [ terms proofs ].
          exists (cons _ term _ terms).
          apply Forall2_cons.
          + unfold blackBoxEmbed in proof.
            simpl freeze in proof.
            rewrite embedApply in proof.
            exact proof.
          + simpl.
            match goal with
            | [ proofs: Forall2 _ _ (fst (split_path _ _ ?prfx))
                |- Forall2 _ _ (fst (split_path _ _ ?prfSx))] =>
              rewrite (split_path_proof_invariant _ _ prfSx prfx)
            end.  
            exact proofs. }
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
      - apply WF_Path; assumption.
      - eassumption.
      - exact (proj2_sig args').
    Defined.
          
    
  End Algebra.
End CLAlgebra.