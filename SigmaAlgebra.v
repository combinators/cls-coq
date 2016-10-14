Require Import Coq.Vectors.Vector.
Require Import VectorQuantification.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.PeanoNat.
Require Import CL.

Import EqNotations.

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

    Definition nth_F_args:
      forall {n : nat} {Var: Set}
        (S : Var -> Sort EmptySet) (argSorts : t (Sort Var) n),
        (forall k, Carrier (applySubst S (nth argSorts k))) ->
        F_args S argSorts.
    Proof.
      intros n Var' S argSorts.
      unfold F_args.
      induction argSorts as [ | ? ? ? IH ].
      - intro; exact tt.
      - intro f.
        split.
        + apply (f (Fin.F1)).
        + apply (IH (fun k => f (Fin.FS k))).
    Defined.

    Definition F_args_nth:
      forall {n : nat} {Var: Set}
        (S : Var -> Sort EmptySet) (argSorts : t (Sort Var) n),
        F_args S argSorts ->
        (forall k, Carrier (applySubst S (nth argSorts k))).
    Proof.
      intros n Var' S argSorts.
      unfold F_args.
      induction argSorts as [ | ? ? ? IH ].
      - intros ? k; inversion k.
      - intros f k.
        apply (Fin.caseS' k).
        + exact (fst f).
        + intro k'; exact (IH (snd f) k').
    Defined.

    Definition F_eq (carrier_eq: forall s s', Carrier s -> Carrier s' -> Prop): forall s, F s -> F s -> Prop :=
      fun s f1 f2 =>
      (op _ f1 = op _ f2) /\
      (fix compare_args n (dom1: t (Sort Var) n) m (dom2: t (Sort Var) m):
         F_args (subst _ f1) dom1 -> F_args (subst _ f2) dom2 -> Prop :=
         match dom1 with
         | cons _ s1 _ ss1 =>
           match dom2 with
           | cons _ s2 _ ss2 =>
             fun fargs1 fargs2 =>
               carrier_eq _ _ (fst fargs1) (fst fargs2) /\ compare_args _ ss1 _ ss2 (snd fargs1) (snd fargs2)
           | nil _ => fun _ _ => False
           end
         | nil _ =>
           match dom2 with
           | nil _ => fun _ _ => True
           | cons _ _ _ _ => fun _ _ => False
           end
         end
      ) _ (domain (op _ f1)) _ (domain (op _ f2)) (args _ f1) (args _ f2).

    Lemma F_eq_refl: forall (carrier_eq: forall s s', Carrier s -> Carrier s' -> Prop),
        (forall s x, carrier_eq s s x x) ->
        forall s x, F_eq carrier_eq s x x.
    Proof.
      intros carrier_eq carrier_eq_refl s x.
      unfold F_eq.
      split.
      - reflexivity.
      - destruct x as [ op arity dom args tgt_le ].
        simpl.
        induction (domain op) as [ | ? ? ? IH ].
        + exact I.
        + split.
          * apply carrier_eq_refl.
          * apply IH.
    Qed.

    Lemma F_eq_sym: forall (carrier_eq: forall s s', Carrier s -> Carrier s' -> Prop),
        (forall s s' x y, carrier_eq s s' x y -> carrier_eq s' s y x) ->
        forall s x y, F_eq carrier_eq s x y -> F_eq carrier_eq s y x.
    Proof.
      intros carrier_eq carrier_eq_sym s x y eq_xy.
      unfold F_eq.
      split.
      - apply eq_sym; exact (proj1 eq_xy).
      - destruct x as [ op xarity dom args tgt_le ].
        destruct y as [ op' yarity dom' args' tgt_le' ].
        simpl.
        unfold F_eq in eq_xy.
        generalize (proj2 eq_xy).
        clear eq_xy.
        simpl.
        clear tgt_le tgt_le'.
        revert args args'.
        generalize (domain op) (domain op').
        generalize (arity op) (arity op').
        clear op op'.
        intros n n' dom1.
        revert n'.
        induction (dom1) as [ | ? ? dom1' IH ];
          intros n' dom2 args1 args2 args_eq.
        + destruct (dom2).
          * exact I.
          * contradiction.
        + destruct (dom2) as [ | ? ? dom2' ].
          * contradiction.
          * split.
            { exact (carrier_eq_sym _ _ _ _ (proj1 args_eq)). }
            { apply (IH dom1' _ dom2' (snd args1) (snd args2) (proj2 args_eq)). }
    Qed.

    Lemma F_eq_trans: forall (carrier_eq: forall s s', Carrier s -> Carrier s' -> Prop),
        (forall s s' s'' x y z, carrier_eq s s' x y -> carrier_eq s' s'' y z -> carrier_eq s s'' x z) ->
        forall s x y z, F_eq carrier_eq s x y -> F_eq carrier_eq s y z -> F_eq carrier_eq s x z.
    Proof.
      intros carrier_eq carrier_eq_trans s x y z eq_xy eq_yz.
      unfold F_eq.
      split.
      - eapply eq_trans; [ exact (proj1 eq_xy) | exact (proj1 eq_yz) ].
      - destruct x as [ op xarity dom args tgt_le ].
        destruct y as [ op' yarity dom' args' tgt_le' ].
        destruct z as [ op'' zarity dom'' args'' tgt_le'' ].
        simpl.
        unfold F_eq in eq_xy.
        unfold F_eq in eq_yz.
        generalize (proj2 eq_xy).
        generalize (proj2 eq_yz).
        clear eq_xy.
        clear eq_yz.
        simpl.
        clear tgt_le tgt_le' tgt_le''.
        revert args args' args''.
        generalize (domain op) (domain op') (domain op'').
        generalize (arity op) (arity op') (arity op'').
        clear op op' op''.
        intros n n' n'' dom1.
        revert n' n''.
        induction (dom1) as [ | ? ? dom1' IH ];
          intros n' n'' dom2 dom3 args1 args2 args3 eq_xy eq_yz.
        + destruct dom3.
          * exact I.
          * destruct dom2; contradiction.
        + destruct (dom3) as [ | ? ? dom3' ].
          * destruct dom2; contradiction.
          * split.
            { destruct dom2.
              - contradiction.
              - destruct eq_xy as [ hd_eq_xy tl_eq_xy ].
                destruct eq_yz as [ hd_eq_yz tl_eq_yz ].
                eapply carrier_eq_trans; eassumption. }
            { destruct dom2.
              - contradiction.
              - destruct eq_xy as [ hd_eq_xy tl_eq_xy ].
                destruct eq_yz as [ hd_eq_yz tl_eq_yz ].
                apply (IH dom1' _ _ _ _ _ _ _ tl_eq_xy tl_eq_yz). }
    Qed.      
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

  Axiom Sort_eq_dec:
    forall (s1 s2: Sort EmptySet), {s1 = s2} + {s1 <> s2}.
  
  Parameter subsorts_dec:
    forall (s1 s2: Sort EmptySet), { subsorts s1 s2 } + { subsorts s1 s2 -> False }.
  
  Axiom SortSubst: `{CanSubst Sort}.
End SignatureSpecification.


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
       (exists s, sigma = freeze (embed s)) -> (exists s, tau = freeze (embed s)) ->
      sigma <= tau -> subsorts (unembed (unfreeze sigma)) (unembed (unfreeze tau)).
  Axiom embed_Path: forall s, Path (freeze (embed s)).
  
  Definition embedSubst: (Signature.Var -> Sort EmptySet) -> (VariableSymbol -> IntersectionType) :=
    fun S alpha => freeze (embed (S alpha)).
  Definition unembedSubst: (VariableSymbol -> IntersectionType) -> (Signature.Var -> Sort EmptySet) :=
    fun S alpha => unembed (unfreeze (S alpha)).

  Axiom embedApply: forall S s, freeze (embed (applySubst S s)) = Apply (embedSubst S) (embed s).
  Axiom unembedApply: forall S tau,
      (exists s, tau = embed s) ->
      Apply S tau = freeze (embed (applySubst (unembedSubst S) (unembed tau))).
  
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

    Lemma Gamma_paths:
      forall (c: CombinatorSymbol) (S: Signature.Var -> Sort EmptySet),
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
End CLAlgebra.