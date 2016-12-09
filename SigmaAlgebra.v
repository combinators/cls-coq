Require Import Coq.Vectors.Vector.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.PeanoNat.

Require Import VectorQuantification.
Require Import DependentFixpoint.

Import EqNotations.

Class Signature (Sort: Set -> Set) (Var: Set) (Operation: Set): Type :=
  { arity: Operation -> nat;
    domain: forall o: Operation, t (Sort Var) (arity o);
    range: forall o: Operation, Sort Var
  }.

Definition EmptySet: Set := False.

Class CanSubst (F: Set -> Set): Type :=
  { applySubst: forall {A: Set}, (A -> F EmptySet) -> F A -> F EmptySet }.

Class SignatureSpecification (Sort: Set -> Set) (Var: Set) (Operation: Set) :=
  { subsorts: Sort EmptySet -> Sort EmptySet -> Prop;
    Sigma :> Signature Sort Var Operation;
    subsorts_pre :> PreOrder subsorts;

    Var_eq_dec:
      forall (alpha beta: Var), { alpha = beta } + { alpha <> beta };
    
    Sort_eq_dec:
      forall (s1 s2: Sort EmptySet), {s1 = s2} + {s1 <> s2};  
    subsorts_dec:
      forall (s1 s2: Sort EmptySet), { subsorts s1 s2 } + { subsorts s1 s2 -> False };
  
    SortSubst :> CanSubst Sort }.

Module Type SignatureSpec.
  Parameter Sort: Set -> Set.
  Parameter Var: Set.
  Parameter Operation: Set.
  Parameter WellFormed: (Var -> Sort EmptySet) -> Prop.
  
  Declare Instance SigSpec: SignatureSpecification Sort Var Operation.
End SignatureSpec.

Module Type Algebraic(Import SigSpec: SignatureSpec).
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

    Definition F_eq (carrier_eq: forall s s', Carrier s -> Carrier s' -> Prop): forall s s', F s -> F s' -> Prop :=
      fun s s' f1 f2 =>
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
        forall s x, F_eq carrier_eq s s x x.
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
        forall s s' x y, F_eq carrier_eq s s' x y -> F_eq carrier_eq s' s y x.
    Proof.
      intros carrier_eq carrier_eq_sym s s' x y eq_xy.
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
        forall s s' s'' x y z, F_eq carrier_eq s s' x y -> F_eq carrier_eq s' s'' y z -> F_eq carrier_eq s s'' x z.
    Proof.
      intros carrier_eq carrier_eq_trans s s' s'' x y z eq_xy eq_yz.
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

  Definition F_mor C C' (f : forall s, C s -> C' s): forall s, F C s -> F C' s.
  Proof.
    intros s x.
    destruct x.
    eapply mkF.
    - eassumption.
    - eapply fmap_args; eassumption.
    - eassumption.
  Defined.

  Lemma F_mor_eq:
    forall C C' (g : forall s, C s -> C' s)
      (carrier_eq: forall s s', C s -> C s' -> Prop)
      (carrier'_eq: forall s s', C' s -> C' s' -> Prop)
      (g_compat: forall s s' (c: C s) (c': C s'), carrier_eq s s' c c' -> carrier'_eq s s' (g s c) (g s' c'))
      s s' f f',
      F_eq _ carrier_eq s s' f f' -> F_eq _ carrier'_eq s s' (F_mor C C' g s f) (F_mor C C' g s' f').
  Proof.
    intros C C' g carrier_eq carrier'_eq g_compat s s' f.
    destruct f as [ op S WF_S args subsorts ].
    destruct f' as [ op' S' WF_S' args' subsorts' ].
    unfold F_mor.
    unfold F_eq.
    simpl.
    intro eq.
    destruct eq as [ op_eq args_eq ].
    split.
    - exact op_eq.
    - revert g_compat args args' args_eq.
      clear subsorts subsorts'.
      rewrite <- op_eq.
      clear ...
      intro g_compat.
      generalize (domain op).
      generalize (arity op).
      intros n params.
      induction params as [ | param n params IH ];
        intros args args' args_eq.
      + trivial.
      + split;
          [ apply g_compat; exact (proj1 args_eq) | apply IH; exact (proj2 args_eq) ].
  Qed.     
    
  Section AlgebraFixpoint.
    Variable C: Sort EmptySet -> Type.
    Variable C': Sort EmptySet -> Type.
    Variable coAlg: SigmaCoAlgebra C.
    Variable alg: SigmaAlgebra C'.
    
    Variable A: Type.
    Variable R: A -> A -> Prop.
    Hypothesis R_wf: well_founded R.

    Variable measure: forall s, C s -> A.

    Fixpoint argsDec s (c: C s) S {n: nat}
             (params: t (Sort SigSpec.Var) n) (args: F_args C S params) {struct params}: Prop :=
      match params as params' return (F_args C S params' -> Prop) with
      | nil _ => fun _ => True
      | cons _ p _ ps =>
        fun args =>
          R (measure _ (fst args)) (measure s c) /\ argsDec s c S ps (snd args)
      end args.

    Hypothesis coAlg_decreasing:
      forall s (c: C s),
        argsDec s c (subst _ _ (coAlg s c)) (domain (op _ _ (coAlg s c))) (args _ _ (coAlg s c)).

    Fixpoint fmap_args_dec
               (S: SigSpec.Var -> Sort EmptySet) {n} (params: t (Sort SigSpec.Var) n)
               s (c: C s)
               (f: forall s' (c': C s'), R (measure s' c') (measure s c) -> C' s')
               (args: F_args C S params)
               (dec: argsDec s c S params args) {struct params}: F_args C' S params :=
      match params as params'
            return (forall (args: F_args C S params'), argsDec s c S params' args -> F_args C' S params') with
      | nil _ => fun _ _ => tt
      | cons _ p _ ps =>
        fun args dec => (f _ (fst args) (proj1 dec), fmap_args_dec S ps s c f (snd args) (proj2 dec))
      end args dec.
        
    Definition canonical_morphism: forall s, C s -> C' s.
    Proof.
      intros s c.
      apply (fun r => DepFix A R R_wf (Sort EmptySet) C (fun s _ => C' s) measure r s c).
      clear s c.
      intros s c morphism_rec.
      apply alg.
      apply (mkF _ _ (op _ _ (coAlg s c)) (subst _ _ (coAlg s c))
                 (wf_subst _ _ (coAlg s c))
                 (fmap_args_dec (subst _ _ (coAlg s c)) (domain (op _ _ (coAlg s c)))
                                s c morphism_rec (args _ _ (coAlg s c)) (coAlg_decreasing s c))
                 (subsort _ _ (coAlg s c))).
    Defined.

    Lemma canonical_morphism_commutes:
      forall s (c: C s), canonical_morphism s c = alg s (F_mor C C' canonical_morphism s (coAlg s c)).
    Proof.
      intros s c.
      unfold canonical_morphism.
      unfold DepFix.
      unfold Fix_F.
      unfold F_mor.
      destruct (R_wf (measure s c)) as [ prf' ].
      apply f_equal.
      generalize (coAlg_decreasing s c).
      destruct (coAlg s c) as [ op S WF_s args subsorts ].
      intro decprf.
      simpl.
      match goal with
      |[|- {| op := _; subst := _; wf_subst := _; args := ?args1; subsort := _ |} =
          {| op := _; subst := _; wf_subst := _; args := ?args2; subsort := _ |} ] =>
       assert (args_eq: args1 = args2); [ | rewrite args_eq; reflexivity ]
      end.
      revert decprf.
      simpl.
      revert args.
      generalize (domain op).
      intro dom.
      induction dom as [ | param n params IH ];
        intros args decprf.
      - simpl.
        destruct args.
        reflexivity.
      - simpl.
        rewrite (IH (snd args) (proj2 decprf)).
        match goal with
        |[|- (?x, _) = (?y, _)] =>
         assert (fst_eq: x = y); [ | rewrite fst_eq; reflexivity ]
        end.
        set (inner_fix:=
               Fix_F A R _ C (fun s _ => C' s) measure
                     (fun t x rec =>
                        alg t
                            {| op := Algebraic.op C t (coAlg t x);
                               subst := subst C t (coAlg t x);
                               wf_subst := wf_subst C t (coAlg t x);
                               args := fmap_args_dec (subst C t (coAlg t x))
                                                     (domain (Algebraic.op C t (coAlg t x))) t x
                                                     (fun (t' : Sort EmptySet) (y : C t')
                                                        (h : R (measure t' y) (measure t x)) =>
                                                        rec t' y h)
                                                     (Algebraic.args C t (coAlg t x))
                                                     (coAlg_decreasing t x);
                               subsort := subsort C t (coAlg t x) |})).
        match goal with
        | [|- _ ?p1 ?arg1 ?dec1 = _ ?p2 ?arg2 ?dec2 ] =>
          assert (fix_eq: inner_fix p1 arg1 dec1 = inner_fix p2 arg2 dec2);
            [ apply (fun r => Fix_F_inv A R _ C (fun s _ => C' s) measure
                                     _ r p1 arg1 dec1 dec2)
            | exact fix_eq ]
        end.
        clear ...
        intros s c g g' gg'_eq.
        apply f_equal.
        match goal with
        |[|- {| op := _; subst := _; wf_subst := _; args := ?args1; subsort := _ |} =
            {| op := _; subst := _; wf_subst := _; args := ?args2; subsort := _ |} ] =>
         assert (args_eq: args1 = args2); [ | rewrite args_eq; reflexivity ]
        end.
        generalize (coAlg_decreasing s c).
        destruct (coAlg s c) as [ op S WF_S args subsorts ].
        simpl.
        revert args.
        generalize (domain op).
        generalize (arity op).
        intros n dom.
        induction dom as [ | param n params IH ]; intros args dec.
        + reflexivity.
        + simpl.
          rewrite gg'_eq.
          rewrite (IH (snd args) (proj2 dec)).
          reflexivity.
    Qed.
    
    Section HomomorphismModulo.
      Variable alg': SigmaAlgebra C.
      
      Variable C_eq: forall s s', C s -> C s' -> Prop.
      Variable C'_eq: forall s s', C' s -> C' s' -> Prop.
      Hypothesis C_eq_refl: forall s c, C_eq s s c c.
      Hypothesis C_eq_trans: forall s s' s'' x y z, C_eq s s' x y -> C_eq s' s'' y z -> C_eq s s'' x z.
      Hypothesis C'_eq_trans: forall s s' s'' x y z, C'_eq s s' x y -> C'_eq s' s'' y z -> C'_eq s s'' x z.

      Hypothesis alg'_compat: forall s s' f f', F_eq C C_eq s s' f f' -> C_eq s s' (alg' s f) (alg' s' f').
      Hypothesis alg_compat: forall s s' f f', F_eq C' C'_eq s s' f f' -> C'_eq s s' (alg s f) (alg s' f').

      Hypothesis coAlg_compat: forall s s' c c', C_eq s s' c c' -> F_eq C C_eq s s' (coAlg s c) (coAlg s' c').

      Hypothesis alg_coAlg_inv: forall s c, C_eq s s c (alg' s (coAlg s c)).
      Hypothesis coAlg_alg_inv: forall s f, F_eq C C_eq s s (coAlg s (alg' s f)) f.

      Lemma canonical_morphism_C_eq_compat:
        forall s s' c c', C_eq s s' c c' -> C'_eq s s' (canonical_morphism s c) (canonical_morphism s' c').
      Proof.
        intros s s' c c'.
        unfold canonical_morphism.
        unfold DepFix.
        generalize (R_wf (measure s' c')).
        revert s' c'.        
        generalize (R_wf (measure s c)).        
        match goal with
        |[|- forall acc s' c' acc',
             _ -> C'_eq s s' (?f_rec s c acc) (?g_rec s' c' acc')] =>
         apply (fun r =>
                  Fix_F A R (Sort EmptySet) C
                        (fun s c => forall acc s' c' acc',
                             C_eq s s' c c' -> C'_eq s s' (f_rec s c acc) (g_rec s' c' acc'))
                        measure r s c (R_wf (measure s c)))
        end.
        clear s c.
        intros s c rec acc s' c' acc' eq.
        destruct acc.
        destruct acc'.
        simpl.
        apply alg_compat.
        generalize (coAlg_compat s s' c c' eq).
        intros [ op_eq args_eq ].
        split.
        - exact op_eq.
        - generalize (coAlg_decreasing s' c').
          generalize (coAlg_decreasing s c).
          destruct (coAlg s c) as [ op S WF_S args subsorts ].
          destruct (coAlg s' c') as [ op' S' WF_S' args' subsorts' ].
          simpl in op_eq.
          revert args args' args_eq.
          simpl.
          clear WF_S WF_S' subsorts subsorts'.
          rewrite <- op_eq; clear op_eq op' eq.
          generalize (arity op) (domain op).
          intros n params.
          induction params as [ | param n params IH ].
          + intros; trivial.
          + intros args args' [ eq args_eq ] accs accs'.
            split.
            * simpl.
              apply rec; [ exact (proj1 accs) | exact eq ].              
            * exact (IH (snd args) (snd args') args_eq (proj2 accs) (proj2 accs')).
      Qed.

      Lemma canonical_morphism_alg_mor:
        forall s s' f f',
          F_eq C C_eq s s' f f' ->
          C'_eq s s' (canonical_morphism s (alg' s f)) (alg s' (F_mor C C' canonical_morphism s' f')).
      Proof.
        intros s s' f f' eq.
        rewrite canonical_morphism_commutes.
        apply alg_compat.
        apply (F_mor_eq _ _ canonical_morphism C_eq C'_eq canonical_morphism_C_eq_compat).
        apply (F_eq_trans C C_eq C_eq_trans s s s' _ f _).
        - apply coAlg_alg_inv.
        - exact eq.
      Qed.

      Lemma canonical_morphism_unique:
        forall (morphism: forall s, C s -> C' s)
          (morphism_compat:
             forall s s' c c', C_eq s s' c c' -> C'_eq s s' (morphism s c) (morphism s' c'))
          (morphism_alg_homo:
             forall s s' f f',
               F_eq C C_eq s s' f f' ->
               C'_eq s s' (morphism s (alg' s f)) (alg s' (F_mor C C' morphism s' f')))
          s c,
          C'_eq s s (morphism s c) (canonical_morphism s c).
      Proof.
        intros morphism morphism_compat morphism_alg_homo s c.
        unfold canonical_morphism.
        unfold DepFix.
        generalize (R_wf (measure s c)).
        match goal with
        |[|- forall acc, C'_eq s s (morphism s c) (?f_rec s c acc) ] =>
         apply (fun r => Fix_F A R _ C
                            (fun s c => forall acc, C'_eq s s (morphism s c) (f_rec s c acc))
                            measure r s c (R_wf (measure s c)))
        end.
        clear s c; intros s c canonical_morphism_unique acc.
        apply (C'_eq_trans s s s _ (morphism s (alg' s (coAlg s c)))).
        - apply morphism_compat.
          apply alg_coAlg_inv.
        - apply (C'_eq_trans s s s _ (alg s (F_mor C C' morphism s (coAlg s c)))).
          + apply morphism_alg_homo.
            apply F_eq_refl.
            apply C_eq_refl.
          + destruct acc.
            apply alg_compat.
            unfold F_mor.
            generalize (coAlg_decreasing s c).
            intro accs.
            destruct (coAlg s c) as [ op S WF_S args subsorts ].
            split; simpl; [ reflexivity | ].
            revert args accs.
            simpl.
            clear subsorts WF_S.            
            generalize (arity op) (domain op).
            intros n params.
            induction params as [ | param n params IH ].
            * intros; trivial.
            * intros args accs.
              split.
              { simpl.
                apply canonical_morphism_unique.
                exact (proj1 accs). }
              { exact (IH (snd args) (proj2 accs)). }
      Qed.
      
    End HomomorphismModulo.
    
  End AlgebraFixpoint.

    
End Algebraic.

