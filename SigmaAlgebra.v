Require Import Coq.Vectors.Vector.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Wf_nat.

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

  Inductive FixF (s : Sort EmptySet): Type :=
  | mkFixF : forall (op: Operation)
               (subst: Var -> Sort EmptySet)
               (wf_subst: WellFormed subst)
               (args: FixF_args s subst _ (domain op))
               (subsort: subsorts (applySubst subst (range op)) s), FixF s        
  with
  FixF_args (s: Sort EmptySet): forall (S : Var -> Sort EmptySet) (n : nat) (argSorts: t (Sort Var) n), Type :=
  | FixF_args_nil : forall S, FixF_args s S 0 (nil _)
  | FixF_args_cons : forall S n argSort argSorts,
      FixF (applySubst S argSort) -> FixF_args s S n argSorts -> FixF_args s S _ (cons _ argSort _ argSorts).

  Definition FixF_args_case0 s S
             (P : forall S n (argSorts: t (Sort Var) n), FixF_args s S n argSorts -> Type)
             (argSorts: t (Sort Var) 0)
             (args: FixF_args s S 0 argSorts): P S 0 (nil _) (FixF_args_nil s S) -> P S 0 argSorts args :=
    (fun n argSorts (args: FixF_args s S n argSorts) =>
       match args as args' in FixF_args _ S' n argSorts'
             return n = 0 -> P S' 0 (nil _) (FixF_args_nil s S') -> P S' n argSorts' args' with
       | FixF_args_nil _ _ => fun _ r => r
       | FixF_args_cons _ _ _ _ _ _ _ =>
         fun eq _ => False_rect _ (@eq_rect_r nat 0 (fun n => match n with | 0 => True | _ => False end) I _ eq)
       end) 0 argSorts args eq_refl.

  Definition FixF_args_caseS' s S n
             (argSorts: t (Sort Var) (Datatypes.S n))
             (args: FixF_args s S (Datatypes.S n) argSorts):
    forall (P : forall S (argSorts: t (Sort Var) (Datatypes.S n)), FixF_args s S (Datatypes.S n) argSorts -> Type),
      (forall S argSort argSorts' arg args',
          P S (cons _ argSort _ argSorts') (FixF_args_cons s S n argSort argSorts' arg args')) ->
      P S argSorts args :=
    match args with
    | FixF_args_nil _ _ => fun devil => False_rect (@IDProp) devil
    | FixF_args_cons _ _ _ _ _ hd tl => fun P H => H _ _ _ hd tl
    end.
    
  Fixpoint FixF_args_to_F_args
           (s: Sort EmptySet) (S: Var -> Sort EmptySet) (n: nat) (argSorts: t (Sort Var) n)
           (args: FixF_args s S n argSorts) {struct args}: F_args FixF S argSorts :=
    match args with
    | FixF_args_nil _ _ => tt
    | FixF_args_cons _ _ n argSort argSorts hd tl => (hd, FixF_args_to_F_args s _ n argSorts tl)
    end.

  Fixpoint F_args_to_FixF_args
           (s: Sort EmptySet) (S: Var -> Sort EmptySet) (n: nat) (argSorts: t (Sort Var) n)
           (args: F_args FixF S argSorts) {struct argSorts}: FixF_args s S n argSorts :=
    match argSorts as argSorts' return F_args FixF S argSorts' -> FixF_args s S _ argSorts' with
    | nil _ => fun _ => FixF_args_nil s S
    | cons _ x _ xs => fun args => FixF_args_cons _ _ _ _ _ (fst args) (F_args_to_FixF_args s _ _ xs (snd args))
    end args.
  
  Definition FixF_alg: forall s, F FixF s -> FixF s :=
    fun s f => mkFixF s (op _ _ f) (subst _ _ f) (wf_subst _ _ f)
                   (F_args_to_FixF_args _ _ _ _ (args _ _ f)) (subsort _ _ f).

  Definition FixF_coalg: forall s, FixF s -> F FixF s :=
    fun s f =>
      match f with
      | mkFixF _ op subst wf_subst args subsort =>
        mkF _ _ op subst wf_subst (FixF_args_to_F_args _ _ _ _ args) subsort
      end.
  
  Lemma FixF_alg_coalg: forall s f, FixF_coalg s (FixF_alg s f) = f.
  Proof.
    intros s f.
    destruct f as [ op subst wf_subst args subsort ].
    simpl.
    assert (args_eq: forall s S n argSorts args,
               FixF_args_to_F_args s S n argSorts (F_args_to_FixF_args s S n argSorts args) = args).
    { clear ...
      intros s S n argSorts.
      induction argSorts as [ | argSort n argSorts IH ].
      - intro args.
        destruct args; reflexivity.
      - intro args.
        destruct args as [ arg args ].
        simpl.
        rewrite (IH args).
        reflexivity. }
    rewrite args_eq.
    reflexivity.
  Qed.

  Lemma FixF_coalg_alg: forall s c, FixF_alg s (FixF_coalg s c) = c.
  Proof.
    intros s c.
    destruct c as [ op subst wf_subst args subsort ].
    unfold FixF_alg.
    simpl.
    assert (args_eq: forall s S n argSorts args,
               F_args_to_FixF_args s S n argSorts (FixF_args_to_F_args s S n argSorts args) = args).
    { clear ...
      intros s S n argSorts args.
      induction args as [ | ? ? ? ? ? ? ? IH ].
      - reflexivity.
      - simpl.
        rewrite IH.
        reflexivity. }        
    rewrite args_eq.
    reflexivity.
  Qed.

 
  Fixpoint FixF_size s (f: FixF s): nat :=
    match f with
    | mkFixF _ _ _ _ args _ =>
      1 + ((fix FixF_args_size s S n argSorts (args : FixF_args s S n argSorts): nat :=
              match args with
              | FixF_args_nil _ _ => 0
              | FixF_args_cons _ _ _ _ _ arg args => (FixF_size _ arg) + (FixF_args_size _ _ _ _ args)
              end) _ _ _ _ args)
    end.
    
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
      
      Inductive AlgebraicallyGenerated: forall s, C' s -> Prop :=
      | FromF : forall s op S WF_S args subsort,
          GeneratedArgs (arity op) (domain op) S args ->
          AlgebraicallyGenerated s (alg s (mkF C' s op S WF_S args subsort))
      with GeneratedArgs: forall n (dom : t (Sort Var) n) S, F_args C' S dom -> Prop :=
           | GeneratedArgs_nil: forall S, GeneratedArgs 0 (nil _) S tt
           | GeneratedArgs_cons:
               forall n s dom' S arg args,
                 AlgebraicallyGenerated (applySubst S s) arg ->
                 GeneratedArgs n dom' S args ->
                 GeneratedArgs _ (cons _ s n dom') S (arg, args).

      Fixpoint GeneratedArgs_nth n dom S args k (args_gen: GeneratedArgs n dom S args):
        AlgebraicallyGenerated (applySubst S (nth dom k)) (F_args_nth _ S dom args k).
      Proof.
        revert k.
        case args_gen.
        - intros S' k; inversion k.
        - intros n' s dom' S' arg args' arg_gen args_gen' k.
          apply (Fin.caseS' k).
          + exact arg_gen.
          + intro k'.
            exact (GeneratedArgs_nth n' dom' S' args' k' args_gen').
      Defined.
      
      Fixpoint AlgebraicallyGenerated_ind'
               (P : forall s c, AlgebraicallyGenerated s c -> Prop)
               (case_nth:
                  forall (s: Sort EmptySet) op (S: Var -> Sort EmptySet) (WF_S: WellFormed S)
                    args (subsort: subsorts (applySubst S (range op)) s)
                    (args_gen : GeneratedArgs (arity op) (domain op) S args),
                    (forall k, P _ (F_args_nth _ S _ args k) (GeneratedArgs_nth _ _ S args k args_gen)) ->
                    P s _ (FromF s op S WF_S args subsort args_gen)
               )
               s c gen {struct gen}: P s c gen.
      Proof.
        case gen as [ s op S WF_S args subsort args_gen ].
        apply case_nth.
        intro k.
        apply
          ((fix rec_args S n dom args args_gen :
              forall (k: Fin.t n), P (applySubst S (nth dom k))
                                (F_args_nth C' S dom args k)
                                (GeneratedArgs_nth n  dom S args k args_gen) :=
              match args_gen as args_gen' in GeneratedArgs n' dom' S' args' return
                    forall (k: Fin.t n'), P (applySubst S' (nth dom' k))
                                       (F_args_nth C' S' dom' args' k)
                                       (GeneratedArgs_nth n' dom' S' args' k args_gen')
              with
              | GeneratedArgs_nil _ => Fin.case0 _
              | GeneratedArgs_cons n s dom subst arg args arg_gen args_gen =>
                fun (k: Fin.t (Datatypes.S n)) =>
                  Fin.caseS' k (fun k => P (applySubst subst (nth (cons _ s n dom) k))
                                        (F_args_nth C' subst (cons _ s n dom) (arg, args) k)
                                        (GeneratedArgs_nth (Datatypes.S n) (cons _ s n dom) subst (arg, args) k
                                                           (GeneratedArgs_cons n s dom subst arg args arg_gen args_gen)))
                             (AlgebraicallyGenerated_ind' P case_nth _ _ arg_gen)
                             (fun k => rec_args subst n dom args args_gen k)
              end) S (arity op) (domain op) args args_gen k).
      Qed.

      Definition GeneratedArgs_hd n s dom S args (args_gen: GeneratedArgs (Datatypes.S n) (cons _ s n dom) S args):
        AlgebraicallyGenerated (applySubst S s) (fst args) :=
        GeneratedArgs_nth (Datatypes.S n) (cons _ s n dom) S args Fin.F1 args_gen.

      Definition GeneratedArgs_caseS n dom S args (args_gen: GeneratedArgs (Datatypes.S n) dom S args):
        forall (P : forall n (dom: t (Sort Var) n) (S: (Var -> Sort EmptySet)) (args: F_args C' S dom), GeneratedArgs _ dom S args -> Prop),
          (forall n s (dom : t (Sort Var) n) S arg args
             (arg_gen : AlgebraicallyGenerated (applySubst S s) arg)
             (args_gen : GeneratedArgs n dom S args),
              P (Datatypes.S n) (cons _ s n dom) S (arg, args) (GeneratedArgs_cons n s dom S arg args arg_gen args_gen)) ->
          P (Datatypes.S n) dom S args args_gen := 
        fun P cons_case =>
          match args_gen as args_gen' in GeneratedArgs n' dom' S' args' return
                (n' = Datatypes.S n) -> P n' dom' S' args' args_gen'
          with
          | GeneratedArgs_nil S' =>
            fun eq => False_ind (P 0 (nil _) S' tt (GeneratedArgs_nil S'))
                             (@eq_ind_r nat (Datatypes.S n)
                                        (fun x => match x with | Datatypes.S _ => True | _ => False end)
                                        I _ eq)
          | GeneratedArgs_cons n s dom S' arg args arg_gen args_gen =>
            fun eq => cons_case n s dom S' arg args arg_gen args_gen
          end (eq_refl (Datatypes.S n)).
      
      Definition GeneratedArgs_tl n s dom S args (args_gen: GeneratedArgs (Datatypes.S n) (cons _ s n dom) S args):
        GeneratedArgs n dom S (snd args) :=
        GeneratedArgs_caseS n (cons _ s n dom) S args args_gen
                            (fun n' dom' S' args' =>
                               match dom' with
                               | nil _ => fun _ _ => GeneratedArgs n dom S (snd args)
                               | cons _ s n dom => fun (args': F_args C' S' (cons _ s n dom)) gen_args' => GeneratedArgs n dom S' (snd args')
                               end args')
                            (fun n s dom S arg args arg_gen args_gen => args_gen).

      Lemma cannonical_morphism_sound: forall s c, AlgebraicallyGenerated s (canonical_morphism s c).
      Proof.
        intros s c.
        apply (fun r => Fix_F A R _ C
                           (fun s c => AlgebraicallyGenerated s (canonical_morphism s c))
                           measure r s c (R_wf (measure s c))).
        clear s c.
        intros s c IH.
        rewrite canonical_morphism_commutes.
        unfold F_mor.
        generalize (coAlg_decreasing s c).
        destruct (coAlg s c) as [ op S WF_S args subsort ].
        simpl.
        intro args_dec.
        apply (FromF s op S WF_S (fmap_args C C' S (domain op) canonical_morphism args) subsort).
        revert args args_dec.
        generalize (domain op).
        generalize (arity op).
        intros n dom.
        induction dom as [ | s' n dom IH' ].
        - intros args agrs_dec.
          simpl.
          destruct args.
          apply GeneratedArgs_nil.
        - intros args args_dec.
          destruct args as [ arg args ].
          apply GeneratedArgs_cons.
          + apply IH.
            exact (proj1 args_dec).
          + exact (IH' args (proj2 args_dec)).
      Qed.
      
      Lemma canonical_morphism_complete:
        forall s c (C_eq_sym: forall s s' c c', C_eq s s' c c' -> C_eq s' s c' c),
          AlgebraicallyGenerated s c ->
          exists c', C'_eq s s c (canonical_morphism s c').
      Proof.
        intros s c C_eq_sym c_gen.
        induction c_gen as [ s op S WF_S args subsort args_gen IH ] using AlgebraicallyGenerated_ind'.
        assert (f_complete: exists f, F_eq C' C'_eq s s (mkF C' s op S WF_S args subsort) (F_mor C C' canonical_morphism s f)).
        { unfold F_eq.
          unfold F_mor.
          simpl.
          assert (f_args: exists f_args, forall k, C'_eq (applySubst S (nth (domain op) k))
                                               (applySubst S (nth (domain op) k))
                                               (F_args_nth C' S (domain op) args k)
                                               (canonical_morphism (applySubst S (nth (domain op) k))
                                                                   (F_args_nth C S (domain op) f_args k))).
          { revert args args_gen IH.
            generalize (domain op).
            generalize (arity op).
            intros n dom args args_gen IH.
            induction dom as [ | s' n dom IH' ].
            - exists tt; apply (Fin.case0).
            - destruct args as [ arg args ].
              destruct (IH (Fin.F1)) as [ f_arg1 f_arg1_prf ].
              destruct (IH' args (GeneratedArgs_tl _ _ _ _ _ args_gen) (fun k => IH (Fin.FS k))) as [ f_args f_args_prfs ].
              exists (f_arg1, f_args).
              intro k.
              apply (Fin.caseS' k); assumption. }
          destruct f_args as [ f_args f_args_prf ].
          exists (mkF C s op S WF_S f_args subsort).
          split.
          - reflexivity.
          - clear args_gen IH.
            revert args f_args f_args_prf.
            simpl.
            generalize (domain op).
            generalize (arity op).
            intros n dom.
            induction dom as [ | s' n dom IH ].
            + intros; trivial.
            + intros args f_args f_args_prf.
              split.
              * exact (f_args_prf (Fin.F1)).
              * exact (IH (snd args) (snd f_args) (fun k => f_args_prf (Fin.FS k))). }
        destruct f_complete as [ f f_prf ].
        exists (alg' s f).
        rewrite canonical_morphism_commutes.
        apply alg_compat.
        eapply (F_eq_trans _ C'_eq C'_eq_trans s s s _ _ _ f_prf).
        apply (F_mor_eq _ _ canonical_morphism C_eq C'_eq canonical_morphism_C_eq_compat).
        apply (F_eq_sym _ C_eq C_eq_sym).
        apply (coAlg_alg_inv).
      Qed.      
    End HomomorphismModulo.
    
  End AlgebraFixpoint.

  Lemma initial_coalg_nth_arg_decreasing:
    forall s c n,
      FixF_size _ (F_args_nth FixF (subst _ _ (FixF_coalg s c)) _ (args _ _ (FixF_coalg s c)) n) <
      FixF_size s c.
  Proof.
    intros s c.
    destruct c as [ op subst subst_wf args subsort ].
    revert args.
    simpl.
    generalize (domain op).
    generalize (arity op).
    intros arity argSorts args.
    induction args as [ | s S arity argSort argSorts arg args IH ]; intro n.
    - inversion n.
    - apply (Fin.caseS' n).
      + simpl.
        unfold "_ < _".
        rewrite <- Nat.succ_le_mono.
        apply Nat.le_add_r.
      + intro n'.
        simpl.
        etransitivity; [ eapply IH; assumption | ].
        rewrite <- Nat.succ_lt_mono.
        apply Nat.lt_add_pos_l.
        unfold FixF_size.
        destruct arg.
        unfold "_ < _".
        apply Nat.le_add_r.
  Qed.       
    
  
  Lemma initial_coalg_decreasing:
      forall s (c: FixF s),
        argsDec FixF nat lt FixF_size s c
                (subst _ _ (FixF_coalg s c)) (domain (op _ _ (FixF_coalg s c))) (args _ _ (FixF_coalg s c)).
  Proof.
    intros s c.
    generalize (initial_coalg_nth_arg_decreasing s c).
    destruct (FixF_coalg s c) as [ op subst subst_wf args subsort ].
    simpl.
    revert args.
    generalize (domain op).
    generalize (arity op).
    intros arity dom.
    induction dom as [ | argSort n argSorts IH ];
      intros args dec_prf.
    - simpl; trivial.
    - split.
      + exact (dec_prf Fin.F1).
      + apply IH.
        exact (fun k => dec_prf (Fin.FS k)).
  Qed.      
  
  Definition initial_algebra_morphism (C: Sort EmptySet -> Type) (alg: SigmaAlgebra C): forall s, FixF s -> C s :=
    canonical_morphism FixF C FixF_coalg alg
                       nat _ (well_founded_ltof _ (fun x => x))
                       FixF_size initial_coalg_decreasing.

  Definition FixF_args_hd s S n argSort argSorts (args: FixF_args s S _ (cons _ argSort n argSorts)):
    FixF (applySubst S argSort) :=
    match args in FixF_args _ S' n' argSorts' return
          (n' = Datatypes.S n) ->
          match argSorts' with
          | nil _ => FixF (applySubst S argSort)
          | cons _ argSort _ _ => FixF (applySubst S' argSort)
          end with
    | FixF_args_nil _ _ =>
      fun eq =>
        False_rect _ (@eq_rect_r nat (Datatypes.S n)
                                 (fun x => match x with | Datatypes.S _ => True | _ => False end)
                                 I _ eq)
    | FixF_args_cons _ _ _ _ _ hd _ => fun eq => hd
    end eq_refl.

  Definition FixF_args_tl s S n argSort argSorts (args: FixF_args s S _ (cons _ argSort n argSorts)):
    FixF_args s S n argSorts :=
    match args in FixF_args _ S' n' argSorts' return
          (n' = Datatypes.S n) ->
          match argSorts' with
          | nil _ => FixF_args s S n argSorts
          | cons _ _ _ argSorts' => FixF_args s S' _ argSorts'
          end with
    | FixF_args_nil _ _ =>
      fun eq =>
        False_rect _ (@eq_rect_r nat (Datatypes.S n)
                                 (fun x => match x with | Datatypes.S _ => True | _ => False end)
                                 I _ eq)
    | FixF_args_cons _ _ _ _ _ _ tl => fun eq => tl
    end eq_refl.

  Fixpoint FixF_eq s s' (c: FixF s) {struct c}: FixF s' -> Prop :=
    fun c' =>
      match c with
      | mkFixF _ op subst wf_subst args subsort =>
        match c' with
        | mkFixF _ op' subst' wf_subst' args' subsort' =>
          (op = op') /\
          ((fix compare_args S S' n (dom1: t (Sort Var) n) m (dom2: t (Sort Var) m) 
              (args1: FixF_args s S n dom1) (args2: FixF_args s' S' m dom2) {struct args1}: Prop :=
              match args1 with
              | FixF_args_cons _ _ _ _ _ hd1 tl1 =>
                match args2 with
                | FixF_args_cons _ _ _ _ _ hd2 tl2 =>
                  (FixF_eq _ _ hd1 hd2) /\ (compare_args _ _ _ _ _ _ tl1 tl2)
                | _ => False
                end
              | FixF_args_nil _ _ =>
                match args2 with
                | FixF_args_nil _ _ => True
                | _ => False
                end
              end
           ) subst subst' _ (domain op) _ (domain op') args args')
        end
      end.

  Lemma FixF_eq_refl: forall s (c: FixF s), FixF_eq s s c c.
  Proof.
    intros s c.
    apply (fun r => DepFix nat lt (well_founded_ltof _ (fun x => x)) (Sort EmptySet) FixF (fun s c => FixF_eq s s c c)
                        (FixF_size) r s c).
    clear s c.
    intros s c IH.
    destruct c as [ op subst wf_subst args subsort ].
    simpl in IH.
    split; [ reflexivity | ].
    revert args IH.
    generalize (domain op).
    generalize (arity op).
    intros arity dom args.
    induction args as [ | s S n argSort argSorts hd tl IH' ].
    - intros; trivial.
    - intro IH.
      split.
      + apply IH.
        unfold "_ < _".
        rewrite <- Nat.succ_le_mono.
        apply Nat.le_add_r.
      + apply IH'; try solve [ assumption ].
        intros s' arg arg_dec.
        apply IH.
        rewrite (Nat.add_comm 1).
        rewrite <- (Nat.add_assoc).
        rewrite (Nat.add_comm _ 1).
        etransitivity; [ apply arg_dec | ].
        apply Nat.lt_add_pos_l.
        destruct hd.
        simpl.
        unfold "_ < _".
        apply Nat.le_add_r.
  Qed.

  Lemma FixF_eq_trans: forall s1 s2 s3 c1 c2 c3,
      FixF_eq s1 s2 c1 c2 -> FixF_eq s2 s3 c2 c3 -> FixF_eq s1 s3 c1 c3.
  Proof.
    intros s1 s2 s3 c1 c2.
    revert s1 s3 c1.
    apply (fun r => DepFix nat lt (well_founded_ltof _ (fun x => x)) (Sort EmptySet) FixF
                        (fun s2 c2 => forall s1 s3 c1 c3, FixF_eq s1 s2 c1 c2 -> FixF_eq s2 s3 c2 c3 -> FixF_eq s1 s3 c1 c3)
                        (FixF_size) r s2 c2).
    clear s2 c2.
    intros s2 c2 IH s1 s3 c1 c3.
    unfold FixF_eq.
    destruct c1 as [ op1 subst1 wf_subst1 args1 subsort1 ].
    destruct c2 as [ op2 subst2 wf_subst2 args2 subsort2 ].
    destruct c3 as [ op3 subst3 wf_subst3 args3 subsort3 ].
    intros [ op12 args12 ] [ op23 args23 ].
    split.
    - etransitivity; [ exact op12 | exact op23 ].
    - revert IH.
      simpl.
      revert args1 args3 args12 args23.
      assert (arity_eq12 : arity op1 = arity op2).
      { rewrite op12; reflexivity. }
      assert (arity_eq32 : arity op3 = arity op2).
      { rewrite <- op23; reflexivity. }
      assert (domain_eq12 : rew arity_eq12 in domain op1 = domain op2).
      { revert arity_eq12.
        rewrite op12.
        intro arity_eq12.
        rewrite (UIP_dec Nat.eq_dec arity_eq12 eq_refl).
        reflexivity. }
      assert (domain_eq32: rew arity_eq32 in domain op3 = domain op2).
      { revert arity_eq32.
        rewrite <- op23.
        intro arity_eq32.
        rewrite (UIP_dec Nat.eq_dec arity_eq32 eq_refl).
        reflexivity. }
      revert args2 arity_eq12 arity_eq32 domain_eq12 domain_eq32.
      generalize (domain op2).
      generalize (arity op2).
      intros arity2 argSorts2 args2.
      generalize (domain op1).
      generalize (arity op1).
      generalize (domain op3).
      generalize (arity op3).        
      induction args2 as [ | s2 S2 n2 argSort2 argSorts2 arg2 args2 IH' ].
      + intros arity3 dom3 arity1 dom1.
        destruct arity1; intro arity_eq12; [ | inversion arity_eq12 ].
        destruct arity3; intro arity_eq32; [ | inversion arity_eq32 ].
        rewrite (UIP_dec Nat.eq_dec arity_eq12 eq_refl).
        rewrite (UIP_dec Nat.eq_dec arity_eq32 eq_refl).
        simpl.
        intros dom1_eq dom3_eq.
        rewrite dom1_eq.
        rewrite dom3_eq.
        intros args1 args3.
        apply (fun P r => FixF_args_case0 s1 subst1 P (nil _) args1 r).
        intro.
        destruct args3.
        * intros; trivial.
        * intro; contradiction.
      + intros arity3 dom3 arity1 dom1.
        destruct arity1; intro arity_eq12; [ inversion arity_eq12 | ].
        inversion arity_eq12 as [ arity_eq12' ].
        revert dom1 arity_eq12; rewrite arity_eq12'.
        intros dom1 arity_eq12.
        rewrite (UIP_dec Nat.eq_dec arity_eq12 eq_refl).
        clear arity_eq12.
        simpl.
        intros arity_eq32 dom1_eq dom3_eq args1 args3.
        revert dom1_eq arity_eq32 dom3_eq IH'.
        apply (FixF_args_caseS' s1 subst1 _ _ args1).
        clear args1 wf_subst1 subsort1 subst1.
        intros subst1 argSort1 argSorts1 arg1 args1 dom1_eq.
        destruct args3 as [ | subst3 arity3 argSort3 argSorts3 arg3 args3 ].
        * intros; contradiction.
        * inversion arity_eq32 as [ arity_eq32' ].
          revert argSorts3 arity_eq32 args3; rewrite arity_eq32'.
          intros argSorts3 arity_eq32 args3.
          rewrite (UIP_dec Nat.eq_dec arity_eq32 eq_refl).
          clear arity_eq32.
          simpl.
          intros dom3_eq IH' [ arg12 args12 ] [ arg23 args23 ] IH.
          split.
          { apply (IH _ arg2); try solve [ assumption ].
            unfold "_ < _".
            rewrite <- Nat.succ_le_mono.
            apply Nat.le_add_r. }
          { apply (IH' wf_subst2 subsort2 _ _ _ _ eq_refl eq_refl); try solve [ assumption ].
            - simpl.
              inversion dom1_eq as [ [ argSort12_eq argSorts12_eq ] ].
              exact (vect_exist_eq _ _ argSorts12_eq).
            - simpl.
              inversion dom3_eq as [ [ argSort32_eq argSorts32_eq ] ].
              exact (vect_exist_eq _ _ argSorts32_eq).
            - intros s arg arg_dec.
              apply IH.
              rewrite (Nat.add_comm 1).
              rewrite <- (Nat.add_assoc _ _ 1).
              rewrite (Nat.add_comm _ 1).
              etransitivity; [ exact arg_dec | ].
              apply Nat.lt_add_pos_l.
              destruct arg2.
              unfold FixF_size.
              simpl.
              unfold "_ < _".
              apply Nat.le_add_r. }
  Qed.
        
  Lemma FixF_eq_sym: forall s s' (c: FixF s) (c': FixF s'), FixF_eq s s' c c' -> FixF_eq s' s c' c.
  Proof.
    intros s s' c.
    revert s'.
    apply (fun r => DepFix nat lt (well_founded_ltof _ (fun x => x)) (Sort EmptySet) FixF
                        (fun s c => forall s' c', FixF_eq s s' c c' -> FixF_eq s' s c' c)
                        (FixF_size) r s c).
    clear s c.
    intros s c IH s' c'.
    destruct c as [ op subst wf_subst args subsort ].
    destruct c' as [ op' subst' wf_subst' args' subsort' ].
    intros [ op_eq args_eq ].
    split; [ rewrite op_eq; reflexivity | ].
    revert args' args_eq.
    assert (arity_eq: arity op' = arity op).
    { rewrite op_eq; reflexivity. }
    assert (dom_eq: rew arity_eq in domain op' = domain op).
    { revert arity_eq.
      rewrite <- op_eq.
      intro arity_eq.
      rewrite (UIP_dec Nat.eq_dec arity_eq eq_refl).
      reflexivity. }
    revert args IH arity_eq dom_eq.      
    simpl.
    generalize (domain op).
    generalize (arity op).
    intros arity1 dom args.
    generalize (domain op').
    generalize (arity op').
    induction args as [ | s subst arity1 argSort argSorts arg args IH' ].
    - intros arity2 dom2 IH.
      destruct arity2; intro arity_eq; [ | inversion arity_eq ].
      rewrite (UIP_dec Nat.eq_dec arity_eq eq_refl).
      simpl.
      intro dom2_eq.
      intro args'.
      apply (fun P r => FixF_args_case0 s' subst' P dom2 args' r).
      intro; trivial.
    - intros arity2 dom2 IH.
      destruct arity2; intro arity_eq; [ inversion arity_eq | ].
      inversion arity_eq as [ arity_eq' ].
      revert arity_eq dom2.
      rewrite arity_eq'.
      intros arity_eq dom2.
      rewrite (UIP_dec Nat.eq_dec arity_eq eq_refl).
      simpl.
      intros dom_eq args2.
      clear arity_eq.
      revert dom_eq IH'.
      apply (FixF_args_caseS' s' subst' _ _ args2).
      clear args2 subst' dom2 wf_subst' subsort'.
      intros subst' argSort' argSorts' arg' args' argSorts_eq IH' [ arg_eq args_eq ].
      split.
      + apply IH; [ | assumption ].
        unfold "_ < _".
        rewrite <- Nat.succ_le_mono.
        apply Nat.le_add_r.
      + apply (fun rec eq => IH' wf_subst subsort _ _ rec eq_refl eq _ args_eq).
        * intros s'' arg'' arg''_dec.
          apply IH.
          rewrite arg''_dec.
          rewrite <- (Nat.succ_lt_mono).
          apply Nat.lt_add_pos_l.
          unfold FixF_size.
          destruct arg.
          unfold "_ < _".
          apply Nat.le_add_r.
        * inversion argSorts_eq as [ [ argSort_eq argSorts_eq' ] ].
          simpl.
          exact (vect_exist_eq _ _ argSorts_eq').
  Qed.

  Section StrongUniqueness.
    Variable Carrier': Sort EmptySet -> Type.
    Variable algebra: SigmaAlgebra Carrier'.
    
    Definition unique_mor := initial_algebra_morphism Carrier' algebra.

    Lemma initial_morphism_alg_mor:
      forall s f,
         (unique_mor s (FixF_alg s f)) =
         (algebra s (F_mor FixF Carrier' unique_mor s f)).
    Proof.
      intros s f.
      unfold unique_mor.
      unfold initial_algebra_morphism.
      rewrite canonical_morphism_commutes.
      rewrite FixF_alg_coalg.
      reflexivity.
    Qed.

    Lemma fmap_args_dec_fmap_args_eq
     : forall (C C' : Sort EmptySet -> Type) (A : Type) (R : A -> A -> Prop)
         (measure : forall s : Sort EmptySet, C s -> A) (S : Var -> Sort EmptySet) (n : nat)
         (params : t (Sort Var) n) (s : Sort EmptySet) (c : C s)
         (f: forall (s' : Sort EmptySet) (c' : C s'), R (measure s' c') (measure s c) -> C' s')
         (g: forall (s' : Sort EmptySet), C s' -> C' s')
         (args : F_args C S params) (args_dec: argsDec C A R measure s c S params args),
        (forall s' c' (acc: R (measure s' c') (measure s c)), f s' c' acc = g s' c') ->
        fmap_args_dec C C' A R measure S params s c f args args_dec =
        fmap_args C C' _ params g args.
    Proof.
      intros C C' A R measure S n params s c f g args args_dec eqprf.
      revert args args_dec.
      induction params as [ | param n params IH ].
      - intros args args_dec.
        destruct args.
        reflexivity.
      - intros args args_dec.
        simpl.
        rewrite eqprf.
        rewrite IH.
        reflexivity.
    Qed.

    Lemma initial_morphism_unique:
      forall (g: forall s, FixF s -> Carrier' s),
        (forall s f, g s (FixF_alg s f) = algebra s (F_mor FixF Carrier' g s f)) ->
        forall s c, g s c = unique_mor s c.
    Proof.
      intros g g_alg_mor s c.
      unfold unique_mor.
      unfold initial_algebra_morphism.
      unfold canonical_morphism.
      unfold DepFix.
      generalize (well_founded_ltof nat (fun x => x) (FixF_size s c)).
      match goal with
      |[|- forall acc, g s c = (?f_rec s c acc)] =>
       apply (fun r => Fix_F nat (ltof nat (fun x => x)) (Sort EmptySet) FixF
                          (fun s c => forall acc, g s c = f_rec s c acc) FixF_size
                          r s c (well_founded_ltof nat (fun x => x) (FixF_size s c)))
      end.
      clear s c.
      intros s c IH acc.
      rewrite <- (FixF_coalg_alg s c) at 1.
      rewrite g_alg_mor.
      destruct acc as [ acc' ].
      simpl.
      unfold F_mor.
      destruct c as [ op subst wf_subst args subsort ].
      simpl.
      apply (f_equal (fun args' =>
                        algebra s {| op := op; subst := subst;
                                     wf_subst := wf_subst; args := args';
                                     subsort := subsort |})).
      apply eq_sym.
      apply (fmap_args_dec_fmap_args_eq).
      intros s' c' acc.
      apply eq_sym.
      eapply IH.
      exact acc.
    Qed.
  End StrongUniqueness.
      
  
    (*Section UniquenessModulo.
      Lemma initial_morphism_alg_mor:
        forall s s' f f',
          F_eq FixF (fun s s' => s = s') s s' f f' ->
          carrier'_eq s s' (unique_mor s (FixF_alg s f))
                      (algebra s' (F_mor FixF Carrier' unique_mor s' f')).
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
    End UniquenessModulo. *)
End Algebraic.

