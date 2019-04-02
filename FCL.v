Require Import PeanoNat.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Arith.Wf_nat.
From mathcomp Require Import all_ssreflect.
Require Import Types.
Require Import Cover.

Set Bullet Behavior "Strict Subproofs".

Delimit Scope it_scope with IT.
Open Scope it_scope.

Import EqNotations.

Reserved Notation "[ 'FCL' Gamma |- M : A ]" (at level 0, M at level 50).
Reserved Notation "M @ N" (at level 50, left associativity).

Definition context_of (combT: finType) (ctorT: ctor) (_: phantom Type (Finite.sort combT)) (_: phantom Type (Constructor.sort ctorT)) :=
  {ffun combT -> @IT ctorT}.
Notation Ctxt Combinator Constructor :=
  (context_of _ _ (Phantom Type Combinator) (Phantom Type Constructor)).

Section FCL.
  Variable Combinator: finType.
  Variable Constructor: ctor.

  Inductive Term : Type :=
  | Var: Combinator -> Term
  | App: Term -> Term -> Term.

  Notation "M @ N" := (App M N) : it_scope.

  Inductive FCL (Gamma: Ctxt Combinator Constructor): Term -> @IT Constructor -> Prop :=
  | FCL__Var: forall c, [FCL Gamma |- Var c : Gamma c ]
  | FCL__MP: forall M N A B, [FCL Gamma |- M : A -> B ] -> [FCL Gamma |- N : A] -> [FCL Gamma |- M @ N : B ]
  | FCL__Sub: forall M A B, [FCL Gamma |- M : A] -> [bcd A <= B] -> [FCL Gamma |- M : B]
  where "[ 'FCL' Gamma |- M : A ]" := (FCL Gamma M A) : it_scope.

  (** Enable mathcomp functionalities on terms **)
  Section TermMathcompInstances.
    Fixpoint Term2tree (M: Term):
      GenTree.tree Combinator :=
      match M with
      | Var c => GenTree.Node 0 [:: GenTree.Leaf c]
      | M @ N => GenTree.Node 1 [:: Term2tree M; Term2tree N]
      end.

    Fixpoint tree2Term (t: GenTree.tree Combinator): option Term :=
      match t with
      | GenTree.Node n args =>
        match n, args with
        | 0, [:: GenTree.Leaf c] => Some (Var c)
        | 1, [:: t1; t2] =>
          if tree2Term t1 is Some M then
            if tree2Term t2 is Some N
            then Some (M @ N)
            else None
          else None
        | _, _ => None
        end
      | _ => None
      end.

    Lemma pcan_Termtree: pcancel Term2tree tree2Term.
    Proof. by elim => //= ? -> ? ->. Qed.

    Definition Term_eqMixin := PcanEqMixin pcan_Termtree.
    Canonical Term_eqType := EqType Term Term_eqMixin.
    Definition Term_choiceMixin := PcanChoiceMixin pcan_Termtree.
    Canonical Term_choiceType := ChoiceType Term Term_choiceMixin.
    Definition Term_countMixin := PcanCountMixin pcan_Termtree.
    Canonical Term_countType := CountType Term Term_countMixin.
  End TermMathcompInstances.

  Definition FCL_inv {Gamma} {M} {B} (prf: [FCL Gamma |- M : B]) :=
    fun (X : Ctxt Combinator Constructor -> Term -> @IT Constructor -> Prop) =>
      let diag M B :=
          match M return Prop with
          | Var c =>
            (X Gamma (Var c) (Gamma c) ->
             (forall A, [FCL Gamma |- Var c : A] -> [bcd A <= B] -> X Gamma (Var c) B) ->
             X Gamma M B)%type
          | M @ N =>
            ((forall A, [FCL Gamma |- M : (A -> B)%IT] -> [FCL Gamma |- N : A] -> X Gamma (M @ N) B) ->
             (forall A, [FCL Gamma |- M @ N : A] -> [bcd A <= B] -> X Gamma (M @ N) B) ->
             X Gamma (M @ N) B)%type
          end in
      match prf in [FCL _ |- M : B] return diag M B with
      | FCL__Var c => fun kv _ => kv
      | FCL__MP M N A B prf1 prf2 => fun kmp _ => kmp A prf1 prf2
      | FCL__Sub (Var c) A B prf1 prf2  => fun _ ksub => ksub A prf1 prf2
      | FCL__Sub (M @ N) A B prf1 prf2 => fun _ ksub => ksub A prf1 prf2
      end.

  Definition revApply M Ns : Term := foldr (fun N M => M @ N) M Ns.
End FCL.

Arguments Term [Combinator].
Arguments Var [Combinator].
Arguments App [Combinator].
Hint Constructors Term.

Arguments FCL [Combinator Constructor].
Arguments FCL__Var [Combinator Constructor] [Gamma c].
Arguments FCL__MP [Combinator Constructor] [Gamma M N] A [B].
Arguments FCL__Sub [Combinator Constructor] [Gamma M] A [B].
Hint Constructors FCL.

Arguments revApply [Combinator].

Notation "M @ N" := (App M N) : it_scope.
Notation "[ 'FCL' Gamma |- M : A ]" := (FCL Gamma M A) : it_scope.

Section FCLProperties.
  Variable Combinator: finType.
  Variable Constructor: ctor.
  Implicit Type c: Combinator.
  Implicit Type A B C: @IT Constructor.
  Implicit Type Gamma: @Ctxt Combinator Constructor.

  Lemma FCL_Var_le: forall Gamma c A, [FCL Gamma |- (Var c) : A] -> [bcd (Gamma c) <= A].
  Proof.
    move => Gamma c A.
    move M__eq: (Var c) => M prf.
    move: M__eq.
    elim: M A / prf.
    - by move => ? [] ->.
    - by discriminate.
    - move => M A B prf IH le_prf M__eq.
        by apply: BCD__Trans; first by apply: IH.
  Qed.

  Lemma FCL_MP_inv: forall Gamma M N B, [FCL Gamma |- M @ N : B] -> exists A, [FCL Gamma |- M : A -> B] /\ [FCL Gamma |- N : A].
  Proof.
    move => Gamma M N B.
    move MN__eq: (M @ N) => MN prf.
    move: MN__eq.
    elim: MN B / prf => //.
    - move => M__tmp N__tmp A B prf1 _ prf2 _ [] -> ->.
        by (exists A); split.
    - move => [] // M__tmp N__tmp B1 B2 _ IH le_prf MN__eq.
      case: (IH MN__eq) => A [] prf1 prf2.
      exists A; split => //.
      apply: (FCL__Sub (A -> B1)) => //.
        by apply: BCD__Sub.
  Qed.

  Lemma FCL_normalized_ind:
    forall Gamma (P : Term -> @IT Constructor -> Prop),
      (forall c, P (Var c) (Gamma c)) ->
      (forall c A, P (Var c) (Gamma c) -> [bcd (Gamma c) <= A] -> P (Var c) A) ->
      (forall M N A B, [FCL Gamma |- M : (A -> B)] -> P M (A -> B) -> [FCL Gamma |- N : A] -> P N A -> P (M @ N) B) ->
      forall M A, [FCL Gamma |- M : A] -> P M A.
  Proof.
    move => Gamma P IH__Var IH__Sub IH__MP.
    elim.
    - move => c A /FCL_Var_le.
      apply: IH__Sub.
        by apply: IH__Var.
    - move => M IH__M N IH__N B /FCL_MP_inv [] A [] prf1 prf2.
        by apply: (IH__MP M N A B prf1 (IH__M (A -> B) prf1) prf2 (IH__N A prf2)).
  Qed.

  Lemma FCL__II:
    forall Gamma M A B, [FCL Gamma |- M : A] -> [FCL Gamma |- M : B] -> [FCL Gamma |- M : A \cap B].
  Proof.
    move => Gamma.
    elim.
    - move => c A B /FCL_Var_le prf1 /FCL_Var_le prf2.
      apply: (FCL__Sub (Gamma c)) => //.
        by apply: BCD__Glb.
    - move => M IH__M N IH__N B1 B2 /FCL_MP_inv [] A1 [] prf1__M prf1__N /FCL_MP_inv [] A2 [] prf2__M prf2__N.
      apply: (FCL__MP (A1 \cap A2)).
      + apply: (FCL__Sub ((A1 -> B1) \cap (A2 -> B2))).
        * by apply: IH__M.
        * by apply: bcd__Arr.
      + by apply: IH__N.
  Qed.

  Lemma FCL__Omega: forall Gamma M, [FCL Gamma |- M : Omega].
  Proof.
    move => Gamma.
    elim.
    - move => c.
        by apply: FCL__Sub.
    - move => M IH__M N IH__N.
      apply: (FCL__MP Omega) => //.
        by apply: (FCL__Sub Omega).
  Qed.

  Lemma FCL__weaken: forall Gamma1 Gamma2 M A,
      (forall c, [bcd (Gamma2 c) <= (Gamma1 c)]) ->
      [FCL Gamma1 |- M : A] -> [FCL Gamma2 |- M : A].
  Proof.
    move => Gamma1 Gamma2 M A weaken prf.
    elim /FCL_normalized_ind: M A / prf.
    - move => c.
        by apply: FCL__Sub; last by apply weaken.
    - move => c A _ /(BCD__Trans _ (weaken c)) res.
        by apply: FCL__Sub; last by exact res.
    - by move => ? ? A *; apply: (FCL__MP A).
  Qed.

  Lemma FCL__App: forall Gamma M Ns m,
      seq.size Ns = seq.size m.1 ->
      (forall n, [FCL Gamma |- (nth M Ns n) : nth (mkArrow m) m.1 n]) ->
      [FCL Gamma |- revApply M Ns : m.2].
  Proof.
    move => Gamma M Ns.
    move: M.
    elim: Ns.
    - move => M [] srcs tgt /=.
      move => /(fun prf => @Logic.eq_sym _ _ _ prf) /size0nil -> prf.
        by apply: (prf 0).
    - move => N Ns IH M [] [] // src srcs tgt /= [] size__eq prfs.
      rewrite /revApply /= -/(revApply M Ns).
      apply: (FCL__MP src).
      + apply: (IH M (srcs, src -> tgt)) => //.
        move => n.
          by exact (prfs n.+1).
      + by exact (prfs 0).
  Qed.

  Lemma FCL__invApp: forall Gamma M Ns tgt,
      [FCL Gamma |- revApply M Ns : tgt] ->
      exists srcs,
        seq.size Ns = seq.size srcs /\
        (forall n, [FCL Gamma |- (nth M Ns n) : nth (mkArrow (srcs, tgt)) srcs n]).
  Proof.
    move => Gamma M Ns.
    move: M.
    elim: Ns.
    - move => M tgt /= prf.
      exists [::]; split => //.
      move => n.
        by rewrite nth_default //= nth_default.
    - move => N Ns IH M tgt /FCL_MP_inv [] src [].
      move => /(IH M (src -> tgt)) [] srcs [] size__eq prf1 prf2.
      exists [:: src & srcs]; split.
      + by rewrite /= size__eq.
      + by case.
  Qed.

  Fixpoint unapply (M: Term) : (Combinator * seq Term) :=
    match M with
    | Var c => (c, [::])
    | M @ N => let (c, Ns) := unapply M in (c, [:: N & Ns])
    end.

  Lemma revapply_unapply: cancel (fun cNs => revApply (Var cNs.1) cNs.2) unapply.
  Proof. move => [] ?; by elim => //= N Ns ->. Qed.

  Lemma unapply_revapply: cancel unapply (fun cNs => revApply (Var cNs.1) cNs.2).
  Proof. by (elim => //= M; case: (unapply M) => c Ns /= ->). Qed.

  Definition minimalArrowTgt (A B: @IT Constructor): @IT Constructor :=
    \bigcap_(A_i <- if (subtype_machine _ [tgt_for_srcs_gte B in
                                             cast (Omega -> Omega \times Omega) A])
                        is exist [check_tgt Delta] _ then Delta else [::]) A_i.

  Fixpoint minimalType (Gamma: Ctxt Combinator Constructor) (M: Term): @IT Constructor :=
    match M with
    | Var c => Gamma c
    | M @ N => minimalArrowTgt (minimalType Gamma M) (minimalType Gamma N)
    end.

  Lemma minimalArrowType_le: forall A B, [bcd A <= B -> minimalArrowTgt A B].
  Proof.
    move => A B.
    apply /subty__sound.
    rewrite /minimalArrowTgt.
    move: (subtype_machine _ [tgt_for_srcs_gte B in cast (B -> minimalArrowTgt A B) A]) => [].
    case.
    - move => b /SubtypeMachine_inv.
        by case: (cast (B -> minimalArrowTgt A B) A).
    - move => Delta prf1.
      move: (subtype_machine _ [subty \bigcap_(A_i <- Delta) A_i of minimalArrowTgt A B]) => [].
      case; last first.
      + move => ? /SubtypeMachine_inv.
          by case: (minimalArrowTgt A B).
      + move => r prf2.
        case isOmega__tgt: (isOmega (minimalArrowTgt A B)).
        * rewrite -(orTb r) -isOmega__tgt /minimalArrowTgt.
            by apply: step__Arr; first by exact prf1.
        * have cast__eq: (cast (Omega -> Omega \times Omega) A) =
                       (cast (B -> minimalArrowTgt A B) A).
          { move: isOmega__tgt.
            clear...
            move: (minimalArrowTgt A B) => C.
            move => isOmega__C.
            elim: A; by rewrite /cast /= isOmega__C. }
          rewrite -(orbT false) -isOmega__tgt.
          apply: (step__Arr (Delta := Delta) (r := true)).
          ** move: prf1.
               by rewrite -cast__eq.
          ** move: prf1.
             rewrite -cast__eq.
             move => prf1.
             move: (subtype_machine Constructor [ tgt_for_srcs_gte B in cast (Omega -> Omega \times Omega) A]) => [] res1 res2.
             move: (Types.Semantics_functional _ _ _ _ prf1 res2) => <-.
               by apply: subty_complete.
  Qed.

  Lemma minimalType_sound: forall Gamma M, FCL Gamma M (minimalType Gamma M).
  Proof.
    move => Gamma.
    elim => //= M IH1 N IH2.
    apply: FCL__MP; last by exact IH2.
    apply: FCL__Sub; first by exact IH1.
      by apply: minimalArrowType_le.
  Qed.

  Lemma minimalArrowType_minimal: forall A B C,
      [bcd A <= B -> C] -> [bcd (minimalArrowTgt A B) <= C].
  Proof.
    move => A B C /subty_complete /SubtypeMachine_inv.
    move => /(fun prf => prf (fun i r =>
                            match i, r with
                            | [subty A of B -> C], Return true => [bcd (minimalArrowTgt A B) <= C]
                            | _, _ => True
                            end)) res.
    apply: res.
    case isOmega__C: (isOmega C).
    - move => /= *.
      apply /subty__sound.
        by apply: subty__Omega.
    - move => Delta [] //= prf1 prf2.
      apply /subty__sound.
      have cast__eq: (cast (Omega -> Omega \times Omega) A = cast (B -> C) A).
      { move: isOmega__C.
        clear...
        move => isOmega__C.
          by elim: A; rewrite /cast /= isOmega__C. }
      rewrite /minimalArrowTgt cast__eq.
      move: (subtype_machine Constructor [ tgt_for_srcs_gte B in cast (B -> C) A]) => [] res1 res2.
        by move: (Types.Semantics_functional _ _ _ _ prf1 res2) => <-.
  Qed.

  Lemma minimalType_minimal: forall Gamma M A, FCL Gamma M A -> [bcd (minimalType Gamma M) <= A].
  Proof.
    move => Gamma M A prf.
    elim /FCL_normalized_ind: M A / prf => //= M N A B _ IH1 _ IH2.
    apply: minimalArrowType_minimal.
    apply: BCD__Trans; first by exact IH1.
      by apply: BCD__Sub.
  Qed.

End FCLProperties.
Arguments FCL_Var_le [Combinator Constructor].
Arguments FCL_MP_inv [Combinator Constructor].
Arguments FCL_normalized_ind [Combinator Constructor].
Arguments FCL__II [Combinator Constructor].
Arguments FCL__Omega [Combinator Constructor].
Arguments FCL__App [Combinator Constructor].
Arguments FCL__invApp [Combinator Constructor].
Arguments unapply [Combinator].
Arguments revapply_unapply [Combinator].
Arguments unapply_revapply [Combinator].
Arguments minimalType [Combinator Constructor].
Arguments minimalArrowTgt [Constructor].
Arguments  minimalArrowType_le [Constructor].
Arguments minimalType_sound [Combinator Constructor].
Arguments  minimalArrowType_minimal [Constructor].
Arguments minimalType_minimal [Combinator Constructor].

Section ConstructorSum.
  Variable Constructor1 Constructor2: ctor.

  Definition ctorSum_countType: countType :=
    sum_countType Constructor1 Constructor2.

  Definition leq_sum (l r: ctorSum_countType): bool :=
    match l, r with
    | inl a, inl b => [ctor a <= b]
    | inr a, inr b => [ctor a <= b]
    | _, _ => false
    end.

  Lemma leq_sum_refl: Constructor.preorder_reflexive ctorSum_countType leq_sum.
  Proof.
    move => [] c; by apply: preorder_reflexive.
  Qed.

  Lemma leq_sum_trans: Constructor.preorder_transitive ctorSum_countType leq_sum.
  Proof.
    move => [] c1 [] c2 [] c3 //=.
    - by apply: preorder_transitive.
    - by rewrite andbF.
    - by rewrite andbF.
    - by apply: preorder_transitive.
  Qed.

  Definition sum_ctorMixin :=
    Constructor.Mixin ctorSum_countType
                      leq_sum leq_sum_refl leq_sum_trans.
  Canonical sum_ctorType := Eval hnf in CtorType ctorSum_countType sum_ctorMixin.
End ConstructorSum.

Module SplitTypeUniverse.  
  Definition classify (Constructor: ctor): Type := (@IT Constructor -> bool)%type.

  Definition dist_arr_partition
             (Constructor: ctor)
             (inPartition : classify Constructor): Type :=
    forall A B, inPartition (A -> B) = inPartition A && inPartition B.
  Definition dist_inter_partition
             (Constructor: ctor)
             (inPartition : classify Constructor): Type :=
    forall A B, inPartition (A \cap B) = inPartition A && inPartition B.
  Definition omega_partition
             (Constructor: ctor)
             (inPartition: classify Constructor): Type :=
    inPartition Omega.

  Definition st_irrel_partition
             (Constructor: ctor)
             (inPartition1 : classify Constructor)
             (inPartition2 : classify Constructor): Type :=
    forall A B C, inPartition1 A -> inPartition2 B -> inPartition1 C -> [bcd (A \cap B) <= C] -> [bcd A <= C].

  Record mixin_of (Constructor: ctor): Type :=
    Mixin {
        inPartition1 : classify Constructor;
        inPartition2 : classify Constructor;
        _: dist_arr_partition Constructor inPartition1;
        _: dist_arr_partition Constructor inPartition2;
        _: dist_inter_partition Constructor inPartition1;
        _: dist_inter_partition Constructor inPartition2;
        _: omega_partition Constructor inPartition1;
        _: omega_partition Constructor inPartition2;
        _: st_irrel_partition Constructor inPartition1 inPartition2;
        _: st_irrel_partition Constructor inPartition2 inPartition1
      }.
  
  Section ClassDef.
    Record class_of (C: Type) :=
      Class {
          base: Constructor.class_of C;
          mixin: mixin_of (Constructor.Pack C base)
        }.
    Local Coercion base : class_of >-> Constructor.class_of.
    Structure type := Pack { sort : Type; _ : class_of sort }.
    Local Coercion sort : type >-> Sortclass.
    Variables (T: Type) (splitUniverse: type).
    Definition class := let: Pack _ c as splitUniverse' := splitUniverse return class_of splitUniverse' in c.
    Definition clone c of phant_id class c := @Pack T c.
    Let xT := let: Pack T _ := splitUniverse in T.
    Notation xclass := (class : class_of xT).
    Definition pack b0 (m0: mixin_of (Constructor.Pack T b0)) :=
      fun bT b & phant_id (Constructor.class bT) b =>
        fun m & phant_id m0 m => Pack T (@Class T b m).
    Definition eqType := Eval hnf in @Equality.Pack splitUniverse xclass xT.
    Definition choiceType := Eval hnf in  @Choice.Pack splitUniverse xclass xT.
    Definition countType := Eval hnf in @Countable.Pack splitUniverse xclass xT.
    Definition ctor := Eval hnf in @Constructor.Pack splitUniverse xclass.
  End ClassDef.

  Module Import Exports.
    Coercion base : class_of >-> Constructor.class_of.
    Coercion mixin: class_of >-> mixin_of.
    Coercion sort : type >-> Sortclass.
    Coercion eqType : type >-> Equality.type.
    Canonical eqType.
    Coercion choiceType : type >-> Choice.type.
    Canonical choiceType.
    Coercion countType : type >-> Countable.type.
    Canonical countType.
    Coercion ctor : type >-> Constructor.type.
    Canonical ctor.

    Notation splitTypeUniverse := type.
    Notation SplitTypeUniverseMixin := Mixin.
    Notation SplitTypeUniverseType C m := (@pack C _ m _ _ id _ id).
    Notation "[ 'splitTypeUniverse' 'of' T 'for' C ]" :=
      (@clone splitTypeUniverse C _ idfun id) (at level 0, format "[ 'splitTypeUniverse' 'of' T 'for' C ]") : form_scope.
    Notation "[ 'splitTypeUniverse' 'of' C ]" :=
      (@clone splitTypeUniverse C _ id id) (at level 0, format "[ 'splitTypeUniverse' 'of' C ]") : form_scope.
  End Exports.
End SplitTypeUniverse.
Export SplitTypeUniverse.Exports.

Definition inPartition1 (U: splitTypeUniverse) := @SplitTypeUniverse.inPartition1 _ (SplitTypeUniverse.class U).
Arguments inPartition1 [U].
Definition inPartition2 (U: splitTypeUniverse) := @SplitTypeUniverse.inPartition2 _ (SplitTypeUniverse.class U).
Arguments inPartition2 [U].
Lemma dist_arr_partition1 U: SplitTypeUniverse.dist_arr_partition _ (@inPartition1 U).
Proof. by case U => ? [] ? []. Qed.
Arguments dist_arr_partition1 [U].
Lemma dist_arr_partition2 U: SplitTypeUniverse.dist_arr_partition _ (@inPartition2 U).
Proof. by case U => ? [] ? []. Qed.
Arguments dist_arr_partition2 [U].
Lemma dist_inter_partition1 U: SplitTypeUniverse.dist_inter_partition _ (@inPartition1 U).
Proof. by case U => ? [] ? []. Qed.
Arguments dist_inter_partition1 [U].
Lemma dist_inter_partition2 U: SplitTypeUniverse.dist_inter_partition _ (@inPartition2 U).
Proof. by case U => ? [] ? []. Qed.
Arguments dist_inter_partition2 [U].
Lemma omega_partition1 U: SplitTypeUniverse.omega_partition _ (@inPartition1 U).
Proof. by case U => ? [] ? []. Qed.
Arguments omega_partition1 [U].
Lemma omega_partition2 U: SplitTypeUniverse.omega_partition _ (@inPartition2 U).
Proof. by case U => ? [] ? []. Qed.
Arguments omega_partition2 [U].
Lemma st_irrel_partition1 U: SplitTypeUniverse.st_irrel_partition _ (@inPartition1 U) (@inPartition2 U).
Proof. by case U => ? [] ? []. Qed.
Arguments st_irrel_partition1 [U].
Lemma st_irrel_partition2 U: SplitTypeUniverse.st_irrel_partition _ (@inPartition2 U) (@inPartition1 U).
Proof. by case U => ? [] ? []. Qed.
Arguments st_irrel_partition2 [U].

Module SplitContextPair.
  Definition pure_context
             (Combinator: finType)
             (Constructor: ctor)
             (Gamma: Ctxt Combinator Constructor)
             (inPartition: SplitTypeUniverse.classify Constructor): Type :=
    forall c, inPartition (Gamma c).

  Record mixin_of (Combinator: finType) (U: splitTypeUniverse): Type :=
    Mixin {
        ctxt1: Ctxt Combinator U;
        ctxt2: Ctxt Combinator U;
        _: pure_context _ _ ctxt1 (@inPartition1 _);
        _: pure_context _ _ ctxt2 (@inPartition2 _)
      }.
  Section ClassDef.
    Structure class_of (Combinator: Type) (Constructor: Type) :=
      Class {
          combinator_base: Finite.class_of Combinator;
          universe_base: SplitTypeUniverse.class_of Constructor;          
          mixin: mixin_of (@Finite.Pack Combinator combinator_base Combinator)
                          (SplitTypeUniverse.Pack Constructor universe_base)
        }.
    Local Coercion combinator_base : class_of >-> Finite.class_of.
    Local Coercion universe_base : class_of >-> SplitTypeUniverse.class_of.
    Structure type := Pack { combinator_sort : Type; constructor_sort: Type; _ : class_of combinator_sort constructor_sort }.
    Variables (Combinator: Type) (Constructor: Type) (splitCtxts: type).
    Definition class := let: Pack _ _ c as splitCtor' := splitCtxts return class_of (combinator_sort splitCtor')
                                                                                    (constructor_sort splitCtor')
                        in c.
    Definition clone c of phant_id class c := @Pack Combinator Constructor c.
    Let xCombinator := (let: Pack Combinator _ _ := splitCtxts in Combinator).
    Let xConstructor := (let: Pack _ Constructor _ := splitCtxts in Constructor).
    Notation xclass := (class : class_of xCombinator xConstructor).
    Definition pack b0 b1 (m0: mixin_of (@Finite.Pack Combinator b0 Combinator) (SplitTypeUniverse.Pack Constructor b1)) :=
      fun bCombinator bcomb & phant_id (Finite.class bCombinator) bcomb =>
        fun bConstructor bctor & phant_id (SplitTypeUniverse.class bConstructor) bctor =>
          fun m & phant_id m0 m => Pack Combinator Constructor (@Class Combinator Constructor bcomb bctor m).

    Definition combEqType := Eval hnf in @Equality.Pack xCombinator xclass xCombinator.
    Definition combChoiceType := Eval hnf in  @Choice.Pack xCombinator xclass xCombinator.
    Definition combCountType := Eval hnf in  @Countable.Pack xCombinator xclass xCombinator.
    Definition finType := Eval hnf in  @Finite.Pack xCombinator xclass xCombinator.

    Definition ctorEqType := Eval hnf in @Equality.Pack xConstructor (SplitTypeUniverse.base _ xclass) xConstructor.
    Definition ctorCountType := Eval hnf in @Countable.Pack xConstructor (SplitTypeUniverse.base _ xclass) xConstructor.
    Definition ctor := Eval hnf in  @Constructor.Pack xConstructor xclass.
    Definition splitTypeUniverse := (SplitTypeUniverse.Pack xConstructor xclass).
  End ClassDef.

  Module Import Exports.
    Coercion universe_base : class_of >-> SplitTypeUniverse.class_of.
    Coercion mixin: class_of >-> mixin_of.
    Coercion ctor : type >-> Constructor.type.
    Canonical ctor.
    Coercion splitTypeUniverse: type >-> SplitTypeUniverse.type.
    Canonical splitTypeUniverse.
    Coercion finType: type >-> Finite.type.
    Canonical finType.

    Notation splitCtxtPair := type.
    Notation SplitCtxtPairMixin := Mixin.
    Notation SplitCtxtPairType Combinator Constructor m := (@pack Combinator Constructor _ _ m _ _ id _ _ id m id).
    Notation "[ 'splitCtxtPair' 'of' Combinator '*' Constructor 'for' splitCtxts ]" :=
      (@clone Combinator Constructor splitCtxts _ idfun)
        (at level 0, format "[ 'splitCtxtPair' 'of' Combinator '*' Constructor 'for' splitCtxts ]") : form_scope.
    Notation "[ 'splitCtxtPair' 'of' Combinator '*' Constructor ]" :=
      (@clone Combinator Constructor _ _ id) (at level 0, format "[ 'splitCtxtPair' 'of' Combinator '*' Constructor ]") : form_scope.
  End Exports.
End SplitContextPair.

Export SplitContextPair.Exports.

Definition ctxt1 (Gammas: splitCtxtPair) :=
  @SplitContextPair.ctxt1 _ _ (@SplitContextPair.class Gammas).
Definition ctxt2 (Gammas: splitCtxtPair) :=
  @SplitContextPair.ctxt2 _ _ (@SplitContextPair.class Gammas).

Lemma pure_context1:
  forall (Gammas: splitCtxtPair),
      SplitContextPair.pure_context _ _ (ctxt1 Gammas) (@inPartition1 Gammas).
Proof. by case => [] ? ? [] ? ? []. Qed.
Lemma pure_context2:
  forall (Gammas: splitCtxtPair),
      SplitContextPair.pure_context _ _ (ctxt2 Gammas) (@inPartition2 Gammas).
Proof. by case => [] ? ? [] ? ? []. Qed.

Section DiagCountTypeCtor.
  Variable Constructor: countType.  

  Lemma eqop_refl: Constructor.preorder_reflexive Constructor eq_op.
  Proof.
    move => x.
      by rewrite eq_refl.
  Qed.

  Lemma eqop_trans: Constructor.preorder_transitive Constructor eq_op.
  Proof.
    move => x y z.
    apply /implyP.
      by move => /andP [] /eqP ->.
  Qed.

  Definition diag_ctorMixin := Constructor.Mixin Constructor eq_op eqop_refl eqop_trans.
  Definition diag_ctorType := Eval hnf in CtorType Constructor diag_ctorMixin.
End DiagCountTypeCtor.

Fixpoint isArrow {C: ctor} (A: @IT C): bool :=
  match A with
  | _ -> _ => true
  | A \cap B => isArrow A || isArrow B
  | _ => false
  end.

Module ITHomomorphism.
  Definition subtype_hom (Constructor1 Constructor2: ctor) (f: @IT Constructor1 -> @IT Constructor2): Type :=
    forall A B, [bcd A <= B] <-> [bcd (f A) <= (f B)].

  Definition arrow_hom (Constructor1 Constructor2: ctor) (f: @IT Constructor1 -> @IT Constructor2): Type :=
    forall A B, f (A -> B) = (f A -> f B).

  Definition inter_hom (Constructor1 Constructor2: ctor) (f: @IT Constructor1 -> @IT Constructor2): Type :=
    forall A B, f (A \cap B) = (f A \cap f B).
  
  Definition omega_hom (Constructor1 Constructor2: ctor) (f: @IT Constructor1 -> @IT Constructor2): Type :=
    f Omega = Omega.

  Definition arrow_preimage (Constructor1 Constructor2: ctor) (f: @IT Constructor1 -> @IT Constructor2): Type :=
    forall A, isArrow (f A) -> isArrow A.
 
  Record mixin_of (Domain Range: ctor): Type :=
    Mixin {
        map_types: @IT Domain -> @IT Range;
        _: subtype_hom _ _ map_types;
        _: arrow_hom _ _ map_types;
        _: inter_hom _ _ map_types;
        _: omega_hom _ _ map_types;
        _: arrow_preimage _ _ map_types
      }.
  Section ClassDef.
    Structure class_of (Domain Range: Type) :=
      Class {
          dom_base: Constructor.class_of Domain;
          rng_base: Constructor.class_of Range;
          mixin: mixin_of (Constructor.Pack Domain dom_base)
                          (Constructor.Pack Range rng_base)
        }.
    Structure type := Pack { domain_sort : Type; range_sort: Type; _ : class_of domain_sort range_sort }.
    Variables (Domain Range: Type) (itHom: type).
    Definition class := let: Pack _ _ c as itHom' := itHom return class_of (domain_sort itHom')
                                                                           (range_sort itHom')
                        in c.
    Definition clone c of phant_id class c := @Pack Domain Range c.
    Let xDomain := let: Pack Domain _ _ := itHom in Domain.
    Let xRange := let: Pack _ Range _ := itHom in Range.
    Notation xclass := (class : class_of xDomain xRange).
    Definition pack b0 b1 (m0: mixin_of (@Constructor.Pack Domain b0) (Constructor.Pack Range b1)) :=
      fun bDomain bdom & phant_id (Constructor.class bDomain) bdom =>
        fun bRange brng & phant_id (Constructor.class bRange) brng =>
          fun m & phant_id m0 m => Pack Domain Range (@Class Domain Range bdom brng m).

    Definition domain := Eval hnf in @Constructor.Pack xDomain (dom_base _ _ xclass).
    Definition range := Eval hnf in @Constructor.Pack xRange (rng_base _ _ xclass).
  End ClassDef.

  Module Import Exports.
    Coercion class: type >-> class_of.
    Coercion mixin: class_of >-> mixin_of.
    Coercion map_types: mixin_of >-> Funclass.

    Notation itHom := type.
    Notation ITHomMixin := Mixin.
    Notation ITHomType Domain Range m := (@pack Domain Range _ _ m _ _ id _ _ id _ id).
    Notation "[ 'itHom' 'of' Domain '*' Range 'for' hom ]" :=
      (@clone Domain Range hom _ idfun)
        (at level 0, format "[ 'itHom' 'of' Domain '*' Range 'for' hom ]") : form_scope.
    Notation "[ 'itHom' 'of' Domain '*' Range ]" :=
      (@clone Domain Range _ _ id) (at level 0, format "[ 'itHom' 'of' Domain '*' Range ]") : form_scope.
  End Exports.
End ITHomomorphism.

Export ITHomomorphism.Exports.

Definition domain_base (f: itHom): ctor :=
  @Constructor.Pack _ (@ITHomomorphism.dom_base _ _ (@ITHomomorphism.class f)).
Definition range_base (f: itHom): ctor :=
  @Constructor.Pack _ (@ITHomomorphism.rng_base _ _ (@ITHomomorphism.class f)).
Lemma subtype_hom: forall (f: itHom), @ITHomomorphism.subtype_hom _ _ f.
Proof. by move => [] ? ? [] ? ? []. Qed.
Lemma arrow_hom: forall (f: itHom), @ITHomomorphism.arrow_hom _ _ f.
Proof. by move => [] ? ? [] ? ? []. Qed.
Lemma inter_hom: forall (f: itHom), @ITHomomorphism.inter_hom _ _ f.
Proof. by move => [] ? ? [] ? ? []. Qed.
Lemma omega_hom: forall (f: itHom), @ITHomomorphism.omega_hom _ _ f.
Proof. by move => [] ? ? [] ? ? []. Qed.
Lemma arrow_preimage: forall (f: itHom), @ITHomomorphism.arrow_preimage _ _ f.
Proof. by move => [] ? ? [] ? ? []. Qed.

Section ContextCoproduct.
  Variables (Constructor1 Constructor2: ctor).
  Definition LiftedConstructor: ctor := sum_ctorType (diag_ctorType [countType of bool])
                                                     (sum_ctorType Constructor1 Constructor2).

  Fixpoint lift {C: ctor}
             (lift_ctor: C -> sum_ctorType Constructor1 Constructor2)
             (isLeft: bool)
             (A: @IT C) {struct A}: @IT LiftedConstructor :=
    match A with
    | Omega => Omega
    | Ctor c A => Ctor (inr (lift_ctor c)) (lift lift_ctor isLeft A)
    | Arrow A B => Arrow (lift lift_ctor isLeft A) (lift lift_ctor isLeft B)
    | Prod A B => Ctor (inl isLeft) (Prod (lift lift_ctor isLeft A) (lift lift_ctor isLeft B))
    | Inter A B => Inter (lift lift_ctor isLeft A) (lift lift_ctor isLeft B)
    end.

  Definition lift1 := lift inl true.
  Definition lift2 := lift inr false.

  Lemma lift_arrow_hom {C: ctor}: forall lift_ctor isLeft, ITHomomorphism.arrow_hom C _ (lift lift_ctor isLeft).
  Proof. done. Qed.

  Lemma lift_inter_hom {C: ctor}: forall lift_ctor isLeft, ITHomomorphism.inter_hom C _ (lift lift_ctor isLeft).
  Proof. done. Qed.

  Lemma lift_arrow_preimage {C: ctor}: forall lift_ctor isLeft, ITHomomorphism.arrow_preimage C _ (lift lift_ctor isLeft).
  Proof.
    move => ? ?.
    elim => // A1 IH1 A2 IH2 /orP [].
    - by move => /IH1 /= ->.
    - move => /IH2 /= ->.
        by rewrite orbT.
  Qed.

  Lemma lift_omega_hom {C: ctor}: forall lift_ctor isLeft, ITHomomorphism.omega_hom C _ (lift lift_ctor isLeft).
  Proof. done. Qed.

  Fixpoint unlift {C: ctor}
           (unlift_ctor: sum_ctorType Constructor1 Constructor2 -> option C)
           (A: @IT LiftedConstructor) {struct A}: option (@IT C) :=
    match A with
    | Omega => Some Omega
    | Ctor (inl _) (Prod A B) =>
      obind (fun A => omap (Prod A) (unlift unlift_ctor B))
            (unlift unlift_ctor A)
    | Ctor (inr c) A =>
      obind (fun c => omap (Ctor c) (unlift unlift_ctor A))
            (unlift_ctor c)
    | Arrow A B =>
      obind (fun A => omap (Arrow A) (unlift unlift_ctor B))
            (unlift unlift_ctor A)
    | Inter A B =>
      obind (fun A => omap (Inter A) (unlift unlift_ctor B))
            (unlift unlift_ctor A)
    | _ => None
    end.

  Lemma unlift_lift {C: ctor}: forall lift_ctor isLeft unlift_ctor,
      pcancel lift_ctor unlift_ctor ->
      pcancel (@lift C lift_ctor isLeft) (unlift unlift_ctor).
  Proof.
    move => lift_ctor isLeft unlift_ctor unlift_lift_ctor.
    elim => //.
    - move => ? ? /=.
        by rewrite unlift_lift_ctor /= => ->.
    - by move => /= ? -> ? ->.
    - by move => /= ? -> ? ->.
    - by move => /= ? -> ? ->.
  Qed.

  Definition unlift_ctor1: sum_ctorType Constructor1 Constructor2 -> option Constructor1 :=
    (fun c => if c is inl x then Some x else None).
  Definition unlift1 := unlift unlift_ctor1.

  Definition unlift_ctor2: sum_ctorType Constructor1 Constructor2 -> option Constructor2 :=
    (fun c => if c is inr x then Some x else None).
  Definition unlift2 := unlift unlift_ctor2.

  Lemma unlift_ctor1_inl: pcancel inl unlift_ctor1.
  Proof. done. Qed.

  Lemma unlift_ctor2_inr: pcancel inr unlift_ctor2.
  Proof. done. Qed.

  Lemma lift_map_bigcap {C: ctor}:
    forall lift_ctor isLeft (Delta: seq (@IT C)),
      lift lift_ctor isLeft (\bigcap_(A_i <- Delta) A_i) =
      \bigcap_(A_i <- map (lift lift_ctor isLeft) Delta) A_i.
  Proof.
    move => lift_ctor isLeft.
    elim => // A1.
    case => // A2 Delta IH.
      by rewrite bigcap_cons [X in _ = X]bigcap_cons -/(map _) -IH.
  Qed.    

  Lemma lift_cast_ctor {C: ctor}:
    forall lift_ctor isLeft,
      (forall c1 c2, [ctor c1 <= c2] = [ctor (lift_ctor c1) <= (lift_ctor c2)]) ->
      forall d (B A: @IT C), cast (lift lift_ctor isLeft (Ctor d B)) (lift lift_ctor isLeft A) =
                        map (lift lift_ctor isLeft) (cast (Ctor d B) A).
  Proof.
    move => lift_ctor isLeft lift_ctor_hom d B.
    elim => //.
    - move => c A _.
      rewrite /cast /=.
      move: (lift_ctor_hom c d).
      rewrite [X in if X then _ else _]/[ctor _ <= _] /=.
        by case: [ctor c <= d] => <-.
    - move => A1 IH1 A2 IH2.
        by rewrite cast_inter // map_cat -IH1 -IH2 cast_inter.
  Qed.

  Lemma isOmega_lift {C: ctor}: forall lift_ctor isLeft (A: @IT C), isOmega A = isOmega (lift lift_ctor isLeft A).
  Proof.
    move => lift_ctor isLeft.
      by elim => //= ? -> ? ->.
  Qed.

  Lemma lift_cast_arr {C: ctor}:
    forall lift_ctor isLeft,
    forall (B1 B2 A: @IT C), cast (lift lift_ctor isLeft (B1 -> B2)) (lift lift_ctor isLeft A) =
                        (map (fun AB => (lift lift_ctor isLeft AB.1, lift lift_ctor isLeft AB.2)) (cast (B1 -> B2) A)).
  Proof.
    move => lift_ctor isLeft B1 B2.
    move: (fun A1 A2 => cast_inter _ A1 A2 (B1 -> B2)).
    move: (fun A1 A2 => cast_inter _ A1 A2 (lift lift_ctor isLeft (B1 -> B2))).
    rewrite /cast -isOmega_lift /=.
    case isOmega__B2: (isOmega B2) => //.
    move => cast_eq1 cast_eq2.
    elim => //= A1 IH1 A2 IH2.
      by rewrite cast_eq1 // cast_eq2 // IH1 IH2 map_cat.
  Qed.

  Lemma lift_cast_prod {C: ctor}:
    forall lift_ctor isLeft,
    forall (B1 B2 A: @IT C), cast (lift lift_ctor isLeft (B1 \times B2)) (lift lift_ctor isLeft A) =
                        (map (fun AB => (Prod (lift lift_ctor isLeft AB.1)
                                           (lift lift_ctor isLeft AB.2))) (cast (B1 \times B2) A)).
  Proof.
    move => lift_ctor isLeft B1 B2.
    elim => //.
    - move => A1 _ A2 _ /=.
        by rewrite /cast /= preorder_reflexive.
    - move => A1 IH1 A2 IH2 /=.
        by rewrite cast_inter // IH1 IH2 -map_cat cast_inter.
  Qed.

  Lemma cast_bigcap_cat {C: ctor}:
    forall (A: @IT C) Delta1 Delta2,
      ~~isOmega A ->
      cast A (\bigcap_(A_i <- Delta1 ++ Delta2) A_i) =
      cast A (\bigcap_(A_i <- Delta1) A_i) ++ cast A (\bigcap_(A_i <- Delta2) A_i).
  Proof.
    move => A.
    elim.
    - move => Delta2 /negbTE.
        by rewrite /cast /= => ->.
    - move => B1 Delta1 IH Delta2 disprf.
      move: IH (IH Delta2 disprf) => _.
      case: Delta1.
      + case: Delta2.
        * by rewrite /cast (negbTE disprf) /= cats0.
        * move => ? ? /=.
            by rewrite cast_inter.
      + move => ? ? /=.
        rewrite cast_inter // cast_inter // => ->.
          by rewrite catA.
  Qed.

  Lemma lift_cast_inter_prod {C: ctor}:
    forall lift_ctor isLeft,
    forall (B1 B2 A: @IT C),
      cast (lift lift_ctor isLeft B1 \times lift lift_ctor isLeft B2)
           (\bigcap_(A__i <- cast (@Ctor LiftedConstructor (inl isLeft)
                                       (lift lift_ctor isLeft B1 \times lift lift_ctor isLeft B2))
                        (lift lift_ctor isLeft A)) A__i) =
      map (fun AB => (lift lift_ctor isLeft AB.1,
                   lift lift_ctor isLeft AB.2))
          (cast (B1 \times B2) A).
  Proof.
    move => lift_ctor isLeft B1 B2.
    elim => //.
    - move => A1 _ A2 _.
        by rewrite /cast /= preorder_reflexive.
    - move => A1 IH1 A2 IH2.
        by rewrite /= cast_inter // cast_inter // cast_bigcap_cat // IH1 IH2 map_cat.
  Qed.

  Lemma map_nilp {a b: Type}: forall (f: a -> b) xs, nilp (map f xs) = nilp xs.
  Proof. by move => ? []. Qed. 

  Lemma lift_subtype_hom {C: ctor}: 
    forall lift_ctor isLeft unlift_ctor,
      (forall c1 c2, [ctor c1 <= c2] = [ctor (lift_ctor c1) <= (lift_ctor c2)]) ->
      pcancel lift_ctor unlift_ctor ->
      ITHomomorphism.subtype_hom C _ (lift lift_ctor isLeft).
  Proof.
    move => lift_ctor isLeft unlift_ctor lift_hom unlift_lift_ctor A B.
    move: (total _ [subty A of B]).
    move => /(Types.Domain_ind _ (fun i =>
                                   match i with
                                   | [ subty A of B] =>
                                     [ bcd (A) <= B] <->
                                     [ bcd (lift lift_ctor isLeft A) <= lift lift_ctor isLeft B]
                                   | [ tgt_for_srcs_gte B1 in Delta] =>
                                     forall Delta',
                                       Types.Semantics [tgt_for_srcs_gte B1 in Delta] [check_tgt Delta'] <->
                                       Types.Semantics [tgt_for_srcs_gte (lift lift_ctor isLeft B1) in
                                                           (map (fun AB => (lift lift_ctor isLeft AB.1,
                                                                         lift lift_ctor isLeft AB.2)) Delta)]
                                                       [check_tgt (map (lift lift_ctor isLeft) Delta')]
                                   end)) res.
    apply: res; move: A B => _ _.
    - by move => ?; split => /=.
    - move => A d B _ IH.
      split.
      + move => /subty_complete /SubtypeMachine_inv.
        move => /(fun prf => prf (fun i r =>
                                match i, r with
                                | [subty A of Ctor d B], Return true =>
                                  [bcd (lift lift_ctor isLeft A) <= lift lift_ctor isLeft (Ctor d B)]
                                | _, _ => True
                                end)) res.
        apply: res.
        case; last by rewrite andbF.
        move => /subty__sound /IH /subty_complete prf.
        case canCast: (~~(nilp (cast (Ctor d B) A))) => //=.
        apply: subty__sound.
        have: (true = ~~(nilp (cast (lift lift_ctor isLeft (Ctor d B)) (lift lift_ctor isLeft A))) && true).
        { move: canCast.
            by rewrite lift_cast_ctor // map_nilp => ->. }
        move => ->.
        apply: step__Ctor.
          by rewrite lift_cast_ctor // -lift_map_bigcap.
      + move => /= /subty_complete /SubtypeMachine_inv.
        move => /(fun prf => prf (fun i r =>
                                match i, r with
                                | [subty A of Ctor d B], Return true =>
                                  if (unlift unlift_ctor A) is Some A
                                  then if (unlift unlift_ctor (Ctor d B)) is Some B
                                       then [bcd A <= B]
                                       else True
                                  else True
                                | _, _ => True
                                end)).
        rewrite unlift_lift //= unlift_lift_ctor /= unlift_lift //=.
        move => res.
        apply: res.
        case; last by rewrite andbF.
        rewrite lift_cast_ctor // map_nilp -lift_map_bigcap.
        move => /subty__sound /IH /subty_complete prf.
        case canCast: (~~(nilp (cast (Ctor d B) A))) => //=.
        apply /subty__sound.
        rewrite -canCast -[X in Return X]andbT.
          by apply: step__Ctor.
    - move => A B1 B2 _ IH1 _ IH2.
      split.
      + move => /subty_complete /SubtypeMachine_inv.
        move => /(fun prf => prf (fun i r =>
                                match i, r with
                                | [subty A of B1 -> B2], Return true =>
                                  [bcd (lift lift_ctor isLeft A) <= lift lift_ctor isLeft (B1 -> B2)]
                                | _, _ => True
                                end)) res.
        apply: res.
        move => Delta.
        case isOmega__B2: (isOmega B2) => /=.
        * move => *.
          apply /subty__sound.
          apply: subty__Omega.
            by rewrite /= -isOmega_lift isOmega__B2.
        * case => // prf1 prf2.
          apply: subty__sound.
          rewrite -[X in Return X]orFb -isOmega__B2 (isOmega_lift lift_ctor isLeft).
          apply: (step__Arr (Delta := map (lift lift_ctor isLeft) Delta)).
          ** rewrite lift_cast_arr.
               by apply /IH1.
          ** rewrite -lift_map_bigcap.
             apply /subty_complete.
             apply /IH2 => //.
               by apply /subty__sound.
      + move => /= /subty_complete /SubtypeMachine_inv.
        move => /(fun prf => prf (fun i r =>
                                match i, r with
                                | [subty A of B], Return true =>
                                  if (unlift unlift_ctor A) is Some A
                                  then if (unlift unlift_ctor B) is Some B
                                       then [bcd A <= B]
                                       else True
                                  else True
                                | _, _ => True
                                end)).
        do 3 rewrite unlift_lift //=.
        move => res.
        apply: res.
        move => Delta.
        rewrite -isOmega_lift.
        case isOmega__B2: (isOmega B2).
        * move => *.
          apply /subty__sound.
            by apply: subty__Omega.
        * case => //.
          rewrite lift_cast_arr.
          move => prf1.
          move: (subtype_machine _ [ tgt_for_srcs_gte B1 in cast (B1 -> B2) A]) => [] r prf12.
          move: (inv_tgt_for_srcs_gte_check_tgt _ prf12) => r__eq.
          move: prf12.
          rewrite r__eq => prf12.
          move: (prf12) => /IH1 /(Types.Semantics_functional _ _ _ _ prf1) [] ->.
          rewrite -lift_map_bigcap.
          move => /subty__sound /(proj2 (IH2 _ prf12)) /subty_complete prf2.
          rewrite orbT.
          apply /subty__sound.
          rewrite -[X in Return X](orbT false) -isOmega__B2.
            by apply: step__Arr; first by exact prf12.
    - move => B A Delta _ IH1 _ IH2 Delta'.
      split.
      + move => /SubtypeMachine_inv.
        move => /(fun prf => prf (fun i r =>
                                match i, r with
                                | [tgt_for_srcs_gte B in Delta], [check_tgt Delta'] =>
                                  Types.Semantics [tgt_for_srcs_gte (lift lift_ctor isLeft B) in
                                                      map (fun AB => (lift lift_ctor isLeft AB.1,
                                                                   lift lift_ctor isLeft AB.2)) Delta]
                                                  [check_tgt (map (lift lift_ctor isLeft) Delta')]
                                | _, _ => True
                                end)) res.
        apply: res.
        move: Delta' => _ Delta'.
        case.
        * move => /subty__sound /IH1 /subty_complete prf1 /IH2 prf2.
            by apply: (step__chooseTgt (r := true)).
        * move => disprf.
          have prf1: (Types.Semantics [subty (lift lift_ctor isLeft B) of lift lift_ctor isLeft A.1]
                                      (Return false)).
          { move: (subtype_machine _ [subty (lift lift_ctor isLeft B) of lift lift_ctor isLeft A.1]) => [] r prf1.
            move: (inv_subtyp_return _ prf1) => r__eq.
            move: prf1.
            rewrite r__eq.
            move: r__eq => _.
            case: r => //.
            case => //.
              by move => /subty__sound /IH1 /subty_complete /(Types.Semantics_functional _ _ _ _ disprf) []. }
          move => /IH2 prf2.
            by apply: (step__chooseTgt (r := false)).
      + move => prf.
        move: (subtype_machine _ [subty B of A.1]) => [] r prf1.
        move: (inv_subtyp_return _ prf1) => r__eq.
        move: prf1.
        rewrite r__eq.
        move: r__eq.
        case: r => //.
        move: (subtype_machine _ [tgt_for_srcs_gte B in Delta]) => [] r2 prf2.
        move: (inv_tgt_for_srcs_gte_check_tgt _ prf2) => r2__eq.
        move: prf2.
        rewrite r2__eq.
        move => prf2.
        move: (prf2) => /IH2 prf21.
        case.
        * move => _ prf1.
          move: (prf1) => /subty__sound /IH1 /subty_complete.
          move /(fun prf1 => step__chooseTgt (A := (lift lift_ctor isLeft A.1, lift lift_ctor isLeft A.2))
                                              (r := true)
                                              prf1 prf21).
          move => /(Types.Semantics_functional _ _ _ _ prf) [].
          move: prf => _.
          case: Delta' => // A2 Delta' [] /(f_equal (unlift unlift_ctor)).
          rewrite unlift_lift // unlift_lift //.
          move => [] -> Delta'__eq.
          apply: (step__chooseTgt (r := true)) => //.
          move: prf21.
          rewrite -Delta'__eq.
            by move => /IH2.
        * move => _ disprf.
          have prf11: (Types.Semantics [subty (lift lift_ctor isLeft B) of (lift lift_ctor isLeft A.1)] (Return false)).
          { case: (subtype_machine _ [subty (lift lift_ctor isLeft B) of (lift lift_ctor isLeft A.1)]) => [] r res.
            move: (inv_subtyp_return _ res) => r__eq.
            move: res.
            move: r__eq => ->.
            case: r => //.
              by case => // /subty__sound /IH1 /subty_complete /(Types.Semantics_functional _ _ _ _ disprf) []. }
          apply: (step__chooseTgt (r := false)) => //.
          apply /IH2.
          move: prf => /SubtypeMachine_inv /=.
          move => /(fun prf => prf (fun i r =>
                                  match i, r with
                                  | [tgt_for_srcs_gte B in [:: _ & Delta]], [check_tgt Delta''] =>
                                    Types.Semantics [ tgt_for_srcs_gte B in Delta]
                                                    [ check_tgt Delta'']
                                  | _, _ => True
                                  end)) res.
          apply: res.
          move => Delta'' r22 /(Types.Semantics_functional _ _ _ _ prf11) [] <-.
            by move => /(Types.Semantics_functional _ _ _ _ prf21) [] <-.
    - move => B Delta'.
      split.
      + by move => /emptyDoneTgt -> /=.
      + move => /= /emptyDoneTgt.
          by case: Delta' => //.
    - move => A B1 B2 _ IH1 _ IH2.
      split.
      + move => /subty_complete /SubtypeMachine_inv.
        move => /(fun prf => prf (fun i r =>
                                match i, r with
                                | [subty A of B1 \times B2], Return true =>
                                  [bcd (lift lift_ctor isLeft A) <= lift lift_ctor isLeft (B1 \times B2)]
                                | _, _ => True
                                end)) res.
        apply: res.
        do 2 (case => //;  last by rewrite andbF).
        move => /subty__sound /IH1 /subty_complete prf1.
        move => /subty__sound /IH2 /subty_complete prf2.
        case canCast: (~~(nilp (cast (B1 \times B2) A))) => //=.
        apply: subty__sound.
        have: (true = ~~(nilp (cast (lift lift_ctor isLeft (B1 \times B2)) (lift lift_ctor isLeft A))) && true).
        { move: canCast.
            by rewrite lift_cast_prod // map_nilp => ->. }
        move => ->.
        apply: step__Ctor.
        have: (true =  ~~ nilp (cast ((lift lift_ctor isLeft B1) \times (lift lift_ctor isLeft B2))
                                     (\bigcap_(A__i <- cast (@Ctor LiftedConstructor
                                                                 (inl isLeft)
                                                                 (lift lift_ctor isLeft B1 \times
                                                                       lift lift_ctor isLeft B2))
                                                  (lift lift_ctor isLeft A)) A__i)) && true && true).
        { by rewrite lift_cast_inter_prod map_nilp canCast. }
        move => ->.
        apply: step__Prod; rewrite lift_cast_inter_prod.
        * rewrite -map_comp.
          rewrite (@eq_map _ _ ([eta fst] \o (fun AB => (lift lift_ctor isLeft AB.1, lift lift_ctor isLeft AB.2)))
                           (fun AB => lift lift_ctor isLeft AB.1)) //.
          rewrite map_comp (@map_comp _ _ _ id (lift lift_ctor isLeft)) -lift_map_bigcap -map_comp.
            by exact prf1.
        * rewrite -map_comp.
          rewrite (@eq_map _ _ ([eta snd] \o (fun AB => (lift lift_ctor isLeft AB.1, lift lift_ctor isLeft AB.2)))
                           (fun AB => lift lift_ctor isLeft AB.2)) //.
          rewrite map_comp (@map_comp _ _ _ id (lift lift_ctor isLeft)) -lift_map_bigcap -map_comp.
            by exact prf2.
      + move => /subty_complete /SubtypeMachine_inv /=.
        move => /(fun prf => prf (fun i r =>
                                match i, r with
                                | [subty A of Ctor c B], (Return true) =>
                                  ~~(nilp (cast (Ctor c B) A)) /\
                                  Types.Semantics [subty (\bigcap_(A_i <- cast (Ctor c B) A) A_i) of B] (Return true)
                                | _, _ => True
                                end)) prf.
        have: (~~nilp (cast (@Ctor LiftedConstructor (inl isLeft)
                                  (lift lift_ctor isLeft B1 \times lift lift_ctor isLeft B2))
                            (lift lift_ctor isLeft A)) /\
               Types.Semantics [ subty \bigcap_(A_i <- cast
                                                    (@Ctor LiftedConstructor (inl isLeft)
                                                          (lift lift_ctor isLeft B1 \times
                                                                lift lift_ctor isLeft B2))
                                                    (lift lift_ctor isLeft A)) A_i
                                       of lift lift_ctor isLeft B1 \times lift lift_ctor isLeft B2]
                               (Return true)).
        { apply: prf.
          case; last by rewrite andbF.
          by case: (~~nilp (cast (@Ctor LiftedConstructor (inl isLeft)
                                        (lift lift_ctor isLeft B1 \times lift lift_ctor isLeft B2))
                                 (lift lift_ctor isLeft A))). }
        move: prf => _ [] canCast1.
        move => /SubtypeMachine_inv /=.
        move => /(fun prf => prf (fun i r =>
                                match i, r with
                                | [subty A of B1 \times B2], (Return true) =>
                                  ~~(nilp (cast (B1 \times B2) A)) /\
                                  Types.Semantics [subty (\bigcap_(A_i <- cast (B1 \times B2) A) A_i.1) of B1]
                                                  (Return true) /\
                                  Types.Semantics [subty (\bigcap_(A_i <- cast (B1 \times B2) A) A_i.2) of B2]
                                                  (Return true)
                                | _, _ => True
                                end)) prf.
        have: (~~nilp (cast (lift lift_ctor isLeft B1 \times lift lift_ctor isLeft B2)
                            (\bigcap_(A_i <- cast (@Ctor LiftedConstructor (inl isLeft)
                                                        (lift lift_ctor isLeft B1 \times lift lift_ctor isLeft B2))
                                          (lift lift_ctor isLeft A)) A_i)) /\
               Types.Semantics [ subty \bigcap_(A_i <- cast (lift lift_ctor isLeft B1 \times lift lift_ctor isLeft B2)
                                                    (\bigcap_(A_i <- cast (@Ctor LiftedConstructor (inl isLeft)
                                                                                (lift lift_ctor isLeft B1 \times
                                                                                      lift lift_ctor isLeft B2))
                                                                  (lift lift_ctor isLeft A)) A_i))
                                       A_i.1 of lift lift_ctor isLeft B1] 
                               (Return true) /\
               Types.Semantics [ subty \bigcap_(A_i <- cast (lift lift_ctor isLeft B1 \times lift lift_ctor isLeft B2)
                                                    (\bigcap_(A_i <- cast (@Ctor LiftedConstructor (inl isLeft)
                                                                                (lift lift_ctor isLeft B1 \times
                                                                                      lift lift_ctor isLeft B2))
                                                                  (lift lift_ctor isLeft A)) A_i))
                                       A_i.2 of lift lift_ctor isLeft B2]
                               (Return true)).
        { apply: prf.
          do 2 (case; last by rewrite andbF).
          by case: (~~(nilp (cast (lift lift_ctor isLeft B1 \times lift lift_ctor isLeft B2)
                                  (\bigcap_(A_i <- cast (@Ctor LiftedConstructor (inl isLeft)
                                                              (lift lift_ctor isLeft B1 \times lift lift_ctor isLeft B2))
                                                (lift lift_ctor isLeft A)) A_i)))). }
        move: prf => _.
        move => [] canCast2 [] prf1 prf2.
        apply: subty__sound.
        have: (true = ~~(nilp (cast (B1 \times B2) A)) && true && true).
        { move: canCast2.
            by rewrite lift_cast_inter_prod map_nilp => ->. }
        move => ->.
        apply: step__Prod.
        * apply: subty_complete.
          apply /IH1.
          apply: subty__sound.
          rewrite (map_comp id fst) lift_map_bigcap -map_comp -map_comp /(_ \o _).
          move: prf1.
            by rewrite lift_cast_inter_prod -(map_comp fst).
        * apply: subty_complete.
          apply /IH2.
          apply: subty__sound.
          rewrite (map_comp id snd) lift_map_bigcap -map_comp -map_comp /(_ \o _).
          move: prf2.
            by rewrite lift_cast_inter_prod -(map_comp snd).
    - move => A B1 B2 _ IH1 _ IH2.
      split.
      + move => prf.
        move: (BCD__Trans _ prf BCD__Lub2) => /IH2.
        move: (BCD__Trans _ prf BCD__Lub1) => /IH1.
          by apply: BCD__Glb.
      + move => prf.
        move: (BCD__Trans _ prf BCD__Lub2) => /IH2.
        move: (BCD__Trans _ prf BCD__Lub1) => /IH1.
          by apply: BCD__Glb.
  Qed.
        
  Lemma lift1_subtype_hom: ITHomomorphism.subtype_hom _ _ lift1.
  Proof. by apply: (lift_subtype_hom _ _ unlift_ctor1). Qed.

  Lemma lift2_subtype_hom: ITHomomorphism.subtype_hom _ _ lift2.
  Proof. by apply: (lift_subtype_hom _ _ unlift_ctor2). Qed.

  Fixpoint inPartition (checkPartition1: bool) (A: @IT LiftedConstructor) {struct A}: bool :=
    match A with
    | Omega => true
    | Ctor (inr (inl _)) A => checkPartition1 && inPartition checkPartition1 A
    | Ctor (inr (inr _)) A => (~~checkPartition1) && inPartition checkPartition1 A
    | Ctor (inl true) (A \times B) => checkPartition1 && inPartition checkPartition1 A && inPartition checkPartition1 B
    | Ctor (inl false) (A \times B) => (~~checkPartition1) && inPartition checkPartition1 A && inPartition checkPartition1 B
    | A -> B => inPartition checkPartition1 A && inPartition checkPartition1 B
    | A \cap B => inPartition checkPartition1 A && inPartition checkPartition1 B
    | _ => false
    end.

  Lemma inPartition_lift1: forall A, inPartition true (lift1 A).
  Proof. elim => //=; by move => ? -> ? ->. Qed.

  Lemma inPartition_lift2: forall A, inPartition false (lift2 A).
  Proof. elim => //=; by move => ? -> ? ->. Qed.

  Lemma dist_arr_inPartition: forall checkPartition1,
      SplitTypeUniverse.dist_arr_partition LiftedConstructor (inPartition checkPartition1).
  Proof. done. Qed.

  Lemma dist_inter_inPartition: forall checkPartition1,
      SplitTypeUniverse.dist_inter_partition LiftedConstructor (inPartition checkPartition1).
  Proof. done. Qed.

  Lemma omega_inPartition: forall checkPartition1,
      SplitTypeUniverse.omega_partition LiftedConstructor (inPartition checkPartition1).
  Proof. done. Qed.

  Lemma inPartition_cast_ctor:
    forall checkPartition1 A c B,
      inPartition checkPartition1 A ->
      inPartition (~~checkPartition1) (Ctor c B) ->
      nilp (cast (Ctor c B) A).
  Proof.
    move => checkPartition1 A c B.
    elim: A => //.
    - rewrite /cast /=.
      case; case => //.
      + case => //.
        move => ? ? _.
        case: c; case.
        * by case: B => // ? ? /andP [] /andP [] ->.
        * by case: B => // ? ? /andP [] /andP [] ->.
        * by move => ? /andP [] /andP [] ->.
        * by move => ? /andP [] /andP [] ->.
      + case => //.
        move => ? ? _.
        case: c; case.
        * by case: B => // ? ? /andP [] /andP [] ->.
        * by case: B => // ? ? /andP [] /andP [] ->.
        * by move => ? /andP [] /andP [] ->.
        * by move => ? /andP [] /andP [] ->.
      + move => ? ? _ /andP [] ->.
          by case: c => //; case.
      + move => ? ? _ /andP [] ->.
          by case: c => //; case.
    - move => A1 IH1 A2 IH2 /andP [] /IH1 prf1 /IH2 prf2 inprf__cB.
      rewrite cast_inter //.
      move: (prf1 inprf__cB) (prf2 inprf__cB).
        by rewrite /nilp size_cat => /eqP -> /eqP ->.
  Qed.

  Lemma inPartition_bigcap: forall checkPartition1 Delta,
      all (inPartition checkPartition1) Delta ->
      inPartition checkPartition1 (\bigcap_(A_i <- Delta) A_i).
  Proof.
    move => checkPartition1.
    elim => // A1 [].
    - by move => _; rewrite all_seq1.
    - by move => A2 Delta IH /andP [] /= -> /IH ->.
  Qed.

  Lemma inPartition_cast_tgts: forall checkPartition1 A B1 B2,
      inPartition checkPartition1 A ->
      all (inPartition checkPartition1) (map snd (cast (B1 -> B2) A)).
  Proof.
    move => checkPartition1 A B1 B2.
    case isOmega__B2: (isOmega B2).
    - by rewrite /cast /= isOmega__B2.
    - elim: A; try by rewrite /cast /= isOmega__B2.
      + move => ? ? ? ? /andP [] _.
          by rewrite /cast /= isOmega__B2 /= /inPartition => ->.
      + move => A1 IH1 A2 IH2 /andP [] /IH1 prf1 /IH2 prf2.
        rewrite cast_inter; last by rewrite /= isOmega__B2.
          by rewrite map_cat all_cat prf1 prf2.
  Qed.

  Lemma tgt_for_srcs_gte_cat {C: ctor}:
    forall (B: @IT C) Delta1 Delta2 Delta,
      Types.Semantics [tgt_for_srcs_gte B in Delta1 ++ Delta2] [check_tgt Delta] ->
      exists Delta1' Delta2',
        Types.Semantics [tgt_for_srcs_gte B in Delta1] [check_tgt Delta1'] /\
        Types.Semantics [tgt_for_srcs_gte B in Delta2] [check_tgt Delta2'] /\
        Delta1' ++ Delta2' = Delta.
  Proof.
    move => B.
    elim.
    - move => Delta2 Delta prf.
      (exists [::], Delta); by split.
    - move => A Delta1 IH Delta2 Delta /= /SubtypeMachine_inv.
      move => /(fun prf => prf (fun i r =>
                              match i, r with
                              | [tgt_for_srcs_gte B in [:: A & Deltas]], [check_tgt Delta'] =>
                                exists r, Types.Semantics [ subty B of A.1] (Return r) /\
                                     Types.Semantics [tgt_for_srcs_gte B in Deltas]
                                                     [check_tgt (if r then behead Delta' else Delta')] /\
                                     Delta' = (if r then [:: A.2 & behead Delta'] else Delta')
                              | _, _ => True
                              end)) res.
      have: exists r, Types.Semantics [ subty B of A.1] (Return r) /\
                 Types.Semantics [tgt_for_srcs_gte B in Delta1 ++ Delta2]
                                 [check_tgt (if r then behead Delta else Delta)] /\
                 Delta = (if r then [:: A.2 & behead Delta] else Delta).
      { apply: res.
        move => Delta' r prf1 prf2.
        exists r; split => //; last by (split; move: prf1 => _; case: r). }
      move => [].
      case.
      + move => [] prf1 [] /IH [] Delta1' [] Delta2' [] prf21 [] prf22 prf23 prf24.
        exists [:: A.2 & Delta1'], Delta2'; split; last split => //.
        * by apply: (step__chooseTgt (r := true)).
        * by rewrite /= prf23 prf24.
      + move => [] prf1 [] /IH [] Delta1' [] Delta2' [] prf21 [] prf22 prf23 _.
        exists Delta1', Delta2'; split => //.
          by apply: (step__chooseTgt (r := false)).
  Qed.

  Lemma st_omega_inPartition: forall checkPartition1 A B,
      inPartition checkPartition1 A -> inPartition (~~checkPartition1) B -> [bcd A <= B] -> isOmega B.
  Proof.
    move => checkPartition1 A B.
    move: (total  _ [subty A of B]).
    move => /(Types.Domain_ind _ (fun i => match i with
                                       | [subty A of B] =>
                                         (inPartition checkPartition1 A ->
                                          inPartition (~~checkPartition1) B ->
                                          [bcd A <= B] -> isOmega B)%type
                                       | _ => True
                                       end)) prf.
    apply: prf; move: A B => _ _ //.
    - move => A c B _ /= IH inprf__A inprf__cB /subty_complete /SubtypeMachine_inv.
      move => /(fun prf => prf (fun i r => match i, r return Prop with
                                    | [subty A of B], Return true => false
                                    | _, _ => True
                                    end)) res.
      apply: res.
        by rewrite (inPartition_cast_ctor checkPartition1 A c B inprf__A inprf__cB).
    - move => A B1 B2 _ _ IH1 IH2 /= inprf__A /andP [] _ inprf__B2 /subty_complete /SubtypeMachine_inv.
      move => /(fun prf => prf (fun i r => match i, r with
                                    | [subty A of B1 -> B2], Return true => isOmega B2
                                    | _, _ => True
                                    end)) res.
      apply: res.
      move => Delta r prf1.
      move: (fun leprf inprf__casted => IH2 Delta prf1 inprf__casted inprf__B2 leprf) => prf.
      case: r; last by case: (isOmega B2).
      move => /subty__sound /prf prf2.
      have: (inPartition checkPartition1 (\bigcap_(A_i <- Delta) A_i)).
      { apply: inPartition_bigcap.
        move: prf1 => /check_tgt_subseq /mem_subseq subprf.
        move: (inPartition_cast_tgts checkPartition1 A B1 B2  inprf__A) => /allP doneprf.
          by apply /allP => x /subprf /doneprf. }
        by move => /prf2 ->.
    - move => A B1 B2 _ IH1 _ IH2 inprf__A /andP [] /(IH1 inprf__A) prf1 /(IH2 inprf__A) prf2 prf.
        by rewrite /= (prf1 (BCD__Trans _ prf BCD__Lub1)) (prf2 (BCD__Trans _ prf BCD__Lub2)).
  Qed.

  Lemma all_addAndFilter {C: ctor}: forall (P: @IT C -> bool) Delta A, all P Delta -> P A -> all P (addAndFilter _ Delta A).
  Proof.
    move => P.
    elim.
    - by move => /= ? _ ->.
    - move => B Delta IH A prfs prf__A /=.
      case: (checkSubtypes B A) => //.
      case: (checkSubtypes A B).
      + apply: IH => //.
          by move: prfs => /andP [].
      + by move: prfs => /andP [] /= -> /(fun prf => IH A prf prf__A) ->.
  Qed.

  Lemma primeComponents_inPartition: forall checkPartition1 A,
      inPartition checkPartition1 A -> all (inPartition checkPartition1) (primeFactors A).
  Proof.
    move => checkPartition1 A.
    rewrite /primeFactors.
    have: all (inPartition checkPartition1) [::] => //.
    have: (forall A, inPartition checkPartition1 A -> inPartition checkPartition1 (locked id A)) by rewrite -lock.
    move: id [::].
    move => contextualize.
    rewrite -(lock contextualize).
    move: A contextualize.
    apply: (fun prf A =>
              @Fix_F _ (fun A B => (size _ A) < (size _ B))%coq_nat
                     (fun A =>
                        forall contextualize Delta,
                          ((forall A, inPartition checkPartition1 A -> inPartition checkPartition1 (contextualize A)) ->
                           all (inPartition checkPartition1) Delta ->
                           inPartition checkPartition1 A ->
                           all (inPartition checkPartition1)
                               (primeFactors_rec _ A contextualize Delta))%type)
                     prf A
                     (well_founded_ltof _ (size _) A)).
    case => //.
    - move => _ contextualize Delta inprf__contextualize inprf__Delta _ /=.
      case: (isOmega (contextualize Omega)) => //.
      apply: all_addAndFilter => //.
        by apply: inprf__contextualize.
    - move => c A /=.
      case: c.
      + case.
        * case: A => // A1 A2 IH contextualize Delta inprf__contextualize inprf__Delta.
          move => /andP [] /andP [] check check__A1 check__A2.
          rewrite /primeFactors /=.
          apply IH => //.
          ** apply /leP.
             rewrite /= addnS ltnS.
             apply: leq_trans; last by apply: leq_addl.
               by apply: leq_addl.
          ** move => A prf.
             apply: inprf__contextualize.
               by rewrite /= prf check.
          ** apply: IH => //.
             *** apply /leP.
                 rewrite /= addnS ltnS.
                 apply: leq_trans; last by apply: leq_addl.
                   by apply: leq_addr.
             *** move => A prf.
                 apply: inprf__contextualize.
                   by rewrite /= prf check.
        * case: A => // A1 A2 IH contextualize Delta inprf__contextualize inprf__Delta.
          move => /andP [] /andP [] check check__A1 check__A2.
          rewrite /primeFactors /=.
          apply IH => //.
          ** apply /leP.
             rewrite /= addnS ltnS.
             apply: leq_trans; last by apply: leq_addl.
               by apply: leq_addl.
          ** move => A prf.
             apply: inprf__contextualize.
               by rewrite /= prf check.
          ** apply: IH => //.
             *** apply /leP.
                 rewrite /= addnS ltnS.
                 apply: leq_trans; last by apply: leq_addl.
                   by apply: leq_addr.
             *** move => A prf.
                 apply: inprf__contextualize.
                   by rewrite /= prf check.
      + case.
        * move => c IH contextualize Delta inprf__contextualize inprf__Delta.
          move => /andP [] check check__A.
          apply: IH => //.
          move => B inprf__B.
          apply: inprf__contextualize.
            by rewrite /= inprf__B check.
        * move => c IH contextualize Delta inprf__contextualize inprf__Delta.
          move => /andP [] check check__A.
          apply: IH => //.
          move => B inprf__B.
          apply: inprf__contextualize.
            by rewrite /= inprf__B check.
    - move => A1 A2 IH contextualize Delta inprf__contextualize inprf__Delta.
      move => /= /andP [] inprf__A1 inprf__A2.
      apply: IH => //.
      + apply /leP.
        rewrite /= ltnS.
          by apply: leq_addl.
      + move => A inprf__A.
        apply: inprf__contextualize.
          by rewrite /= inprf__A1 inprf__A.
    - move => A1 A2 IH contextualize Delta inprf__contextualize inprf__Delta.
      move => /= /andP [] inprf__A1 inprf__A2.
      apply IH => //.
      + apply /leP.
        rewrite /= ltnS.
          by apply: leq_addl.
      + apply: IH => //.
        apply /leP.
        rewrite /= ltnS.
          by apply: leq_addr.
  Qed.

  Lemma st_irrel_check_inPartition: forall checkPartition1,
      SplitTypeUniverse.st_irrel_partition _ (inPartition checkPartition1) (inPartition (~~checkPartition1)).
  Proof.
    move => checkPartition1 A B C inprf__A inprf__B inprf__C.
    move => /(fun prf => BCD__Trans C prf (primeFactors_geq C)) prf.
    apply: BCD__Trans; last by apply: primeFactors_leq.
    move: prf.
    move: (primeFactors_prime C).
    move: (primeComponents_inPartition _ C inprf__C).
    elim: (primeFactors C); first by rewrite /=.
    move => C1 Cs IH /andP [] inprf__C1 inprf__Cs  /andP [] prime__C1 prime__Cs.
    move => /(fun prf => BCD__Trans _ prf (bcd_cat_bigcap _ [:: C1] Cs)) prf.
    apply: BCD__Trans; last by apply (bcd_bigcap_cat _ [:: C1] Cs).
    apply: BCD__Glb.
    - move: (BCD__Trans _ prf BCD__Lub1).
      move => /(fun prf => primeComponentPrime _ _ _ _ prf (isPrimeComponentP prime__C1)).
      case => //.
      move => /(st_omega_inPartition _ _ _ inprf__B) omega_prf.
      apply: subty__sound.
      apply: subty__Omega.
      apply: omega_prf.
      move: inprf__C1.
      clear...
      case: checkPartition1 => //=.
    - apply: IH => //.
      apply: BCD__Trans; first by exact prf.
        by apply: BCD__Lub2.
  Qed.  

  Variable Combinator: finType.
  Variable (Ctxt1: Ctxt Combinator Constructor1) (Ctxt2: Ctxt Combinator Constructor2).

  Definition LiftedCtxt1: Ctxt Combinator LiftedConstructor := [ffun c => lift1 (Ctxt1 c) ].
  Definition LiftedCtxt2: Ctxt Combinator LiftedConstructor := [ffun c => lift2 (Ctxt2 c) ].
  Definition MergedCtxt: Ctxt Combinator LiftedConstructor := [ffun c => LiftedCtxt1 c \cap LiftedCtxt2 c].

  Lemma pure_LiftedCtxt1: SplitContextPair.pure_context Combinator LiftedConstructor LiftedCtxt1 (inPartition true).
  Proof.
    move => c.
    rewrite /LiftedCtxt2 ffunE.
      by apply: inPartition_lift1.
  Qed.

  Lemma pure_LiftedCtxt2: SplitContextPair.pure_context Combinator LiftedConstructor LiftedCtxt2 (inPartition false).
  Proof.
    move => c.
    rewrite /LiftedCtxt2 ffunE.
      by apply: inPartition_lift2.
  Qed.
End ContextCoproduct.


Definition sum1_itHomMixin (Constructor1 Constructor2: ctor):
    ITHomomorphism.mixin_of (Constructor.Pack Constructor1 (Constructor.class Constructor1))
                            (Constructor.Pack (LiftedConstructor Constructor1 Constructor2)
                                              (Constructor.class (LiftedConstructor Constructor1 Constructor2))).
Proof.
  move: (ITHomomorphism.Mixin _ _ (lift1 _ _) (lift1_subtype_hom _ _)
                              (@lift_arrow_hom _ Constructor2 Constructor1 inl true)
                              (@lift_inter_hom _ Constructor2 Constructor1 inl true)
                              (@lift_omega_hom _ Constructor2 Constructor1 inl true)
                              (@lift_arrow_preimage Constructor1 Constructor2 Constructor1 inl true)).
  by case: Constructor1.
Defined.

Canonical sum1_ITHomType {Constructor1 Constructor2: ctor} :=
  Eval hnf in ITHomType _ _ (sum1_itHomMixin Constructor1 Constructor2).

Definition sum2_itHomMixin (Constructor1 Constructor2: ctor):
    ITHomomorphism.mixin_of (Constructor.Pack Constructor2 (Constructor.class Constructor2))
                            (Constructor.Pack (LiftedConstructor Constructor1 Constructor2)
                                              (Constructor.class (LiftedConstructor Constructor1 Constructor2))).
Proof.
  move: (ITHomomorphism.Mixin _ _ (lift2 _ _) (lift2_subtype_hom _ _)
                              (@lift_arrow_hom Constructor1 Constructor2 Constructor2 inr false)
                              (@lift_inter_hom Constructor1 Constructor2 Constructor2 inr false)
                              (@lift_omega_hom Constructor1 Constructor2 Constructor2 inr false)
                              (@lift_arrow_preimage Constructor1 Constructor2 Constructor2 inr false)).
  by case: Constructor2.
Defined.

Canonical sum2_ITHomType {Constructor1 Constructor2: ctor} :=
  Eval hnf in ITHomType _ _ (sum2_itHomMixin Constructor1 Constructor2).

Definition sum_splitTypeUniverseMixin (Constructor1 Constructor2: ctor):
  SplitTypeUniverse.mixin_of (LiftedConstructor Constructor1 Constructor2) :=
  SplitTypeUniverse.Mixin (LiftedConstructor Constructor1 Constructor2)
                          (inPartition _ _ true) (inPartition _ _ false)
                          (dist_arr_inPartition _ _ true) (dist_arr_inPartition _ _ false)
                          (dist_inter_inPartition _ _ true) (dist_inter_inPartition _ _ false)
                          (omega_inPartition _ _ true) (omega_inPartition _ _ false)
                          (st_irrel_check_inPartition _ _ true) (st_irrel_check_inPartition _ _ false).

Canonical sum_splitTypeUniverseType {Constructor1 Constructor2: ctor} :=
  Eval hnf in SplitTypeUniverseType (LiftedConstructor Constructor1 Constructor2)
                                    (sum_splitTypeUniverseMixin Constructor1 Constructor2).
                          
Definition sum_splitCtxtPairMixin {Combinator: finType} {Constructor1 Constructor2: ctor}
           (Ctxt1: Ctxt Combinator Constructor1) (Ctxt2: Ctxt Combinator Constructor2):
  SplitContextPair.mixin_of (Finite.Pack (Finite.class Combinator) (let: Finite.Pack T _ _ := Combinator in T))
                            (SplitTypeUniverse.Pack
                               (LiftedConstructor Constructor1 Constructor2)
                               (SplitTypeUniverse.class (@sum_splitTypeUniverseType Constructor1 Constructor2))).
Proof.
  move: Ctxt1 Ctxt2.
  case: Combinator => T1 c T2.
  move => Ctxt1 Ctxt2.
  move: (SplitContextPair.Mixin (Finite.Pack c T1)
                                (@sum_splitTypeUniverseType Constructor1 Constructor2)
                                (LiftedCtxt1 _ _ _ [ffun c: Finite.Pack c T1 => Ctxt1 c])
                                (LiftedCtxt2 _ _ _ [ffun c : Finite.Pack c T1 => Ctxt2 c])
                                (pure_LiftedCtxt1 _ _ _ _) (pure_LiftedCtxt2 _ _ _ _)).
    by rewrite /LiftedConstructor /sum_splitTypeUniverseType.
Defined.

Definition sum_splitCtxtPairType {Combinator: finType} {Constructor1 Constructor2: ctor}
           (Ctxt1: Ctxt Combinator Constructor1) (Ctxt2: Ctxt Combinator Constructor2)  :=
  Eval hnf in SplitCtxtPairType Combinator
                                (LiftedConstructor Constructor1 Constructor2)
                                (sum_splitCtxtPairMixin Ctxt1 Ctxt2).

Section FCLITHomomorphism.
  Variable Combinator: finType.
  Variable f: itHom.

  Lemma bigcap_hom: forall Delta, f (\bigcap_(A_i <- Delta) A_i) = \bigcap_(A_i <- Delta) f A_i.
  Proof.
    elim.
    - by rewrite omega_hom.
    - move => A1 [] // A2  Delta IH.
        by rewrite bigcap_cons [X in _ = X]bigcap_cons -IH inter_hom.
  Qed.

  Lemma hom_arrow_cast:
    forall A, cast (Omega -> Omega \times Omega) (f A) =
         map (fun AB => (f AB.1, f AB.2)) (cast (Omega -> Omega \times Omega) A).
  Proof.
    elim.
    - by rewrite omega_hom.
    - move => c A _.
      move: (arrow_preimage f (Ctor c A)).
      elim: (f (Ctor c A)) => //.
      + by move => ? _ ? _ /(fun prf => prf isT).
      + move => fA1 IH1 fA2 IH2 notArrow.
        rewrite cast_inter // IH1; first rewrite IH2 //.
        * move => prf.
          apply: notArrow.
            by rewrite /= prf orbT.
        * move => prf.
          apply: notArrow.
            by rewrite /= prf.
    - move => ? _ ? _.
        by rewrite arrow_hom.
    - move => A1 _ A2 _.
      move: (arrow_preimage f (A1 \times A2)).
      elim: (f (A1 \times A2)) => //.
      + by move => ? _ ? _ /(fun prf => prf isT).
      + move => fA1 IH1 fA2 IH2 notArrow.
        rewrite cast_inter // IH1; first rewrite IH2 //.
        * move => prf.
          apply: notArrow.
            by rewrite /= prf orbT.
        * move => prf.
          apply: notArrow.
            by rewrite /= prf.
    - move => A1 IH1 A2 IH2.
        by rewrite cast_inter // inter_hom cast_inter // IH1 IH2 map_cat.
  Qed.

  Lemma minimalType_hom: forall (Gamma : Ctxt Combinator (domain_base f)) M,
      minimalType [ffun c => f (Gamma c)] M = f (minimalType Gamma M).
  Proof.
    move => Gamma M.
    elim: M.
    - move => c.
        by rewrite /minimalType ffunE.
    - move => M IH1 N IH2.
      rewrite /= IH1 IH2 /minimalArrowTgt bigcap_hom (map_comp id f).
      rewrite hom_arrow_cast.
      apply: f_equal.
      clear...
      elim: (cast (Omega -> Omega \times Omega) (minimalType Gamma M)).
      + move: (subtype_machine _ [ tgt_for_srcs_gte f (minimalType Gamma N) in [::]]) => [] r1 /SubtypeMachine_inv.
        move: (subtype_machine _ [ tgt_for_srcs_gte (minimalType Gamma N) in [::]]) => [] r2 /SubtypeMachine_inv.
        case: r2 => // [] [] // _.
          by case: r1 => // [] [] //.
      + move => [] A1 A2 Delta IH /=.
        move: (subtype_machine _ [ tgt_for_srcs_gte f (minimalType Gamma N) in
                                     [:: (f A1, f A2) & map (fun AB => (f AB.1, f AB.2)) Delta]]) => [] r1 /SubtypeMachine_inv.
        move: (subtype_machine _ [ tgt_for_srcs_gte (minimalType Gamma N) in
                                     [:: (A1, A2) & Delta]]) => [] r2 /SubtypeMachine_inv.
        case: r2 => // Delta2 prf2.
        case: r1 => // Delta1 prf1.
        have: (Delta1 = if (checkSubtypes (f (minimalType Gamma N)) (f A1))
                        then [:: f A2 & if subtype_machine _ [ tgt_for_srcs_gte f (minimalType Gamma N) in
                                                                 map (fun AB => (f AB.1, f AB.2)) Delta ]
                                                           is exist [check_tgt Delta] _
                                        then Delta else [::]]
                        else if subtype_machine _ [ tgt_for_srcs_gte f (minimalType Gamma N) in
                                                      map (fun AB => (f AB.1, f AB.2)) Delta ]
                                                is exist [check_tgt Delta] _
                             then Delta else [::]).
        { move: (prf1 (fun i r =>
                         match i, r with
                         | [tgt_for_srcs_gte B in [:: (A1, A2) & Delta]], [check_tgt Delta'] =>
                           Delta' = if (checkSubtypes B A1)
                                    then [:: A2 & if subtype_machine _ [ tgt_for_srcs_gte B in Delta ]
                                                                     is exist [check_tgt Delta] _
                                                  then Delta else [::]]
                                    else if subtype_machine _ [ tgt_for_srcs_gte B in Delta ]
                                                            is exist [check_tgt Delta] _
                                         then Delta else [::]
                         | _, _ => True
                         end)) => res.
          apply: res.
          move => Delta' r prf prfs /=.
          have: r = (checkSubtypes (f (minimalType Gamma N)) (f A1)).
          { move: prf.
            clear ...
            rewrite /checkSubtypes.
            move => /(Types.Semantics_functional).
            move: (subtype_machine _ [subty f (minimalType Gamma N) of f A1]) => [] v rel.
            move => /(fun prf => prf v rel) <-.
              by case: r. }
          move => ->.
          have: Delta' = (if subtype_machine _ [tgt_for_srcs_gte f (minimalType Gamma N) in
                                                   map (fun AB => (f AB.1, f AB.2)) Delta]
                                             is exist [check_tgt Delta] _
                          then Delta else [::]).
          { move: prfs.
            clear...
            move => /(Types.Semantics_functional).
            move: (subtype_machine _ [tgt_for_srcs_gte f (minimalType Gamma N) in
                                                       map (fun AB => (f AB.1, f AB.2)) Delta]) => [] v rel.
              by move => /(fun prf => prf v rel) <-. }
            by move => <-. }
        move => ->.
        have: (Delta2 = if (checkSubtypes (minimalType Gamma N) A1)
                        then [:: A2 & if subtype_machine _ [ tgt_for_srcs_gte (minimalType Gamma N) in  Delta ]
                                                           is exist [check_tgt Delta] _
                                        then Delta else [::]]
                        else if subtype_machine _ [ tgt_for_srcs_gte (minimalType Gamma N) in Delta ]
                                                is exist [check_tgt Delta] _
                             then Delta else [::]).
        { move: (prf2 (fun i r =>
                         match i, r with
                         | [tgt_for_srcs_gte B in [:: (A1, A2) & Delta]], [check_tgt Delta'] =>
                           Delta' = if (checkSubtypes B A1)
                                    then [:: A2 & if subtype_machine _ [ tgt_for_srcs_gte B in Delta ]
                                                                     is exist [check_tgt Delta] _
                                                  then Delta else [::]]
                                    else if subtype_machine _ [ tgt_for_srcs_gte B in Delta ]
                                                            is exist [check_tgt Delta] _
                                         then Delta else [::]
                         | _, _ => True
                         end)) => res.
          apply: res.
          move => Delta' r prf prfs /=.
          have: r = (checkSubtypes (minimalType Gamma N) A1).
          { move: prf.
            clear ...
            rewrite /checkSubtypes.
            move => /(Types.Semantics_functional).
            move: (subtype_machine _ [subty (minimalType Gamma N) of A1]) => [] v rel.
            move => /(fun prf => prf v rel) <-.
              by case: r. }
          move => ->.
          have: Delta' = (if subtype_machine _ [tgt_for_srcs_gte (minimalType Gamma N) in Delta]
                                             is exist [check_tgt Delta] _
                          then Delta else [::]).
          { move: prfs.
            clear...
            move => /(Types.Semantics_functional).
            move: (subtype_machine _ [tgt_for_srcs_gte (minimalType Gamma N) in Delta]) => [] v rel.
              by move => /(fun prf => prf v rel) <-. }
            by move => <-. }
        move => ->.
        have: (checkSubtypes (minimalType Gamma N) A1 = checkSubtypes (f (minimalType Gamma N)) (f A1)).
        { apply /subtypeMachineP.
          case prf: (checkSubtypes (f (minimalType Gamma N)) (f A1)).
          - apply /(subtype_hom f).
              by apply /subtypeMachineP.
          - move => /(subtype_hom f) /subtypeMachineP.
              by rewrite prf. }
        move => <-.
        case: (checkSubtypes (minimalType Gamma N) A1).
        * by rewrite /= IH.
        * by rewrite IH.
  Qed.

  Lemma FCL__hom: forall (Gamma : Ctxt Combinator (domain_base f)) M A,
      FCL Gamma M A <-> FCL [ffun c => f (Gamma c)] M (f A).
  Proof.
    move => Gamma M A.
    split.
    - move => prf.
      elim /FCL_normalized_ind: M A / prf.
      + move => c.
          by rewrite -(ffunE (fun c => f (Gamma c))).
      + by move => c A prf /subtype_hom /(FCL__Sub _ prf).
      + move => M N A B _.
        rewrite arrow_hom.
        move => prf1 _ prf2.
          by apply: (FCL__MP _ prf1 prf2).
    - move fA__eq: (f A) => fA prf.
      move: A fA__eq.
      elim /FCL_normalized_ind: M fA / prf.
      + move => c A fA__eq.
        have: [bcd (f (Gamma c)) <= f A] by rewrite fA__eq ffunE.
          by move => /subtype_hom /(FCL__Sub _ FCL__Var).
      + move => c fA IH prf A fA__eq.
        move: prf.
        rewrite -fA__eq ffunE.
          by move => /subtype_hom /(FCL__Sub _ FCL__Var).
      + move => M N fA fB prf1 IH1 prf2 IH2.
        move: (FCL__MP _ prf1 prf2) => /(minimalType_minimal).
        rewrite minimalType_hom.
        move => le_prf A A__eq.
        apply: (FCL__Sub (minimalType Gamma (M @ N))).
        * by apply: minimalType_sound.
        * apply /(subtype_hom f).
            by rewrite A__eq.
  Qed.
End FCLITHomomorphism.

Section SplitContexts.
  Variable Gammas: splitCtxtPair.
  Implicit Type A B: @IT Gammas.
  Implicit Type M N: @Term Gammas.

  Lemma inPartition1_bigcap: forall Delta,
      @inPartition1 Gammas (\bigcap_(A_i <- Delta) A_i) = all (@inPartition1 Gammas) Delta.
  Proof.
    elim; first by rewrite omega_partition1.
    move => A1 []; first by rewrite /= andbT.
    move => A2 Delta IH.
      by rewrite dist_inter_partition1 IH.
  Qed.

  Lemma inPartition2_bigcap: forall Delta,
      @inPartition2 Gammas (\bigcap_(A_i <- Delta) A_i) = all (@inPartition2 Gammas) Delta.
  Proof.
    elim; first by rewrite omega_partition2.
    move => // A1 []; first by rewrite /= andbT.
    move => A2 Delta IH.
      by rewrite dist_inter_partition2 IH.
  Qed.

  Lemma inPartition1_minimalType: forall M, inPartition1 (minimalType (ctxt1 Gammas) M).
  Proof.
    elim.
    - by apply: pure_context1.
    - move => M IH1 N IH2.
      rewrite /= /minimalArrowTgt.
      move: (subtype_machine _ [ tgt_for_srcs_gte (minimalType (ctxt1 Gammas) N)
                                 in cast (Omega -> Omega \times Omega) (minimalType (ctxt1 Gammas) M) ]).
      move => [] [];
               first by (move => ? /SubtypeMachine_inv;
                                case: (cast (Omega -> Omega \times Omega) (minimalType (ctxt1 Gammas) M))).
      move => Delta.
      move /choose_tgt_subseq.
      move: IH2 IH1 Delta => _.
      elim: (minimalType (ctxt1 Gammas) M).
      + by move => /= ? ? /eqP -> /=.
      + by (move => /= ? ? ? _ _ /eqP -> /=; apply: omega_partition1).
      + move => A1 _ A2 _ prf Delta.
        move: prf.
        rewrite dist_arr_partition1 /cast /=.        
        case: Delta; first by (move => *; apply: omega_partition1).
        move => A2' Delta' /andP [] _ res.
        case A2__eq: (A2' == A2) => // /eqP ->.
          by rewrite (eqP A2__eq).
      + move => ? ? ? ? ? _ /= /eqP ->; by apply: omega_partition1.
      + move => A1 IH1 A2 IH2.
        rewrite dist_inter_partition1.
        move => /andP [] /IH1 prf1 /IH2 prf2.
        rewrite cast_inter // map_cat.
        move => Delta /subseq_split [] [] Delta1 Delta2 [] ->.
        rewrite inPartition1_bigcap all_cat -inPartition1_bigcap -inPartition1_bigcap.        
          by move => [] /prf1 -> /prf2 ->.
  Qed.

   Lemma inPartition2_minimalType: forall M, inPartition2 (minimalType (ctxt2 Gammas) M).
  Proof.
    elim.
    - by apply: pure_context2.
    - move => M IH1 N IH2.
      rewrite /= /minimalArrowTgt.
      move: (subtype_machine _ [ tgt_for_srcs_gte (minimalType (ctxt2 Gammas) N)
                                 in cast (Omega -> Omega \times Omega) (minimalType (ctxt2 Gammas) M) ]).
      move => [] [];
               first by (move => ? /SubtypeMachine_inv;
                                case: (cast (Omega -> Omega \times Omega) (minimalType (ctxt2 Gammas) M))).
      move => Delta.
      move /choose_tgt_subseq.
      move: IH2 IH1 Delta => _.
      elim: (minimalType (ctxt2 Gammas) M).
      + by move => /= ? ? /eqP -> /=.
      + by (move => /= ? ? ? _ _ /eqP -> /=; apply: omega_partition2).
      + move => A1 _ A2 _ prf Delta.
        move: prf.
        rewrite dist_arr_partition2 /cast /=.        
        case: Delta; first by (move => *; apply: omega_partition2).
        move => A2' Delta' /andP [] _ res.
        case A2__eq: (A2' == A2) => // /eqP ->.
          by rewrite (eqP A2__eq).
      + move => ? ? ? ? ? _ /= /eqP ->; by apply: omega_partition2.
      + move => A1 IH1 A2 IH2.
        rewrite dist_inter_partition2.
        move => /andP [] /IH1 prf1 /IH2 prf2.
        rewrite cast_inter // map_cat.
        move => Delta /subseq_split [] [] Delta1 Delta2 [] ->.
        rewrite inPartition2_bigcap all_cat -inPartition2_bigcap -inPartition2_bigcap.        
          by move => [] /prf1 -> /prf2 ->.
  Qed.

  Lemma minimalType_partitioned:
    forall M, exists Delta1 Delta2,
        (minimalType [ffun c => (ctxt1 Gammas c) \cap (ctxt2 Gammas c)] M = \bigcap_(A_i <- Delta1 ++ Delta2) A_i) /\
        minimalType (ctxt1 Gammas) M = \bigcap_(A_i <- Delta1) A_i /\
        minimalType (ctxt2 Gammas) M = \bigcap_(A_i <- Delta2) A_i.
  Proof.
    elim.
    - move => c.
      exists [:: (ctxt1 Gammas c)], [:: (ctxt2 Gammas c)]; split; last by split.
        by rewrite /= ffunE.
    - move => M [] Delta__M1 [] Delta__M2 [] eq__M12 [] eq__M1 eq__M2 N [] Delta__N1 [] Delta__N2 [] eq__N12 [] eq__N1 eq__N2.
      rewrite /= /minimalArrowTgt eq__M12 eq__M1 eq__M2 eq__N12 eq__N1 eq__N2.
      exists (if subtype_machine _ [tgt_for_srcs_gte (\bigcap_(A_i <- Delta__N1) A_i) in
                                  (cast (Omega -> Omega \times Omega) (\bigcap_(A_i <- Delta__M1) A_i))]
                            is exist [check_tgt Delta] _ then Delta else [::]).
      exists (if subtype_machine _ [tgt_for_srcs_gte (\bigcap_(A_i <- Delta__N2) A_i) in
                                  (cast (Omega -> Omega \times Omega) (\bigcap_(A_i <- Delta__M2) A_i))]
                            is exist [check_tgt Delta] _ then Delta else [::]).
      split; last by split.
      rewrite cast_bigcap_cat //.
      apply: f_equal.
      apply: f_equal.
      move: (subtype_machine _ [tgt_for_srcs_gte (\bigcap_(A_i <- (Delta__N1 ++ Delta__N2)) A_i) in
                                       (cast (Omega -> Omega \times Omega) (\bigcap_(A_i <- Delta__M1) A_i))
                                         ++ (cast (Omega -> Omega \times Omega) (\bigcap_(A_i <- Delta__M2) A_i))]).
      move => [].
      case;
        first by
          (move => ? /SubtypeMachine_inv;
                  case ((cast (Omega -> Omega \times Omega) (\bigcap_(A_i <- Delta__M1) A_i))
                          ++ (cast (Omega -> Omega \times Omega) (\bigcap_(A_i <- Delta__M2) A_i)))).
      move => Delta prf__Delta.
      move: (tgt_for_srcs_gte_cat
               (\bigcap_(A_i <- (Delta__N1 ++ Delta__N2)) A_i)
               (cast (Omega -> Omega \times Omega) (\bigcap_(A_i <- Delta__M1) A_i))
               (cast (Omega -> Omega \times Omega) (\bigcap_(A_i <- Delta__M2) A_i))
               Delta prf__Delta).
      move => [] Delta1 [] Delta2 [] prf__Delta1 [] prf__Delta2 <-.
      apply: f_equal2.
      + move: (subtype_machine _ [tgt_for_srcs_gte (\bigcap_(A_i <- Delta__N1) A_i) in
                                       (cast (Omega -> Omega \times Omega) (\bigcap_(A_i <- Delta__M1) A_i))]).
        move => [].
        case;
          first by
            (move => ? /SubtypeMachine_inv;
                    case (cast (Omega -> Omega \times Omega) (\bigcap_(A_i <- Delta__M1) A_i))).
        move: Delta1 prf__Delta1.
        move: (inPartition2_minimalType N).
        rewrite eq__N2.
        move: (inPartition1_minimalType N).
        rewrite eq__N1.
        have: (all (fun AB => @inPartition1 Gammas AB.1) (cast (Omega -> Omega \times Omega) (\bigcap_(A_i <- Delta__M1) A_i))).
        { move: (inPartition1_minimalType M).
          rewrite eq__M1.
          clear...
          elim: (\bigcap_(A_i <- Delta__M1) A_i) => //.
          - move => A1 IH1 A2 IH2.
            rewrite /= dist_arr_partition1.
              by move => /andP [] ->.
          - move => A1 IH1 A2 IH2.
            rewrite cast_inter // all_cat dist_inter_partition1.
              by move => /andP [] /IH1 -> /IH2 ->. }
        clear ...
        elim: (cast (Omega -> Omega \times Omega) (\bigcap_(A_i <- Delta__M1) A_i)).
        * by move => _ _ _ Delta1 /emptyDoneTgt -> Delta1' /emptyDoneTgt ->.
        * move => [] A1 A2 Delta IH inprf__M1 inprf__N1 inprf__N2 Delta1.
          move => /SubtypeMachine_inv /(fun prf => prf (fun i r =>
                                                      match i, r with
                                                      | [tgt_for_srcs_gte B in [:: A & Delta]], [check_tgt Delta'] =>
                                                        exists Delta'' r,
                                                        Types.Semantics [subty B of A.1] (Return r) /\
                                                        Types.Semantics [tgt_for_srcs_gte B in Delta] [check_tgt Delta''] /\
                                                        Delta' = if r then [:: A.2 & Delta''] else Delta''
                                                      | _, _ => True
                                                      end)) res.
          have: exists Delta' r,
              Types.Semantics [subty (\bigcap_(A_i <- (Delta__N1 ++ Delta__N2)) A_i) of A1] (Return r) /\
              Types.Semantics [tgt_for_srcs_gte (\bigcap_(A_i <- (Delta__N1 ++ Delta__N2)) A_i) in Delta] [check_tgt Delta'] /\
              Delta1 = if r then [:: A2 & Delta'] else Delta'.
          { apply: res.
            move => Delta' r prf1 prf2.
            exists Delta', r; split => //; by split. }
          move => [] Delta' [] r [] prf1 [] prf2 Delta__eq.
          have: Types.Semantics [tgt_for_srcs_gte \bigcap_(A_i <- Delta__N1) A_i in Delta] [ check_tgt Delta'].
          { move: inprf__M1 => /andP [] _ inprf__M1.
            move: (IH inprf__M1 inprf__N1 inprf__N2 Delta' prf2).
            move: (subtype_machine _  [ tgt_for_srcs_gte \bigcap_(A_i <- Delta__N1) A_i in Delta]) => [].
            case; first by move => ? /SubtypeMachine_inv; case Delta.
              by move => Delta'' prf /(fun p => p Delta'' prf) ->. }
          have: Types.Semantics [ subty (\bigcap_(A_i <- Delta__N1) A_i) of (A1, A2).1] (Return r).
          { move: Delta__eq prf1 => _.
            case: r.
            - move => /subty__sound prf1.
              apply /subty_complete.
              move: inprf__M1 => /andP [] inprf__M1 _.
                by (apply /st_irrel_partition1;
                    last by exact (BCD__Trans _ (bcd_bigcap_cat _ _ _) prf1)). 
            - move => prf1.
              move: (subtype_machine _ [subty (\bigcap_(A_i <- Delta__N1) A_i) of (A1, A2).1]) => [].
              case; last by move => ? /SubtypeMachine_inv; case A1.
              case => //.
              move => /subty__sound /(BCD__Trans _ (@BCD__Lub1 _ _ (\bigcap_(A_i <- Delta__N2) A_i))).
              move => /(BCD__Trans _ (bcd_cat_bigcap _ _ _)) /subty_complete.
                by move => /(Types.Semantics_functional _ _ _ _ prf1) []. }
          move => prf1' prf2'.
          move: (step__chooseTgt prf1' prf2').
          rewrite -Delta__eq.
            by move => prf' ? /(Types.Semantics_functional _ _ _ _ prf') [].
      + move: (subtype_machine _ [tgt_for_srcs_gte (\bigcap_(A_i <- Delta__N2) A_i) in
                                       (cast (Omega -> Omega \times Omega) (\bigcap_(A_i <- Delta__M2) A_i))]).
        move => [].
        case;
          first by
            (move => ? /SubtypeMachine_inv;
                    case (cast (Omega -> Omega \times Omega) (\bigcap_(A_i <- Delta__M2) A_i))).
        move: Delta2 prf__Delta2.
        move: (inPartition2_minimalType N).
        rewrite eq__N2.
        move: (inPartition1_minimalType N).
        rewrite eq__N1.
        have: (all (fun AB => @inPartition2 Gammas AB.1) (cast (Omega -> Omega \times Omega) (\bigcap_(A_i <- Delta__M2) A_i))).
        { move: (inPartition2_minimalType M).
          rewrite eq__M2.
          clear...
          elim: (\bigcap_(A_i <- Delta__M2) A_i) => //.
          - move => A1 IH1 A2 IH2.
            rewrite /= dist_arr_partition2.
              by move => /andP [] ->.
          - move => A1 IH1 A2 IH2.
            rewrite cast_inter // all_cat dist_inter_partition2.
              by move => /andP [] /IH1 -> /IH2 ->. }
        clear ...
        elim: (cast (Omega -> Omega \times Omega) (\bigcap_(A_i <- Delta__M2) A_i)).
        * by move => _ _ _ Delta2 /emptyDoneTgt -> Delta2' /emptyDoneTgt ->.
        * move => [] A1 A2 Delta IH inprf__M2 inprf__N1 inprf__N2 Delta2.
          move => /SubtypeMachine_inv /(fun prf => prf (fun i r =>
                                                      match i, r with
                                                      | [tgt_for_srcs_gte B in [:: A & Delta]], [check_tgt Delta'] =>
                                                        exists Delta'' r,
                                                        Types.Semantics [subty B of A.1] (Return r) /\
                                                        Types.Semantics [tgt_for_srcs_gte B in Delta] [check_tgt Delta''] /\
                                                        Delta' = if r then [:: A.2 & Delta''] else Delta''
                                                      | _, _ => True
                                                      end)) res.
          have: exists Delta' r,
              Types.Semantics [subty (\bigcap_(A_i <- (Delta__N1 ++ Delta__N2)) A_i) of A1] (Return r) /\
              Types.Semantics [tgt_for_srcs_gte (\bigcap_(A_i <- (Delta__N1 ++ Delta__N2)) A_i) in Delta] [check_tgt Delta'] /\
              Delta2 = if r then [:: A2 & Delta'] else Delta'.
          { apply: res.
            move => Delta' r prf1 prf2.
            exists Delta', r; split => //; by split. }
          move => [] Delta' [] r [] prf1 [] prf2 Delta__eq.
          have: Types.Semantics [tgt_for_srcs_gte \bigcap_(A_i <- Delta__N2) A_i in Delta] [ check_tgt Delta'].
          { move: inprf__M2 => /andP [] _ inprf__M2.
            move: (IH inprf__M2 inprf__N1 inprf__N2 Delta' prf2).
            move: (subtype_machine _  [ tgt_for_srcs_gte \bigcap_(A_i <- Delta__N2) A_i in Delta]) => [].
            case; first by move => ? /SubtypeMachine_inv; case Delta.
              by move => Delta'' prf /(fun p => p Delta'' prf) ->. }
          have: Types.Semantics [ subty (\bigcap_(A_i <- Delta__N2) A_i) of (A1, A2).1] (Return r).
          { move: Delta__eq prf1 => _.
            case: r.
            - move => /subty__sound prf1.
              apply /subty_complete.
              move: inprf__M2 => /andP [] inprf__M2 _.
              apply /st_irrel_partition2; last first.
              + apply: BCD__Trans; last by exact (BCD__Trans _ (bcd_bigcap_cat _ _ _) prf1).
                  by (apply: BCD__Glb; last by apply BCD__Lub1).
              + done.
              + done.
              + done.
            - move => prf1.
              move: (subtype_machine _ [subty (\bigcap_(A_i <- Delta__N2) A_i) of (A1, A2).1]) => [].
              case; last by move => ? /SubtypeMachine_inv; case A1.
              case => //.
              move => /subty__sound /(BCD__Trans _ (@BCD__Lub2 _ (\bigcap_(A_i <- Delta__N1) A_i) _)).
              move => /(BCD__Trans _ (bcd_cat_bigcap _ _ _)) /subty_complete.
                by move => /(Types.Semantics_functional _ _ _ _ prf1) []. }
          move => prf1' prf2'.
          move: (step__chooseTgt prf1' prf2').
          rewrite -Delta__eq.
            by move => prf' ? /(Types.Semantics_functional _ _ _ _ prf') [].
  Qed.

   Lemma FCL__split:
    forall A B M,
      @inPartition1 Gammas A ->
      @inPartition2 Gammas B ->
      [FCL [ffun c => (ctxt1 Gammas c) \cap (ctxt2 Gammas c)] |- M : A \cap B ] <->
      [FCL (ctxt1 Gammas) |- M : A] /\ [FCL (ctxt2 Gammas) |- M : B].
   Proof.
     move => A B M inprf__A inprf__B.
     split.
     - move => /minimalType_minimal.
       move: (minimalType_partitioned M) => [] Delta1 [] Delta2 [] -> [] Delta1__eq Delta2__eq prf.
       split.
       + apply: FCL__Sub; first by apply: minimalType_sound.
         move: prf => /(fun prf => BCD__Trans _ (BCD__Trans _ (bcd_bigcap_cat _ _ _) prf) BCD__Lub1).
         move => /(st_irrel_partition1).
         rewrite -Delta1__eq -Delta2__eq.
           by move => /(fun prf => prf (inPartition1_minimalType M) (inPartition2_minimalType M) inprf__A).
       + apply: FCL__Sub; first by apply: minimalType_sound.
         move: prf => /(fun prf => BCD__Trans _ (BCD__Trans _ (bcd_bigcap_cat _ _ _) prf) BCD__Lub2).
         move => /(BCD__Trans _ (BCD__Glb BCD__Lub2 BCD__Lub1)).
         move => /(st_irrel_partition2).
         rewrite -Delta1__eq -Delta2__eq.
           by move => /(fun prf => prf (inPartition2_minimalType M) (inPartition1_minimalType M) inprf__B).
     - move => [] prf1 prf2.
       apply: FCL__II.
       + apply: FCL__weaken; last by exact prf1.
           by move => c; rewrite ffunE.
       + apply: FCL__weaken; last by exact prf2.
           by move => c; rewrite ffunE.
   Qed.
End SplitContexts.


Section InhabitationMachine.
  Variable Combinator: finType.
  Variable Constructor: ctor.
  Variable Gamma: Ctxt Combinator Constructor.

  Definition SplitCtxt: {ffun Combinator -> seq (seq (@MultiArrow Constructor))} :=
    [ffun c => splitTy (Gamma c)].

  Inductive Rule : Type :=
  | RuleFail : @IT Constructor -> Rule
  | RuleCombinator : @IT Constructor -> Combinator -> Rule
  | RuleApply : @IT Constructor -> @IT Constructor -> @IT Constructor -> Rule.

  Section RuleMathcompInstances.
    Definition Rule2tree (r: Rule):
      GenTree.tree (@IT Constructor + ((@IT Constructor * Combinator) + (@IT Constructor * @IT Constructor * @IT Constructor))) :=
      match r with
      | RuleFail A => GenTree.Node 0 [:: GenTree.Leaf (inl A)]
      | RuleCombinator A c => GenTree.Node 1 [:: GenTree.Leaf (inr (inl (A, c)))]
      | RuleApply A B C => GenTree.Node 2 [:: GenTree.Leaf (inr (inr (A, B, C)))]
      end.

    Fixpoint tree2Rule (t: GenTree.tree (@IT Constructor + ((@IT Constructor * Combinator) + (@IT Constructor * @IT Constructor * @IT Constructor)))):
      option Rule :=
      match t with
      | GenTree.Node n args =>
        match n, args with
        | 0, [:: GenTree.Leaf (inl A)] => Some (RuleFail A)
        | 1, [:: GenTree.Leaf (inr (inl (A, c)))] => Some (RuleCombinator A c)
        | 2, [:: GenTree.Leaf (inr (inr (A, B, C)))] => Some (RuleApply A B C)
        | _, _ => None
        end
      | _ => None
      end.

    Lemma pcan_Ruletree: pcancel Rule2tree tree2Rule.
    Proof. by elim => //=. Qed.

    Definition Rule_eqMixin := PcanEqMixin pcan_Ruletree.
    Canonical Rule_eqType := EqType Rule Rule_eqMixin.
    Definition Rule_choiceMixin := PcanChoiceMixin pcan_Ruletree.
    Canonical Rule_choiceType := ChoiceType Rule Rule_choiceMixin.
    Definition Rule_countMixin := PcanCountMixin pcan_Ruletree.
    Canonical Rule_countType := CountType Rule Rule_countMixin.
  End RuleMathcompInstances.

  Definition TreeGrammar: Type := seq Rule.

  Fixpoint updatedExisting (G: TreeGrammar) (A: @IT Constructor): bool * bool * TreeGrammar :=
    if G is [:: r & G]
    then
      match r with
      | RuleFail B =>
        if checkSubtypes A B
        then (true, true, if A == B then [:: r & G] else [:: RuleFail A, r & G])
        else let: (hasUpdate, failed, updated) := updatedExisting G A in (hasUpdate, failed, [:: r & updated])
      | RuleCombinator B c =>
        let: (hasUpdate, failed, updated) := updatedExisting G A in
        let: AB__eq := A == B in
        if ~~failed && ~~AB__eq && checkSubtypes A B && checkSubtypes B A
        then (true, false, [::RuleCombinator A c, r & updated])
        else (AB__eq || hasUpdate, failed, [:: r & updated])
      | RuleApply B F X =>
        let: (hasUpdate, failed, updated) := updatedExisting G A in
        let: AB__eq := A == B in
        if ~~failed && ~~AB__eq && checkSubtypes A B && checkSubtypes B A
        then (true, false, [:: RuleApply A F X, r & updated])
        else (AB__eq || hasUpdate, failed, [:: r & updated])
      end
    else (false, false, [::]).

  Fixpoint commitMultiArrow (accTgts: TreeGrammar) (c: Combinator)
           (srcs: seq (@IT Constructor)) (currentTgt: @IT Constructor) {struct srcs}: TreeGrammar :=
    if srcs is [:: src & srcs]
    then
      commitMultiArrow [:: RuleApply currentTgt (src -> currentTgt) src & accTgts] c srcs (src -> currentTgt)
    else
      [:: RuleCombinator currentTgt c & accTgts].

  Fixpoint commitUpdates (accTgts: TreeGrammar) (currentTgt: @IT Constructor) (c: Combinator)
           (covers: seq MultiArrow) {struct covers}: TreeGrammar :=
    if covers is [:: (srcs, _) & ms]
    then commitUpdates (commitMultiArrow accTgts c srcs currentTgt) currentTgt c ms
    else accTgts.

  Fixpoint dropTargets (targets: TreeGrammar): TreeGrammar :=
    if targets is [:: RuleApply _ _ _ & targets]
    then dropTargets targets
    else targets.

  Definition accumulateCovers
             (currentTarget: @IT Constructor)
             (toCover: seq (@IT Constructor))
             (s: TreeGrammar * bool)
             (c: Combinator): TreeGrammar * bool :=
    let: (newTargets, failed) := s in
    let mss := SplitCtxt c in
    let: (exist covers _) :=
       coverMachine ([::], map (fun ms =>
                                  Cover (map (fun m => (m, filter (checkSubtypes m.2) toCover)) ms) toCover)
                               mss) in
    let: reducedCovers := reduceMultiArrows covers in
    (commitUpdates newTargets currentTarget c reducedCovers, failed && ~~nilp covers).

  Definition inhabit_cover (targets: TreeGrammar) (currentTarget: @IT Constructor): bool * TreeGrammar :=
    let factors := primeFactors currentTarget in
    let: (newTargets, failed) :=
       foldl (accumulateCovers currentTarget factors) ([::], true) (enum Combinator) in
    if failed
    then (true, [:: RuleFail currentTarget & targets])
    else (false, targets ++ newTargets).
             
  Definition inhabitation_step (stable: TreeGrammar) (targets: TreeGrammar): TreeGrammar * TreeGrammar :=
    match targets with
    | [:: RuleApply A B currentTarget & targets] =>
      if isOmega currentTarget then (stable, targets)
      else if updatedExisting stable currentTarget is (true, failed, updated)
           then (updated, if failed then [:: RuleFail currentTarget & targets] else targets)
           else let: (failed, nextTargets) := inhabit_cover targets currentTarget in
                if failed
                then (stable, nextTargets)
                else ([:: RuleApply A B currentTarget & stable], nextTargets)
    | [:: RuleCombinator A c & targets] =>
      if RuleCombinator A c \in stable
      then (stable, dropTargets targets)
      else ([:: RuleCombinator A c & stable], targets)
    | [:: RuleFail _ & targets] => (stable, dropTargets targets)
    | [::] => (stable, [::])
    end.

  Inductive InhabitationSemantics: TreeGrammar * TreeGrammar -> TreeGrammar * TreeGrammar -> Prop :=
  | step__inhab : forall stable target targets,
      InhabitationSemantics (stable, [:: target & targets]) (inhabitation_step stable targets).

  Definition OmegaRules : TreeGrammar :=
    [:: RuleApply Omega Omega Omega & map (fun c => RuleCombinator Omega c) (enum Combinator)].

  Fixpoint word (G: TreeGrammar) (root: @IT Constructor) (w: @Term Combinator) {struct w}: bool :=
    match w with
    | Var c =>
      has (fun r => if r is RuleCombinator B d then (root == B) && (c == d) else false) G
    | M @ N => 
      has (fun r => if r is RuleApply B C D then (root == B) && word G C M && word G D N else false) G
    end.
End InhabitationMachine.

Arguments SplitCtxt [Combinator Constructor].
Arguments Rule [Combinator Constructor].
Arguments RuleFail [Combinator Constructor].
Arguments RuleCombinator [Combinator Constructor].
Arguments RuleApply [Combinator Constructor].
Arguments TreeGrammar [Combinator Constructor].
Hint Constructors Rule.

Arguments updatedExisting [Combinator Constructor].
Arguments commitMultiArrow [Combinator Constructor].
Arguments commitUpdates [Combinator Constructor].
Arguments dropTargets [Combinator Constructor].
Arguments accumulateCovers [Combinator Constructor].
Arguments inhabit_cover [Combinator Constructor].
Arguments inhabitation_step [Combinator Constructor].
Arguments InhabitationSemantics [Combinator Constructor].
Arguments OmegaRules [Combinator Constructor].
Arguments word [Combinator Constructor].

Section InhabitationMachineProperties.
  Variable Combinator: finType.
  Variable Constructor: ctor.
  Variable Gamma: Ctxt Combinator Constructor.

  Implicit Types stable targets G : @TreeGrammar Combinator Constructor.

  Definition FCL_sound G: Prop :=
    all (fun r =>
           match r with
           | RuleCombinator A c => checkSubtypes (Gamma c) A
           | RuleApply A B C => checkSubtypes B (C -> A)
           | _ => true
           end) G.

  Lemma FCL_sound_sound: forall G A M, FCL_sound G -> word G A M -> [FCL Gamma |- M : A].
  Proof.
    move => G A M /allP sound.
    move: A.
    elim: M.
    - move => c A /hasP [].
      case => // B d /sound le_prf /andP [] /eqP -> /eqP ->.
      apply: FCL__Sub; first by apply: FCL__Var.
        by apply /subtypeMachineP.
    - move => M IH__M N IH__N A /hasP [].
      case => // B C D /sound le_prf /andP [] /andP [] /eqP -> /IH__M prf__M /IH__N prf__N.
      apply: (FCL__MP D); last by exact prf__N.
      apply: FCL__Sub; first by exact prf__M.
        by apply /subtypeMachineP.
  Qed.

  Lemma dropTargets_suffix: forall G, suffix (dropTargets G) G.
  Proof.
    elim => //.
    case.
    - move => ? ? _.
        by rewrite /= eq_refl.
    - move => ? ? ? _.
        by rewrite /= eq_refl.
    - move => ? ? ? ? /= ->.
        by rewrite orbT.
  Qed.

  Lemma suffix_word: forall G1 G2, suffix G1 G2 -> forall A M, word G1 A M -> word G2 A M.
  Proof.
    move => G1 G2 /suffixP [] prefix /eqP G2__eq A M.
    move: A.
    elim: M.
    - move => c A.
      rewrite /word /= G2__eq has_cat => ->.
        by rewrite orbT.
    - move => M IH__M N IH__N A.
      rewrite /word /= G2__eq has_cat.
      move => /hasP [].
      case => // B C D inprf /andP [] /andP [] A__eq /IH__M prf__M /IH__N prf__N.
      apply /orP.
      right.
      apply /hasP.
      eexists; first by exact inprf.
        by rewrite /= -G2__eq A__eq -/(word G2 C M) prf__M -/(word G2 D N) prf__N.
  Qed.

  Lemma suffix_sound: forall G1 G2, suffix G1 G2 -> FCL_sound G2 -> FCL_sound G1.
  Proof.
    move => G1 G2 /suffixP [] prefix /eqP G2__eq.
      by rewrite /FCL_sound G2__eq all_cat => /andP [].
  Qed.

  Lemma word_perm: forall G1 G2, perm_eq G1 G2 -> forall A M, word G1 A M -> word G2 A M.
  Proof.
    move => G1 G2 perm_prf A M.
    move: A.
    elim: M.
    - move => c A /hasP [] r inprf prf.
      apply /hasP.
      exists r.
      + by rewrite -(perm_eq_mem perm_prf r).
      + done.
    - move => M IH__M N IH__N A.
      move => /hasP [].
      case => // B C D inprf /andP [] /andP [] A__eq /IH__M prf__M /IH__N prf__N.
      apply /hasP.
      exists (RuleApply B C D).
      + by rewrite -(perm_eq_mem perm_prf _).
      + by rewrite /= A__eq -/(word G2 C M) prf__M -/(word G2 D N) prf__N.
  Qed.

  Lemma perm_sound: forall G1 G2, perm_eq G1 G2 -> FCL_sound G2 -> FCL_sound G1.
  Proof.
    move => G1 G2 perm_prf prf.
      by rewrite /FCL_sound (perm_eq_all _ perm_prf).
  Qed.

  Lemma cat_sound: forall G1 G2, FCL_sound G1 -> FCL_sound G2 -> FCL_sound (G1 ++ G2).
  Proof.
    move => G1 G2 prf1 prf2.
      by rewrite /FCL_sound all_cat prf1 prf2.
  Qed.

  Lemma updatedExisting_sound:
    forall G A, FCL_sound G -> FCL_sound ((updatedExisting G A).2).
  Proof.
    move => G A.
    elim: G => // r G IH.
    rewrite /updatedExisting.
    case: r.
    - move => B.
      case: (checkSubtypes A B).
      + by case: (A == B).
      + move => /IH.
        rewrite -/(updatedExisting G A).
          by case: (updatedExisting G A) => [] [].
    - move => B c.
      rewrite -/(updatedExisting G A).
      move => /andP [] prf /IH.
      case: (updatedExisting G A) => [] [] ? failed updated /= prfs.
      have: (FCL_sound [:: RuleCombinator B c & updated]).
      { by rewrite /FCL_sound /= prf prfs. }
      move: (A == B) => AB__eq.
      case le_prf: (checkSubtypes B A).
      + case: (~~failed && ~~AB__eq && checkSubtypes A B && true).
        * rewrite /FCL_sound /= => ->.
          rewrite andbT /=.
          apply /subtypeMachineP.
          apply: BCD__Trans; first by (apply /subtypeMachineP; exact prf).
            by apply /subtypeMachineP.
        * by rewrite /=.
      + by rewrite andbF /=.
    - move => B C D.
      rewrite -/(updatedExisting G A).
      move => /andP [] prf /IH.
      case: (updatedExisting G A) => [] [] ? failed updated /= prfs.
      have: (FCL_sound [:: RuleApply B C D & updated]).
      { by rewrite /FCL_sound /= prf prfs. }
      move: (A == B) => AB__eq.
      case le_prf: (checkSubtypes B A).
      + case: (~~failed && ~~AB__eq && checkSubtypes A B && true).
        * rewrite /FCL_sound /= => ->.
          rewrite andbT /=.
          apply /subtypeMachineP.
          apply: BCD__Trans; first by (apply /subtypeMachineP; exact prf).
          apply: BCD__Sub; first by done.
            by apply /subtypeMachineP.
        * by rewrite /=.
      + by rewrite andbF /=.
  Qed.

  Lemma commitMultiArrow_sound:
    forall G A m c,
      FCL_sound G ->
      checkSubtypes (Gamma c) (mkArrow m) ->
      checkSubtypes m.2 A ->
      FCL_sound (commitMultiArrow G c m.1 A).
  Proof.
    move => G A [] srcs tgt c.
    rewrite /commitMultiArrow /=.
    move: A tgt G.
    elim: srcs.
    - move => A tgt G prfs.
      rewrite /mkArrow /= /FCL_sound /= prfs andbT.
      move => /subtypeMachineP prf1 /subtypeMachineP prf2.
      apply /subtypeMachineP.
        by (apply: BCD__Trans; first by exact prf1).
    - move => src srcs IH A tgt G.
      rewrite /= -/(commitMultiArrow [:: RuleApply A (src -> A) src & G] c srcs (src -> A)).
      move => prfs le_prf tgt_prf.
      apply: (IH (src -> A) (src -> A) [:: RuleApply A (src -> A) src & G]).
      + rewrite /FCL_sound /= prfs andbT.
          by apply /subtypeMachineP.
      + apply /subtypeMachineP.
        apply: BCD__Trans; first by (apply /subtypeMachineP; exact le_prf).
        apply: mkArrow_tgt_le.
          by apply /subtypeMachineP.
      + by apply /subtypeMachineP.
  Qed.


  Lemma commitUpdates_sound:
    forall G A ms c,
      FCL_sound G ->
      all (fun m : MultiArrow => checkSubtypes (Gamma c) (mkArrow m)) ms ->
      all (fun m : MultiArrow => checkSubtypes m.2 A) ms ->
      FCL_sound (commitUpdates G A c ms).
  Proof.
    move => G A ms c.
    move: G A.
    rewrite /commitUpdates.
    elim: ms => //.
    move => [] srcs tgt ms IH G A G_sound /andP [] le_prf le_prfs /andP [] tgt_prf tgt_prfs.
      by (apply: IH; first by apply: (commitMultiArrow_sound G A (srcs, tgt) c)).
  Qed.

  Lemma accumulateCovers_sound:
    forall A G b c,
      ~~(isOmega A) ->
      FCL_sound G ->
      FCL_sound (accumulateCovers Gamma A (primeFactors A) (G, b) c).1.
  Proof.
    move => A G b c notOmega__A G_sound.
    rewrite /accumulateCovers.
    move: (coverMachine ([::], map (fun ms =>
                                      Cover (map (fun m => (m, filter (checkSubtypes m.2) (primeFactors A))) ms) (primeFactors A))
                                   (SplitCtxt Gamma c))) => [] s.
    rewrite /SplitCtxt ffunE.
    move => prf.
    move: (prf) => /(coverMachine_splitTy_sound _ (Gamma c) A s notOmega__A) /soundnessPreserving cover_sound.
    move: prf => /(coverMachine_splitTy_tgt_sound _ (Gamma c) A s) /tgt_soundnessPreserving cover_tgt_sound.
      by apply: commitUpdates_sound.
  Qed.

  Lemma foldl_accumulateCovers_sound:
    forall A G b,
      ~~(isOmega A) ->
      FCL_sound G ->
      FCL_sound (foldl (accumulateCovers Gamma A (primeFactors A)) (G, b) (enum Combinator)).1.
  Proof.
    elim: (enum Combinator) => // c cs IH A G b notOmega__A G_sound.
    rewrite /foldl -/(foldl (accumulateCovers Gamma A (primeFactors A))).
    move: (accumulateCovers_sound A G b c notOmega__A G_sound) => /IH.
    case: (accumulateCovers Gamma A (primeFactors A) (G, b) c) => G' b' res.
      by apply: res.
  Qed.

  Lemma inhabit_cover_sound:
    forall (targets: TreeGrammar) (currentTarget: @IT Constructor),
      ~~isOmega currentTarget ->
      FCL_sound targets ->
      FCL_sound (inhabit_cover Gamma targets currentTarget).2.
  Proof.
    move => targets currentTarget notOmega__currentTarget targets_sound.
    rewrite /inhabit_cover.
    move: (foldl_accumulateCovers_sound currentTarget [::] true notOmega__currentTarget isT).
    case: (foldl (accumulateCovers Gamma currentTarget (primeFactors currentTarget)) ([::], true) (enum Combinator)) => G' [] //=.
    rewrite /FCL_sound all_cat targets_sound => ->.
      by rewrite andbT.
  Qed.


  Lemma inhabitation_step_sound:
    forall stable targets,
      FCL_sound stable ->
      FCL_sound targets ->
      FCL_sound (inhabitation_step Gamma stable targets).1 /\ FCL_sound (inhabitation_step Gamma stable targets).2.
  Proof.
    move => stable targets stable_sound.
    case: targets => //.
    case.
    - move => A targets /=.
      move => /(suffix_sound _ _ (dropTargets_suffix _)).
      move => /(suffix_sound _ _ (suffix_behead _ _ (suffix_refl _))).
        by move => /(suffix_sound _ _ (dropTargets_suffix _)).
    - move => A c targets /andP [] prf prfs /=.
      case: (RuleCombinator A c \in stable).
      + split => //.
          by move: prfs => /(suffix_sound _ _ (dropTargets_suffix _)).
      + split => //.
          by apply /andP.
    - move => A B C targets /=.
      case isOmega__C: (isOmega C).
      + move => /andP [] _ prf.
          by split.
      + move: (updatedExisting_sound _ C stable_sound).
        case: (updatedExisting stable C) => [] [] hasExisting failed updated.
        case: hasExisting.
        * case: failed; by move => ? /andP [].
        * move => updated_sound /andP [] le_prf targets_sound.
          move: (inhabit_cover_sound targets C (negbT isOmega__C) targets_sound).
          case: (inhabit_cover Gamma targets C) => [] nextFailed nextTargets.
          case: nextFailed => //=.
          move => nextTargets_sound.
          split => //.
            by apply /andP; split.
  Qed.

  Definition lhs (rule: @Rule Combinator Constructor): @IT Constructor :=
    match rule with
    | RuleFail A => A
    | RuleCombinator A _ => A
    | RuleApply A _ _ => A
    end.
    
  Fixpoint grammarTypes (srcs: seq (@IT Constructor)) (tgt: @IT Constructor): seq (@IT Constructor) :=
    if srcs is [:: src & srcs]
    then [:: src , tgt & grammarTypes srcs (src -> tgt)]
    else [:: tgt ].

  Definition maxTypes (A: @IT Constructor): seq (@IT Constructor) :=
    flatten (map (fun c => flatten (map (fun ms => flatten (map (fun m => grammarTypes m.1 m.2 ++ grammarTypes m.1 A)
                                                          (filterMergeMultiArrows _ (subseqs ms))))
                                     (SplitCtxt Gamma c)))
                 (enum Combinator)).

  Definition recursiveTargets (G: @TreeGrammar Combinator Constructor): seq (@IT Constructor) :=
    pmap (fun r => match r with
                | RuleApply _ _ C => Some C
                | RuleCombinator A _ => Some A
                | _ => None
                end) G.

  Lemma grammarTypes_src_mem: forall src srcs tgt, src \in srcs -> src \in grammarTypes srcs tgt.
  Proof.
    move => src1.
    elim => // src2 srcs IH tgt.
    rewrite /= in_cons.
    move => /orP.
    case.
    - move => /eqP ->.
        by apply: mem_head.
    - move => /(IH (src2 -> tgt)).
      rewrite in_cons in_cons => ->.
        by rewrite orbT orbT.
  Qed.

  Lemma commitMultiArrow_subset:
    forall (Delta: seq (@IT Constructor)) G c srcs tgt,
      {subset (undup (recursiveTargets G)) <= Delta} ->
      {subset grammarTypes srcs tgt <= Delta} ->
      {subset (undup (recursiveTargets (commitMultiArrow G c srcs tgt))) <= Delta}.
  Proof.
    move => Delta G c srcs.
    move: G.
    elim: srcs.
    - move => G tgt /= targets_subset inprf__tgt.
      case: (tgt \in recursiveTargets G) => //.
      move => A.
      rewrite in_cons.
      move => /orP.
      case.
      + move => /eqP ->.
        apply: inprf__tgt.
          by rewrite mem_seq1.
      + by move => /targets_subset.
    - move => /= src srcs IH G tgt G_prf inprf__srctgt.
      apply: IH.
      + rewrite /=.
        case: (src \in recursiveTargets G) => //.
        move => x /orP.
        case.
        * move => /eqP ->.
          apply: inprf__srctgt.
            by rewrite in_cons eq_refl.
        * by move => /G_prf.
      + move => x inprf.
        apply: inprf__srctgt.
          by rewrite in_cons in_cons inprf orbT orbT.
  Qed.

  Lemma commitUpdates_subset:
    forall (Delta: seq (@IT Constructor)) G currentTarget c (ms : seq (@MultiArrow Constructor)),
      {subset (undup (recursiveTargets G)) <= Delta} ->
      (forall m,  m \in ms -> {subset (grammarTypes m.1 currentTarget) <= Delta}) ->
      {subset (undup (recursiveTargets (commitUpdates G currentTarget c ms))) <= Delta}.
  Proof.
    move => Delta G currentTarget c ms.
    move: G.
    elim: ms => // [] [] srcs tgt ms IH G subset__G subset__ms.
    rewrite /=.
    apply: IH.
    - apply: commitMultiArrow_subset => //.
      apply: (subset__ms (srcs, tgt)).
        by rewrite in_cons eq_refl.
    - move => m inprf__m.
      apply: subset__ms.
        by rewrite in_cons inprf__m orbT.
  Qed.
  
  Lemma accumulateCovers_subset:
    forall c targets b currentTarget initialTarget,
      (currentTarget \in [:: initialTarget & (recursiveTargets targets)]) ->
      {subset (undup (recursiveTargets targets)) <= maxTypes initialTarget} ->
      {subset
         (undup (recursiveTargets
                   (accumulateCovers Gamma currentTarget (primeFactors currentTarget) (targets, b) c).1)) <=
       maxTypes initialTarget}.
  Proof.
    move => c targets b currentTarget initialTarget currentTarget_member.
    rewrite /accumulateCovers.
    move: (coverMachine ([::],
                         map (fun ms =>
                                Cover (map (fun m => (m, filter (checkSubtypes m.2)
                                                             (primeFactors currentTarget))) ms)
                                      (primeFactors currentTarget))
                             (SplitCtxt Gamma c))) => [] covers steps.
    move: (semantics_mergeComponents _ _ (covers, [::]) steps).
    rewrite /sound.
    move => /allP /(fun prf x inprf => prf x (mem_subseq (reduction_subseq _ _) inprf)).    
    move: steps => _.
    case: covers => // m covers prf prfs.
    apply: commitUpdates_subset => //.
    move: prf.
    rewrite [([::], _).1]/= [seq.size [::]]/= subn0 take_size.
    move => prf.
    move => [] srcs tgt /prf.
    rewrite [([::], _).2]/= -map_comp.
    have: ((fun i => (filterMergeMultiArrows _ (subseqs (mergeComponentsOf Constructor i))))
             \o (fun ms =>
                   Cover (map (fun m => (m, filter (checkSubtypes m.2)
                                                (primeFactors currentTarget))) ms)
                         (primeFactors currentTarget))
           =1 (fun ms => filterMergeMultiArrows _ (subseqs ms))).
    { move => ms /=.
      rewrite -map_comp.
      apply f_equal.
      apply f_equal.
        by apply: map_id. }
    move => /eq_map ->.
    rewrite /maxTypes.
    move => inprf__srcstgt src inprf__src.
    apply /flatten_mapP.
    exists c.
    - by rewrite mem_enum.
    - apply /flattenP.
      move: inprf__srcstgt => /flatten_mapP [] ms inprf__ms inprf__srcstgt.
      exists (flatten (map (fun m => grammarTypes m.1 m.2 ++ grammarTypes m.1 initialTarget) (filterMergeMultiArrows _ (subseqs ms)))).
      + apply /mapP.
          by (exists ms).
      + apply /flatten_mapP.
        exists (srcs, tgt) => //.
        rewrite mem_cat.
        apply /orP.
        move: inprf__src currentTarget_member.
        case currentTarget__eq: (currentTarget == initialTarget).
        * rewrite (eqP currentTarget__eq).
            by move => * /=; right.
        * rewrite in_cons currentTarget__eq orFb.
          rewrite -[_ \in recursiveTargets _]mem_undup.
          move => inprf__src /prfs.

        left.
        rewrite /=.
        apply: grammarTypes_src_mem.
  Qed.


  Lemma foldl_accumulateCovers_subset:
     forall targets b currentTarget,
      {subset (undup (recursiveTargets targets)) <= [:: currentTarget & maxTypes]} ->
      {subset
         (undup (recursiveTargets
                   (foldl (accumulateCovers Gamma currentTarget (primeFactors currentTarget))
                          (targets, b) (enum Combinator)).1)) <=
       [:: currentTarget & maxTypes]}.
  Proof.
    elim: (enum Combinator) => // c combinators IH targets b currentTarget prf.
    rewrite (foldl_cat _ _ [:: c]).
    move: (accumulateCovers_subset c targets b currentTarget prf).
    rewrite [accumulateCovers _ _ _]lock /= -lock.
    case: (accumulateCovers Gamma currentTarget (primeFactors currentTarget) (targets, b) c).
    move => nextTargets failed nextTargets_subeset.
      by apply: IH.
  Qed.

  Lemma pmap_cat {T1 T2: Type}: forall (f: T1 -> option T2) xs ys, pmap f (xs ++ ys) = pmap f xs ++ pmap f ys.
  Proof.
    move => f.
    elim => //= x xs IH ys.
    rewrite IH.
      by case: (f x).
  Qed.

  Lemma inhabit_cover_subset:
    forall targets currentTarget,
      {subset (undup (recursiveTargets targets)) <= [:: currentTarget & maxTypes]} ->
      {subset (undup (recursiveTargets
                        (inhabit_cover Gamma targets currentTarget).2)) <=
       [:: currentTarget & maxTypes]}.
  Proof.
    move => targets currentTarget targets_subset.
    rewrite /inhabit_cover.
    move: (foldl_accumulateCovers_subset [::] true currentTarget (mem_subseq (sub0seq _))).
    case: (foldl (accumulateCovers Gamma currentTarget (primeFactors currentTarget))
                 ([::], true) (enum Combinator)).
    move => nextTargets failed.
    case: failed => // nextTargets_subset.
    rewrite /recursiveTargets pmap_cat.
    move => A.
    rewrite mem_undup mem_cat.
    move => /orP.
    case.
    - rewrite -mem_
                 undup.
        by apply: targets_subset.
    - rewrite -mem_undup.
        by apply: nextTargets_subset.
  Qed.

  Lemma inhabitation_step_subset:
    forall tgt stable targets,
      {subset (undup (map lhs stable)) <= [:: tgt & maxTypes]} ->
      {subset (undup (recursiveTargets targets)) <= [:: tgt & maxTypes]} ->
      {subset (undup (map lhs (inhabitation_step Gamma stable targets).1)) <= [:: tgt & maxTypes]} /\
      {subset (undup (recursiveTargets (inhabitation_step Gamma stable targets).2)) <= [:: tgt & maxTypes]}.
  Proof.
    move => tgt stable.
    rewrite /inhabitation_step.
    case => //.
    case.
    - move => A targets stable_subset targets_subset.
      split => //.
      rewrite /=.
      move => B.
      rewrite mem_undup.
      rewrite /recursiveTargets.
      move: (dropTargets_suffix targets) => /suffixP [] prefix /eqP targets_eq inprf.
      apply: targets_subset.
      rewrite mem_undup /= targets_eq /recursiveTargets pmap_cat mem_cat.
      apply /orP.
        by right.
    - move => A c targets stable_subset targets_subset.
      split.
      + case inprf: (RuleCombinator A c \in stable) => //.
        




  Lemma inhabitation_step_stable_size:
    forall stable targets,
      all (fun 
      seq.size 

  










  Definition Constructor: ctor := sum_ctorType Constructor1 Constructor2.

  Definition Ctxt1 := Ctxt Combinator Constructor1.
  Definition Ctxt2 := Ctxt Combinator Constructor2.
  Definition Ctxt__sum := Ctxt Combinator Constructor.




  Fixpoint mapctor {C1 C2: ctor} (f: C1 -> C2) (A: @IT C1): @IT C2 :=
    match A with
    | Ctor c A => Ctor (f c) (mapctor f A)
    | A -> B => mapctor f A -> mapctor f B
    | A \times B => mapctor f A \times mapctor f B
    | A \cap B => mapctor f A \cap mapctor f B
    | Omega => Omega
    end.

  Definition lift1 := @mapctor Constructor1 Constructor inl.
  Definition lift2 := @mapctor Constructor2 Constructor inr.

  Lemma mapctor_isOmega {C1 C2 : ctor}:
    forall (f: C1 -> C2) A, isOmega A = isOmega (mapctor f A).
  Proof.
    move => f.
      by elim => //= ? -> ? ->.
  Qed.   

  Lemma mapctor_cast_hom {C1 C2 : ctor}:
    forall (f: C1 -> C2),
      (forall c d, [ctor c <= d] = [ctor (f c) <= (f d)]) ->
      forall A B,
        cast (mapctor f A) (mapctor f B) =
        map (match A as A' return arity A' -> arity (mapctor f A') with
             | Omega => fun _ =>  tt
             | Ctor _ _ => mapctor f
             | _ => (fun (AB: IT * IT) => (mapctor f AB.1, mapctor f AB.2))
             end) (cast A B).
  Proof.
    move => f f_prf.
    case => //.
    - move => c A B.
      elim: B => //.
      + move => d B _.
        rewrite /cast /=.
        move: (f_prf d c).
          by case: [ctor d <= c] => <-.
      + move => B1 IH1 B2 IH2.
          by rewrite cast_inter //= cast_inter //= map_cat IH1 IH2.
    - move => A1 A2 B /=.
      rewrite slow_cast_cast slow_cast_cast /slow_cast /= -(mapctor_isOmega f).
      case: (isOmega A2) => //.
      elim: B => //= B1 IH1 B2 IH2.
        by rewrite map_cat IH1 IH2.
    - move => A1 A2 B /=.
      rewrite slow_cast_cast slow_cast_cast /slow_cast /=.
      elim: B => //= B1 IH1 B2 IH2.
        by rewrite map_cat IH1 IH2.
    - move => A1 A2 B /=.
      rewrite slow_cast_cast slow_cast_cast /slow_cast /= -(mapctor_isOmega f) -(mapctor_isOmega f).
      case: (isOmega A1 && isOmega A2) => //.
      elim: B => //= B1 IH1 B2 IH2.
        by rewrite map_cat IH1 IH2.
  Qed.

  (*Lemma mapctor_cast_subseq {C1 C2 : ctor}:
    forall (f: C1 -> C2),
      (forall c d, [ctor c <= d] -> [ctor (f c) <= (f d)]) ->
      forall A B, match A with
             | Ctor c A => subseq (map (mapctor f) (cast (Ctor c A) B)) (cast (mapctor f (Ctor c A)) (mapctor f B))
             | Omega => subseq (cast Omega B) (cast (mapctor f Omega) (mapctor f B))
             | A => subseq (map (fun A1A2 => (mapctor f A1A2.1, mapctor f A1A2.2)) (cast A B))
                          (cast (mapctor f A) (mapctor f B))
             end.
  Proof.
     move => f f_prf.
    case => //.
    - move => c A B.
      elim: B => //.
      + move => d B _.
        rewrite /cast /=.
        move: (f_prf d c).
        case: [ctor d <= c]; last by move => _; apply: sub0seq.
        move => /(fun prf => prf isT) ->.
          by apply: subseq_refl.
      + move => B1 IH1 B2 IH2.
        rewrite cast_inter //= cast_inter //= map_cat.
          by apply: cat_subseq.
    - move => A1 A2 B.
      rewrite /A.
      rewrite slow_cast_cast slow_cast_cast /slow_cast /= -(mapctor_isOmega f).
      case: (isOmega A2) => //.
      elim: B => //= B1 IH1 B2 IH2.
      + by rewrite eq_refl.
      + rewrite map_cat.
          by apply: cat_subseq.
    - move => A1 A2 B.
      rewrite /A.
      move: A => _.
      rewrite slow_cast_cast slow_cast_cast /slow_cast /=.
      elim: B => //= B1 IH1 B2 IH2.
      + by rewrite eq_refl.
      + rewrite /= map_cat.
          by apply: cat_subseq.
    - move => A1 A2 B.
      rewrite /A.
      rewrite slow_cast_cast slow_cast_cast /slow_cast /= -(mapctor_isOmega f) -(mapctor_isOmega f).
      case: (isOmega A1 && isOmega A2) => //.
      elim: B => //= B1 IH1 B2 IH2.
      rewrite map_cat.
        by apply cat_subseq.
  Qed.

  Lemma cast_mapctor_subseq {C1 C2 : ctor}:
    forall (f: C1 -> C2),
      (forall c d, [ctor (f c) <= (f d)] -> [ctor c <= d]) ->
      forall A B, match A with
             | Ctor c A => subseq (cast (mapctor f (Ctor c A)) (mapctor f B)) (map (mapctor f) (cast (Ctor c A) B))
             | Omega => subseq (cast (mapctor f Omega) (mapctor f B)) (cast Omega B)
             | A => subseq (cast (mapctor f A) (mapctor f B))
                          (map (fun A1A2 => (mapctor f A1A2.1, mapctor f A1A2.2)) (cast A B))
             end.
  Proof.
    move => f f_prf.
    case => //.
    - move => c A B.
      elim: B => //.
      + move => d B _.
        rewrite /cast /=.
        move: (f_prf d c).
        case: [ctor (f d) <= (f c)]; last by move => _; apply: sub0seq.
        move => /(fun prf => prf isT) ->.
          by apply: subseq_refl.
      + move => B1 IH1 B2 IH2.
        rewrite cast_inter //= cast_inter //= map_cat.
          by apply: cat_subseq.
    - move => A1 A2 B.
      rewrite /A.
      rewrite slow_cast_cast slow_cast_cast /slow_cast /= -(mapctor_isOmega f).
      case: (isOmega A2) => //.
      elim: B => //= B1 IH1 B2 IH2.
      + by rewrite eq_refl.
      + rewrite map_cat.
          by apply: cat_subseq.
    - move => A1 A2 B.
      rewrite /A.
      move: A => _.
      rewrite slow_cast_cast slow_cast_cast /slow_cast /=.
      elim: B => //= B1 IH1 B2 IH2.
      + by rewrite eq_refl.
      + rewrite /= map_cat.
          by apply: cat_subseq.
    - move => A1 A2 B.
      rewrite /A.
      rewrite slow_cast_cast slow_cast_cast /slow_cast /= -(mapctor_isOmega f) -(mapctor_isOmega f).
      case: (isOmega A1 && isOmega A2) => //.
      elim: B => //= B1 IH1 B2 IH2.
      rewrite map_cat.
        by apply cat_subseq.
  Qed.*)


  Lemma mapctor_map_bigcap {a : Type} {C1 C2 : ctor}:
    forall (f: a -> @IT C1) (g: C1 -> C2) Delta,
      mapctor g (\bigcap_(A_i <- Delta) f A_i) = \bigcap_(A_i <- map (mapctor g \o f) Delta) A_i.
  Proof.
    move => f g.
    elim => // A Delta.
    rewrite bigcap_cons bigcap_cons.
      by case: Delta => //= ? ? ->.
  Qed.

  Lemma map_nilp {a b: Type}: forall (f: a -> b) xs, nilp (map f xs) = nilp xs.
  Proof. by move => ? []. Qed.

  (*Lemma mapctor_cast_nilp {C1 C2: ctor}:
    forall (f: (C1 -> C2)%type),
      (forall c d, [ctor c <= d] -> [ctor (f c) <= (f d)]) ->
      forall A B, 
        ~~nilp (cast A B) -> ~~nilp (cast (mapctor f A) (mapctor f B)).
  Proof.
    move => f f_prf A B.
    move: (mapctor_cast_subseq f f_prf A B).
    case: A => //.
    - move => c A.
      case: (cast (Ctor c A) B) => //.
        by case: (cast (mapctor f (Ctor c A)) (mapctor f B)).
    - move => A1 A2 /=.
      case: (cast (A1 -> A2) B) => //.
        by case: (cast (mapctor f (A1 -> A2)) (mapctor f B)).
    - move => A1 A2 /=.
      case: (cast (A1 \times A2) B) => //.
        by case: (cast (mapctor f (A1 \times A2)) (mapctor f B)).
    - move => A1 A2 /=.
      case: (cast (A1 \cap A2) B) => //.
        by case: (cast (mapctor f (A1 \cap A2)) (mapctor f B)).
  Qed.

  Lemma cast_mapctor_nilp {C1 C2: ctor}:
    forall (f: (C1 -> C2)%type),
      (forall c d, [ctor (f c) <= (f d)] -> [ctor c <= d]) ->
      forall A B, 
        ~~nilp (cast (mapctor f A) (mapctor f B)) -> ~~nilp (cast A B).
  Proof.
    move => f f_prf A B.
    move: (cast_mapctor_subseq f f_prf A B).
    case: A => //.
    - move => c A.
      case: (cast (Ctor c A) B) => //.
        by case: (cast (mapctor f (Ctor c A)) (mapctor f B)).
    - move => A1 A2 /=.
      case: (cast (A1 -> A2) B) => //.
        by case: (cast (mapctor f (A1 -> A2)) (mapctor f B)).
    - move => A1 A2 /=.
      case: (cast (A1 \times A2) B) => //.
        by case: (cast (mapctor f (A1 \times A2)) (mapctor f B)).
    - move => A1 A2 /=.
      case: (cast (A1 \cap A2) B) => //.
        by case: (cast (mapctor f (A1 \cap A2)) (mapctor f B)).
  Qed.*)

  Lemma mapctor_cast_nilp {C1 C2: ctor}:
    forall (f: (C1 -> C2)%type),
      (forall c d, [ctor c <= d] = [ctor (f c) <= (f d)]) ->
      forall A B, 
        nilp (cast A B) = nilp (cast (mapctor f A) (mapctor f B)).
  Proof.
    move => f f_hom A B.
    rewrite (mapctor_cast_hom f f_hom).
      by rewrite map_nilp.
  Qed.

  Lemma injective_mapctor {C1 C2 : ctor}:
    forall (f: C1 -> C2), injective f -> injective (mapctor f).
  Proof.
    move => f f_inj.
    elim.
    - by case.
    - move => c A IH.
        by case => //= d B [] /f_inj -> /IH ->.
    - move => A1 IH1 A2 IH2.
        by case => //= ? ? [] /IH1 -> /IH2 ->.
    - move => A1 IH1 A2 IH2.
        by case => //= ? ? [] /IH1 -> /IH2 ->.
    - move => A1 IH1 A2 IH2.
        by case => //= ? ? [] /IH1 -> /IH2 ->.
  Qed.

  Lemma mapctor_le {C1 C2 : ctor}:
    forall (f: C1 -> C2),
      (forall c d, [ctor c <= d] -> [ctor (f c) <= (f d)]) ->
      forall A B,
        [bcd A <= B] ->
        [bcd (mapctor f A) <= (mapctor f B)].
  Proof.
    move => f f_prf A B prf.
    elim: A B / prf => //=.
    - by move => *; apply: BCD__CAx; auto.
    - by move => *; apply: BCD__Sub.
    - by move => *; apply: BCD__ProdSub.
    - by move => *; apply: BCD__Trans; eauto.
    - by move => *; apply: BCD__Glb.
  Qed.

  Lemma subtypeMachine_mapctor {C1 C2 : ctor}:
    forall (f: C1 -> C2),
      (forall c d, [ctor c <= d] = [ctor (f c) <= (f d)]) ->
      forall i r,
        Types.Semantics i r ->
        match i, r with
        | [subty fA of fB], Return r =>
          forall A, mapctor f A = fA ->
               forall B, mapctor f B = fB ->
                    Types.Semantics [subty A of B] (Return r)
        | [tgt_for_srcs_gte fB in fDelta1], [check_tgt fDelta2] =>
          forall B, mapctor f B = fB ->
               forall Delta1, map (fun AB => (mapctor f AB.1, mapctor f AB.2)) Delta1 = fDelta1 ->
                         exists Delta2, map (mapctor f) Delta2 = fDelta2 /\
                                   Types.Semantics [tgt_for_srcs_gte B in Delta1]
                                                   [check_tgt Delta2]
        | _, _ => True
        end.
  Proof.
    move => f f_hom i r prf.
    elim: i r / prf.
    - by move => A A__tmp _ [].
    - move => fA fc fB r prf IH A fA__eq cB fcB__eq.
      have: (exists c B, (cB = Ctor c B) /\ (f c = fc) /\ (mapctor f B = fB)).
      { move: fcB__eq.
        clear...
        case: cB => // c B [] <- <-.
          by (exists c, B); split => //; split. }
      move => [] c [] B [] -> [] c__eq B__eq.
      rewrite -c__eq -B__eq -fA__eq.
      rewrite (mapctor_cast_hom f f_hom (Ctor c B) A) map_nilp.
      constructor.
      apply: IH; last by rewrite B__eq.
      rewrite -fA__eq.
      rewrite mapctor_map_bigcap -(mapctor_cast_hom f f_hom (Ctor c B) A).
      do 2 apply: f_equal.
        by rewrite /= -c__eq -B__eq.
    - move => fA fB1 fB2 fDelta2 r prf1 IH1 prf2 IH2 A fA__eq B fB__eq.
      have: (exists B1 B2, (B = (B1 -> B2)%IT) /\ (mapctor f B1 = fB1) /\ (mapctor f B2 = fB2)).
      { move: fB__eq.
        clear...
        case: B => // B1 B2 [] <- <-.
          by (exists B1, B2); split => //; split. }
      move => [] B1 [] B2 [] -> [] fB1__eq fB2__eq.
      rewrite -fB2__eq -(mapctor_isOmega f).
      have: (exists Delta2, map (mapctor f) Delta2 = fDelta2 /\
                       Types.Semantics [ tgt_for_srcs_gte B1 in cast (B1 -> B2) A]
                                       [ check_tgt Delta2]).
      { apply: IH1 => //.
          by rewrite -(mapctor_cast_hom f f_hom (B1 -> B2)) /= -fB1__eq -fB2__eq -fA__eq. }
      move => [] Delta2 [] fDelta2__eq prf__Delta2.
      apply: step__Arr => //; first by exact prf__Delta2.
      apply: IH2 => //.
        by rewrite -fDelta2__eq mapctor_map_bigcap.
    - move => fB [] fA1 fA2 fDelta1 fDelta2 [] prf1 IH1 prf2 IH2 B fB__eq [] // []
                A1 A2 Delta1 [] [] fA1__eq fA2__eq fDelta1__eq.
      + move: (IH2 B fB__eq Delta1 fDelta1__eq) => [] Delta2 [] fDelta2__eq rest_prf.
        exists [:: A2 & Delta2]; split.
        * by rewrite /= fA2__eq fDelta2__eq.
        * apply: (step__chooseTgt (r := true)) => //.
            by apply: IH1.
      + move: (IH2 B fB__eq Delta1 fDelta1__eq) => [] Delta2 [] fDelta2__eq rest_prf.
        exists Delta2; split => //.
        apply: (step__chooseTgt (r := false)) => //.
          by apply: IH1.        
    - move => ? ? [] // _ [] // _.
        by (exists [::]); split.
    - move => fA fB1 fB2 r1 r2 prf1 IH1 prf2 IH2 A fA__eq B fB__eq.
      rewrite -fB__eq -fA__eq -(mapctor_cast_nilp f f_hom).
      have: (exists B1 B2, ((B = (B1 \times B2)) /\
                       (fB1 = mapctor f B1) /\
                       (fB2 = mapctor f B2))).
      { move: fB__eq => [].
        clear ...
        case: B => // B1 B2 /= [] <- <-.
          by (exists B1, B2). }
      move => [] B1 [] B2 [] B__eq [] fB1__eq fB2__eq.
      rewrite B__eq.
      apply: step__Prod.
      + apply: IH1 => //.
        rewrite mapctor_map_bigcap fB1__eq fB2__eq -fA__eq (mapctor_cast_hom f f_hom (B1 \times B2)).
          by rewrite -map_comp -map_comp.
      + apply: IH2 => //.
        rewrite mapctor_map_bigcap fB1__eq fB2__eq -fA__eq (mapctor_cast_hom f f_hom (B1 \times B2)).
          by rewrite -map_comp -map_comp.
    - move => fA fB1 fB2 r1 r2 prf1 IH1 prf2 IH2 A fA__eq B fB__eq.
       have: (exists B1 B2, ((B = (B1 \cap B2)) /\
                       (fB1 = mapctor f B1) /\
                       (fB2 = mapctor f B2))).
      { move: fB__eq => [].
        clear ...
        case: B => // B1 B2 /= [] <- <-.
          by (exists B1, B2). }
      move: fB__eq => _.
      move => [] B1 [] B2 [] fB__eq [] B1__eq B2__eq.
      rewrite fB__eq.
      constructor.
      + by apply: IH1.
      + by apply: IH2.
  Qed.

  Lemma le_mapctor {C1 C2 : ctor}:
    forall (f: C1 -> C2),
      (forall c d, [ctor c <= d] = [ctor (f c) <= (f d)]) ->
      forall A B, [bcd (mapctor f A) <= (mapctor f B)] -> [bcd A <= B].
  Proof.
    move => f f_hom A B /subty_complete prf.
    apply /subty__sound.
      by apply: (subtypeMachine_mapctor f f_hom _ _ prf).
  Qed.

  Lemma lift1_hom: forall A B, [bcd A <= B] <-> [bcd (lift1 A) <= lift1 B].
  Proof.
    move => A B.
    split.
    - move => /(@mapctor_le Constructor1 Constructor inl) res.
        by apply: res.
    - move => /(@le_mapctor Constructor1 Constructor inl) res.
        by apply: res.
  Qed.

  Lemma lift2_hom: forall A B, [bcd A <= B] <-> [bcd (lift2 A) <= lift2 B].
  Proof.
    move => A B.
    split.
    - move => /(@mapctor_le Constructor2 Constructor inr) res.
        by apply: res.
    - move => /(@le_mapctor Constructor2 Constructor inr) res.
        by apply: res.
  Qed.

  Lemma injective_lift1: injective lift1.
  Proof. by apply: injective_mapctor; move => ? ? []. Qed.

  Lemma injective_lift2: injective lift2.
  Proof. by apply: injective_mapctor; move => ? ? []. Qed.


  (*Fixpoint pmapctor {C1 C2: ctor} (f: C1 -> option C2) (A: @IT C1): option (@IT C2) :=
    match A with
    | Ctor c A =>
      if f c is Some c
      then if pmapctor f A is Some A
           then Some (Ctor c A)
           else None
      else None
    | A -> B =>
      if pmapctor f A is Some A
      then if pmapctor f B is Some B
           then Some (A -> B)
           else None
      else None
    | A \times B =>
      if pmapctor f A is Some A
      then if pmapctor f B is Some B
           then Some (A \times B)
           else None
      else None
    | A \cap B =>
      if pmapctor f A is Some A
      then if pmapctor f B is Some B
           then Some (A \cap B)
           else None
      else None
    | Omega => Some Omega
    end.

  Definition unlift1 := @pmapctor Constructor Constructor1 (fun c => if c is inl c then Some c else None).
  Definition unlift2 := @pmapctor Constructor Constructor2 (fun c => if c is inr c then Some c else None).

  Lemma mapctor_pmapctor_pcancel {C1 C2: ctor}:
    forall (f: C1 -> C2) (g: C2 -> option C1),
      pcancel f g -> pcancel (mapctor f) (pmapctor g).
  Proof.
    move => f g fg_pcancel.
    elim => //.
    - move => c A /=.
      rewrite (fg_pcancel c).
        by move ->.
    - by move => /= ? -> ? ->.
    - by move => /= ? -> ? ->.
    - by move => /= ? -> ? ->.
  Qed.

  Lemma lift1_unlift1_pcancel: pcancel lift1 unlift1.
  Proof. by apply: mapctor_pmapctor_pcancel. Qed.

  Lemma lift2_unlift2_pcancel: pcancel lift2 unlift2.
  Proof. by apply: mapctor_pmapctor_pcancel. Qed. *)

  Definition intersectCtxt (Gamma1: Ctxt1) (Gamma2: Ctxt2): Ctxt__sum :=
    [ffun c => lift1 (Gamma1 c) \cap lift2 (Gamma2 c)].

  Lemma FCL__join: forall Gamma1 Gamma2 M A1 A2,
      [FCL Gamma1 |- M : A1] ->
      [FCL Gamma2 |- M : A2] ->
      [FCL intersectCtxt Gamma1 Gamma2 |- M : lift1 A1 \cap lift2 A2].
  Proof.
    move => Gamma1 Gamma2 M A1 A2 prf1 prf2.
    apply: FCL__II.
    - move: prf2 => _.
      elim /FCL_normalized_ind: M A1 / prf1.
      + move => c.
        apply: (FCL__Sub (lift1 (Gamma1 c) \cap lift2 (Gamma2 c))) => //.
        move: (@FCL__Var _ _ (intersectCtxt Gamma1 Gamma2) c).
          by rewrite ffunE.
      + move => c A prf le_prf.
          by apply: (FCL__Sub (lift1 (Gamma1 c))); last by apply: (proj1 (lift1_hom _ _)).
      + move => M N A B _ prf1 _ prf2.
          by apply: (FCL__MP (lift1 A)).
    - move: prf1 => _.
      elim /FCL_normalized_ind: M A2 / prf2.
      + move => c.
        apply: (FCL__Sub (lift1 (Gamma1 c) \cap lift2 (Gamma2 c))) => //.
        move: (@FCL__Var _ _ (intersectCtxt Gamma1 Gamma2) c).
          by rewrite ffunE.
      + move => c A prf le_prf.
          by apply: (FCL__Sub (lift2 (Gamma2 c))); last by apply: (proj1 (lift2_hom _ _)).
      + move => M N A B _ prf1 _ prf2.
          by apply: (FCL__MP (lift2 A)).
  Qed.

  Lemma hom_addAndFilter {C1 C2: ctor}:
    forall Delta A (f : C1 -> C2),
      (forall c d, [ctor c <= d] = [ctor (f c) <= (f d)]) ->
      map (mapctor f) (addAndFilter _ Delta A) = addAndFilter _ (map (mapctor f) Delta) (mapctor f A).
  Proof.
    elim => //= B Delta IH A f f_hom.
    have st_f : (forall A B, checkSubtypes A B = checkSubtypes (mapctor f A) (mapctor f B)).
    { move => A1 A2.
      case le12: (checkSubtypes A1 A2).
      - apply: Logic.eq_sym.
        apply /subtypeMachineP.
        apply: mapctor_le.
        + move => ? ?.
            by rewrite f_hom.
        + by apply /subtypeMachineP.
      - case lef12: (checkSubtypes (mapctor f A1) (mapctor f A2)) => //.
          by move: lef12 le12 => /subtypeMachineP /(le_mapctor f f_hom) /subtypeMachineP -> ->. }
    move: (st_f B A) => <-.
    case: (checkSubtypes B A) => //.
    move: (st_f A B) => <-.
    case: (checkSubtypes A B) => //;
      by rewrite /= IH.
  Qed.    

  Lemma map_hom_primeFactors {C1 C2: ctor}: forall (f: C1 -> C2),
      (forall c d, [ctor c <= d] = [ctor (f c) <= (f d)]) ->
      forall A, map (mapctor f) (primeFactors A) = primeFactors (mapctor f A).
  Proof.
    rewrite /primeFactors.
    move => f f_hom A.
    have: ((mapctor f \o id) =1 (id \o mapctor f)) => //.
    have: (map (mapctor f) [::] = [::]) => //.
    move: (@id (@IT C1)) (@id (@IT C2)).
    move: (@nil (@IT C1)) (@nil (@IT C2)).
    elim: A => //=.
    - move => Delta1 Delta2 g1 g2 <- prf.
      move: (prf Omega) => /= <-.
      rewrite -mapctor_isOmega.
      case: (isOmega (g1 Omega)) => //.
        by apply: hom_addAndFilter.
    - move => c A IH Delta1 Delta2 g1 g2 prf1 prf2.
      apply: IH => //.
      move => B.
        by apply: prf2.
    - move => A1 IH1 A2 IH2 Delta1 Delta2 g1 g2 prf1 prf2.
      apply: IH2 => //.
      move => B.
        by apply: prf2.
    - move => A1 IH1 A2 IH2 Delta1 Delta2 g1 g2 prf1 prf2.
      apply: IH2 => //.
      + apply: IH1 => //.
        move => B.
          by apply: prf2.
      + move => B.
          by apply: prf2.
    - move => A1 IH1 A2 IH2 Delta1 Delta2 g1 g2 prf1 prf2.
      apply: IH2 => //.
        by apply: IH1.
  Qed.

  Lemma mapctor_prime {C1 C2: ctor}: forall (f: C1 -> C2) (A: @IT C1), isPrimeComponent A -> isPrimeComponent (mapctor f A).
  Proof.
    move => f.
    elim => // A1 IH1 A2 IH2.
    move: IH1 IH2.
      by case: A1; case: A2 => //.
  Qed.

  Lemma lift1_cast_lift2: forall c A B, cast (lift1 (Ctor c A)) (lift2 B) = [::].
  Proof.
    move => c A.
    elim => // B1 IH1 B2 IH2.
      by rewrite /= cast_inter -/mapctor //= IH1 IH2.
  Qed.

  Lemma lift2_cast_lift1: forall c A B, cast (lift2 (Ctor c A)) (lift1 B) = [::].
  Proof.
    move => c A.
    elim => // B1 IH1 B2 IH2.
      by rewrite /= cast_inter -/mapctor //= IH1 IH2.
  Qed.

  Lemma split_subseq {a: eqType}: forall (xs ys zs: seq a),
      subseq xs (ys ++ zs) -> exists xs1 xs2, xs == xs1 ++ xs2 /\ subseq xs1 ys /\ subseq xs2 zs.
  Proof.
    move => xs ys.
    move: xs.
    elim: ys.
    - move => xs ys prf.
        by exists [::], xs; split.
    - move => y ys IH xs zs /=.
      case: xs.
      + move => _.
        exists [::], [::]; split => //; split => //.
          by apply: sub0seq.
      + move => x xs.
        case x__eq: (x == y).
        * move => /IH [] xs1 [] xs2 [] /eqP xs__eq [] prf1 prf2.
          exists [:: x & xs1], xs2; split.
          ** by rewrite xs__eq.
          ** by rewrite x__eq; split.
        * move => /IH [] xs1 [] xs2 [] /eqP xs__eq [] prf1 prf2.
          exists xs1, xs2; split.
          ** by rewrite xs__eq.
          ** split => //.
             move: xs__eq prf1.
             case: xs1 => // x1 xs1 [] <-.
               by rewrite x__eq.
  Qed.

  Lemma injective_bigcap {C: ctor}:
    forall (Delta1 Delta2: seq (@IT C)),
      seq.size Delta1 = seq.size Delta2 ->
      \bigcap_(A_i <- Delta1) A_i = \bigcap_(A_i <- Delta2) A_i ->
      Delta1 = Delta2.
  Proof.
    elim.
    - by case.
    - move => A Delta1 IH.
      case => // B Delta2 [] size_prf.
      move: IH size_prf (IH _ size_prf) => _.
      case: Delta1.
      + by case: Delta2 => //= _ _ ->.
      + move => A2 Delta1.
          by case: Delta2 => // B2 Delta2 _ IH /= [] -> /IH ->.
  Qed.     


  Lemma mapctor_tgtctxt {C1 C2: ctor}:
    forall (f: C1 -> C2) A B1 B2 fDelta2,
      subseq fDelta2 (map snd (cast (B1 -> B2) (mapctor f A))) ->
      exists Delta2,
        seq.size fDelta2 = seq.size Delta2 /\
        \bigcap_(A_i <- fDelta2) A_i = mapctor f (\bigcap_(A_i <- Delta2) A_i).
  Proof.
    move => f A B1 B2.
    case isOmega__B2: (isOmega B2).
    - rewrite /cast /= isOmega__B2.
      case.
      + move => _.
          by (exists [::]).
      + move => B fDelta2 prf.
        (exists [:: Omega]).
        move: prf.
        case: fDelta2.
        * by rewrite sub1seq mem_seq1 /= => /eqP ->.
        * move => ? ? /=.
            by case: (B == Omega).
    - elim: A.
      + rewrite /cast /= isOmega__B2.
        move => [] // _.
          by (exists [::]).
      + rewrite /cast /= isOmega__B2.
        move => ? ? _ [] // _.
          by (exists [::]).
      + move => A1 _ A2 _.
        case.
        * move => _.
            by (exists [::]).
        * move => B fDelta2 prf.
          (exists [:: A2]).
          move: prf.
          case: fDelta2.
          ** by rewrite /cast /= isOmega__B2 sub1seq mem_seq1 /= => /eqP ->.
          ** move => ? ? /=.
             rewrite /cast /= isOmega__B2 /=.
               by case: (B == mapctor f A2).
      + rewrite /cast /= isOmega__B2.
        move => ? _ ? _ [] // _.
          by (exists [::]).
      + move => A1 IH1 A2 IH2 fDelta2.
        rewrite cast_inter -/(mapctor f); last by rewrite /= isOmega__B2.
        rewrite map_cat.
        move => /split_subseq [] fDelta21 [] fDelta22 [] /eqP fDelta2__eq [].
        move => /IH1 [] Delta21 [] fDelta21__size fDelta21__eq.
        move => /IH2 [] Delta22 [] fDelta22__size fDelta22__eq.
        exists (Delta21 ++ Delta22); split.
        * by rewrite fDelta2__eq size_cat size_cat fDelta21__size fDelta22__size.
        * rewrite fDelta2__eq mapctor_map_bigcap.
          move: fDelta21__eq.
          rewrite mapctor_map_bigcap.
          move => /injective_bigcap.
          rewrite size_map.
          move => /(fun prf => prf fDelta21__size) ->.
          move: fDelta22__eq.
          rewrite mapctor_map_bigcap.
          move => /injective_bigcap.
          rewrite size_map.
          move => /(fun prf => prf fDelta22__size) ->.
            by rewrite [map _ (Delta21 ++ Delta22)]map_cat.
  Qed.

  Lemma mapctor_prod {C1 C2: ctor}:
    forall (f: C1 -> C2) A B1 B2,
      exists Delta2,
        seq.size (cast (B1 \times B2) (mapctor f A)) = seq.size Delta2 /\
        \bigcap_(A_i <- (cast (B1 \times B2) (mapctor f A))) A_i.1 = mapctor f (\bigcap_(A_i <- Delta2) A_i.1) /\
        \bigcap_(A_i <- (cast (B1 \times B2) (mapctor f A))) A_i.2 = mapctor f (\bigcap_(A_i <- Delta2) A_i.2).
  Proof.
    move => f A B1 B2.
    elim: A; try by (exists [::]).
    - move => A1 _ A2 _.
        by (exists [:: (A1, A2)]).
    - move => A1 [] Delta21 [] fDelta21__size [] fDelta21__fst fDelta21__snd.
      move => A2 [] Delta22 [] fDelta22__size [] fDelta22__fst fDelta22__snd.
      exists (Delta21 ++ Delta22); split; last split.
      + by rewrite cast_inter // size_cat fDelta21__size fDelta22__size size_cat.
      + rewrite mapctor_map_bigcap map_cat.
        move: fDelta21__fst.
        rewrite mapctor_map_bigcap (eqP (bigcap_map_eq _ _ _ fst)).
        move => /injective_bigcap.
        do 2 rewrite size_map.
        move => /(fun prf => prf fDelta21__size) <-.
        move: fDelta22__fst.
        rewrite mapctor_map_bigcap (eqP (bigcap_map_eq _ _ _ fst)).
        move => /injective_bigcap.
        do 2 rewrite size_map.
        move => /(fun prf => prf fDelta22__size) <-.
        rewrite -map_cat.
        rewrite (eqP (bigcap_map_eq _ _ _ fst)).
          by rewrite cast_inter.
      + rewrite mapctor_map_bigcap map_cat.
        move: fDelta21__snd.
        rewrite mapctor_map_bigcap (eqP (bigcap_map_eq _ _ _ snd)).
        move => /injective_bigcap.
        do 2 rewrite size_map.
        move => /(fun prf => prf fDelta21__size) <-.
        move: fDelta22__snd.
        rewrite mapctor_map_bigcap (eqP (bigcap_map_eq _ _ _ snd)).
        move => /injective_bigcap.
        do 2 rewrite size_map.
        move => /(fun prf => prf fDelta22__size) <-.
        rewrite -map_cat.
        rewrite (eqP (bigcap_map_eq _ _ _ snd)).
          by rewrite cast_inter.
  Qed.

  Lemma lift2_nle_lift1: forall A B, ~~(isOmega B) -> Types.Semantics [subty (lift1 A) of (lift2 B)] (Return false).
  Proof.
    move => A B.
    move: A.
    elim: B => //=.
    - move => d B _ A _.
      have: (exists r, Types.Semantics [ subty \bigcap_(A__i <- cast (lift2 (Ctor d B)) (lift1 A)) A__i of lift2 B] (Return r)).
      { move: (subtype_machine _ [ subty \bigcap_(A__i <- cast (lift2 (Ctor d B)) (lift1 A)) A__i of lift2 B]) => [] r res.
        move: res (inv_subtyp_return _ res).
        case: r => // r res _.
          by (exists r). }
      move => [] r prf. 
      have: (~~nilp (cast (lift2 (Ctor d B)) (lift1 A)) && r = false) by rewrite lift2_cast_lift1.
      move => <-.
        by apply: (step__Ctor prf).
    - move => B1 _ B2 IH A /= notOmega.
      have: (exists fDelta, Types.Semantics [ tgt_for_srcs_gte lift2 B1 in cast (lift2 (B1 -> B2)) (lift1 A)] [check_tgt fDelta]).
      { move: (subtype_machine _ [ tgt_for_srcs_gte lift2 B1 in cast (lift2 (B1 -> B2)) (lift1 A)]) => [] r res.
        move: res (inv_tgt_for_srcs_gte_check_tgt _ res).
        case: r => // r res _.
          by (exists r). }
      move => [] fDelta prf.
      have notOmega__fB2: (isOmega (lift2 B2) = false).
      { move: notOmega.
          by rewrite (@mapctor_isOmega Constructor2 Constructor inr B2) /lift2 => /negbTE ->. }
      have: (isOmega (lift2 B2) || false = false) by rewrite notOmega__fB2.
      move => <-.
      apply: (step__Arr prf).
      move: (check_tgt_subseq _ _ _ _ prf).
      move => /mapctor_tgtctxt [] Delta2 [] fDelta2__size fDelta2__eq.
      rewrite fDelta2__eq.
        by apply: IH.
    - move => B1 IH1 B2 IH2 A _.
      have: (false = ~~ nilp (cast (lift2 (B1 \times B2)) (lift1 A)) && false && false) by rewrite andbF.
      move => ->.
      move: (@mapctor_prod Constructor1 Constructor inl A (lift2 B1) (lift2 B2)).
      move => [] Delta [] Delta__size [] Delta__fst Delta__snd.
      apply: (step__Prod (r1 := false) (r2 := false)).
      + rewrite -/mapctor Delta__fst.
        apply: IH1.
        admit.
      + admit.
  Admitted.   
  

  (*Lemma BCD__unliftsum1: forall A B C,
      [bcd (lift1 A \cap lift2 B) <= lift1 C] ->
      [bcd A <= C].
  Proof.
    move => A B C /(fun prf => BCD__Trans (lift1 C) prf (primeFactors_geq (lift1 C))).
    rewrite -(@map_hom_primeFactors Constructor1 Constructor inl) => // prf.
    apply: BCD__Trans; last by apply: primeFactors_leq.
    apply: (proj2 (lift1_hom _ _)).
    move: prf.
    rewrite /lift1.
    rewrite mapctor_map_bigcap.
    have: (@mapctor Constructor1 Constructor inl \o id = @mapctor Constructor1 Constructor inl) => // ->.
    have: (all (@isPrimeComponent Constructor) (map (@mapctor Constructor1 Constructor inl) (primeFactors C))).
    { move: (primeFactors_prime C) => /allP prf.
      rewrite all_map.
      apply /allP.
      move => ? /prf /=.
        by apply: mapctor_prime. }
    have: (all (
    elim: (map (@mapctor Constructor1 Constructor inl) (primeFactors C)).
    - move => _ _ /=.
        by apply: BCD__omega.
    - move => C1 Delta IH /andP [] prf1 prfs /(fun prf => BCD__Trans _ prf (bcd_cat_bigcap _ [:: C1] Delta)) le_prf.
      apply: BCD__Trans; last by apply: (bcd_bigcap_cat _ [:: _] _).
      apply: BCD__Glb.
      + move: le_prf => /(fun prf => BCD__Trans _ prf BCD__Lub1).
        move => /primeComponentPrime.
        move: prf1 => /isPrimeComponentP prf1 /(fun prf => prf prf1) [] => //.
        * 




    rewrite (@mapctor_map_bigcap (@IT Constructor1) Constructor1 Constructor id inl (primeFactors C)).
    rewrite /lift1.
    have: 
    have: ([ bcd (lift1 A \cap lift2 B) <= mapctor inl (\bigcap_(A_i <- primeFactors C) A_i)]).

    apply: BCD__Trans; last by exact prf.


    move => prf.
    apply: 
*)



  Lemma FCL__split: forall Gamma1 Gamma2 M A1 A2,
      [FCL intersectCtxt Gamma1 Gamma2 |- M : lift1 A1 \cap lift2 A2] ->
      [FCL Gamma1 |- M : A1] /\ [FCL Gamma2 |- M : A2].
  Proof.
    move => Gamma1 Gamma2 M A1 A2.
    move A__eq: (lift1 A1 \cap lift2 A2) => A prf.
    move: A1 A2 A__eq.
    elim /FCL_normalized_ind: M A / prf.
    - move => c A1 A2.
      rewrite /intersectCtxt ffunE.
      move => [] /injective_lift1 -> /injective_lift2 ->.
        by split.
    - move => c A /(fun prf => prf (Gamma1 c) (Gamma2 c)).
      rewrite /intersectCtxt ffunE.
      move => /(fun prf => prf Logic.eq_refl) [] prf1 prf2.
      move => le_prf A1 A2.
      move: le_prf.
      case: A => // ? ? le_prf [] A1__eq A2__eq.
      move: le_prf.
      rewrite -A1__eq -A2__eq.
      move => le_prf.
      













  Definition MultiArrow: Type := seq (@IT Constructor) * (@IT Constructor).

  Definition safeSplit (Delta: seq (seq MultiArrow)): seq MultiArrow * seq (seq MultiArrow) :=
    match Delta with
    | [::] => ([::], [::])
    | [:: Delta ] => (Delta, [::])
    | [:: Delta1 & Delta2 ] => (Delta1, Delta2)
    end.

  Fixpoint splitRec
           (A: @IT Constructor)
           (srcs: seq (@IT Constructor))
           (Delta: seq (seq MultiArrow)):
    seq (seq MultiArrow) :=
    match A with
    | Arrow A B =>
      let (Delta1, Delta2) := safeSplit Delta in
      [:: [:: ([:: A & srcs], B) & Delta1] & splitRec B [:: A & srcs] Delta2]
    | A \cap B =>
      if (isOmega A) then splitRec B srcs Delta
      else if (isOmega B) then splitRec A srcs Delta
           else splitRec A srcs (splitRec B srcs Delta)
    | _ => Delta
    end.

  Definition splitTy (A: @IT Constructor): seq (seq MultiArrow) :=
    if isOmega A
    then [::]
    else [:: ([::], A) ] :: splitRec A [::] [::].

End Split.


Arguments MultiArrow [Constructor].
Arguments splitTy [Constructor].


(** Instructions for a machine covering paths with multi arrows **)
Section CoverInstuctions.
  Variable Constructor: ctor.

  Inductive Instruction: Type :=
  | Cover (splits : seq (@MultiArrow Constructor * seq (@IT Constructor)))
          (toCover : seq (@IT Constructor))
  | ContinueCover
      (splits : seq (@MultiArrow Constructor * seq (@IT Constructor)))
      (toCover : seq (@IT Constructor))
      (currentResult : @MultiArrow Constructor)
  | CheckCover
      (splits : seq (@MultiArrow Constructor * seq (@IT Constructor)))
      (toCover : seq (@IT Constructor))
  | CheckContinueCover
      (splits : seq (@MultiArrow Constructor * seq (@IT Constructor)))
      (toCover : seq (@IT Constructor))
      (currentResult : @MultiArrow Constructor).

  Definition State: Type := seq (@MultiArrow Constructor).

  (** Enable mathcomp functionalities on instructions **)
  Section InstructionMathcompInstances.
    Fixpoint Instruction2tree (i: Instruction):
      GenTree.tree (seq ((@MultiArrow Constructor * seq (@IT Constructor))) + seq (@IT Constructor) + @MultiArrow Constructor) :=
      match i with
      | Cover splits toCover => GenTree.Node 0 [:: GenTree.Leaf (inl (inl splits)); GenTree.Leaf (inl (inr toCover))]
      | ContinueCover splits toCover currentResult =>
        GenTree.Node 1 [:: GenTree.Leaf (inl (inl splits)); GenTree.Leaf (inl (inr toCover)); GenTree.Leaf (inr currentResult)]
      | CheckCover splits toCover =>
        GenTree.Node 2 [:: GenTree.Leaf (inl (inl splits)); GenTree.Leaf (inl (inr toCover))]
      | CheckContinueCover splits toCover currentResult =>
        GenTree.Node 3 [:: GenTree.Leaf (inl (inl splits)); GenTree.Leaf (inl (inr toCover)); GenTree.Leaf (inr currentResult)]
      end.

    Fixpoint tree2Instruction
             (t: GenTree.tree (seq ((@MultiArrow Constructor * seq (@IT Constructor)))
                               + seq (@IT Constructor)
                               + @MultiArrow Constructor)): option Instruction :=
      match t with
      | GenTree.Node n args =>
        match n, args with
        | 0, [:: GenTree.Leaf (inl (inl splits)); GenTree.Leaf (inl (inr toCover))] => Some (Cover splits toCover)
        | 1, [:: GenTree.Leaf (inl (inl splits)); GenTree.Leaf (inl (inr toCover)); GenTree.Leaf (inr currentResult)] =>
          Some (ContinueCover splits toCover currentResult)
        | 2, [:: GenTree.Leaf (inl (inl splits)); GenTree.Leaf (inl (inr toCover))] => Some (CheckCover splits toCover)
        | 3, [:: GenTree.Leaf (inl (inl splits)); GenTree.Leaf (inl (inr toCover)); GenTree.Leaf (inr currentResult)] =>
          Some (CheckContinueCover splits toCover currentResult)
        | _, _ => None
        end
      | _ => None
      end.

    Lemma pcan_Instructiontree: pcancel Instruction2tree tree2Instruction.
    Proof. by case => //= [] [] //=. Qed.

    Definition Instruction_eqMixin := PcanEqMixin pcan_Instructiontree.
    Canonical Instruction_eqType := EqType Instruction Instruction_eqMixin.
    Definition Instruction_choiceMixin := PcanChoiceMixin pcan_Instructiontree.
    Canonical Instruction_choiceType := ChoiceType Instruction Instruction_choiceMixin.
    Definition Instruction_countMixin := PcanCountMixin pcan_Instructiontree.
    Canonical Instruction_countType := CountType Instruction Instruction_countMixin.
  End InstructionMathcompInstances.
End CoverInstuctions.

Arguments Instruction [Constructor].
Arguments State [Constructor].
Arguments Cover [Constructor].
Arguments ContinueCover [Constructor].
Arguments CheckCover [Constructor].
Arguments CheckContinueCover [Constructor].
Hint Constructors Instruction.