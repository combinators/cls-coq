Require Import PeanoNat.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Wellfounded.Inverse_Image.
Require Import Coq.Wellfounded.Lexicographic_Product.
From mathcomp Require Import all_ssreflect.
Require Import PreOrders.
Require Import Types.
Require Import Cover.

Set Bullet Behavior "Strict Subproofs".

Delimit Scope it_scope with IT.
Open Scope it_scope.

Import EqNotations.

Reserved Notation "[ 'FCL' Gamma |- M : A ]" (at level 0, M at level 50).
Reserved Notation "M @ N" (at level 50, left associativity).

Definition context_of (combT: finType) (ctorT: ctor) (_: phantom Type (Finite.sort combT)) (_: phantom Type (PreOrdered.sort ctorT)) :=
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

  Definition typeCheck Gamma (M: Term) (A: IT): bool :=
    checkSubtypes (minimalType Gamma M) A.

  Lemma fclP : forall Gamma M A, reflect [FCL Gamma |- M : A] (typeCheck Gamma M A).
  Proof.
    move => Gamma M A.
    case checks: (typeCheck Gamma M A).
    - constructor.
      apply: FCL__Sub; first by apply: minimalType_sound.
        by apply /subtypeMachineP.
    - constructor.
      move => prf.
      move: (minimalType_minimal _ _ _ prf) => /subtypeMachineP.
      move: checks.
      rewrite /typeCheck.
        by move => ->.
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
Arguments typeCheck [Combinator Constructor].

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

  Lemma leq_sum_refl: PreOrdered.preorder_reflexive ctorSum_countType leq_sum.
  Proof.
    move => [] c; by apply: preorder_reflexive.
  Qed.

  Lemma leq_sum_trans: PreOrdered.preorder_transitive ctorSum_countType leq_sum.
  Proof.
    move => [] c1 [] c2 [] c3 //=.
    - by apply: preorder_transitive.
    - by rewrite andbF.
    - by rewrite andbF.
    - by apply: preorder_transitive.
  Qed.

  Definition sum_preOrderedMixin :=
    PreOrdered.Mixin ctorSum_countType
                     leq_sum leq_sum_refl leq_sum_trans.
  Canonical sum_preOrderedType := Eval hnf in PreOrderedType ctorSum_countType sum_preOrderedMixin.
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
          base: PreOrdered.class_of C;
          mixin: mixin_of (PreOrdered.Pack C base)
        }.
    Local Coercion base : class_of >-> PreOrdered.class_of.
    Structure type := Pack { sort : Type; _ : class_of sort }.
    Local Coercion sort : type >-> Sortclass.
    Variables (T: Type) (splitUniverse: type).
    Definition class := let: Pack _ c as splitUniverse' := splitUniverse return class_of splitUniverse' in c.
    Definition clone c of phant_id class c := @Pack T c.
    Let xT := let: Pack T _ := splitUniverse in T.
    Notation xclass := (class : class_of xT).
    Definition pack b0 (m0: mixin_of (PreOrdered.Pack T b0)) :=
      fun bT b & phant_id (PreOrdered.class bT) b =>
        fun m & phant_id m0 m => Pack T (@Class T b m).
    Definition eqType := Eval hnf in @Equality.Pack splitUniverse xclass.
    Definition choiceType := Eval hnf in  @Choice.Pack splitUniverse xclass.
    Definition countType := Eval hnf in @Countable.Pack splitUniverse xclass.
    Definition preOrdered := Eval hnf in @PreOrdered.Pack splitUniverse xclass.
  End ClassDef.

  Module Import Exports.
    Coercion base : class_of >-> PreOrdered.class_of.
    Coercion mixin: class_of >-> mixin_of.
    Coercion sort : type >-> Sortclass.
    Coercion eqType : type >-> Equality.type.
    Canonical eqType.
    Coercion choiceType : type >-> Choice.type.
    Canonical choiceType.
    Coercion countType : type >-> Countable.type.
    Canonical countType.
    Coercion preOrdered : type >-> PreOrdered.type.
    Canonical preOrdered.

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
          mixin: mixin_of (@Finite.Pack Combinator combinator_base)
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
    Definition pack b0 b1 (m0: mixin_of (@Finite.Pack Combinator b0) (SplitTypeUniverse.Pack Constructor b1)) :=
      fun bCombinator bcomb & phant_id (Finite.class bCombinator) bcomb =>
        fun bConstructor bctor & phant_id (SplitTypeUniverse.class bConstructor) bctor =>
          fun m & phant_id m0 m => Pack Combinator Constructor (@Class Combinator Constructor bcomb bctor m).

    Definition combEqType := Eval hnf in @Equality.Pack xCombinator xclass.
    Definition combChoiceType := Eval hnf in  @Choice.Pack xCombinator xclass.
    Definition combCountType := Eval hnf in  @Countable.Pack xCombinator xclass.
    Definition finType := Eval hnf in  @Finite.Pack xCombinator xclass.

    Definition ctorEqType := Eval hnf in @Equality.Pack xConstructor (SplitTypeUniverse.base _ xclass).
    Definition ctorCountType := Eval hnf in @Countable.Pack xConstructor (SplitTypeUniverse.base _ xclass).
    Definition preOrdered := Eval hnf in  @PreOrdered.Pack xConstructor xclass.
    Definition splitTypeUniverse := (SplitTypeUniverse.Pack xConstructor xclass).
  End ClassDef.

  Module Import Exports.
    Coercion universe_base : class_of >-> SplitTypeUniverse.class_of.
    Coercion mixin: class_of >-> mixin_of.
    Coercion preOrdered : type >-> PreOrdered.type.
    Canonical preOrdered.
    Coercion splitTypeUniverse: type >-> SplitTypeUniverse.type.
    Canonical splitTypeUniverse.
    Coercion finType: type >-> Finite.type.
    Canonical finType.

    Notation splitCtxtPair := type.
    Notation SplitCtxtPairMixin := Mixin.
    Notation SplitCtxtPairType Combinator Constructor m := (@pack Combinator Constructor _ _ m _ _ id _ _ id m id).
    Notation "[ 'splitCtxtPair' 'of' Combinator 'and' Constructor 'for' splitCtxts ]" :=
      (@clone Combinator Constructor splitCtxts _ idfun)
        (at level 0, format "[ 'splitCtxtPair' 'of'  Combinator 'and' Constructor 'for' splitCtxts ]") : form_scope.
    Notation "[ 'splitCtxtPair' 'of' Combinator 'and' Constructor ]" :=
      (@clone Combinator Constructor _ _ id) (at level 0, format "[ 'splitCtxtPair' 'of' Combinator 'and' Constructor ]") : form_scope.
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
          dom_base: PreOrdered.class_of Domain;
          rng_base: PreOrdered.class_of Range;
          mixin: mixin_of (PreOrdered.Pack Domain dom_base)
                          (PreOrdered.Pack Range rng_base)
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
    Definition pack b0 b1 (m0: mixin_of (@PreOrdered.Pack Domain b0) (@PreOrdered.Pack Range b1)) :=
      fun bDomain bdom & phant_id (PreOrdered.class bDomain) bdom =>
        fun bRange brng & phant_id (PreOrdered.class bRange) brng =>
          fun m & phant_id m0 m => Pack Domain Range (@Class Domain Range bdom brng m).

    Definition domain := Eval hnf in @PreOrdered.Pack xDomain (dom_base _ _ xclass).
    Definition range := Eval hnf in @PreOrdered.Pack xRange (rng_base _ _ xclass).
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
  @PreOrdered.Pack _ (@ITHomomorphism.dom_base _ _ (@ITHomomorphism.class f)).
Definition range_base (f: itHom): ctor :=
  @PreOrdered.Pack _ (@ITHomomorphism.rng_base _ _ (@ITHomomorphism.class f)).
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
  Definition LiftedConstructor: ctor := sum_preOrderedType
                                          (diag_preOrderedType [countType of bool])
                                          (sum_preOrderedType Constructor1 Constructor2).

  Fixpoint lift {C: ctor}
             (lift_ctor: C -> sum_preOrderedType Constructor1 Constructor2)
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
           (unlift_ctor: sum_preOrderedType Constructor1 Constructor2 -> option C)
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

  Definition unlift_ctor1: sum_preOrderedType Constructor1 Constructor2 -> option Constructor1 :=
    (fun c => if c is inl x then Some x else None).
  Definition unlift1 := unlift unlift_ctor1.

  Definition unlift_ctor2: sum_preOrderedType Constructor1 Constructor2 -> option Constructor2 :=
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
    ITHomomorphism.mixin_of (PreOrdered.Pack Constructor1 (PreOrdered.class Constructor1))
                            (PreOrdered.Pack (LiftedConstructor Constructor1 Constructor2)
                                             (PreOrdered.class
                                                (LiftedConstructor Constructor1 Constructor2))).
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
    ITHomomorphism.mixin_of (PreOrdered.Pack Constructor2 (PreOrdered.class Constructor2))
                            (PreOrdered.Pack (LiftedConstructor Constructor1 Constructor2)
                                             (PreOrdered.class
                                                (LiftedConstructor Constructor1 Constructor2))).
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
  SplitContextPair.mixin_of (Finite.Pack (Finite.class Combinator))
                            (SplitTypeUniverse.Pack
                               (LiftedConstructor Constructor1 Constructor2)
                               (SplitTypeUniverse.class (@sum_splitTypeUniverseType Constructor1 Constructor2))).
Proof.
  move: Ctxt1 Ctxt2.
  case: Combinator => T c.
  move => Ctxt1 Ctxt2.
  move: (SplitContextPair.Mixin (Finite.Pack c)
                                (@sum_splitTypeUniverseType Constructor1 Constructor2)
                                (LiftedCtxt1 _ _ _ [ffun c: Finite.Pack c => Ctxt1 c])
                                (LiftedCtxt2 _ _ _ [ffun c : Finite.Pack c => Ctxt2 c])
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

Section CanonicalCombinedContexts.
  Variable Combinator: finType.
  Variables Constructor1 Constructor2: ctor.
  Variables (Gamma1: Ctxt Combinator Constructor1) (Gamma2: Ctxt Combinator Constructor2).
  Let Gammas := [splitCtxtPair of Combinator and _ for
                              @sum_splitCtxtPairType Combinator Constructor1 Constructor2 Gamma1 Gamma2 ].
  Let Gamma :=
    [ffun c: Combinator => (ctxt1 Gammas c) \cap (ctxt2 Gammas c)]. 

  Theorem canonicalCoproductLifted:
    forall M (A: @IT Constructor1) (B: @IT Constructor2),
      [FCL Gamma |- M : (lift1 _ _ A) \cap (lift2 _ _ B)] <->
      [FCL Gamma1 |- M : A] /\ [FCL Gamma2 |- M : B].
  Proof.
    move => M A B.
    move: (FCL__split Gammas (lift1 _ _ A) (lift2 _ _ B)).
    move: (@FCL__hom _ (@sum1_ITHomType Constructor1 Constructor2) Gamma1 M A).
    move: (@FCL__hom _ (@sum2_ITHomType Constructor1 Constructor2) Gamma2 M B).
    rewrite /Gamma /Gammas /= /ctxt1 /ctxt2 /= /SplitContextPair.ctxt1 /SplitContextPair.ctxt2 /sum_splitCtxtPairMixin /=.
    rewrite /sum2_itHomMixin /=.
    move: M A B Gamma1 Gamma2.
    clear Gamma1 Gamma2 Gammas Gamma.
    case: Combinator => /= c fc.
    case: Constructor1 => /= C1 pC1.
    case: Constructor2 => /= C2 pC2.
    move => M A B Gamma1 Gamma2 homprf2 homprf1 splitprf.
    split.
    - move => /(splitprf M (inPartition_lift1 _ _ A) (inPartition_lift2 _ _ B)) [] res1 res2.
      split.
      + apply /homprf1.
        move: res1.
          by rewrite /LiftedCtxt1 ffunK.
      + apply /homprf2.
        move: res2.
          by rewrite /LiftedCtxt2 ffunK.
    - move => [] res1 res2.
      apply /(splitprf M (inPartition_lift1 _ _ A) (inPartition_lift2 _ _ B)).
      rewrite /LiftedCtxt1 ffunK /LiftedCtxt2 ffunK.
      split.
      + by apply /homprf1.
      + by apply /homprf2.
  Qed.

End CanonicalCombinedContexts.

Section InhabitationMachine.
  Variable Combinator: finType.
  Variable Constructor: ctor.
  Variable Gamma: {ffun Combinator -> seq (seq (@MultiArrow Constructor))}. 

  Definition SplitCtxt (Gamma: Ctxt Combinator Constructor) :=
    [ffun c => splitTy (Gamma c)].

  Inductive Rule : Type :=
  | RuleFail : @IT Constructor -> Rule
  | RuleCombinator : @IT Constructor -> Combinator -> Rule
  | RuleApply : @IT Constructor -> @IT Constructor -> @IT Constructor -> Rule.

  Definition lhs (rule: Rule): @IT Constructor :=
    match rule with
    | RuleFail A => A
    | RuleCombinator A _ => A
    | RuleApply A _ _ => A
    end.

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

  Fixpoint computeFailExisting(G: TreeGrammar) (A: @IT Constructor): bool * bool :=
    if G is [:: r & G]
    then
      match r with
      | RuleFail B =>
        if A == B
        then (true, true)
        else
          if checkSubtypes A B
          then (true, RuleFail A \in G)
          else computeFailExisting G A
      | RuleCombinator B c => computeFailExisting G A
      | RuleApply B C D =>
        if (A == D)
        then (false, true)
        else computeFailExisting G A 
      end
    else (false, false).

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
    else if targets is [:: RuleFail _ & targets]
         then dropTargets targets
         else targets.

  Definition accumulateCovers
             (currentTarget: @IT Constructor)
             (toCover: seq (@IT Constructor))
             (s: TreeGrammar * bool)
             (c: Combinator): TreeGrammar * bool :=
    let: (newTargets, failed) := s in
    let mss := Gamma c in
    let: (exist covers _) :=
       coverMachine ([::], map (fun ms =>
                                  Cover (map (fun m => (m, filter (checkSubtypes m.2) toCover)) ms) toCover)
                               mss) in
    let: reducedCovers := reduceMultiArrows covers in
    (commitUpdates newTargets currentTarget c reducedCovers, failed && nilp covers).

  Definition inhabit_cover (targets: TreeGrammar) (currentTarget: @IT Constructor): bool * TreeGrammar :=
    let factors := primeFactors currentTarget in
    let: (newTargets, failed) :=
       foldl (accumulateCovers currentTarget factors) ([::], true) (enum Combinator) in
    if failed
    then (true, targets)
    else (false, targets ++ newTargets).

   Definition OmegaRules (A: @IT Constructor): TreeGrammar :=
    [:: RuleApply A A A & map (fun c => RuleCombinator A c) (enum Combinator)].

  Definition inhabitation_step (stable: TreeGrammar) (targets: TreeGrammar): TreeGrammar * TreeGrammar :=
    match targets with
    | [:: RuleApply A B currentTarget & targets] =>
      if RuleApply A B currentTarget \in stable
      then (stable, targets)
      else
        let (failed, existing) := computeFailExisting stable currentTarget in
        if failed
        then (if ~~existing then [:: RuleFail currentTarget & stable] else stable, dropTargets targets)
        else if existing
             then ([:: RuleApply A B currentTarget & stable], targets)
             else
               if isOmega currentTarget
               then ([:: RuleApply A B currentTarget & OmegaRules currentTarget ++ stable], targets)
               else let: (failed, nextTargets) := inhabit_cover targets currentTarget in
                    if failed
                    then ([:: RuleFail currentTarget & stable], dropTargets targets)
                    else ([:: RuleApply A B currentTarget & stable], nextTargets)
    | [:: RuleCombinator A c & targets] =>
      if RuleCombinator A c \in stable
      then (stable, targets)
      else ([:: RuleCombinator A c & stable], targets)
    | [:: RuleFail _ & targets] => (stable, dropTargets targets)
    | [::] => (stable, [::])
    end.  

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

Arguments lhs [Combinator Constructor].
Arguments computeFailExisting [Combinator Constructor].
Arguments commitMultiArrow [Combinator Constructor].
Arguments commitUpdates [Combinator Constructor].
Arguments dropTargets [Combinator Constructor].
Arguments accumulateCovers [Combinator Constructor].
Arguments inhabit_cover [Combinator Constructor].
Arguments inhabitation_step [Combinator Constructor].
Arguments OmegaRules [Combinator Constructor].
Arguments word [Combinator Constructor].

Inductive InhabitationSemantics
          {Combinator: finType} {Constructor: ctor}
          (Gamma: {ffun  Combinator -> seq (seq (@MultiArrow Constructor))}): TreeGrammar * TreeGrammar -> TreeGrammar * TreeGrammar -> Prop :=
| step__inhab : forall stable target targets,
    InhabitationSemantics Gamma (stable, [:: target & targets]) (inhabitation_step Gamma stable [:: target & targets]).

Arguments InhabitationSemantics [Combinator Constructor].


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
    - move => ? ? /= ->.
        by rewrite orbT.
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

  (*Lemma word_perm: forall G1 G2, perm_eq G1 G2 -> forall A M, word G1 A M -> word G2 A M.
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
  Qed.*)

  Lemma cat_sound: forall G1 G2, FCL_sound G1 -> FCL_sound G2 -> FCL_sound (G1 ++ G2).
  Proof.
    move => G1 G2 prf1 prf2.
      by rewrite /FCL_sound all_cat prf1 prf2.
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
      FCL_sound (accumulateCovers (SplitCtxt Gamma) A (primeFactors A) (G, b) c).1.
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
      FCL_sound (foldl (accumulateCovers (SplitCtxt Gamma) A (primeFactors A)) (G, b) (enum Combinator)).1.
  Proof.
    elim: (enum Combinator) => // c cs IH A G b notOmega__A G_sound.
    rewrite /foldl -/(foldl (accumulateCovers (SplitCtxt Gamma) A (primeFactors A))).
    move: (accumulateCovers_sound A G b c notOmega__A G_sound) => /IH.
    case: (accumulateCovers (SplitCtxt Gamma) A (primeFactors A) (G, b) c) => G' b' res.
      by apply: res.
  Qed.

  Lemma inhabit_cover_sound:
    forall (targets: TreeGrammar) (currentTarget: @IT Constructor),
      ~~isOmega currentTarget ->
      FCL_sound targets ->
      FCL_sound (inhabit_cover (SplitCtxt Gamma) targets currentTarget).2.
  Proof.
    move => targets currentTarget notOmega__currentTarget targets_sound.
    rewrite /inhabit_cover.
    move: (foldl_accumulateCovers_sound currentTarget [::] true notOmega__currentTarget isT).
    case: (foldl (accumulateCovers (SplitCtxt Gamma) currentTarget
                                   (primeFactors currentTarget))
                 ([::], true) (enum Combinator)) => G' [] //=.
    rewrite /FCL_sound all_cat targets_sound => ->.
      by rewrite andbT.
  Qed.

  
  Lemma OmegaRules_sound:
    forall A, isOmega A -> FCL_sound (OmegaRules A).
  Proof.
    move => A isOmega.
    apply /andP.
    split.
    - apply /subtypeMachineP.
      apply: BCD__Trans; first by apply: BCD__omega.
      apply: BCD__Trans; first by apply: BCD__ArrOmega.
      apply: BCD__Sub => //.
      apply /subty__sound.
        by apply: subty__Omega.
    - apply /allP.
      move => r /mapP [] c _ ->.
      apply /subtypeMachineP.
      apply /subty__sound.
        by apply: subty__Omega.
  Qed.

  Lemma inhabitation_step_sound:
    forall stable targets,
      FCL_sound stable ->
      FCL_sound targets ->
      FCL_sound (inhabitation_step (SplitCtxt Gamma) stable targets).1 /\
      FCL_sound (inhabitation_step (SplitCtxt Gamma) stable targets).2.
  Proof.
    move => stable targets stable_sound.
    case: targets => //.
    case.
    - move => A targets /=.
        by move => /(suffix_sound _ _ (dropTargets_suffix _)).
    - move => A c targets /andP [] prf prfs /=.
      case: (RuleCombinator A c \in stable) => //.
      split => //.
        by apply /andP.
    - move => A B C targets /=.
      case: (RuleApply A B C \in stable); first by move => /andP [].
      case: (computeFailExisting stable C) => failed existing.
      case: failed.
      + case: existing.
        * move => /= targets_sound.
          split => //.
          apply: suffix_sound; first by apply: dropTargets_suffix.
            by move: targets_sound => /andP [].
        * move => /= targets_sound.
          split => //.
          apply: suffix_sound; first by apply: dropTargets_suffix.
            by move: targets_sound => /andP [].
      + case: existing.
        * move => /andP [] rule_sound targets_sound.
          split => //.
            by apply /andP.
        * move => /andP [] le_prf targets_sound.
          case isOmega__C: (isOmega C).
          ** split; last by done.
             rewrite /= /FCL_sound (all_cat _ [:: _]) [[:: RuleApply _ _ _ & _ ++ _]]lock /= le_prf /= -lock.
             rewrite -cat_cons /FCL_sound  all_cat stable_sound andbT.
               by apply: (OmegaRules_sound C).
          ** move: (inhabit_cover_sound targets C (negbT isOmega__C) targets_sound).
             case: (inhabit_cover (SplitCtxt Gamma) targets C) => [] nextFailed nextTargets.
             case: nextFailed.
             *** move => nextTargets_sound.
                 split => //.
                   by apply: suffix_sound; first by apply: dropTargets_suffix.
             *** move => nextTargets_sound.
                 split => //.
                   by apply /andP; split.
  Qed.

  Definition parameterTypes (G: @TreeGrammar Combinator Constructor): seq (@IT Constructor) :=
    pmap (fun r => match r with
                | RuleApply _ _ C => Some C
                | _ => None
                end) G.

  Lemma computeFailExisting_exists_param:
    forall G A,
      (A \in (parameterTypes G)) ->
      ~~(computeFailExisting G A).1 ->
      (computeFailExisting G A).2.
  Proof.
    elim => //.
    case.
    - move => B G IH A /IH /=.
      case: (A == B) => //.
        by case: (checkSubtypes A B) => //.
    - by move => B c G IH A /IH /=.
    - move => B C D G IH A /=.
      rewrite in_cons.
      move => /orP.
      case.
      + by move => ->.
      + move => /IH.
          by case: ((A == D)) => //.
  Qed.


  Fixpoint grammarTypes (srcs: seq (@IT Constructor)) (tgt: @IT Constructor): seq (@IT Constructor) :=
    if srcs is [:: src & srcs]
    then [:: src , tgt & grammarTypes srcs (src -> tgt)]
    else [:: tgt ].

  Definition maxParameterTypes (A: @IT Constructor): seq (@IT Constructor) :=
    [:: A & flatten (map (fun c => flatten (map (fun ms => flatten (map (fun m => grammarTypes m.1 m.2 ++ grammarTypes m.1 A)
                                                                  (filterMergeMultiArrows _ (subseqs ms))))
                                             (SplitCtxt Gamma c)))
                         (enum Combinator))].

  Definition targetTypes (G: @TreeGrammar Combinator Constructor): seq (@IT Constructor) := map (@lhs Combinator _) G.

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

  Lemma grammarTypes_tgt_mem: forall srcs tgt n, mkArrow (take n srcs, tgt) \in grammarTypes srcs tgt.
  Proof.
    elim.
    - move => tgt n.
        by rewrite /= /mkArrow /= in_cons eq_refl.
    - move => src srcs IH tgt.
      case.
      + by rewrite take0 /mkArrow /= in_cons in_cons eq_refl orbT.
      + move => n.
          by rewrite /= /mkArrow /= -/(mkArrow (take n srcs, src -> tgt)) in_cons in_cons (IH (src -> tgt) n) orbT orbT.
  Qed.

  Lemma commitMultiArrow_parameterTypes_subset:
    forall (Delta: seq (@IT Constructor)) G c srcs tgt,
      {subset (undup (parameterTypes G)) <= Delta} ->
      {subset srcs <= Delta} ->
      {subset (undup (parameterTypes (commitMultiArrow G c srcs tgt))) <= Delta}.
  Proof.
    move => Delta G c srcs.
    move: G.
    elim: srcs => //.
    move => /= src srcs IH G tgt G_prf inprf__srcs.
    apply: IH.
    - rewrite /=.
      case: (src \in parameterTypes G) => //.
      move => x /orP.
      case.
      + move => /eqP ->.
        apply: inprf__srcs.
          by rewrite in_cons eq_refl.
      + by move => /G_prf.
    - move => x inprf.
      apply: inprf__srcs.
        by rewrite in_cons inprf orbT.
  Qed.

  (*Lemma commitMultiArrow_targetTypes_subset:
    forall (Delta: seq (@IT Constructor)) G c srcs tgt,
      {subset (undup (targetTypes G)) <= Delta} ->
      (forall n, (mkArrow (take n srcs, tgt)) \in Delta) ->
      {subset (undup (targetTypes (commitMultiArrow G c srcs tgt))) <= Delta}.
  Proof.
    move => Delta G c srcs.
    move: G.
    elim: srcs.
    - move => G tgt G_prf inprf__srcstgt.
      rewrite /=.
      case: (tgt \in targetTypes G) => //.
      move => A.
      rewrite in_cons.
      move => /orP.
      case.
      + move => /eqP ->.
          by apply: (inprf__srcstgt 0).
      + by apply: G_prf.
    - move => src srcs IH G tgt G_prf inprf__srcstgt.
      rewrite /=.
      apply: IH.
      + rewrite /=.
        case: (tgt \in targetTypes G) => //.
        move => A.
        rewrite in_cons.
        move => /orP.
        case.
        * move => /eqP ->.
            by apply: (inprf__srcstgt 0).
        * by apply: G_prf.
      + move => n.
          by apply: (inprf__srcstgt n.+1).
  Qed.    *)

  Lemma commitUpdates_parameterTypes_subset:
    forall (Delta: seq (@IT Constructor)) G currentTarget c (ms : seq (@MultiArrow Constructor)),
      {subset (undup (parameterTypes G)) <= Delta} ->
      (forall m,  m \in ms -> {subset m.1 <= Delta}) ->
      {subset (undup (parameterTypes (commitUpdates G currentTarget c ms))) <= Delta}.
  Proof.
    move => Delta G currentTarget c ms.
    move: G.
    elim: ms => // [] [] srcs tgt ms IH G subset__G subset__ms.
    rewrite /=.
    apply: IH.
    - apply: commitMultiArrow_parameterTypes_subset => //.
      apply: (subset__ms (srcs, tgt)).
        by rewrite in_cons eq_refl.
    - move => m inprf__m.
      apply: subset__ms.
        by rewrite in_cons inprf__m orbT.
  Qed.
  
  Lemma accumulateCovers_parameterTypes_subset:
    forall c targets b currentTarget initialTarget,
      {subset (undup (parameterTypes targets)) <= maxParameterTypes initialTarget} ->
      {subset
         (undup (parameterTypes
                   (accumulateCovers (SplitCtxt Gamma) currentTarget (primeFactors currentTarget) (targets, b) c).1)) <=
       maxParameterTypes initialTarget}.
  Proof.
    move => c targets b currentTarget initialTarget.
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
    apply: commitUpdates_parameterTypes_subset => //.
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
    move => inprf__srcstgt src inprf__src.
    rewrite /maxParameterTypes in_cons.
    apply /orP.
    right.
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
        left.
          by apply: grammarTypes_src_mem.
  Qed.

  Lemma maxParameterTypes_initialTarget:
    forall initialTarget, initialTarget \in maxParameterTypes initialTarget.
  Proof. move => initialTarget; by rewrite /maxParameterTypes in_cons eq_refl. Qed.

  Lemma foldl_accumulateCovers_parameterTypes_subset:
     forall targets b currentTarget initialTarget,
       {subset (undup (parameterTypes targets)) <= maxParameterTypes initialTarget} ->
       {subset
          (undup (parameterTypes
                    (foldl (accumulateCovers (SplitCtxt Gamma) currentTarget (primeFactors currentTarget))
                           (targets, b) (enum Combinator)).1)) <=
        maxParameterTypes initialTarget}.
  Proof.
    elim: (enum Combinator) => // c combinators IH targets b currentTarget initialTarget prf.
    rewrite (foldl_cat _ _ [:: c]).
    move: (accumulateCovers_parameterTypes_subset c targets b currentTarget initialTarget prf).
    rewrite [accumulateCovers _ _ _]lock /= -lock.
    case: (accumulateCovers (SplitCtxt Gamma) currentTarget (primeFactors currentTarget) (targets, b) c).
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

  Lemma inhabit_cover_parameterTypes_subset:
    forall targets currentTarget initialTarget,
      {subset (undup (parameterTypes targets)) <= maxParameterTypes initialTarget} ->
      {subset (undup (parameterTypes
                        (inhabit_cover (SplitCtxt Gamma) targets currentTarget).2)) <=
       maxParameterTypes initialTarget}.
  Proof.
    move => targets currentTarget initialTarget targets_subset.
    rewrite /inhabit_cover.
    move: (foldl_accumulateCovers_parameterTypes_subset [::] true currentTarget initialTarget (mem_subseq (sub0seq _))).
    case: (foldl (accumulateCovers (SplitCtxt Gamma) currentTarget (primeFactors currentTarget))
                 ([::], true) (enum Combinator)).
    move => nextTargets failed.
    case: failed => // nextTargets_subset.
    rewrite /parameterTypes pmap_cat.
    move => A.
    rewrite mem_undup mem_cat.
    move => /orP.
    case.
    - rewrite -mem_undup.
        by apply: targets_subset.
    - rewrite -mem_undup.
        by apply: nextTargets_subset.
  Qed.

  (*Lemma OmegaRules_targets:
    forall A, targetTypes (OmegaRules A) =i [:: A].
  Proof.
    move => A B.
    rewrite /= in_cons mem_seq1.
    case AB__eq: (B == A) => //=.
    elim: (enum Combinator) => //= c combinators IH.
      by rewrite in_cons AB__eq IH.
  Qed.*)

  Lemma OmegaRules_params:
    forall A, parameterTypes (OmegaRules A) =i [:: A].
  Proof.
    move => A B.
    rewrite /= in_cons mem_seq1.
    case AB__eq: (B == A) => //=.
      by elim: (enum Combinator).
  Qed.

  Lemma OmegaRules_subset:
    forall A initialTarget,
      (A \in maxParameterTypes initialTarget) ->
      {subset (undup (parameterTypes (OmegaRules A))) <= maxParameterTypes initialTarget}.
  Proof.
    move => A initialTarget inprf.
    move => D.
      by rewrite mem_undup OmegaRules_params mem_seq1 => /eqP ->.
  Qed.

  Lemma inhabitation_step_subset:
    forall initialTarget stable targets,
      {subset (undup (parameterTypes targets)) <= maxParameterTypes initialTarget} ->
      {subset (undup (parameterTypes stable)) <= maxParameterTypes initialTarget} ->
      {subset (undup (parameterTypes (inhabitation_step (SplitCtxt Gamma) stable targets).2)) <= maxParameterTypes initialTarget} /\
      {subset (undup (parameterTypes (inhabitation_step (SplitCtxt Gamma) stable targets).1)) <= maxParameterTypes initialTarget}.
  Proof.
    move => initialTarget stable.
    rewrite /inhabitation_step.
    case => //.
    case.
    - move => A targets target_parametersSubset.
      split => //.
      rewrite /=.
      move => B.
      rewrite mem_undup.
      rewrite /parameterTypes.
      move: (dropTargets_suffix targets) => /suffixP [] prefix /eqP targets_eq inprf.
      apply: target_parametersSubset.
      rewrite mem_undup /= targets_eq /parameterTypes pmap_cat mem_cat.
      apply /orP.
        by right.
    - move => A c targets target_parametersSubset.
      split.
      + move: target_parametersSubset => /= target_parametersSubset.
          by case inprf: (RuleCombinator A c \in stable) => // B inprf__B.
      + by case: (RuleCombinator A c \in stable).
    - move => A B C targets all_target_parameterSubset stable_parameterSubset.
      have target_parametersSubset: {subset undup (parameterTypes targets) <= maxParameterTypes initialTarget}.
      { move => D.
        rewrite mem_undup.
        move => inprf__D.
        apply: all_target_parameterSubset.
          by rewrite mem_undup in_cons inprf__D orbT. }
      case: (RuleApply A B C \in stable) => //.
      have dropTargets_parametersSubset: {subset undup (parameterTypes (dropTargets targets)) <= maxParameterTypes initialTarget}.
      { move => D.
        rewrite mem_undup.
        move => inprf.
        apply: target_parametersSubset.
        move: (dropTargets_suffix targets) => /suffixP [] prefix /eqP ->.
          by rewrite mem_undup /parameterTypes pmap_cat mem_cat inprf orbT. }
      have inprf__C: C \in maxParameterTypes initialTarget.
      { apply: all_target_parameterSubset.
          by rewrite mem_undup in_cons /= eq_refl. }
      have fail_subset: {subset (undup (parameterTypes [:: RuleFail C & stable])) <= maxParameterTypes initialTarget}.
      { move => D /=.
          by apply: stable_parameterSubset. }
      have existing_subset: {subset (undup (parameterTypes [:: RuleApply A B C & stable])) <= maxParameterTypes initialTarget}.
      { move => D /=.
        case: (C \in parameterTypes stable).
        + by apply: stable_parameterSubset.
        + case /orP.
          * by move => /eqP ->.
          * by apply: stable_parameterSubset. }
      have: {subset (undup (parameterTypes [:: RuleApply A B C & OmegaRules C ++ stable])) <= maxParameterTypes initialTarget}.
      { move: (OmegaRules_subset C initialTarget inprf__C) => p2.
        move => D.
        rewrite mem_undup [OmegaRules C]lock /= in_cons.
        case /orP; first  by move => /eqP ->.
        rewrite -lock mem_pmap map_cat mem_cat -mem_pmap -mem_pmap.
        case /orP.
        + rewrite -mem_undup.
            by move => /p2.
        + rewrite -mem_undup.
            by move => /stable_parameterSubset. }
      move: fail_subset.
      move: existing_subset.
      case: (computeFailExisting stable C) => [].
      case.
      + by case.
      + case => //.
        case: (isOmega C) => //.
        move => _ _ _.
        move: (inhabit_cover_parameterTypes_subset targets C initialTarget target_parametersSubset) => nextTarget_parametersSubset.
        have: {subset undup (parameterTypes (dropTargets (inhabit_cover (SplitCtxt Gamma) targets C).2)) <=
               maxParameterTypes initialTarget}.
        { move => D.
          rewrite mem_undup.
          move => inprf.
          apply: nextTarget_parametersSubset.
          move: (dropTargets_suffix (inhabit_cover (SplitCtxt Gamma) targets C).2) => /suffixP [] prefix /eqP ->.
            by rewrite mem_undup /parameterTypes pmap_cat mem_cat inprf orbT. }
        have: {subset undup (parameterTypes [:: RuleApply A B C & stable]) <= maxParameterTypes initialTarget}.
        { move => r.
          rewrite mem_undup in_cons.
          move => /orP.
          case.
          - by move => /eqP ->.
          - rewrite -mem_undup.
              by apply: stable_parameterSubset. }
        move: nextTarget_parametersSubset.
        case: (inhabit_cover (SplitCtxt Gamma) targets C).
          by case.
  Qed.

  Definition inhabit_step_rel (initialTarget: @IT Constructor):
    (TreeGrammar * TreeGrammar) -> (TreeGrammar * TreeGrammar) -> Prop :=
    fun s1 s2 =>
      lexprod (seq (@IT Constructor)) (fun _ => @TreeGrammar Combinator Constructor)
              (ltof _ (fun stableParams => (seq.size (maxParameterTypes initialTarget)).+1 - seq.size stableParams))
              (fun _ => ltof _  seq.size)
              (existT _ (undup (parameterTypes s1.1)) s1.2)
              (existT _ (undup (parameterTypes s2.1)) s2.2).


  Lemma inhabit_step_rel_wf:
    forall initialTarget,
      well_founded (inhabit_step_rel initialTarget).
  Proof.
    move => initialTarget.
    rewrite /inhabit_step_rel.
    apply: wf_inverse_image.
    apply: wf_lexprod.
    - by exact: well_founded_ltof.
    - move => ?.
        by exact: well_founded_ltof.
  Qed.

  Lemma inhabit_step_rel_cons:
    forall initialTarget stable1 targets1 stable2 targets2 r,
      {subset (undup (parameterTypes stable1)) <= maxParameterTypes initialTarget} ->
      inhabit_step_rel initialTarget (stable1, targets1) (stable2, targets2) ->
      inhabit_step_rel initialTarget ([:: r & stable1], targets1) (stable2, targets2).
  Proof.
    move => initialTarget stable1 targets1 stable2 targets2 r subset_params.
    rewrite /inhabit_step_rel.
    set (exleft :=
           (existT (fun _ : seq IT => TreeGrammar)
                   (undup (parameterTypes (stable1, targets1).1))
                   (stable1, targets1).2)).
    rewrite -/exleft.
    have: (projT2 exleft = (stable1, targets1).2) by done.
    have: (projT1 exleft = undup (parameterTypes (stable1, targets1).1)) by done.
    move: exleft => exleft p1 p2 prf.
    move: prf p1 p2.
    rewrite [maxParameterTypes]lock.
    case.
    - move => ? ? ? ? lt_prf /= p1 _.
      move: lt_prf.
      rewrite p1.
      move => lt_prf.
      left.
      case: r => //= _ _ C.
      case: (C \in parameterTypes stable1) => //.
      rewrite /ltof /=.
      apply /leP.
      apply: leq_ltn_trans; last by move: lt_prf => /leP lt_prf; exact lt_prf.
        by apply: leq_sub2r.
    - move => x y ? lt_prf x__eq y__eq.
      move: y__eq lt_prf.
      rewrite [projT2 _]/= => ->.
      rewrite [parameterTypes [:: r & _]]/=.
      case r; try by move => * /=; move: x__eq => /= ->; right.
      move => /= ? ? C.
      case: (C \in parameterTypes stable1); first by move => * /=; move: x__eq => /= ->; right.
      left.
      move: x__eq => /= ->.
      rewrite /ltof /=.
      apply /leP.
      rewrite ltn_sub2l // ltnS uniq_leq_size //; first by rewrite undup_uniq.
          by rewrite -lock.
  Qed.

  Lemma dropTargets_size: forall targets, seq.size (dropTargets targets) <= seq.size targets.
  Proof.
    elim => // r targets IH.
    case: r => //= *;
                by apply: leq_trans; first by exact IH.
  Qed.

  Lemma commitUpdates_nil_eq:
    forall targets currentTarget c covers,
      nilp covers ->
      targets = commitUpdates targets currentTarget c covers.
  Proof.
    move => targets currentTarget c.
      by case => //.
  Qed.

  Lemma reduceMultiArrows_nil:
    forall (covers: seq (@MultiArrow Constructor)), nilp covers -> nilp (reduceMultiArrows covers).
  Proof. by case. Qed.

  Lemma accumulateCovers_failed_targets_eq:
    forall currentTarget toCover (s: TreeGrammar * bool) c,
      s.2 ->
      ((accumulateCovers (SplitCtxt Gamma) currentTarget toCover s c).2) ->
      s.1 = (accumulateCovers (SplitCtxt Gamma) currentTarget toCover s c).1.
  Proof.
    move => currentTarget toCover s c.
    rewrite /accumulateCovers.
    case: (coverMachine ([::], (map (fun ms => Cover (map (fun m => (m, filter (checkSubtypes m.2) toCover)) ms)
                                                  toCover)
                                    (SplitCtxt Gamma c)))).
    move => covers _.
    case: s => newTargets failed.
    case covers__empty: (nilp covers).
    + by case: failed;
        rewrite /= -(commitUpdates_nil_eq newTargets currentTarget c (reduceMultiArrows covers)
                                          (reduceMultiArrows_nil _ covers__empty)).
    + by case: failed => //=.
  Qed.

  Lemma accumulateCovers_failed_rev:
    forall currentTarget toCover (s: TreeGrammar * bool) c,
      (accumulateCovers (SplitCtxt Gamma) currentTarget toCover s c).2 -> s.2.
  Proof.
    move => currentTarget toCover [] targets [] // c.
    rewrite /accumulateCovers.
    case: (coverMachine ([::], (map (fun ms => Cover (map (fun m => (m, filter (checkSubtypes m.2) toCover)) ms)
                                                    toCover)
                                    (SplitCtxt Gamma c)))).
      by move => [].
  Qed.

  Lemma foldl_accumulateCovers_failed_rev:
    forall currentTarget toCover (s: TreeGrammar * bool) combinators,
      (foldl (accumulateCovers (SplitCtxt Gamma) currentTarget toCover) s combinators).2 ->
      s.2.
  Proof.
    move => currentTarget toCover s combinators.
    move: s.
    elim: combinators => // c combinators IH s /IH.
      by apply: accumulateCovers_failed_rev.
  Qed.

  Lemma foldl_accumulateCovers_failed_targets_eq:
    forall currentTarget toCover combinators (s: TreeGrammar * bool),
      (foldl (accumulateCovers (SplitCtxt Gamma) currentTarget toCover) s combinators).2 ->
      s.1 = (foldl (accumulateCovers (SplitCtxt Gamma) currentTarget toCover) s combinators).1.
  Proof.
    move => currentTarget toCover combinatros.
    elim: combinatros => // c combinators IH s prf.
    move: (prf) => /IH prf2.
    rewrite -prf2.
    apply: accumulateCovers_failed_targets_eq.
    + by move: prf => /foldl_accumulateCovers_failed_rev.
    + by move: prf => /= /foldl_accumulateCovers_failed_rev.
  Qed.

  Lemma inhabit_cover_failed_targets_eq:
    forall targets currentTarget,
      (inhabit_cover (SplitCtxt Gamma) targets currentTarget).1 ->
      (inhabit_cover (SplitCtxt Gamma) targets currentTarget).2 = targets.
  Proof.
    rewrite /inhabit_cover.
    elim: (enum Combinator) => // c combinators IH targets currentTarget.
    move: (foldl_accumulateCovers_failed_targets_eq currentTarget (primeFactors currentTarget) [:: c & combinators] ([::], true)).
      by case: (foldl (accumulateCovers (SplitCtxt Gamma) currentTarget (primeFactors currentTarget))
                      ([::], true) [:: c & combinators]) => [] ? [] //=.
  Qed.

  Lemma computeFailExisting_notFound:
    forall G A,
      ~~(computeFailExisting G A).1 ->
      ~~(computeFailExisting G A).2 ->
      ~~(A \in parameterTypes G).
  Proof.
    elim => // r G IH A.
    case: r.
    - move => B /=.
      case AB__eq: (A == B) => //.
      case: (checkSubtypes A B) => //.
        by apply: IH.
    - move => B c /=.
        by apply: IH.
    - move => B C D /=.
      case AD__eq: (A == D) => //.
      rewrite in_cons AD__eq /=.
        by apply: IH.
  Qed.

  Lemma inhabitation_step_sizes:
    forall initialTarget s,
      ~~(nilp s.2) ->
      {subset (undup (parameterTypes s.1)) <= maxParameterTypes initialTarget} ->
      {subset (undup (parameterTypes s.2)) <= maxParameterTypes initialTarget} ->
      inhabit_step_rel initialTarget (inhabitation_step (SplitCtxt Gamma) s.1 s.2) s.
  Proof.
    move => initialTarget [] stable targets /=.
    elim: targets => // r targets IH _.
    case: r.
    - move => A _ _.
      right.
      rewrite /= /ltof.
      apply /leP.
      rewrite ltnS.
        by apply: dropTargets_size.
    - move => A c _ _ /=.
      case: (RuleCombinator A c \in stable).
      + right.
        apply /leP.
          by rewrite ltnS /= leqnn.
      + right.
        rewrite /= /ltof.
          by apply /leP.
    - move => A B C /= stable_parametersSubset.
      case: (RuleApply A B C \in stable); first by right.
      move: (computeFailExisting_notFound stable C).
      case: (computeFailExisting stable C).
      case.
      + case => /= _.
        * right.
          rewrite /=.
          apply /leP.
          rewrite ltnS /=.
            by apply: dropTargets_size.
        * right.
          apply /leP.
          rewrite ltnS /=.
            by apply: dropTargets_size.
      + case.
        * move => _ targets_parametersSubset.
          case inprf__C: (C \in (parameterTypes stable)).
          ** rewrite /inhabit_step_rel /= inprf__C.
             right.
               by apply /leP.
          ** left.
             apply /leP.
             rewrite ltn_sub2l //.
             *** apply: uniq_leq_size; first by apply: undup_uniq.
                 move => D inprf.
                 apply /stable_parametersSubset.
                 rewrite mem_undup.
                 move: inprf.
                   by rewrite mem_undup.
             *** by rewrite /= inprf__C.
        * move => /(fun prf => prf isT isT) notInprf_params__C targets_parametersSubset.
          case: (isOmega C).
          ** left.
             apply /leP.
             rewrite ltn_sub2l //.
             { by apply: uniq_leq_size; first by apply: undup_uniq. }
             { rewrite (@leq_trans (seq.size (undup [:: C & parameterTypes stable]))) //.
               - by rewrite /= (negbTE notInprf_params__C).  
               - apply: uniq_leq_size; first by apply: undup_uniq.
                 move => D.
                 rewrite mem_undup /= [C \in _]in_cons eq_refl /= /parameterTypes /= pmap_cat.
                 repeat rewrite -/(parameterTypes _).
                 have: (parameterTypes [seq RuleCombinator C c | c <- enum Combinator] = [::]) by elim: (enum Combinator) => //.
                 move => ->.
                 rewrite cat0s.
                   by rewrite (negbTE notInprf_params__C) in_cons in_cons mem_undup. }
          ** case: (inhabit_cover (SplitCtxt Gamma) targets C) => [].
             case.
             *** move => _.
                 right.
                 apply /leP.
                 rewrite ltnS.
                   by apply: dropTargets_size.
             *** move => nextTargets.
                 left.
                 apply /leP.
                 apply: ltn_sub2l.
                 **** apply: uniq_leq_size; first by apply: undup_uniq.
                      move => r2 inprf.
                      apply: stable_parametersSubset.
                      move: inprf.
                        by rewrite mem_undup.
                 **** rewrite /=.
                        by move: notInprf_params__C => /negbTE ->.
  Qed.
 
  Definition FailSound G :=
    forall A, RuleFail A \in G -> forall M, [FCL Gamma |- M : A] -> False.

  Lemma FailSound_cat:
    forall G1 G2, FailSound G1 -> FailSound G2 -> FailSound (G1 ++ G2).
  Proof.
    move => G1 G2 prf1 prf2 A.
    rewrite mem_cat.
    move => /orP.
    case.
    - by move => /prf1.
    - by move => /prf2.
  Qed.

  Lemma cat_FailSound:
    forall G1 G2, FailSound (G1 ++ G2) -> FailSound G1 /\ FailSound G2.
  Proof.
    move => G1 G2 prf.
    split.
    - move => A inprf.
      apply: prf.
        by rewrite mem_cat inprf.
    - move => A inprf.
      apply: prf.
        by rewrite mem_cat inprf orbT.
  Qed.

  Lemma computeFailExisting_FailSound:
    forall G A, FailSound G -> (computeFailExisting G A).1 -> FailSound [:: RuleFail A & G].
  Proof.
    elim => // r G IH A.
    case: r.
    - move => B /=.
      case AB__eq: (A == B).
      + rewrite (eqP AB__eq).
        move => fsprf _ C.
        rewrite in_cons.
        case /orP; last by apply: fsprf.
        move => CB__eq.
        apply: fsprf.
          by rewrite in_cons CB__eq.
      + case le_prf: (checkSubtypes A B).
        * move => fsprf _ C.
          rewrite in_cons.
          case /orP; last by apply: fsprf.
          move => /eqP [] CA__eq.
          move: le_prf.
          rewrite CA__eq.
          move => /subtypeMachineP le_prf M /(fun prf => FCL__Sub _ prf le_prf).
          apply: fsprf.
            by rewrite mem_head.
        * move => fsprf failprf C.
          rewrite in_cons in_cons orbCA -in_cons.
          case /orP.
          ** move => /eqP CB__eq.
             apply: fsprf.
             rewrite CB__eq.
               by apply: mem_head.
          ** apply: IH => //.
               by move: fsprf => /(cat_FailSound [:: _]) [].
    - move => B c /= .
      move => /(cat_FailSound [::_]) [] fsprf1 fsprf2 failedprf.
      move: (IH A fsprf2 failedprf) => /(cat_FailSound [:: _]) [] fsprf3 _.
        by apply (FailSound_cat [:: _]).
    - move => B C D /=.
      case (A == D) => //.
      move => /(cat_FailSound [::_]) [] fsprf1 fsprf2 failedprf.
      move: (IH A fsprf2 failedprf) => /(cat_FailSound [:: _]) [] fsprf3 _.
        by apply (FailSound_cat [:: _]).
  Qed.

  Lemma accumulateCovers_FailSound:
    forall C c srcs targets,
      ~~isOmega C ->
      (accumulateCovers (SplitCtxt Gamma) C (primeFactors C) (targets, true) c).2 ->
      [FCL Gamma |- (Var c) : mkArrow (srcs, C)] -> False.
  Proof.
    move => C c srcs targets notOmega__C.
    rewrite /accumulateCovers.
    rewrite /=.
    move => disprf prf.
    have: [bcd (Gamma c) <= (mkArrow (srcs, C))] by move: prf => /minimalType_minimal.
    move => /coverMachine_splitTy_complete.
    move => /(fun prf => prf [::] notOmega__C) /= res.
    suff: false by done.
    apply: res.
    move: disprf.
    case: (coverMachine
             ([::], map (fun ms =>
                          Cover (map (fun m => (m, filter (checkSubtypes m.2) (primeFactors C))) ms) (primeFactors C))
                       (SplitCtxt Gamma c))).
    rewrite /SplitCtxt ffunE.
      by case.
  Qed.

  Lemma inhabit_cover_FailSound:
    forall targets C,
      ~~isOmega C ->
      (inhabit_cover (SplitCtxt Gamma) targets C).1 ->
      forall M, [FCL Gamma |- M : C] -> False.
  Proof.
    move => targets C notOmega__C disprf M.
    move: (unapply_revapply M) => <- /FCL__invApp [] srcs [] srcs_size /(fun prf => prf (seq.size srcs)).
    rewrite nth_default; last by rewrite srcs_size.
    rewrite nth_default //.
    move: notOmega__C disprf.
    clear...
    rewrite /inhabit_cover.
    have: (unapply M).1 \in (enum Combinator) by apply: mem_enum.
    move: [::].
    elim: (enum Combinator) => // c combinators IH rules.
    rewrite in_cons.
    case /orP.
    - move => /eqP ->.
      move => /(accumulateCovers_FailSound C c srcs rules).
      rewrite [accumulateCovers _ _ _]lock.
      rewrite /= -lock.
      move => disprf foldprf.
      apply: disprf.
      apply: (foldl_accumulateCovers_failed_rev C (primeFactors C) _ combinators).
      move: foldprf.
        by case: (foldl (accumulateCovers (SplitCtxt Gamma) C (primeFactors C))
                        (accumulateCovers (SplitCtxt Gamma) C (primeFactors C)
                                          (rules, true) c) combinators) => [] ? [].
    - move => inprf notOmega__C.
      rewrite [accumulateCovers _ _ _]lock /= -lock.
      move => foldprf.
      have: (accumulateCovers (SplitCtxt Gamma) C (primeFactors C) (rules, true) c).2 = true.
      { apply: (foldl_accumulateCovers_failed_rev C (primeFactors C) _ combinators).
        move: foldprf.
        by case: (foldl (accumulateCovers (SplitCtxt Gamma) C (primeFactors C))
                        (accumulateCovers (SplitCtxt Gamma) C (primeFactors C)
                                          (rules, true) c) combinators) => [] ? []. }
      move: foldprf.
      move: (accumulateCovers (SplitCtxt Gamma) C (primeFactors C) (rules, true) c) => [] nextRules [] //.
      move => foldprfs _.
        by apply: (IH nextRules).
  Qed.

  Lemma OmegaRules_FailSound:
    forall A, FailSound (OmegaRules A).
  Proof.
    move => A.
    rewrite /OmegaRules.
    move => B.
    rewrite in_cons /=.
      by elim: (enum Combinator).
  Qed.

  Lemma inhabit_step_FailSound:
    forall stable targets,
      FailSound stable ->
      FailSound (inhabitation_step (SplitCtxt Gamma) stable targets).1.
  Proof.
    move => stable targets.
    case: targets => //.
    case => //.
    - move => A c targets /=.
        by case: (RuleCombinator A c \in stable).
    - move => A B C targets fsprf__stable /=.
      case: (RuleApply A B C \in stable) => //.
      move: (computeFailExisting_FailSound stable C fsprf__stable).
      case: (computeFailExisting stable C) => [] [].
      + case => //.
          by move => /(fun prf => prf isT).
      + case => // _.
        move: (OmegaRules_FailSound C) => fsprf_omega.
        case isOmega__C: (isOmega C); first by rewrite -cat_cons; apply: FailSound_cat.
        move: (inhabit_cover_FailSound targets C (negbT isOmega__C)).
        case: (inhabit_cover (SplitCtxt Gamma) targets C) => [] [].
        * move => nextTargets /(fun prf => prf isT) res D.
          rewrite /FailSound in_cons.
          case /orP.
          ** by move => /eqP [] ->.
          ** by move => /fsprf__stable.
        * move => nextTargets _.
            by exact fsprf__stable.
  Qed.

  Definition noTargetFailures targets := all (fun r => if r is RuleFail _ then false else true) targets.

  Lemma noTargetFailures_suffix:
    forall targets nextTargets,
      noTargetFailures targets ->
      suffix nextTargets targets ->
      noTargetFailures nextTargets.
  Proof.
    move => targets nextTargets noFail /suffixP [] prefix /eqP targets__eq.
    move: noFail.
      by rewrite targets__eq /noTargetFailures all_cat => /andP [].
  Qed.

  Lemma inhabit_cover_noTargetFailures:
    forall targets C,
      noTargetFailures targets ->
      noTargetFailures (inhabit_cover (SplitCtxt Gamma) targets C).2.
  Proof.
    move => targets C noFail.
    rewrite /inhabit_cover.
    suff: noTargetFailures ((foldl (accumulateCovers (SplitCtxt Gamma) C (primeFactors C))
                                   ([::], true) (enum Combinator)).1).
    { case: (foldl (accumulateCovers (SplitCtxt Gamma) C (primeFactors C))
                   ([::], true) (enum Combinator)) => nextTargets [] //.
      move: noFail.
        by rewrite /noTargetFailures all_cat => -> ->. }
    have: (noTargetFailures ([::], true).1) by done.
    move: ([::], true).
    elim: (enum Combinator) => // c combinators IH [] nextTargets failed nextTargetsOk.
    rewrite /=.
    apply: IH.
    rewrite /accumulateCovers.
     case: (coverMachine
             ([::], map (fun ms =>
                          Cover (map (fun m => (m, filter (checkSubtypes m.2) (primeFactors C))) ms) (primeFactors C))
                       (SplitCtxt Gamma c))) => covers _ /=.
     rewrite /commitUpdates.
     move: nextTargets nextTargetsOk C.
     clear...
     elim: (reduceMultiArrows (covers)) => // [] [] srcs tgt nextCovers IH nextTargets nextTargetsOk C.
     apply: IH.
     rewrite /= /commitMultiArrow.
     move: nextTargets nextTargetsOk C.
     elim: srcs => // src srcs IH nextTargets nextTargetsOk C.
       by apply: IH.
  Qed.

  Lemma inhabitation_step_noTargetFailures:
    forall stable targets,
      noTargetFailures targets ->
      noTargetFailures (inhabitation_step (SplitCtxt Gamma) stable targets).2.
  Proof.
    move => stable.
    case => // r targets.
    case: r.
    - done.
    - rewrite /=.
      move => A c.
        by case: (RuleCombinator A c \in stable) => //.
    - move => A B C noFail /=.
      move: (noTargetFailures_suffix _ _ noFail (dropTargets_suffix [:: RuleApply A B C & targets])) => noFail_dropped.
      case: (RuleApply A B C \in stable) => //.
      case: (computeFailExisting stable C).
      case; case => //.
      case: (isOmega C) => //.
      move: (inhabit_cover_noTargetFailures targets C noFail).
      case: (inhabit_cover (SplitCtxt Gamma) targets C) => [] failed nextTargets.
        by case: failed => //.
  Qed.

  
  Definition updateGroups (groups: seq (@TreeGrammar Combinator Constructor)) (r: Rule) :=
    if r is RuleCombinator A c
    then [:: [:: RuleCombinator A c] & groups]
    else if groups is [:: g1 & groups]
         then [:: rcons g1 r & groups]
         else [:: [:: r] ].

  Definition group (targets: @TreeGrammar Combinator Constructor): seq (@TreeGrammar Combinator Constructor) :=
    rev (foldl updateGroups [::] targets).

  Lemma cancel_group_flatten: cancel group flatten.
  Proof.
    move => targets.
    rewrite /group.
    have: (flatten (rev [::]: seq (@TreeGrammar Combinator Constructor)) = [::]) by done.
    rewrite -[X in (_ -> _ = X)%type]cat0s.
    move: [::] [::].
    elim: targets.
    - move => targets2 groups /=.
        by rewrite cats0.
    - move => r targets IH targets2 groups eq_prf /=.
      rewrite (IH (targets2 ++ [:: r])).
      + by rewrite -catA cat_cons cat0s.
      + case: r.
        * move => A.
          move: eq_prf.
          case: groups.
          ** by move => <- /=.
          ** move => /= targets3 groups.
             rewrite /= rev_cons rev_cons => <-.
               by rewrite -cats1 flatten_cat -cats1 /= -cats1 flatten_cat /= cats0 cats0 catA.
        * move => A c.
            by rewrite /= rev_cons -cats1 flatten_cat /= eq_prf.
        * move => A B C.
          move: eq_prf.
          case: groups.
          ** by move => <- /=.
          ** move => /= targets3 groups.
             rewrite /= rev_cons rev_cons => <-.
               by rewrite -cats1 flatten_cat -cats1 /= -cats1 flatten_cat /= cats0 cats0 catA.
  Qed.

  Lemma updateGroups0:
    forall r, updateGroups [::] r = [:: [:: r]].
  Proof. by case. Qed.

  Lemma group_notComb:
    forall group groups targets,
      all (fun r => if r is RuleCombinator _ _ then false else true) targets ->
      foldl updateGroups [:: group & groups] targets = [:: group ++ targets & groups].
  Proof.
    move => group groups targets.
    move: group groups.
    elim: targets.
    - move => group groups _ /=.
        by rewrite cats0.
    - move => r targets IH group groups /andP [] notcomb prfs /=.
      move: notcomb.
      case: r => //=.
      + move => A _.
          by rewrite (IH _ _ prfs) -cats1 -catA.
      + move => A B C _.
          by rewrite (IH _ _ prfs) -cats1 -catA.
  Qed.

  Lemma group_comb:
    forall groups A c targets,
      foldl updateGroups groups [:: RuleCombinator A c & targets] =
      (foldl updateGroups [::] [:: RuleCombinator A c & targets]) ++ groups.
  Proof.
    move => groups A c targets /=.
    have: (forall r, updateGroups [:: [:: RuleCombinator A c] & groups ] r = updateGroups [:: [:: RuleCombinator A c]] r ++ groups)
      by case.
    move: groups [:: [:: RuleCombinator A c] & groups] [:: [:: RuleCombinator A c]].
    elim: targets.
    - by move => groups gs1 gs2 /= /(fun prf => prf (RuleCombinator A c)) /= [].
    - move => r targets IH groups gs1 gs2 prf.
      rewrite /=.
      apply: IH.
      rewrite (prf r).
      clear prf.
      case: r.
      + move => B r.
        case: gs2; by case: r.
      + move => B d r.
        case: gs2; by case: r.
      + move => B C D r.
        case: gs2; by case: r.
  Qed.

  Lemma dropTargets_notCombinator:
    forall targets prefix,
      targets = prefix ++ dropTargets targets ->
      all (fun r => if r is RuleCombinator _ _ then false else true) prefix.
  Proof.
    elim.
    - by case.
    - move => r.
      case r__eq: r.
      + move => targets IH /=.
        case => //.
        case => //= A prefix.
          by case => _ /IH.
      + move => targets _ /=.
        case => // r2 prefix.
        rewrite -[X in X = _]cat0s => /(f_equal seq.size) /eqP.
        do 2 rewrite size_cat.
          by rewrite eqn_add2r /= -addn1 eq_sym addn_eq0 andbF.
      + move => targets IH /=.
        case => //.
        case => //= A B C prefix.
          by case => _ _ _ /IH.
  Qed.

  Lemma dropTargets_combinatorOrEmpty:
    forall targets,
      if dropTargets targets is [:: RuleCombinator A c & _]
      then true
      else if dropTargets targets is [::]
           then true
           else false.
  Proof. elim => //; by case. Qed.

  Lemma group_split: forall r targets prefix,
      targets = prefix ++ dropTargets targets ->
      group [:: r & targets] = [:: [:: r & prefix] & group (dropTargets targets)].
  Proof.
    move => r targets prefix eq_prf.
    rewrite /group /= [X in foldl _ _ X]eq_prf.
    rewrite updateGroups0.
    rewrite foldl_cat (group_notComb [:: r] [::] prefix (dropTargets_notCombinator targets prefix eq_prf)).
    move: (dropTargets_combinatorOrEmpty targets).
    move: eq_prf => _.
    case: (dropTargets targets) => //.
    case => // A c rest _.
      by rewrite group_comb rev_cat.
  Qed.

  Fixpoint future_word stable targets A M : Prop :=
    match M with
    | Var c =>
      (RuleCombinator A c \in stable)
      \/ (exists g, (g \in (group targets)) /\
              (RuleCombinator A c \in g) /\
              (forall B, (B \in parameterTypes g) -> exists M, [FCL Gamma |- M : B]))
    | M @ N =>
      exists B C, (RuleApply A B C \in stable /\ future_word stable targets B M /\ future_word stable targets C N) \/
               (exists g, (g \in (group targets)) /\
                     (RuleApply A B C \in g) /\
                     (future_word stable targets B M) /\
                     (forall B, (B \in parameterTypes g) -> exists M, [FCL Gamma |- M : B]) /\
                     [FCL Gamma |- N : C])
    end.
                                              
  Lemma future_word_word: forall stable A M, future_word stable [::] A M -> word stable A M.
  Proof.
    move => stable A M.
    move: A.
    elim: M.
    - move => c A /=.
      case.
      + move => inprf.
        apply /hasP.
        exists (RuleCombinator A c) => //.
          by do 2 rewrite eq_refl.
      + by case => ? [].
    - move => M IH__M N IH__N A /=.
      case => B [] C.
      case.
      + move => [] inprf [] /IH__M prf__M /IH__N prf__N.
        apply /hasP.
        * exists (RuleApply A B C) => //.
            by rewrite eq_refl prf__M prf__N.
      + by move => [] ? [].
  Qed.

  Lemma future_word_weaken:
    forall stable1 targets stable2,
      {subset stable1 <= stable2} ->
      forall A M,
        future_word stable1 targets A M ->
        future_word stable2 targets A M.
  Proof.
    move => stable1 targets stable2 subset_prf A M.
    move: A.
    elim: M.
    - move => c A /=.
      case.
      + move => /subset_prf result.
          by left.
      + move => result.
          by right.
    - move => M IH__M N IH__N A /= [] B [] C.
      case.
      + move => [] /subset_prf inprf [] /IH__M prf__M /IH__N prf__N.
        exists B, C.
          by left.
      + move => [] g [] inprf [] inprf__g [] /IH__M prf__M inhab_prf.
        exists B, C.
        right.
          by (exists g).
  Qed.

  Lemma rule_absorbl:
    forall stable targets A c,
      (RuleCombinator A c \in stable) ->
      forall B M, future_word stable [:: RuleCombinator A c & targets] B M ->
             future_word stable targets B M.
  Proof.
    move => stable targets A c inprf B M.
    move: B.
    elim: M.
    - move => d B /=.
      case.
      + by move => ?; left.
      + case r__eq: (RuleCombinator A c == RuleCombinator B d).
        * rewrite -(eqP r__eq).
            by move => _; left.
        * move => [] g [] /=.
          move: (dropTargets_suffix targets) => /suffixP [] prefix /eqP eq_prf.
          rewrite (group_split (RuleCombinator A c) targets prefix eq_prf) in_cons.
          case /orP.
          ** move => /eqP ->.
             move: (dropTargets_notCombinator _ _ eq_prf) r__eq => /allP disprf.
               by rewrite eq_sym in_cons => -> /= [] /disprf.
          ** move => inprf__g props.
             right.
             exists g; split => //.
             rewrite eq_prf /group.
             move: eq_prf => /(dropTargets_notCombinator).
             case: prefix => //= r prefix /andP [] _ notCombinators.
             rewrite updateGroups0 foldl_cat group_notComb //.
             move: (dropTargets_combinatorOrEmpty targets) inprf__g.
             case: (dropTargets targets) => //; case => // C e dropped _.
             rewrite group_comb rev_cat -/(group _) mem_cat => ->.
               by rewrite orbT.
    - move => M IH__M N IH__N B /= [] C [] D.
      case.
      + move => [] inprf__r [] /IH__M prf__M /IH__N prf__N.
        exists C, D.
          by left.
      + move => [] g [].
        move: (dropTargets_suffix targets) => /suffixP [] prefix /eqP eq_prf.
        rewrite (group_split _ _ _ eq_prf) in_cons.
        case /orP.
        * move => /eqP -> [].
          rewrite in_cons /=.
          move => inprf__BCD [] /IH__M prf__M params_prf.
          exists C, D.
          right.
          exists prefix.
          split; last split => //.
          rewrite eq_prf /group.
          move: eq_prf => /dropTargets_notCombinator.
          rewrite foldl_cat.
          clear params_prf.
          move: inprf__BCD.
          case: prefix => //.
          move => r prefix _ /andP [] _ notCombinators.
          rewrite /= updateGroups0 group_notComb //.
          move: (dropTargets_combinatorOrEmpty targets).
          case: (dropTargets targets).
          ** move => _ /=.
               by apply: mem_head.
          ** case => // E d dropped _.
               by rewrite group_comb rev_cat mem_cat /= mem_head.
        * move => inprf__g [] inprf__BCD [] /IH__M prf__M param_prfs.
          exists C, D.
          right.
          exists g.
          split => //.
          rewrite eq_prf.
          move: eq_prf => /dropTargets_notCombinator.
          move: inprf__g.
          clear...
          case: prefix => //.
          move => r prefix inprf__g /andP [] _ notCombinators.
          rewrite /group foldl_cat /= updateGroups0 group_notComb //.
          move: (dropTargets_combinatorOrEmpty targets) inprf__g.
          case: (dropTargets targets) => //; case => // A c dropped _.
          rewrite group_comb rev_cat mem_cat -/(group _) => ->.
            by rewrite orbT.
  Qed.

  Fixpoint takeTargets (targets: @TreeGrammar Combinator Constructor) :  @TreeGrammar Combinator Constructor :=
    match targets with
    |[:: RuleApply A B C & targets] => [:: RuleApply A B C & (takeTargets targets)]
    |[:: RuleFail A & targets] => [:: RuleFail A & (takeTargets targets)]
    | _ => [::]
    end.

  Lemma takeDropTargets: forall targets, targets = (takeTargets targets) ++ (dropTargets targets).
  Proof.
    elim => // r targets IH.
    case: r => //.
    - move => A /=.
        by rewrite [X in [:: _ & X] = _]IH.
    - move => A B C /=.
        by rewrite [X in [:: _ & X] = _]IH.
  Qed.    

  Definition FCL_complete initialType stable targets :=
    forall A, (A == initialType)
         || (A \in parameterTypes stable)
         || (A \in targetTypes (pmap (ohead \o rev) (group targets))) ->
         forall M, [FCL Gamma |- M : A] -> future_word stable targets A M.

  Lemma FCL_complete_emptyTargets:
    forall initialType stable, FCL_complete initialType stable [::] ->
              forall A, (A == initialType) || (A \in parameterTypes stable) ->
                   forall M, [FCL Gamma |- M : A] -> word stable A M.
  Proof.
    move => initalType stable prf_complete A inprf__A M prf.
    apply: future_word_word.
    apply: prf_complete => //.
      by rewrite inprf__A.
  Qed.

  Lemma future_word_dropFailed:
    forall stable targets A B C,
      (forall M, [FCL Gamma |- M : C] -> False) ->
      forall D M, future_word stable [:: RuleApply A B C & targets] D M ->
             future_word stable (dropTargets targets) D M.
  Proof.
    move => stable targets A B C disprf__C D M.
    move: D.
    elim: M.
    - move => D c.
      case.
      + by left.
      + move => [] g [].
        move: (dropTargets_suffix targets) => /suffixP [] prefix /eqP eq_prf.
        rewrite (group_split _ _ _ eq_prf) in_cons.
        case /orP.
        * by move => /eqP -> [] _ /(fun prf => prf C (mem_head _ _)) [] ? /disprf__C.
        * move => inprf__g props.
          right.
            by (exists g).
    - move => M IH__M N IH__N D [] E [] F.
      rewrite -/future_word.
      case.
      + move => [] inprf__r [] /IH__M prf__M /IH__N prf__N.
        exists E, F.
          by left.
      + move => [] g [].
        move: (dropTargets_suffix targets) => /suffixP [] prefix /eqP eq_prf.
        rewrite (group_split _ _ _ eq_prf) in_cons.
        case /orP.
        * by move => /eqP -> [] _ [] _ [] /(fun prf => prf C (mem_head _ _)) [] ? /disprf__C.
        * move => inprf__g [] inprf__r [] /IH__M prf__M props.
          exists E, F.
          right.
            by exists g.
  Qed.

  Lemma takeDropTargets_empty:
    forall targets, takeTargets (dropTargets targets) = [::].
  Proof.
    move => targets.
    move: (dropTargets_combinatorOrEmpty targets).
    case: (dropTargets targets) => //.
      by case.
  Qed.

  Lemma dropTargetsI:
    forall targets, dropTargets (dropTargets targets) = dropTargets targets.
  Proof.
    move => targets.
    move: (dropTargets_combinatorOrEmpty targets).
    case: (dropTargets targets) => //.
      by case.
  Qed.

  Lemma computeFailExisting_failed_complete:
    forall initialType stable targets A B C,
      FailSound stable ->
      (computeFailExisting stable C).1 ->
      FCL_complete initialType stable [:: RuleApply A B C & targets] ->
      FCL_complete initialType
                   (if ~~(computeFailExisting stable C).2 then [:: RuleFail C & stable] else stable)
                   (dropTargets targets).
  Proof.
    move => initialType stable targets A B C fsprf /(computeFailExisting_FailSound stable C fsprf) fsprf2 prf_complete D inprf__D M prf.
    suff: (future_word stable (dropTargets targets) D M).
    { case: (~~(computeFailExisting stable C).2) => // prf_complete2.
      apply: future_word_weaken; last by exact prf_complete2.
      move => E.
      rewrite in_cons => ->.
        by rewrite orbT. }
    apply: (future_word_dropFailed _ _ A B C).
    - by apply: fsprf2; apply: mem_head.
    - move: inprf__D.
      case: (~~(computeFailExisting stable C).2).
      + case /orP.
        * rewrite /=.
          case /orP.
          ** move => inprf.
             apply: prf_complete => //.
               by rewrite inprf.
          ** move => inprf.
             apply: prf_complete => //.
               by rewrite inprf orbT.
        * move: (dropTargets_suffix targets) => /suffixP [] prefix /eqP targets__eq.
          move => inprf__D.
          apply: prf_complete => //.
          move: inprf__D.
          rewrite (group_split _ _ _ targets__eq) (pmap_cat _ [::_]) /targetTypes map_cat mem_cat => ->.
            by repeat rewrite orbT.
      + case /orP.
        * move => inprf__D.
          apply: prf_complete => //.
            by rewrite inprf__D.
        * move: (dropTargets_suffix targets) => /suffixP [] prefix /eqP targets__eq.
          move => inprf__D.
          apply: prf_complete => //.
          move: inprf__D.
          rewrite (group_split _ _ _ targets__eq) (pmap_cat _ [::_]) /targetTypes map_cat mem_cat => ->.
            by repeat rewrite orbT.
  Qed.

  Lemma rule_absorbl_apply:
    forall initialType stable targets A B C,
      FCL_complete initialType stable [:: RuleApply A B C & targets] ->
      (RuleApply A B C \in stable) ->
      forall D M, future_word stable [:: RuleApply A B C & targets] D M ->
             future_word stable targets D M.
  Proof.
    move => initialType stable targets A B C prf_complete inprf D M.
    move: D.
    elim: M.
    - move => c D.
      case.
      + move => inprf__r.
          by left.
      + clear prf_complete inprf.
        move => [] g [].
        move: (dropTargets_suffix targets) => /suffixP [] prefix /eqP targets__eq.
        rewrite (group_split _ _ _ targets__eq) in_cons.
        case /orP.
        * move => /eqP ->.
          move: (dropTargets_notCombinator _ _ targets__eq) => /allP disprf.
            by rewrite in_cons /= => [] [] /disprf.
        * move => inprf__g props.
          right.
          exists g; split => //.
          rewrite targets__eq /group foldl_cat.
          move: targets__eq.
          case: prefix => // r prefix targets__eq.          
          move: (dropTargets_notCombinator _ _ targets__eq) => /andP [] _ notCombinators.
          rewrite /= updateGroups0 group_notComb //.
          move: (dropTargets_combinatorOrEmpty targets).
          move: inprf__g.
          case: (dropTargets targets) => //.
          case => // E d droppedTargets inprf__g _.
            by rewrite group_comb rev_cat -/(group _) mem_cat inprf__g orbT.
    - move => M IH__M N IH__N D [] E [] F.
      repeat rewrite -/future_word.
      case.
      + move => [] inprf__DEF [] /IH__M prf__M /IH__N prf__N.
        exists E, F.
          by left.
      + move => [] g [].
        move: (dropTargets_suffix targets) => /suffixP [] prefix /eqP targets__eq.
        rewrite (group_split _ _ _ targets__eq) in_cons.
        case /orP.
        * move => /eqP ->.
          rewrite in_cons => [] [].
          case /orP.
          ** move => /eqP [] -> -> ->.
             clear D E F.
             move => [] /IH__M prf__M [] prfs /prf_complete mkPrf__N.
             have prf__N: (future_word stable targets C N).
             { apply: IH__N.
               apply: mkPrf__N.
               apply /orP; left; apply /orP; right.
               rewrite mem_pmap.
                 by move: inprf => /(map_f (fun r => if r is RuleApply _ _ C then Some C else None)). }
             exists B, C.
               by left.
          ** move => inprf__DEF [] /IH__M prf__M [] inhabprf prf.
             exists E, F.
             right.
             exists prefix.
             split; last split => //; last split => //; last split => //.
             *** rewrite targets__eq /group foldl_cat.
                 move:  targets__eq inprf__DEF (dropTargets_notCombinator _ _ targets__eq).
                 clear inhabprf.
                 case: prefix => //.
                 move => r prefix targets__eq _ /andP [] _ notCombinators.
                 rewrite /= updateGroups0 (group_notComb _ _ _ notCombinators).
                 move: (dropTargets_combinatorOrEmpty targets).
                 case: (dropTargets targets).
                 **** by rewrite /= mem_seq1.
                 **** case => // ? ? ? _.
                        by rewrite group_comb rev_cat mem_cat mem_seq1 /= eq_refl.
             *** move => G inprf__G.
                 apply: inhabprf.
                   by rewrite in_cons inprf__G orbT.
        * move => inprf__g [] inprf__DEF [] /IH__M prf__M props.
          exists E, F.
          right.
          exists g.
          split; last split => //.
          rewrite targets__eq /group foldl_cat.
          move: targets__eq inprf__DEF inprf__g (dropTargets_notCombinator _ _ targets__eq).
          case: prefix => //.
          move => r prefix targets__eq _ inprf__g /andP [] _ notCombinators.
          rewrite /= updateGroups0 (group_notComb _ _ _ notCombinators).
          move: inprf__g (dropTargets_combinatorOrEmpty targets).
          case: (dropTargets targets) => //.
          case => // ? ? ? inprf__g _.
            by rewrite group_comb rev_cat mem_cat inprf__g orbT.
  Qed.

  Lemma computeFailExisting_existing:
    forall G A,
      ~~(computeFailExisting G A).1 ->
      (computeFailExisting G A).2 ->
      (A \in parameterTypes G).
  Proof.
    elim => // r G IH A.
    case: r.
    - move => B /=.
      case AB__eq: (A == B) => //.
      case: (checkSubtypes A B) => //.
        by apply: IH.
    - move => B c /=.
        by apply: IH.
    - move => B C D /=.
      case AD__eq: (A == D); first by rewrite (eqP AD__eq) mem_head.
      move => noFail existing.
        by rewrite in_cons IH // orbT.
  Qed.

  Lemma OmegaRules_future_word:
    forall stable targets C M,
      isOmega C ->
      future_word (OmegaRules C ++ stable) targets C M.
  Proof.
    move => stable targets C M isOmega__C.
    elim: M.
    - move => c.
      left.
      rewrite mem_cat.
      apply /orP; left.
      rewrite /= in_cons.
      apply /orP; right.
      apply /mapP.
      exists c => //.
        by apply: mem_enum.
    - move => M IH__M N IH__N.
      exists C, C.
      left; split => //.
        by apply: mem_head.
  Qed.

  Lemma rule_MP:
    forall stable targets A B C,
      (forall N, [FCL Gamma |- N : C] -> future_word [:: RuleApply A B C & stable] targets C N) ->
      forall D M, future_word stable [:: RuleApply A B C & targets] D M ->
             future_word [:: RuleApply A B C & stable] targets D M.
  Proof.
    move => stable targets A B C complete_C D M.
    move: D.
    elim: M.
    - move => c D.
      case.
      + move => inprf.
        left.
          by rewrite in_cons inprf orbT.
      + move => [] g [].
        move: (dropTargets_suffix targets) => /suffixP [] prefix /eqP targets__eq.
        rewrite (group_split _ _ _ targets__eq).
        rewrite in_cons.
        case /orP.
        * move => /eqP -> [].
            by move: (dropTargets_notCombinator _ _ targets__eq) => /allP disprf /disprf.
        * move => inprf props.
          right.
          exists g; split => //.
          rewrite targets__eq /group foldl_cat.
          move: (dropTargets_combinatorOrEmpty targets) inprf.
          case: (dropTargets targets) => //.
          case => // ? ? ? _ inprf__g.
            by rewrite group_comb rev_cat mem_cat inprf__g orbT.
    - move => M IH__M N IH__N D /= [] E [] F.
      case.
      + move => [] inprf [] /IH__M prf__M /IH__N prf__N.
        exists E, F.
        left; split => //.
          by rewrite in_cons inprf orbT.
      + move => [] g [].
        move: (dropTargets_suffix targets) => /suffixP [] prefix /eqP targets__eq.
        rewrite (group_split _ _ _ targets__eq).
        rewrite in_cons.
        case /orP.
        * move => /eqP -> [].
          rewrite in_cons.
          case /orP.
          ** move => /eqP r__eq [] /IH__M prf__M [] prfs prf.
             rewrite -r__eq.
             exists E, F.
             left.
             split; last split => //.
             *** by apply: mem_head.
             *** by rewrite r__eq.
             *** rewrite r__eq.
                 move: r__eq prf => [] _ _ ->.
                 apply: complete_C.
          ** move => inprf [] /IH__M prf__M [] prfs prf.
             exists E, F; right.
             exists prefix; split; last split => //.
             *** rewrite targets__eq /group foldl_cat.
                 suff: (prefix \in group prefix).
                 { move: (dropTargets_combinatorOrEmpty targets).
                   clear targets__eq.
                   case: (dropTargets targets) => //.
                   case => // ? ? ? _.
                     by rewrite group_comb rev_cat mem_cat => ->. }
                 rewrite /group.
                 move: targets__eq => /(dropTargets_notCombinator).
                 move: inprf.
                 clear prfs.
                 case: prefix => //.
                 move => r prefix _ /andP [] _ notCombinators.
                   by rewrite /= updateGroups0 group_notComb // mem_seq1.
             *** split => //; split => //.
                 move => G inprf__G.
                 apply: prfs.
                   by rewrite /= in_cons inprf__G orbT.
        * move => inprf__g [] inprf [] /IH__M prf__M props.
          exists E, F.
          right.
          exists g; split => //.
          rewrite targets__eq /group foldl_cat.
          move: (dropTargets_combinatorOrEmpty targets) inprf__g.
          clear ...
          case: (dropTargets targets) => //.
          case => // ? ? ? _ inprf.
            by rewrite group_comb rev_cat mem_cat inprf orbT.
  Qed.

  Lemma FCL_Omega_complete:
    forall initialType stable targets A B C,
      isOmega C ->
      FCL_complete initialType stable [:: RuleApply A B C & targets] ->
      FCL_complete initialType [:: RuleApply A B C & OmegaRules C ++ stable] targets.
  Proof.
    move => initialType stable targets A B C isOmega__C prf_complete D inprf__D M prf.
    apply: rule_MP.
    { move => N prf__N.
      apply: future_word_weaken; last by apply: (OmegaRules_future_word stable).
      move => ? inprf.
        by rewrite in_cons inprf orbT. }
    case DC__eq: (D == C).
    - rewrite (eqP DC__eq).
        by apply: OmegaRules_future_word.
    - apply: (future_word_weaken stable).
      { by move => E; rewrite mem_cat => ->; by rewrite orbT. }
      apply: prf_complete => //.
      move: inprf__D.
      rewrite [OmegaRules C]lock.
      case /orP; first case /orP.
      + by move => ->.
      + rewrite /= in_cons.
        case /orP.
        * by rewrite DC__eq.
        * rewrite /parameterTypes pmap_cat mem_cat.
          repeat rewrite -/(parameterTypes _).
          case /orP; last by move => ->; rewrite orbT.
            by rewrite -lock (OmegaRules_params) mem_seq1 DC__eq.
      + move: (dropTargets_suffix targets) => /suffixP [] prefix /eqP targets__eq.
        rewrite (group_split _ _ _ targets__eq) (pmap_cat _ [::_]) /targetTypes map_cat mem_cat /= rev_cons.
        rewrite [X in group X]targets__eq.
        move: targets__eq.
        case: prefix.
        * move => /= _ ->.
            by repeat rewrite orbT.
        * move => r prefix /=.
          rewrite -cat_cons [group (_ ++ _)]/group foldl_cat /= updateGroups0.
          rewrite -cat_cons.
          move => /(dropTargets_notCombinator).
          move: (dropTargets_combinatorOrEmpty targets).
          case: (dropTargets targets).
          ** move => /= _ /andP [] _ /group_notComb => ->.
             rewrite [rev [:: _]]/rev /catrev /= rev_cons /=.
             case: (rev prefix).
             *** rewrite /= => ->.
                   by repeat rewrite orbT.
             *** move => r2 rprefix /= => ->.
                   by repeat rewrite orbT.
          ** case => //.
             move => ? ? ? _ /andP []  _ /(group_notComb) => ->.
             rewrite group_comb rev_cat pmap_cat map_cat mem_cat.
             case /orP.
             *** rewrite /= rev_cons /=.
                 case: (rev prefix).
                 **** move => /= ->.
                        by repeat rewrite orbT.
                 **** move => ? ? /= ->.
                        by repeat rewrite orbT.
             *** move => ->.
                   by repeat rewrite orbT.
  Qed.

  Lemma accumulateCovers_cat:
    forall C s c b,
      ((accumulateCovers (SplitCtxt Gamma) C (primeFactors C) s c).1 =
       (accumulateCovers (SplitCtxt Gamma) C (primeFactors C) ([::], b) c).1 ++ s.1).
  Proof.
    move => C s c b.
    rewrite /accumulateCovers.
    case: (coverMachine ([::], map (fun ms =>
                                      Cover (map (fun m => (m, filter (checkSubtypes m.2) (primeFactors C))) ms) (primeFactors C))
                                   (SplitCtxt Gamma c))) => covers _.
    case: s => /= s _.
    rewrite -[X in commitUpdates X]cat0s.
    move: [::] s.
    elim: (reduceMultiArrows covers) => // [] [] srcs tgt ms IH s1 s2 /=.
    rewrite -IH.
    apply: (f_equal (fun x => commitUpdates x C c ms)).
    clear...
    move: s1 s2 C.
    elim: srcs => // src srcs IH s1 s2 C /=.
      by rewrite -(IH [:: RuleApply C (src -> C) src & s1] s2).
  Qed.

 
  Lemma inhabit_cover_flatten:
    forall C,
      (foldl (accumulateCovers (SplitCtxt Gamma) C (primeFactors C)) ([::], true) (enum Combinator)).1 =
      flatten (map (fun c => (accumulateCovers (SplitCtxt Gamma) C (primeFactors C) ([::], true) c).1)
                   (rev (enum Combinator))).
  Proof.
    move => C.
    have p: (flatten (map (fun c =>  (accumulateCovers (SplitCtxt Gamma) C (primeFactors C) ([::], true) c).1) (rev [::])) =
             ([::], true).1) by done.
    rewrite -[X in _ = X]cats0.
    have empty__eq: (([::] : (@TreeGrammar Combinator Constructor)) = ([::], true).1) by done.
    rewrite [X in _ = _ ++ X]empty__eq.
    move: true => b.
    move s__eq: ([::], b) => s.
    rewrite -[X in accumulateCovers _ _ _ X]s__eq.
    clear s__eq p.
    move: s.
    elim: (enum Combinator) => // c combinators IH s.
    rewrite [accumulateCovers]lock /=.
    rewrite -lock.
    rewrite IH.
    rewrite (rev_cat [:: c]) map_cat flatten_cat.
    rewrite [accumulateCovers]lock /= -lock.
      by rewrite (accumulateCovers_cat _ s _ b) cats0 catA.
  Qed.

  Lemma inhabit_cover_empty:
    forall C,
      (foldl (accumulateCovers (SplitCtxt Gamma) C (primeFactors C)) ([::], true) (enum Combinator)).2 ->
      ((foldl (accumulateCovers (SplitCtxt Gamma) C (primeFactors C)) ([::], true) (enum Combinator)).1 = [::]).
  Proof.
    move => C prf.
      by rewrite -foldl_accumulateCovers_failed_targets_eq //.
  Qed.

  Lemma future_word_weaken_targets1:
    forall stable targets1 targets2 A M,
      (if targets2 is [:: RuleCombinator _ _ & _]
       then true
       else if targets2 is [::]
            then true
            else false) ->
      future_word stable targets1 A M ->
      future_word stable (targets1 ++ targets2) A M.
  Proof.
    move => stable targets1 targets2 A M targets2_combinatorOrEmpty.
    move: A.
    elim: M.
    - move => c A.
      case.
      + move => r.
          by left.
      + move => [] g [] inprf__g props.
        right.
        exists g; split => //.
        rewrite /group foldl_cat.
        move: targets2_combinatorOrEmpty inprf__g.
        clear...
        case: targets2 => //.
        case => // A c targets2 _ inprf__g.
          by rewrite group_comb rev_cat mem_cat inprf__g.
    - move => M IH__M N IH__N A /= [] B [] C.
      case.
      + move => [] inprf__r [] /IH__M prf__M /IH__N prf__N.
          by exists B, C; left.
      + move => [] g [] inprf__g [] inprf__r [] /IH__M prf__M props.
        exists B, C.
        right.
        exists g; split => //.
        rewrite /group foldl_cat.
        move: targets2_combinatorOrEmpty inprf__g.
        clear...
        case: targets2 => //.
        case => // A c targets2 _ inprf__g.
          by rewrite group_comb rev_cat mem_cat inprf__g.
  Qed.

  Lemma future_word_weaken_targets2:
    forall stable targets1 targets2 A M,
      (if targets2 is [:: RuleCombinator _ _ & _]
       then true
       else if targets2 is [::]
            then true
            else false) ->
      future_word stable targets2 A M ->
      future_word stable (targets1 ++ targets2) A M.
  Proof.
    move => stable targets1 targets2 A M targets2_combinatorOrEmpty.
    move: A.
    elim: M.
    - move => c A.
      case.
      + move => r.
          by left.
      + move => [] g [] inprf__g props.
        right.
        exists g; split => //.
        rewrite /group foldl_cat.
        move: targets2_combinatorOrEmpty inprf__g.
        clear...
        case: targets2 => //.
        case => // A c targets2 _ inprf__g.
          by rewrite group_comb rev_cat mem_cat inprf__g orbT.
    - move => M IH__M N IH__N A /= [] B [] C.
      case.
      + move => [] inprf__r [] /IH__M prf__M /IH__N prf__N.
          by exists B, C; left.
      + move => [] g [] inprf__g [] inprf__r [] /IH__M prf__M props.
        exists B, C.
        right.
        exists g; split => //.
        rewrite /group foldl_cat.
        move: targets2_combinatorOrEmpty inprf__g.
        clear...
        case: targets2 => //.
        case => // A c targets2 _ inprf__g.
          by rewrite group_comb rev_cat mem_cat inprf__g orbT.
  Qed.

  Lemma commitMultiArrow_cons:
    forall G A c srcs,
      commitMultiArrow G c srcs A =
      (commitMultiArrow [::] c srcs A) ++ G.
  Proof.
    move => G A c srcs.
    rewrite -[X in commitMultiArrow X]cat0s.
    move: [::].
    move: A G.
    elim: srcs => // src srcs IH A G1 G2 /=.
      by rewrite -(IH _ G1 [:: _ & G2]).
  Qed.

  Lemma commitUpdates_flatten:
    forall G A c covers,
      commitUpdates G A c covers =
      rev (flatten (map (fun m => rev (commitMultiArrow [::] c m.1 A)) covers)) ++ G.
  Proof.
    move => G A c covers.
    move: G.
    elim: covers => // [] [] srcs tgt covers IH G /=.
    rewrite IH.
      by rewrite commitMultiArrow_cons rev_cat revK catA.
  Qed.

  Lemma commitMultiArrow_size:
    forall (c: Combinator) (srcs: seq (@IT Constructor)) tgt,
      seq.size (commitMultiArrow [::] c srcs tgt) = (seq.size srcs).+1.
  Proof.
    move => c srcs tgt.
    rewrite -[X in (seq.size X).+1]cats0.
    have: (seq.size ([::]: @TreeGrammar Combinator Constructor) = seq.size ([::]: seq (@IT Constructor))) by done.
    move: tgt [::] [::].
    elim: srcs.
    - by move => tgt srcs2 G2 /= ->.
    - move => src srcs IH tgt srcs2 G prf /=.
      rewrite commitMultiArrow_cons size_cat (IH (src -> tgt) [::] [::]) //=.
      rewrite prf size_cat size_cat /= addn0 -addn1 -[(seq.size srcs2).+1]addn1 addnAC addnA -addn2.
        by rewrite -(addnA _ 1 1) addn1.
  Qed.    

  Lemma commitMultiArrow_nth:
    forall (c: Combinator) (srcs: seq (@IT Constructor)) tgt n,
      nth (RuleApply tgt ((mkArrow (take (seq.size srcs - n.-1) srcs, tgt))) (nth tgt srcs (seq.size srcs - n))) (commitMultiArrow [::] c srcs tgt) n =
      if n == 0
      then RuleCombinator (mkArrow (srcs, tgt)) c
      else RuleApply (mkArrow (take (seq.size srcs - n) srcs, tgt))
                     (mkArrow (take (seq.size srcs - n.-1) srcs, tgt))
                     (nth tgt srcs (seq.size srcs - n)).
  Proof.
    move => c srcs.
    elim: srcs.
    - move => tgt n /=.
      case: n => //= n.
        by rewrite nth_default.
    - move => src srcs IH tgt n.
      rewrite [commitMultiArrow _ _ _ _]/= commitMultiArrow_cons nth_cat.
      case n_lt: (n < seq.size (commitMultiArrow [::] c srcs (src -> tgt))).
      + rewrite (set_nth_default (RuleApply (src -> tgt)
                                            (mkArrow (take (seq.size srcs - n.-1) srcs, src -> tgt))
                                            ((nth (src -> tgt) srcs (seq.size srcs - n))))) // IH.
        case n__eq: (n == 0) => //.
        rewrite -subn1 subnBA; last first.
        { move: n__eq; case n => //. }
        have: ((mkArrow (take (seq.size srcs - n) srcs, src -> tgt)) =
               (mkArrow (take (seq.size (src :: srcs) - n) (src :: srcs), tgt))).
        { have: ((mkArrow (take (seq.size srcs - n) srcs, src -> tgt)) =
                 (mkArrow ([:: src & (take (seq.size srcs - n) srcs)], tgt))) by done.
          move => ->.
          have: (seq.size (src :: srcs) - n = (seq.size srcs - n).+1).
          { rewrite /= subSn //.
            move: n_lt.
              by rewrite commitMultiArrow_size ltnS. }
            by move => ->. }
        move => ->.
        apply /f_equal2.
        * have: ((mkArrow (take (seq.size srcs + 1 - n) srcs, src -> tgt)) =
                 (mkArrow ([:: src & (take (seq.size srcs + 1 - n) srcs)], tgt))) by done.
          move => ->.
          have: ((seq.size (src :: srcs) - (n - 1)) = (seq.size srcs + 1 - n).+1).
          { rewrite /= subnBA; last by move: n__eq; clear n_lt; case: n.
            rewrite addn1.
            rewrite subSn; first by rewrite addn1.
            move: n_lt.
            rewrite  commitMultiArrow_size ltnS.
            move => ?.
              by apply: leqW. }
            by move => ->.
        * have: ((seq.size (src :: srcs) - n) = (seq.size srcs - n).+1).
          { rewrite /= subSn //.
            move: n_lt.
              by rewrite commitMultiArrow_size ltnS. }
          move => -> /=.
          apply set_nth_default.
          rewrite -subSn.
          ** rewrite -addn1 -subnBA; first by apply: leq_subr.
               by move: n__eq; clear n_lt; case n.
          ** move: n_lt.
               by rewrite commitMultiArrow_size ltnS.
      + case n__eq: (n - seq.size (commitMultiArrow [::] c srcs (src -> tgt)) == 0).
        * rewrite (eqP n__eq) [nth _ _ 0]/=.
          have: (n == 0) = false.
          { move: n_lt.
            rewrite commitMultiArrow_size.
            clear ...
              by case: n. }
          move => n__eq2.
          rewrite n__eq2.
          have src_size: (seq.size (src :: srcs) - n = 0).
          { move: n_lt.
            rewrite commitMultiArrow_size /= => prf.
            apply /eqP.
            rewrite subn_eq0.
              by rewrite ltnNge -ltnS prf. }
          rewrite src_size take0 nth0 [head _ _]/=.
          apply /f_equal2 => //.
          rewrite -subn1 subnBA; last by move: n__eq2; clear n__eq n_lt src_size; case: n.
          rewrite addn1 subSn.
          ** by rewrite src_size /= take0.
          ** rewrite -subn_eq0.
             move: n__eq.
               by rewrite commitMultiArrow_size.
        * rewrite nth_default; last first.
          { rewrite /=.
            move: n__eq.
              by case: (n - seq.size (commitMultiArrow [::] c srcs (src -> tgt))). }
          have n__eq2: (n == 0) = false.
          { move: n__eq.
            clear ...
              by case: n. }
          rewrite n__eq2.
          have src_size: ((seq.size (src :: srcs) - n) = 0).
          { rewrite /=.
            apply /eqP.
            rewrite subn_eq0.
            move: n__eq.
            rewrite commitMultiArrow_size.
            rewrite subn_eq0 leqNgt.
            move => prf.
            apply: ltn_trans; first by apply: ltnSn.
            move: prf.
              by case: ((seq.size srcs).+1 < n). }
            by rewrite src_size take0.
  Qed.

  Lemma commitMultiArrows_combinatorOrEmpty:
    forall (C: @IT Constructor) (c: Combinator) (ms: seq (@MultiArrow Constructor)) nextTargets,
      nextTargets = rev (flatten (map (fun m => rev (commitMultiArrow [::] c m.1 C)) ms)) ->
      if nextTargets is [:: RuleCombinator _ _ & _]
       then true
       else if nextTargets is [::]
            then true
            else false.
  Proof.
    move => C c.
    elim /last_ind.
    - move => nextTargets -> //.
    - move => ms m IH nextTargets -> /=.
      rewrite map_rcons rev_flatten map_rcons rev_rcons revK.
      move: (commitMultiArrow_nth c m.1 C 0).
      case: (commitMultiArrow [::] c m.1 C).
      * by rewrite eq_refl /=.
      * move => hd ?.
          by rewrite eq_refl /= => ->.
  Qed.

  Lemma nextTargets_combinatorOrEmpty:
    forall C combinators nextTargets,
      nextTargets = flatten (map (fun c => (accumulateCovers (SplitCtxt Gamma) C (primeFactors C) ([::], true) c).1) combinators) ->
      if nextTargets is [:: RuleCombinator _ _ & _]
       then true
       else if nextTargets is [::]
            then true
            else false.
  Proof.
    move => C.
    elim.
    - move => nextTargets -> //.
    - move => c combinators IH nextTargets -> /=.
      case: (coverMachine ([::], map (fun ms =>
                                        Cover (map (fun m => (m, filter (checkSubtypes m.2) (primeFactors C))) ms) (primeFactors C))
                                     (SplitCtxt Gamma c))) => covers _.
      elim /last_ind: (reduceMultiArrows covers).
      + by apply: IH.
      + move => m ms _.
        rewrite commitUpdates_flatten cats0 map_rcons rev_flatten map_rcons rev_rcons revK.
        move: (commitMultiArrow_nth c ms.1 C 0).
        case: (commitMultiArrow [::] c ms.1 C).
        * by rewrite eq_refl /=.
        * move => hd ?.
            by rewrite eq_refl /= => ->.
  Qed.

  Lemma group_commitMultiArrow:
    forall c srcs tgt,
      group (commitMultiArrow [::] c srcs tgt) = [:: commitMultiArrow [::] c srcs tgt].
  Proof.
    move => c srcs tgt.
    rewrite /group.
    suff: ((foldl updateGroups [::] (commitMultiArrow [::] c srcs tgt)) = [:: commitMultiArrow [::] c srcs tgt]) by move => ->.
    move: tgt.
    elim: srcs => // src srcs IH tgt.
      by rewrite /= commitMultiArrow_cons /= foldl_cat /= IH cats1.
  Qed.

  Lemma future_word_weaken_inhabapply:
    forall targets A B C,
      (exists N, [FCL Gamma |- N : C]) ->
      forall D M,
        future_word [::] (targets) D M ->
        future_word [::] (targets ++ [:: RuleApply A B C]) D M.
  Proof.
    move => targets A B C prf D M.
    move: D.
    elim: M.
    - move => c D.
      case => // [] [] g [] inprf__g [] inprf__r prfs.
      right.
      move: inprf__g.
      rewrite /group foldl_cat.
      case: (foldl updateGroups [::] targets) => // g1 gs inprf__g.
      rewrite (group_notComb) //.
      move: inprf__g.
      rewrite mem_rev in_cons.
      case /orP.
      + move => g__eq.
        exists (g1 ++ [:: RuleApply A B C]); split; last split.
        * by rewrite mem_rev mem_head.
        * by rewrite -(eqP g__eq) mem_cat inprf__r.
        * move => E.
          rewrite /parameterTypes pmap_cat mem_cat.
          case /orP.
          ** rewrite -(eqP g__eq).
               by apply: prfs.
          ** by rewrite mem_seq1 => /eqP ->.
      + move => inprf__g.
        exists g; split => //.
          by rewrite mem_rev in_cons inprf__g orbT.
    - move => M IH__M N IH__N D /= [] E [] F.
      case; first by case.
      move => [] g [] inprf__g [] inprf__r [] /IH__M prf__M [] prfs prf__N.
      exists E, F.
      right.
      move: inprf__g.
      rewrite /group foldl_cat.
      case: (foldl updateGroups [::] targets) => // g1 gs inprf__g.
      rewrite (group_notComb) //.
      move: inprf__g.
      rewrite mem_rev in_cons.
      case /orP.
      + move => g__eq.
        exists (g1 ++ [:: RuleApply A B C]); split; last split; last split => //; last split => //.
        * by rewrite mem_rev mem_head.
        * by rewrite -(eqP g__eq) mem_cat inprf__r.
        * move => G.
          rewrite /parameterTypes pmap_cat mem_cat.
          case /orP.
          ** rewrite -(eqP g__eq).
               by apply: prfs.
          ** by rewrite mem_seq1 => /eqP ->.
      + move => inprf__g.
        exists g; split => //.
          by rewrite mem_rev in_cons inprf__g orbT.
  Qed.


  Lemma commitMultiArrow_parameters:
    forall c srcs tgt, parameterTypes (commitMultiArrow [::] c srcs tgt) = rev srcs.
  Proof.
    move => c.
    elim => // src srcs IH tgt.
    rewrite /= commitMultiArrow_cons.
    rewrite /parameterTypes pmap_cat.
    repeat rewrite -/(parameterTypes _).
      by rewrite IH /= rev_cons cats1.
  Qed.

  Lemma future_word_covers:
    forall C M,
      ~~(isOmega C) ->
      [FCL Gamma |- M : C] ->
      future_word [::] ((flatten
                            (map (fun c => (accumulateCovers (SplitCtxt Gamma) C (primeFactors C) ([::], true) c).1)
                                 (rev (enum Combinator))))) C M.
  Proof.
    move => C M notOmega__C prf.
    suff: (future_word [::]
                       ((accumulateCovers (SplitCtxt Gamma) C (primeFactors C) ([::], true) (unapply M).1).1)
                       C M).
    { have: ((unapply M).1 \in (rev (enum Combinator))) by rewrite mem_rev; apply mem_enum.
      elim: (rev (enum Combinator)) => // c combinators IH.
      rewrite in_cons.
      case /orP.
      - move => /eqP ->.
        rewrite [accumulateCovers]lock /=.
        apply: future_word_weaken_targets1.
        rewrite -lock.
          by apply: nextTargets_combinatorOrEmpty.
      - move => inprf fwprf.
        rewrite [accumulateCovers]lock /= -lock.
        apply: future_word_weaken_targets2.
        + by apply: nextTargets_combinatorOrEmpty.
        + by apply: IH. }
    rewrite /=.
    move: prf.
    move: (unapply_revapply M) => <- /FCL__invApp [] srcs [] srcs_size__eq prfs.
    move: (prfs) => /(fun prf => prf (seq.size srcs)).
    rewrite nth_default; last by rewrite srcs_size__eq.
    rewrite nth_default //.
    move => /minimalType_minimal le_prf.
    move: (le_prf) => /coverMachine_splitTy_complete.
    rewrite (unapply_revapply).
    case: (coverMachine ([::], map (fun ms =>
                                      Cover (map (fun m => (m, filter (checkSubtypes m.2) (primeFactors C))) ms) (primeFactors C))
                                   (SplitCtxt Gamma (unapply M).1))) => s.
    rewrite /minimalType /SplitCtxt ffunE => steps_prf.
    move => /(fun prf => prf s notOmega__C steps_prf).
    move => /completenessPreserving hasprf.
    move: (coverMachine_splitTy_tgt_sound _ _ _ s steps_prf) => /hasprf /hasP [] m inprf__m /andP [] m_srcs_size__eq /andP [] srcs_ge tgt_le.
    rewrite commitUpdates_flatten.
    suff: future_word [::] (commitMultiArrow [::] (unapply M).1 m.1 C) C M.
    { move: inprf__m.
      elim: (reduceMultiArrows s) => // m0 ms IH.
      rewrite in_cons.
      case /orP.
      - move => /eqP <- /=.
        rewrite rev_cat revK cats0.
        apply: future_word_weaken_targets2.
        move: (commitMultiArrow_nth (unapply M).1 m.1 C 0) => /=.
        rewrite subn0.
          by case: (commitMultiArrow [::] (unapply M).1 m.1 C) => // ? ? ->.
      - rewrite cats0 /= rev_cat revK.
        move => inprf /(IH inprf).
        rewrite cats0 /=.
        apply: future_word_weaken_targets1.
        move: (commitMultiArrow_nth (unapply M).1 m0.1 C 0) => /=.
        rewrite subn0.
          by case: (commitMultiArrow [::] (unapply M).1 m0.1 C) => // ? ? ->. }
    have: (forall n : nat, [ FCL Gamma |- nth (Var (unapply M).1) (unapply M).2 n : nth (minimalType Gamma (Var (unapply M).1)) srcs n]).
    { move => n.
      case n_lt: (n < (seq.size srcs)).
      - move: (prfs n).
        rewrite (set_nth_default (minimalType Gamma (Var (unapply M).1))) => //.
      - rewrite nth_default.
        + rewrite nth_default.
          * by apply: minimalType_sound.
          * by rewrite leqNgt n_lt.
        + by rewrite srcs_size__eq leqNgt n_lt. }
    clear s steps_prf hasprf inprf__m prfs.
    move: m_srcs_size__eq srcs_ge.
    clear tgt_le le_prf.
    case: m.
    move => m_srcs /= _.
    move: C notOmega__C srcs srcs_size__eq m_srcs.
    elim: M.
    - move => c C notOmega__C srcs.
      rewrite /=.
      case: srcs => //.
      move => _.
      case => [] // _ _ _/=.
      right.
      exists [:: RuleCombinator C c]; split; last split => //; by apply: mem_head.
    - move => M IH__M N IH__N C notOmega__C srcs.
      case: srcs; first by rewrite /=; case: (unapply M) => //.
      move => src srcs srcs_size__eq m_srcs.
      case: m_srcs => // m_src1 m_srcs m_srcs_size__eq srcs_ge prfs.
      exists (m_src1 -> C), m_src1.
      right.
      rewrite group_commitMultiArrow.
      exists (commitMultiArrow [::] (let (c, Ns) := unapply M in (c, N :: Ns)).1 ([:: m_src1 & m_srcs], C).1 C).
      split; first by apply: mem_head.
      split; last split; last split.
      + by rewrite /= commitMultiArrow_cons mem_cat mem_head orbT.
      + have: ((unapply (M @ N)).1 = (unapply M).1).
        { rewrite /=; by case: (unapply M). }
        move => -> /=.
        rewrite commitMultiArrow_cons.
        apply: future_word_weaken_inhabapply.
        * exists N.
          apply: (FCL__Sub src).
          ** move: (prfs 0).
             rewrite /=.
               by case: (unapply M) => ? ? /=.
          ** by move: srcs_ge => /andP [] /subtypeMachineP.
        * apply: (IH__M _ _ srcs) => //.
          ** move: srcs_size__eq => /=.
               by case: (unapply M) => ? ? /= [] ->.
          ** by move: srcs_ge => /andP [].
          ** move => n.
             move: (prfs n.+1) => /=.
               by case: (unapply M) => ? ? /=.
      + rewrite commitMultiArrow_parameters.
        move => B.
        rewrite mem_rev /= => /(nthP (Gamma (unapply (M @ N)).1)) [] n n_lt  <-.
        exists (nth (Var (unapply (M @ N)).1) (unapply (M @ N)).2 n).
        apply: FCL__Sub; first by apply: (prfs n).
        have: ((nth (Gamma (unapply (M @ N)).1) (src :: srcs) n) =
               (nth (Gamma (unapply (M @ N)).1) (src :: srcs) n, nth (Gamma (unapply (M @ N)).1) (m_src1 :: m_srcs) n).1) by done.
        move => ->.
        have: ((nth (Gamma (unapply (M @ N)).1) (m_src1 :: m_srcs) n) =
               (nth (Gamma (unapply (M @ N)).1) (src :: srcs) n, nth (Gamma (unapply (M @ N)).1) (m_src1 :: m_srcs) n).2) by done.
        move => ->.
        rewrite -nth_zip; last by rewrite (eqP m_srcs_size__eq).
        apply /subtypeMachineP.
        move: srcs_ge => /all_nthP srcs_ge.
        apply: srcs_ge.
          by rewrite size_zip -(eqP m_srcs_size__eq) minnn.
      + move: (prfs 0).
        rewrite /=.
        case: (unapply M) => ? ? /=.
        move => /FCL__Sub res.
        apply: res.
        apply /subtypeMachineP.
          by move: srcs_ge => /andP [].
  Qed.


  Lemma rule_absorbl_apply_covers:
    forall stable targets A B C D M,
      ~~isOmega C ->
      future_word stable (RuleApply A B C :: targets) D M ->
      future_word (RuleApply A B C :: stable)
                  (targets ++ (flatten
                                 (map (fun c => (accumulateCovers (SplitCtxt Gamma) C (primeFactors C) ([::], true) c).1)
                                      (rev (enum Combinator))))) D M.
  Proof.
    move => stable targets A B C D M notOmega__C.
    move: D.
    elim: M.
    - move => c D.
      case.
      + move => inprf__Dc.
        left.
          by rewrite in_cons inprf__Dc orbT.
      + move => [] g [].
        move: (dropTargets_suffix targets) => /suffixP [] prefix /eqP targets__eq.
        rewrite (group_split _ _ _ targets__eq) in_cons.
        case /orP.
        * move => /eqP -> [].
          rewrite in_cons.
          case /orP => //.
            by move: (dropTargets_notCombinator _ _ targets__eq) => /allP disprf /disprf.
        * move => inprf__g props.
          right.
          exists g; split => //.
          rewrite targets__eq -catA /group foldl_cat.
          move: (dropTargets_combinatorOrEmpty targets) inprf__g.
          case: (dropTargets targets) => //.
          case => // E d dropped _ inprf__g.
          rewrite cat_cons group_comb -cat_cons rev_cat mem_cat foldl_cat.
          move: (nextTargets_combinatorOrEmpty C (rev (enum Combinator)) _ erefl).
          case: (flatten
                   (map (fun c => (accumulateCovers (SplitCtxt Gamma) C (primeFactors C) ([::], true) c).1)
                        (rev (enum Combinator)))).
          ** by rewrite inprf__g orbT.
          ** case => // [] F e ?.
               by rewrite group_comb rev_cat mem_cat inprf__g orbT.
    - move => M IH__M N IH__N D /= [] E [] F.
      case.
      + move => [] inprf__r [] /IH__M prf__M /IH__N prf__N.
        exists E, F.
        left; split => //.
          by rewrite in_cons inprf__r orbT.
      + move => [] g [] inprf__g props.
        exists E, F.
        move: inprf__g.
        move: (dropTargets_suffix targets) => /suffixP [] prefix /eqP targets__eq.
        rewrite (group_split _ _ _ targets__eq) in_cons.
        case /orP.
        * move => /eqP g__eq.
          move: props.
          move: g__eq => -> [].
          rewrite in_cons.
          case /orP.
          ** move => /eqP r__eq.
             rewrite r__eq.
             move => [] /IH__M prf__M props.
             left; split; last split => //; first by rewrite in_cons eq_refl.
             move: r__eq => [] D__eq E__eq F__eq.
             rewrite F__eq.
             apply: (future_word_weaken [::]) => //.
             rewrite -/accumulateCovers_cat.
             apply: future_word_weaken_targets2; first by apply: nextTargets_combinatorOrEmpty.
             apply: (future_word_covers C N notOmega__C).
             move: props => [].
               by rewrite F__eq.
          ** move => inprf__r [] /IH__M prf__M [] prfs prf.
             right.
             exists prefix.
             split; last split => //; last split => //; last split => //.
             *** rewrite targets__eq -catA /group foldl_cat.
                 move: (dropTargets_combinatorOrEmpty targets).
                 case: (dropTargets targets) => //.
                 { move: (nextTargets_combinatorOrEmpty C (rev (enum Combinator)) _ erefl).
                   case: (flatten
                            (map (fun c => (accumulateCovers (SplitCtxt Gamma) C (primeFactors C) ([::], true) c).1)
                                 (rev (enum Combinator)))).
                   - move => _ _ /=.
                     move: inprf__r.
                     move: (dropTargets_notCombinator _ _ targets__eq).
                     clear targets__eq prfs.
                     case: prefix => // r prefix /andP [] _ notCombinators _ /=.
                       by rewrite updateGroups0 (group_notComb _ _ _ notCombinators) mem_head.
                   - case => // ? ? ? _ _.
                     rewrite cat0s group_comb rev_cat mem_cat.
                     move: inprf__r.
                     move: (dropTargets_notCombinator _ _ targets__eq).
                     clear targets__eq prfs.
                     case: prefix => // r prefix /andP [] _ notCombinators _ /=.
                       by rewrite updateGroups0 (group_notComb _ _ _ notCombinators) mem_head. }
                 { case => // ? ? ? _.
                   rewrite cat_cons group_comb rev_cat mem_cat.
                     move: inprf__r.
                     move: (dropTargets_notCombinator _ _ targets__eq).
                     clear targets__eq prfs.
                     case: prefix => // r prefix /andP [] _ notCombinators _ /=.
                       by rewrite updateGroups0 (group_notComb _ _ _ notCombinators) mem_head. }
             *** move => ? inprf.
                 apply: prfs.
                   by rewrite in_cons inprf orbT.
        * move => inprf_g.
          move: props => [] inprf__r [] /IH__M prf__M props.
          right.
          exists g; split; last split => //.
          rewrite targets__eq /group foldl_cat.
          suff: (g \in rev (foldl updateGroups (foldl updateGroups [::] (prefix ++ dropTargets targets)) [::])).
          { move: (nextTargets_combinatorOrEmpty C (rev (enum Combinator)) _ erefl).
            case:  (flatten
                      (map (fun c => (accumulateCovers (SplitCtxt Gamma) C (primeFactors C) ([::], true) c).1)
                           (rev (enum Combinator)))) => //.
            case => // ? ? ? _.
              by rewrite group_comb rev_cat mem_cat => ->. }
          rewrite /= foldl_cat.
          move: (dropTargets_combinatorOrEmpty targets) inprf_g.
          case: (dropTargets targets) => //.
          case => // ? ? ? _.
          rewrite group_comb rev_cat mem_cat => ->.
            by rewrite orbT.
  Qed.

  Lemma takeTargets_prefix:
    forall prefix targets,
      match targets with
      | RuleCombinator _ _ :: _ => true
      | _ => match targets with
            | [::] => true
            | _ :: _ => false
            end
      end ->
      takeTargets (prefix ++ targets) = takeTargets prefix.
  Proof.
    elim.
    - by case => //; case.
    - move => r prefix IH targets targets_prf.
      case: r => //.
      + move => ?.
          by rewrite /= IH.
      + move => ? ? ?.
          by rewrite /= IH.
  Qed.

  Lemma prefix_target_groups:
    forall r targets B,
      (B \in targetTypes (pmap (ohead \o rev) (group targets))) ->
      (B \in targetTypes (pmap (ohead \o rev) (group [:: r & targets]))).
  Proof.
    move => r targets B.
    move: (dropTargets_suffix targets) => /suffixP [] prefix /eqP targets__eq.
    rewrite (group_split _ _ _ targets__eq).
    rewrite (pmap_cat _ [:: _]) /targetTypes map_cat mem_cat.
    rewrite [X in (group X)]targets__eq.
    move: (dropTargets_notCombinator _ _ targets__eq).
    move: (dropTargets_combinatorOrEmpty targets).
    move: targets__eq.
    case: prefix; first by move => _ _ _ ->; rewrite orbT.
    move => r2 prefix targets__eq drop_combinator /andP [] _ notCombinators.
    rewrite /group foldl_cat.
    move: drop_combinator.
    case: (dropTargets targets).
    - move => _.
      rewrite /= updateGroups0 (group_notComb _ _ _ notCombinators).
      rewrite [rev [:: _]]/rev /catrev /= rev_cons rev_cons rev_cons.
      case: (rev prefix).
      + by rewrite /= => ->.
      + by move => ? ? /= ->.
    - case => // ? ? ? _.
      rewrite group_comb rev_cat pmap_cat map_cat mem_cat.
      case /orP.
      + rewrite /= updateGroups0 (group_notComb _ _ _ notCombinators).
        rewrite [rev [:: _]]/rev /catrev /= rev_cons rev_cons rev_cons.
        case: (rev prefix).
        * by rewrite /= => ->.
        * by move => ? ? /= ->.
      + move => ->.
          by rewrite orbT.
  Qed.

  Lemma nil_reduceMultiArrows:
    forall (covers: seq (@MultiArrow Constructor)), nilp (reduceMultiArrows covers) -> nilp covers.
  Proof.
    elim => // m ms IH.
    rewrite /=.
    case: (reduceMultiArrows ms) => // m2 ms2.
      by case: (has (fun m2 =>
                       (seq.size m2.1 == seq.size m.1) && all (fun AB : IT * IT => checkSubtypes AB.1 AB.2) (zip m.1 m2.1))
                    [:: m2 & ms2]).
  Qed.

  Lemma empty_inhabit_cover:
    forall C : IT,
      (foldl (accumulateCovers (SplitCtxt Gamma) C (primeFactors C)) ([::], true) (enum Combinator)).1 = [::] ->
      (foldl (accumulateCovers (SplitCtxt Gamma) C (primeFactors C)) ([::], true) (enum Combinator)).2.
  Proof.
    move => C.
    suff: (nilp (foldl (accumulateCovers (SplitCtxt Gamma) C (primeFactors C)) ([::], true) (enum Combinator)).1 = 
           (foldl (accumulateCovers (SplitCtxt Gamma) C (primeFactors C)) ([::], true) (enum Combinator)).2).
    { by case: ((foldl (accumulateCovers (SplitCtxt Gamma) C (primeFactors C)) ([::], true) (enum Combinator)).1) => //. }
    have: (nilp ([::]: @TreeGrammar Combinator Constructor) = true) by done.
    move: [::] true.
    elim: (enum Combinator) => // c combinators IH.
    - move => results b.
      rewrite /=.
      case: (coverMachine ([::], map (fun ms =>
                                      Cover (map (fun m => (m, filter (checkSubtypes m.2) (primeFactors C))) ms) (primeFactors C))
                                     (SplitCtxt Gamma c))) => covers _.
      case covers_empty: (nilp covers).
      + move => prf.
        rewrite IH => //.
        move: covers_empty => /nilP -> /=.
          by rewrite prf andbT.
      + move => prf.
        rewrite andbF.
        rewrite IH //.
        move: (nil_reduceMultiArrows covers).
        rewrite commitUpdates_flatten.
        case: (reduceMultiArrows covers).
        * by rewrite covers_empty => /(fun prf => prf isT).
        * move => m ms _.
          move: (commitMultiArrow_size c m.1 C) => /=.
          rewrite rev_cat revK /nilp size_cat size_cat => ->.
          rewrite -addn1 addnAC addnA addn1.
            by case: (seq.size (rev (flatten [seq rev (commitMultiArrow [::] c m0.1 C) | m0 <- ms])) + seq.size results + seq.size m.1) => //.
  Qed.

  Lemma cover_targets:
    forall C,
      all (fun A => A == C)
          (targetTypes (pmap (ohead \o rev)
                             (group (flatten (map (fun c => (accumulateCovers (SplitCtxt Gamma) C (primeFactors C) ([::], true) c).1)
                                                  (rev (enum Combinator))))))).
  Proof.
    move => C.
    elim (rev (enum Combinator)) => // c combinators IH.
    rewrite /=.
    case: (coverMachine ([::], map (fun ms =>
                                      Cover (map (fun m => (m, filter (checkSubtypes m.2) (primeFactors C))) ms) (primeFactors C))
                                   (SplitCtxt Gamma c))) => covers _.
    suff: (all (fun A => A == C)
               (targetTypes (pmap (ohead \o rev) (group (commitUpdates [::] C c (reduceMultiArrows covers), nilp covers).1)))).
    { move => prf.
      move: IH.
      move: (nextTargets_combinatorOrEmpty C combinators _ erefl).
      case: (flatten (map (fun c => (accumulateCovers (SplitCtxt Gamma) C (primeFactors C) ([::], true) c).1) combinators)).
      - by rewrite cats0.
      - case => // ? ? ? _ IH.
          by rewrite /group foldl_cat group_comb rev_cat pmap_cat /targetTypes map_cat all_cat IH prf. }
    clear ...
    elim: (reduceMultiArrows covers) => // m ms IH.
    rewrite commitUpdates_flatten cats0 /= rev_cat revK /group foldl_cat.
    move: (commitMultiArrows_combinatorOrEmpty C c [:: m] _ erefl) => /=.
    rewrite cats0 revK.
    move: (commitMultiArrow_nth c m.1 C).
    move: (group_commitMultiArrow c m.1 C).
    move: (commitMultiArrow_size c m.1 C).
    case: (commitMultiArrow [::] c m.1 C).
    - move => _ _ _ _ /=.
      rewrite -/(group _).
      move: IH.
        by rewrite commitUpdates_flatten /= cats0.
    - case => // A d apps size_eq grp_eq prf _.
      rewrite group_comb rev_cat pmap_cat /targetTypes map_cat all_cat.
      rewrite -/(group _).
      move: IH.
      rewrite commitUpdates_flatten cats0 => ->.
      rewrite -/(group _) grp_eq /=.
      move: (prf (seq.size apps)).
      rewrite nth_last.
      clear prf grp_eq.
      move: size_eq.
      elim /last_ind: apps.
      + rewrite /=.
        case: (m.1) => // _ [] -> _.
          by rewrite andbT.
      + move => apps app _ size_eq.
        rewrite /= last_rcons size_rcons /= rev_cons rev_rcons /= => -> /=.
        move: size_eq => /=.
        rewrite size_rcons => [] [] ->.
          by rewrite subnn take0 andbT.
  Qed.

  Lemma inhabit_cover_complete:
    forall initialType stable targets A B C,
      FCL_complete initialType stable [:: RuleApply A B C & targets] ->
      ~~(isOmega C) ->
      FCL_complete initialType
        (match inhabit_cover (SplitCtxt Gamma) targets C with
         | (true, nextTargets) => (RuleFail C :: stable, dropTargets targets)
         | (false, nextTargets) => (RuleApply A B C :: stable, nextTargets)
         end.1)
        (match inhabit_cover (SplitCtxt Gamma) targets C with
         | (true, nextTargets) => (RuleFail C :: stable, dropTargets targets)
         | (false, nextTargets) => (RuleApply A B C :: stable, nextTargets)
         end.2).
  Proof.
    move => inititalType stable targets A B C prf_complete notOmega__C.
    rewrite /inhabit_cover.
    move: (empty_inhabit_cover C).
    move: (inhabit_cover_empty C).
    move: (inhabit_cover_flatten C).
    move: (nextTargets_combinatorOrEmpty C (rev (enum Combinator))
                                         (foldl (accumulateCovers (SplitCtxt Gamma) C (primeFactors C)) ([::], true) (enum Combinator)).1).
    case: (foldl (accumulateCovers (SplitCtxt Gamma) C (primeFactors C)) ([::], true) (enum Combinator)).
    move => nextTargets b.
    case: b.
    - move => next_combOrEmpty -> /(fun prf => prf isT) notargets _ D inprf__D M prf.
      apply: (future_word_dropFailed _ _ A B C).
      + move => N prf__N.
        move: (future_word_covers C N notOmega__C prf__N).
        rewrite notargets.
        clear...
        case: N.
        * move => c.
          case => //.
            by case => [] g [].
        * by move => M N /= [] A [] B [] [] // ? [].
      + rewrite /=.
        apply: (future_word_weaken stable).
        { by move => ?; rewrite in_cons => ->; rewrite orbT. }
        apply: prf_complete => //.
        move: inprf__D.
        case /orP.
        * by move => /= ->.
        * move => /= inprf.
          move: (dropTargets_suffix targets) => /suffixP [] prefix /eqP targets__eq.
            by rewrite (group_split _ _ _ targets__eq) (pmap_cat _ [:: _]) /targetTypes map_cat mem_cat inprf orbT orbT.
    - move => next_combOrEmpty nextTargets__eq _ notnotargets /= D.
      case /orP; first case /orP.
      + move => inprf__D M /prf_complete.
        rewrite inprf__D /=.
        move => /(fun prf => prf isT).
        move: nextTargets__eq => /= ->.
          by apply: rule_absorbl_apply_covers.
      + rewrite /= in_cons.
        case /orP.
        * move => /eqP -> M prf.
          apply: future_word_weaken_targets2; first by apply: next_combOrEmpty.
          apply: (future_word_weaken [::]) => //.
          move: nextTargets__eq => /= ->.
            by apply: future_word_covers.
        * move => inprf__D M /prf_complete.
          rewrite inprf__D orbT.
          move => /(fun prf => prf isT).
          move: nextTargets__eq => /= ->.
            by apply: rule_absorbl_apply_covers.
      + rewrite /group foldl_cat.
        move: next_combOrEmpty nextTargets__eq.
        move: notnotargets.
        case: nextTargets.
        * by move => /(fun prf => prf erefl).
        * move => r nextTargets _ rnextTargets__comb rnextTargets__eq.
          move: (rnextTargets__comb rnextTargets__eq).
          move: rnextTargets__eq.
          clear rnextTargets__comb.
          case: r => // E c.
          move => rnextTargets__eq _.
          rewrite group_comb rev_cat pmap_cat /targetTypes map_cat mem_cat.
          repeat rewrite -/(targetTypes _).
          case /orP.
          ** move => inprf__D M prf.
             move: rnextTargets__eq => /= ->.
             apply: rule_absorbl_apply_covers => //.
             apply: prf_complete => //.
               by rewrite (prefix_target_groups _ _ _ inprf__D) orbT.
          ** move => inprf__D M prf.
             apply: (future_word_weaken [::]) => //.
             apply: (future_word_weaken_targets2) => //.
             move: rnextTargets__eq inprf__D.
             rewrite [(_, _).1]/= => -> inprf__D.
             move: prf.
             have: (D == C).
             { by move: (cover_targets C) inprf__D => /allP eqprfs /eqprfs. }
             move => /eqP ->.
               by apply: future_word_covers.
  Qed.  

  Lemma inhabit_step_complete:
    forall initialType stable targets,
      FailSound stable ->
      noTargetFailures targets ->
      FCL_complete initialType stable targets ->
      FCL_complete initialType
                   (inhabitation_step (SplitCtxt Gamma) stable targets).1
                   (inhabitation_step (SplitCtxt Gamma) stable targets).2.
  Proof.
    move => initialType stable targets fsprf.
    case: targets => // r targets.
    case: r.
    - done.
    - move => A c _ prf_complete B /= /orP.
      case.
      + case inprf__Ac: (RuleCombinator A c \in stable).
        * move => in_stable M prf__MB.
          move: (fun inprf => prf_complete B inprf M prf__MB).
          rewrite in_stable orTb.
          move => /(fun prf => prf isT) res.
          rewrite /=.
            by apply: (rule_absorbl _ _ _ _ inprf__Ac).
        * move => inprf M prf__MB /=.
          apply: (rule_absorbl _ _ A c); first by apply: mem_head.
          apply: (future_word_weaken stable) => //.
          { move => x; rewrite in_cons => ->; by rewrite orbT. }
          apply: prf_complete => //.
          move: inprf.
            by rewrite /= => ->.
      + case inprf__Ac: (RuleCombinator A c \in stable).
        * move => in_targets M prf__MB.
          move: (fun inprf => prf_complete B inprf M prf__MB).
          rewrite /=.
          rewrite (prefix_target_groups _ _ _ in_targets) orbT.
          move => /(fun prf => prf isT).
            by apply: rule_absorbl.
        * move => in_targets M prf__MB /=.
          apply: (rule_absorbl _ _ A c); first by apply: mem_head.
          apply: (future_word_weaken stable) => //.
          { move => x; rewrite in_cons => ->; by rewrite orbT. }
          apply: prf_complete => //.
          rewrite (prefix_target_groups _ _ _ in_targets).
            by repeat rewrite orbT.
    - move => A B C noFail prf_complete /=.
      case inprf__r: (RuleApply A B C \in stable).
      + move => D inprf__D M prf /=.
        apply: (rule_absorbl_apply initialType _ _ A B C) => //.        
        apply: prf_complete => //.
        move: inprf__D.
        case /orP; first case /orP; try by move => ->; repeat rewrite orbT.
        move => /prefix_target_groups ->.
          by rewrite orbT.
      + move: (computeFailExisting_existing stable C).
        move: (fun prf => computeFailExisting_failed_complete initialType stable targets A B C fsprf prf prf_complete).
        case: (computeFailExisting stable C) => [].
        case; first by move => ? /(fun prf => prf isT) //=.
        case; move => _.
        * move => /(fun prf => prf isT isT) inprf__C /= D inprf__D M prf.
          suff: (FCL_complete initialType [:: RuleApply A B C & stable] [:: RuleApply A B C & targets]).
          { move => res.
            apply: rule_absorbl_apply; first by exact res.
            - by apply: mem_head.
            - apply: res => //.
              move: inprf__D.
              case /orP; first by move => ->.
              move => /prefix_target_groups ->.
                by rewrite orbT. }
          clear D inprf__D M prf.
          move => D inprf__D M prf.
          apply: (future_word_weaken stable).
          { move => E; rewrite in_cons => ->; by rewrite orbT. }
          apply: prf_complete => //.
          move: inprf__D.
          case /orP; first case /orP.
          ** by move => ->.
          ** rewrite /= in_cons.
             case /orP.
             *** move => /eqP DC__eq.
                 move: inprf__C.
                 rewrite DC__eq => ->.
                   by rewrite orbT.
             *** move => ->.
                   by rewrite orbT.
          ** move => ->.
               by repeat rewrite orbT.
        * move => _.
          case isOmega__C: (isOmega C); first by apply FCL_Omega_complete.
          apply: inhabit_cover_complete => //.
            by rewrite isOmega__C.     
  Qed.

  Section Algorithm.

    Inductive Domain (GammaSplit: {ffun Combinator -> seq (seq (@MultiArrow Constructor))}):
      (@TreeGrammar Combinator Constructor * @TreeGrammar Combinator Constructor) -> Prop :=
    | Domain__done: forall G, Domain GammaSplit (G, [::])
    | Domain__step: forall s1 s2, InhabitationSemantics GammaSplit s1 s2 -> Domain GammaSplit s2 -> Domain GammaSplit s1.

    Lemma domain_start: forall A, Domain (SplitCtxt Gamma) ([::], (inhabit_cover (SplitCtxt Gamma) [::] A).2).
    Proof.
      move => A.
      have: {subset undup (parameterTypes (inhabit_cover (SplitCtxt Gamma) [::] A).2)
             <= maxParameterTypes A}.
      { by apply: inhabit_cover_parameterTypes_subset. }
      have: {subset undup (parameterTypes [::]) <= maxParameterTypes A} by done.
      move: (inhabit_step_rel_wf A ([::], (inhabit_cover (SplitCtxt Gamma) [::] A).2)).
      move: [::] ((inhabit_cover (SplitCtxt Gamma) [::] A).2).
      move => empty targets acc.
      have: (empty = (empty, targets).1) by done.
      move => ->.
      have: (targets = (empty, targets).2) by done.
      move => ->.
      move: acc.
      move: (empty, targets).
      clear empty targets.
      move => s acc.
      elim: s /acc.
      move => [] nextStable nextTargets.
      case: nextTargets.
      - move => _ _ _ _.
          by constructor.
      - move => nextTarget nextTargets acc IH nextTargetsOk nextStableOk.
        move: (inhabitation_step_subset _ _ _ nextStableOk nextTargetsOk) => [] stepNextTargetsOk stepNextStableOk.
        move: (IH (inhabitation_step (SplitCtxt Gamma) nextStable [:: nextTarget & nextTargets])
                  (inhabitation_step_sizes A (nextStable, [:: nextTarget & nextTargets]) isT nextTargetsOk nextStableOk)
                  stepNextStableOk stepNextTargetsOk) => dom.
        apply: Domain__step; last by exact dom.
          by apply: step__inhab.
    Qed.

    Lemma InhabitationSemantics_functional_step:
      forall (GammaSplit: {ffun Combinator -> seq (seq (@MultiArrow Constructor))})
        s s1 s2, InhabitationSemantics GammaSplit s s1 -> InhabitationSemantics GammaSplit s s2 -> s1 = s2.
    Proof.
      move => ? s s1 s2.
      case.
      move => stable target targets.
      move s__eq: (stable, [:: target & targets]) => s' prf.
      move: s__eq.
      case: prf.
        by move => ? ? ? [] -> -> ->.
    Qed.

    Lemma domain_continue:
      forall GammaSplit s (dom: Domain GammaSplit s),
        InhabitationSemantics GammaSplit s (inhabitation_step GammaSplit s.1 s.2) ->
        Domain GammaSplit (inhabitation_step GammaSplit s.1 s.2).
    Proof.
      move => GammaSplit s [].
      - move => G.
        move s2__eq: (G, [::]) => s2 prf.
        move: s2__eq.
          by case: prf.
      - move => s1 s2 prf dom2 prf2.
          by rewrite (InhabitationSemantics_functional_step _ _ _ _ prf2 prf).
    Defined.

    Fixpoint inhabit_rec GammaSplit s (dom: Domain GammaSplit s) :=
      match s as s return Domain GammaSplit s -> { G: TreeGrammar | clos_refl_trans_1n _ (InhabitationSemantics GammaSplit) s (G, [::]) } with
      | (G, [:: target & targets]) =>
        fun dom =>
          let: exist res prf :=
             inhabit_rec GammaSplit
                         (inhabitation_step GammaSplit G [:: target & targets])
                         (domain_continue GammaSplit (G, [:: target & targets]) dom (step__inhab GammaSplit G target targets)) in
          exist _ res (rt1n_trans _ (InhabitationSemantics GammaSplit) _ _ (res, [::]) (step__inhab GammaSplit G target targets) prf)
      | (G, [::]) => fun _ => exist _ G (rt1n_refl _ _ (G, [::]))
      end dom.
      
    Definition inhabit (A: @IT Constructor): TreeGrammar :=
      if isOmega A
      then OmegaRules A
      else
        let GammaSplit := (SplitCtxt Gamma) in
        (if inhabit_cover GammaSplit [::] A is (false, nextTargets) as r
            return (Domain GammaSplit ([::], r.2) -> TreeGrammar)%type
         then fun dom => proj1_sig (inhabit_rec GammaSplit ([::], nextTargets) dom)
         else fun _ => [:: RuleFail A]) (domain_start A).
  End Algorithm.

  Lemma inhabit_multistep_sound:
    forall s1 s2,
      clos_refl_trans_1n _ (InhabitationSemantics (SplitCtxt Gamma)) s1 s2 ->
      FCL_sound s1.1 ->
      FCL_sound s1.2 ->
      FCL_sound s2.1 /\ FCL_sound s2.2.
  Proof.
    move => s1 s2 steps.
    elim: s1 s2 /steps => // s1 s2 s3 step steps IH prf1 prf2.
    move: (inhabitation_step_sound s1.1 s1.2 prf1 prf2).
    move: steps IH.
    case: step => stable target targets steps IH [] prf12 prf22.
      by apply: IH.
  Qed.

  Lemma inhabit_multistep_complete:
    forall initialType s1 s2,
      clos_refl_trans_1n _ (InhabitationSemantics (SplitCtxt Gamma)) s1 s2 ->
      FailSound s1.1 ->
      noTargetFailures s1.2 ->
      FCL_complete initialType s1.1 s1.2 ->
      FCL_complete initialType s2.1 s2.2.
  Proof.
    move => initialType s1 s2 steps.
    elim: s1 s2 /steps => // s1 s2 s3 step steps IH fsprf nofailprf prf_complete.
    move: (inhabit_step_FailSound s1.1 s1.2 fsprf).
    move: (inhabitation_step_noTargetFailures s1.1 s1.2 nofailprf).
    move: (inhabit_step_complete initialType s1.1 s1.2 fsprf nofailprf prf_complete).
    move: steps IH.
    case: step => stable target targets steps IH prf_complete2 nofailprf2 fsprf2.
      by apply: IH.
  Qed.

  Theorem inhabit_sound: forall A M, word (inhabit A) A M -> [FCL Gamma |- M : A].
  Proof.
    move => A M.
    apply: FCL_sound_sound.
    rewrite /inhabit.
    case isOmega__A: (isOmega A).
    - by apply: (OmegaRules_sound A isOmega__A).
    - move: (inhabit_cover_sound [::] A (negbT isOmega__A) isT).
      have: (FCL_sound [::]) by done.
      move: (domain_start A).
      case: (inhabit_cover (SplitCtxt Gamma) [::] A).
      case => //.
      move => G dom.
      rewrite [_.2]/= => stable_sound targets_sound.
        by case:  (inhabit_multistep_sound _ _ (proj2_sig ((inhabit_rec (SplitCtxt Gamma) ([::], G) dom))) stable_sound targets_sound).
  Qed.

  Theorem inhabit_complete: forall A M, [FCL Gamma |- M : A] -> word (inhabit A) A M.
  Proof.
    move => A M.
    apply: (FCL_complete_emptyTargets A); last by rewrite eq_refl.
    move => B.
    clear M.
    rewrite /inhabit.
    case isOmega__A: (isOmega A).
    - move => inprf__B M prf.
      move: (OmegaRules_future_word [::] [::] A M isOmega__A).
      rewrite cats0.
      move: inprf__B.
      case /orP => //.
      case /orP.
      + by move => /eqP ->.
      + by rewrite OmegaRules_params mem_seq1 => /eqP ->.
    - move => inprf__B M prf.
      have: (FailSound [::]) by done.
      have: (noTargetFailures (inhabit_cover (SplitCtxt Gamma) [::] A).2) by apply: inhabit_cover_noTargetFailures.
      have: (FCL_complete A [::] (inhabit_cover (SplitCtxt Gamma) [::] A).2).
      { move: isOmega__A.
        clear ...
        move => isOmega__A B inprf__B M prf.
        rewrite /inhabit_cover.
        move: inprf__B => /=.
        case /orP => //.
        + case /orP => // AB__eq.
          move: prf.
          rewrite (eqP AB__eq).
          move => /(future_word_covers A M (negbT isOmega__A)).
          rewrite -inhabit_cover_flatten.
          move: (inhabit_cover_empty A).
          case: (foldl (accumulateCovers (SplitCtxt Gamma) A (primeFactors A)) ([::], true) (enum Combinator)).
          move => r.
          case => //.
          move => /(fun prf => prf isT) ->.
          clear...
          case: M.
          * move => c.
             case => //.
               by case => [] g [].
          * by move => M N /= [] ? [] ? [] [] // ? [].
        + move: (cover_targets A) => /allP /=.
          rewrite -inhabit_cover_flatten.
          move => prfs.
          move: (future_word_covers A M (negbT isOmega__A)) (inhabit_cover_empty A) prfs.
          rewrite -inhabit_cover_flatten.
          rewrite /inhabit_cover.
          case: ((foldl (accumulateCovers (SplitCtxt Gamma) A (primeFactors A)) ([::], true) (enum Combinator))).
          move => targets.
          case => //.
          move => fwprf _ prfs /prfs /eqP eq_prf.
          move: prf.
          rewrite eq_prf.
            by apply: fwprf. }
      move: inprf__B.
      move: (domain_start A).
      move: (inhabit_cover_empty A).
      rewrite /inhabit_cover.
      case: (foldl (accumulateCovers (SplitCtxt Gamma) A (primeFactors A)) ([::], true) (enum Combinator)) => targets failed.
      case: failed.
      + move => /(fun prf => prf isT) emptyprf /= _.
        rewrite in_nil orbF orbF.
        move => /eqP eq_prf.
        move: prf.
        rewrite eq_prf.
        move => prf prf_complete.
        move: (prf_complete A).
        rewrite eq_refl /=.
        move => /(fun pc => pc isT M prf).
        clear...
        case: M.
        * move => c.
          case => //.
            by case => [] g [].
        * by move => M N /= [] ? [] ? [] [] // ? [].
      + move => _.
        rewrite cat0s [(_, _).2]/=.
        move => dom inprf__B prf_complete prf_ok fsprf.
        move: (inhabit_multistep_complete A _ _
                                          (proj2_sig (inhabit_rec (SplitCtxt Gamma) ([::], targets) dom))
                                          fsprf prf_ok prf_complete).
          by move => /(fun res => res _ inprf__B M prf).
  Qed.   

End InhabitationMachineProperties.

