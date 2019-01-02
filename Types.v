Require Import PeanoNat.
Require Import Coq.Arith.Wf_nat.
From mathcomp Require Import all_ssreflect.

Set Bullet Behavior "Strict Subproofs".

Delimit Scope it_scope with IT.
Open Scope it_scope.

Import EqNotations.

Section IntersectionTypes.
  (** The set of type constructors. **)
  Variable Constructor: countType.

  (** Intersection types with constructors and products. **)
  Inductive IT : Type :=
  | Omega : IT
  | Ctor : Constructor -> IT -> IT
  | Arrow : IT -> IT -> IT
  | Prod : IT -> IT -> IT 
  | Inter : IT -> IT -> IT.

  (** Enable mathcomp functionalities on Intersection Types **)
  Section ITMathcompInstances.
    Fixpoint IT2tree (A: IT): GenTree.tree Constructor :=
      match A with
      | Omega => GenTree.Node 0 [::]
      | Ctor C A => GenTree.Node 1 [:: GenTree.Leaf C; IT2tree A  ]
      | Arrow A1 A2 => GenTree.Node 2 [:: IT2tree A1; IT2tree A2 ]
      | Prod A1 A2 => GenTree.Node 3 [:: IT2tree A1; IT2tree A2 ]
      | Inter A1 A2 => GenTree.Node 4 [:: IT2tree A1; IT2tree A2 ]
      end.

    Fixpoint tree2IT (t: GenTree.tree Constructor): option IT :=
      match t with
      | GenTree.Node n args =>
        match n, args with
        | 0, [::] => Some Omega
        | 1, [:: GenTree.Leaf C;  t] => option_map (Ctor C) (tree2IT t)
        | 2, [:: t1; t2] => if tree2IT t1 is Some A1 then
                             if tree2IT t2 is Some A2 then Some (Arrow A1 A2) else None
                           else None
        | 3, [:: t1; t2] => if tree2IT t1 is Some A1 then
                             if tree2IT t2 is Some A2 then Some (Prod A1 A2) else None
                           else None
        | 4, [:: t1; t2] => if tree2IT t1 is Some A1 then
                             if tree2IT t2 is Some A2 then Some (Inter A1 A2) else None
                           else None
        | _, _ => None
        end
      | _ => None
      end.

    Lemma pcan_ITtree: pcancel IT2tree tree2IT.
    Proof.
      elim => //=; by [ move => ? -> ? -> || move => ? ? -> ].
    Qed.

    Definition IT_eqMixin := PcanEqMixin pcan_ITtree.
    Canonical IT_eqType := EqType IT IT_eqMixin.
    Definition IT_choiceMixin := PcanChoiceMixin pcan_ITtree.
    Canonical IT_choiceType := ChoiceType IT IT_choiceMixin.
    Definition IT_countMixin := PcanCountMixin pcan_ITtree.
    Canonical IT_countType := CountType IT IT_countMixin.
  End ITMathcompInstances.

  (** Check if a type is Omega or an Arrow ending in Omega **)
  Fixpoint isOmega (A: IT) {struct A}: bool :=
    match A with
    | Omega => true
    | Arrow A B => isOmega B
    | Inter A B => isOmega A && isOmega B
    | _ => false
    end.

  (** The arity of the outermost constructor **)
  Definition arity (A: IT): eqType :=
    match A with
    | Omega => [eqType of unit]
    | Ctor _ _ => [eqType of IT]
    | Arrow _ _ => [eqType of IT * IT]
    | Prod _ _ => [eqType of IT * IT]
    | Inter _ _ => [eqType of IT * IT]
    end.

  Definition omegaArg (A: IT): arity A :=
    match A with
    | Omega => tt
    | Ctor _ _ => Omega
    | Arrow _ _ => (Omega, Omega)
    | Prod _ _ => (Omega, Omega)
    | Inter _ _ => (Omega, Omega)
    end.

  Fixpoint intersect (xs: seq IT) : IT :=
    match xs with
    | [::] => Omega
    | [:: A] => A
    | [:: A & Delta] => Inter A (intersect Delta)
    end.
End IntersectionTypes.
Arguments IT [Constructor].
Arguments Omega [Constructor].
Arguments Ctor [Constructor].
Arguments Arrow [Constructor].
Arguments Prod [Constructor].
Arguments Inter [Constructor].
Hint Constructors IT.

Arguments isOmega [Constructor].
Arguments arity [Constructor].
Arguments omegaArg [Constructor].
Arguments intersect [Constructor].

Notation "\bigcap_ ( i <- xs ) F" :=
  (intersect (map (fun i => F) xs)) (at level 41, F at level 41, i, xs at level 50,
                          format "'[' \bigcap_ ( i <- xs ) '/ ' F ']'") : it_scope.
Notation "\prod_ ( i <- xs ) F" :=
  (\big[(@Prod _)/(last Omega xs)]_(i <- behead (belast Omega xs)) F).

Notation "A -> B" := (Arrow A B) : it_scope.
Notation "A \cap B" := (Inter A B) (at level 80, right associativity) : it_scope.
Notation "A \times B" := (Prod A B) (at level 40, left associativity) : it_scope.

Lemma bigcap_cons: forall (Constructor: countType) (T: Type) (F: T -> @IT Constructor) (A: T) (Delta: seq T),
    \bigcap_(A__i <- [:: A & Delta]) (F A__i) = match Delta with
                                            | [::] => F A
                                            | [:: A' & Delta] =>  F A \cap \bigcap_(A__i <- A'::Delta) (F A__i)
                                            end.
Proof. 
  move => ? T F A Delta.
    by case: Delta.
Qed.
Arguments bigcap_cons [Constructor T F A Delta].

Module Constructor.
  Definition ctor_preorder (ctor: countType) := (ctor -> ctor -> bool)%type.
  Definition preorder_reflexive (ctor: countType) (lessOrEqual: ctor_preorder ctor): Type :=
    forall c, lessOrEqual c c = true.

  Definition preorder_transitive (ctor: countType) (lessOrEqual: ctor_preorder ctor): Type :=
    forall (c: ctor) (d: ctor) (e: ctor),
      lessOrEqual c d && lessOrEqual d e ==> lessOrEqual c e.

  Record mixin_of (ctor: countType): Type :=
    Mixin {
        lessOrEqual : ctor_preorder ctor;
        _: preorder_reflexive ctor lessOrEqual;
        _: preorder_transitive ctor lessOrEqual
      }.
  Notation class_of := mixin_of (only parsing).
  Section ClassDef.
    Structure type := Pack { sort : countType; _ : class_of sort }.
    Variables (ctor: countType) (cCtor: type).
    Definition class := let: Pack _ c := cCtor return class_of (sort cCtor) in c.
    Definition pack c := @Pack ctor c.
    Definition clone c & phant_id class c := Pack ctor c.
  End ClassDef.
  Module Exports.
    Coercion sort : type >-> countType.
    Notation ctor := type.
    Notation CtorMixin := Mixin.
    Notation CtorType C m := (@pack C m).
    Notation "[ 'ctorMixin' 'of' ctor ]" :=
      (class _ : mixin_of ctor) (at level 0, format "[ 'ctorMixin' 'of' ctor ]") : form_scope.
    Notation "[ 'ctorType' 'of' ctor 'for' C ]" :=
      (@clone ctor C _ idfun id) (at level 0, format "[ 'ctorType' 'of' ctor 'for' C ]") : form_scope.
    Notation "[ 'ctorType' 'of' C ]" :=
      (@clone ctor _ _ id id) (at level 0, format "[ 'ctorType' 'of' C ]") : form_scope.
  End Exports.
End Constructor.
Export Constructor.Exports.

Definition lessOrEqual c := Constructor.lessOrEqual _ (Constructor.class c).
Arguments lessOrEqual [c].
Notation "[ 'ctor' c <= d ]" := (lessOrEqual c d) (at level 0, c at next level): it_scope.
Lemma preorder_reflexive c: Constructor.preorder_reflexive _ (@lessOrEqual c).
Proof. by case c => ? []. Qed.
Arguments preorder_reflexive [c].
Lemma preorder_transitive c: Constructor.preorder_transitive _ (@lessOrEqual c).
Proof. by case c => ? []. Qed.
Arguments preorder_transitive [c].

Reserved Notation "[ 'bcd' A <= B ]" (at level 0, A at next level).
(** BCD Rules with Products and distributing covariant constructors. **)
Section BCD.
  Variable Constructor: ctor.

  Inductive BCD: @IT Constructor -> @IT Constructor -> Prop :=
  | BCD__CAx: forall a b A B, [ ctor a <= b] -> [ bcd A <= B] -> [ bcd (Ctor a A) <= (Ctor b B)]
  | BCD__omega: forall A, [ bcd A <= Omega]
  | BCD__CDist: forall a A1 A2, [ bcd ((Ctor a A1) \cap (Ctor a A2)) <= (Ctor a (A1 \cap A2))]
  | BCD__ArrOmega: [ bcd Omega <= Omega -> Omega]
  | BCD__Sub: forall A1 A2 B1 B2, [ bcd B1 <= A1] -> [ bcd A2 <= B2] -> [ bcd (A1 -> A2) <= (B1 -> B2)]
  | BCD__Dist: forall A B1 B2, [ bcd ((A -> B1) \cap (A -> B2)) <= (A -> B1 \cap B2)]
  | BCD__ProdSub: forall A1 A2 B1 B2, [ bcd A1 <= B1] -> [ bcd A2 <= B2] ->
                               [ bcd (A1 \times A2) <= (B1 \times B2)]
  | BCD__ProdDist: forall A1 A2 B1 B2,
      [ bcd ((A1 \times A2) \cap (B1 \times B2)) <= (A1 \cap B1) \times (A2 \cap B2)]
  | BCD__Refl: forall A, [ bcd A <= A]
  | BCD__Trans: forall A B C, [ bcd A <= B] -> [ bcd B <= C] -> [ bcd A <= C]
  | BCD__Glb: forall A B1 B2, [ bcd A <= B1] -> [ bcd A <= B2] -> [ bcd A <= (B1 \cap B2)]
  | BCD__Lub1: forall A B, [ bcd (A \cap B) <= A]
  | BCD__Lub2: forall A B, [ bcd (A \cap B) <= B]
  where "[ 'bcd' A <= B ]" := (BCD A B).

  Lemma BCD__Idem: forall A, [ bcd A <= A \cap A].
  Proof.
    move => A.
      by apply: BCD__Glb; apply: BCD__Refl.
  Qed.
End BCD.

Arguments BCD [Constructor].
Arguments BCD__CAx [Constructor] [a b A B].
Arguments BCD__omega [Constructor] [A].
Arguments BCD__CDist [Constructor] [a A1 A2].
Arguments BCD__ArrOmega [Constructor].
Arguments BCD__Sub [Constructor] [A1 A2 B1 B2].
Arguments BCD__Dist [Constructor] [A B1 B2].
Arguments BCD__Idem [Constructor] [A].
Arguments BCD__Trans [Constructor] [A] B [C].
Arguments BCD__Glb [Constructor] [A B1 B2].
Arguments BCD__Lub1 [Constructor] [A B].
Arguments BCD__Lub2 [Constructor] [A B].
Arguments BCD__Refl [Constructor] [A].
Hint Constructors BCD.
Notation "[ 'bcd' A <= B ]" := (BCD A B) : it_scope.
Hint Resolve BCD__Refl.

(** Instructions for a machine deciding subtyping on intersection types **)
Section SubtypeMachineInstuctions.
  Variable Constructor: ctor.

  Inductive Instruction: Type :=
  | LessOrEqual of (@IT Constructor * @IT Constructor)
  | TgtForSrcsGte of (@IT Constructor * seq (@IT Constructor * @IT Constructor)).

  Inductive Result: Type :=
  | Return of bool
  | CheckTgt of seq (@IT Constructor).

  (** Enable mathcomp functionalities on instructions **)
  Section InstructionMathcompInstances.
    Fixpoint Instruction2tree (i: Instruction): GenTree.tree (@IT Constructor + seq (@IT Constructor * @IT Constructor)) :=
      match i with
      | LessOrEqual (A, B) => GenTree.Node 0 [:: GenTree.Leaf (inl A); GenTree.Leaf (inl B)]
      | TgtForSrcsGte (A, Delta) => GenTree.Node 1 [:: GenTree.Leaf (inl A); GenTree.Leaf (inr Delta) ]
      end.

    Fixpoint Result2tree (r: Result): GenTree.tree (bool + seq (@IT Constructor)) :=
      match r with
      | Return b => GenTree.Node 0 [:: (GenTree.Leaf (inl b)) ]
      | CheckTgt Delta => GenTree.Node 1 [:: GenTree.Leaf (inr Delta) ]
      end.

    Fixpoint tree2Instruction (t: GenTree.tree (@IT Constructor + seq (@IT Constructor * @IT Constructor))): option Instruction :=
      match t with
      | GenTree.Node n args =>
        match n, args with
        | 0, [:: GenTree.Leaf (inl A); GenTree.Leaf (inl B)] => Some (LessOrEqual (A, B))
        | 1, [:: GenTree.Leaf (inl A); GenTree.Leaf (inr Delta)] => Some (TgtForSrcsGte (A, Delta))
        | _, _ => None
        end
      | _ => None
      end.

    Fixpoint tree2Result (t: GenTree.tree (bool + seq (@IT Constructor))): option Result :=
      match t with
      | GenTree.Node n args =>
        match n, args with
        | 0, [:: GenTree.Leaf (inl b)] => Some (Return b)
        | 1, [:: GenTree.Leaf (inr Delta)] => Some (CheckTgt Delta)
        | _, _ => None
        end
      | _ => None
      end.

    Lemma pcan_Instructiontree: pcancel Instruction2tree tree2Instruction.
    Proof. by case => //= [] [] //=. Qed.

    Lemma pcan_Resulttree: pcancel Result2tree tree2Result.
    Proof. by case => //= []. Qed.

    Definition Instruction_eqMixin := PcanEqMixin pcan_Instructiontree.
    Canonical Instruction_eqType := EqType Instruction Instruction_eqMixin.
    Definition Instruction_choiceMixin := PcanChoiceMixin pcan_Instructiontree.
    Canonical Instruction_choiceType := ChoiceType Instruction Instruction_choiceMixin.
    Definition Instruction_countMixin := PcanCountMixin pcan_Instructiontree.
    Canonical Instruction_countType := CountType Instruction Instruction_countMixin.
    Definition Result_eqMixin := PcanEqMixin pcan_Resulttree.
    Canonical Result_eqType := EqType Result Result_eqMixin.
    Definition Result_choiceMixin := PcanChoiceMixin pcan_Resulttree.
    Canonical Result_choiceType := ChoiceType Result Result_choiceMixin.
    Definition Result_countMixin := PcanCountMixin pcan_Resulttree.
    Canonical Result_countType := CountType Result Result_countMixin.
  End InstructionMathcompInstances.
End SubtypeMachineInstuctions.

Arguments Instruction [Constructor].
Arguments LessOrEqual [Constructor].
Arguments TgtForSrcsGte [Constructor].
Hint Constructors Instruction.

Arguments Result [Constructor].
Arguments Return [Constructor].
Arguments CheckTgt [Constructor].
Hint Constructors Result.

Notation "[ 'subty' A 'of' B ]" := (LessOrEqual (A, B)) (at level 0): it_scope.
Notation "[ 'tgt_for_srcs_gte' A 'in' Delta ]" := (TgtForSrcsGte (A, Delta)) (at level 0): it_scope.
Notation "[ 'check_tgt' A ]" := (CheckTgt A) (at level 0): it_scope.

(** A machine deciding subtyping on intersection types **)
Reserved Notation "A '~~>' B" (at level 70, no associativity).
Section SubtypeMachine.
  Variable Constructor: ctor.

  (** Pick components of A wich are relevant for deciding A <= B **)
  Definition slow_cast (B A: @IT Constructor): seq (arity B) :=
    if isOmega B then [:: omegaArg B]
    else (fix cast_rect A : seq (arity B) :=
            match A with
            | Omega => [::]
            | Ctor c arg => if B is Ctor d arg' then if [ ctor c <= d] then [:: arg ] else [::] else [::]
            | A1 -> A2 => if B is _ -> _ then [:: (A1, A2)] else [::]
            | A1 \times A2 => if B is _ \times _ then [:: (A1, A2)] else [::]
            | A1 \cap A2 => cast_rect A1 ++ cast_rect A2
            end) A.

  Definition cast (B A: @IT Constructor): seq (arity B) :=
    if isOmega B then [:: omegaArg B]
    else (fix cast_rect A: seq (arity B) -> seq (arity B) :=
            match A with
            | Omega => fun result => result
            | Ctor c arg =>
              if B is Ctor d arg'
              then fun result => if [ ctor c <= d] then [:: arg & result ] else result
              else fun result => result
            | A1 -> A2 =>
              if B is _ -> _ then fun result => [:: (A1, A2) & result] else fun result => result
            | A1 \times A2 => 
                if B is _ \times _ then fun result => [:: (A1, A2) & result] else fun result => result
            | A1 \cap A2 =>
              fun result => cast_rect A1 (cast_rect A2 result)
            end) A [::].
  Hint View for apply / cast | 1.
  Hint View for move / cast | 1.

  Lemma slow_cast_cast: forall A B, cast B A = slow_cast B A.
  Proof.
    move => A B.
    rewrite /cast /slow_cast.
    case: (isOmega B) => //.
    move l__eq: [::] => l.
    rewrite -[in X in _ = X]l__eq.
    rewrite -[X in _ = X](cats0) [X in _ = _ ++ X]l__eq.
    move: l__eq => _.
    move: B l.
    elim: A => //.
    - move => a A _; case => //=.
      move => b B l.
      case [ ctor a <= b] => //=.
    - by move => A1 _ A2 _; case.
    - by move => A1 _ A2 _; case.
    - move => A1 IH1 A2 IH2.
      case;
        by move => *; rewrite IH1 IH2 catA.
  Qed.

  (** Semantics of the subtype machine **)
  Inductive Semantics : Instruction -> Result -> Prop :=
  | step__Omega : forall A, [subty A of Omega ] ~~> Return true
  | step__Ctor: forall A b B r,
      [subty (\bigcap_(A__i <- cast (Ctor b B) A) A__i) of B] ~~> Return r ->
      [subty A of Ctor b B] ~~> Return (~~nilp (cast (Ctor b B) A) && r)
  | step__Arr: forall A B1 B2 Delta r,
      [tgt_for_srcs_gte B1 in cast (B1 -> B2) A] ~~> [check_tgt Delta] ->
      [subty (\bigcap_(A__i <- Delta) A__i) of B2] ~~> Return r ->
      [subty A of B1 -> B2] ~~> Return (isOmega B2 || r)
  | step__chooseTgt: forall B A Delta Delta' r,
      [subty B of A.1] ~~> Return r ->
      [tgt_for_srcs_gte B in Delta] ~~> [check_tgt Delta'] ->
      [tgt_for_srcs_gte B in [:: A & Delta ]] ~~> [check_tgt if r then [:: A.2 & Delta'] else Delta' ]
  | step__doneTgt: forall B, [tgt_for_srcs_gte B in [::]] ~~> [check_tgt [::]]
  | step__Prod: forall A B1 B2 r1 r2,
      [subty (\bigcap_(A__i <- cast (B1 \times B2) A) A__i.1) of B1] ~~> Return r1 ->
      [subty (\bigcap_(A__i <- cast (B1 \times B2) A) A__i.2) of B2] ~~> Return r2 ->
      [subty A of B1 \times B2] ~~> Return (~~nilp (cast (B1 \times B2) A) && r1 && r2)
  | step__Inter: forall A B1 B2 r1 r2,
      [subty A of B1] ~~> Return r1 ->
      [subty A of B2] ~~> Return r2 ->
      [subty A of B1 \cap B2] ~~> Return (r1 && r2)
  where "p1 ~~> p2" := (Semantics p1 p2).
End SubtypeMachine.

Arguments Semantics [Constructor].
Arguments step__Omega [Constructor A].
Arguments step__Ctor [Constructor A b B r].
Arguments step__Arr [Constructor A B1 B2 Delta r].
Arguments step__chooseTgt [Constructor B A Delta Delta' r].
Arguments step__doneTgt [Constructor B].
Arguments step__Prod [Constructor A B1 B2 r1 r2].
Arguments step__Inter [Constructor A B1 B2 r1 r2].
Hint Constructors Semantics.
Notation "p1 ~~> p2" := (Semantics p1 p2).

Arguments slow_cast [Constructor].
Arguments cast [Constructor].

Section SubtypeMachineSpec.
  Variable Constructor: ctor.
  Implicit Type p: @Instruction Constructor.
  Implicit Type r: @Result Constructor.


  (** The last step of execution is ... **)
  Section Inversion.
    Lemma emptyDoneTgt:
      forall (B: @IT Constructor) Delta, [ tgt_for_srcs_gte B in [::]] ~~> [ check_tgt Delta] -> Delta = [::].
    Proof.
      move => B Delta.
      move p__eq: [ tgt_for_srcs_gte B in [::]] => p.
      move r__eq: [ check_tgt Delta] => r prf.
      move: r__eq p__eq.
      case: p r / prf => //.
        by move => _ [] -> _.
    Qed.
  End Inversion.

  (** The subtype machine always computes the same result on the same inputs **)
  Lemma Semantics_functional: forall p r1 r2, p ~~> r1 -> p ~~> r2 -> r1 = r2.
  Proof.
    move => p r1 r2 pr1.
    move: r2.
    elim: p r1 / pr1 => //.
    - move => A r2.
      move instr__eq: [subty A of Omega ] => instr pr2.
      move: instr__eq.
      case: r2 / pr2 => //.
    - move => A b B r.
      move instr__eq: [subty A of (Ctor b B) ] => instr rec IH r2 pr2.
      move: instr__eq rec IH.
      case: r2 / pr2 => // A' b' B' r' rec1 [] -> [] -> -> rec2 IH.
        by move: (IH _ rec1) => [] ->.
    - move => A B1 B2 Delta r.
      move instr__eq: [subty A of B1 -> B2 ] => instr rec__src IH__src rec__tgt IH__tgt r2 pr2.
      move: instr__eq rec__src IH__src rec__tgt IH__tgt.
      case: r2 / pr2 => // A' B1' B2' Delta' r' rec__src1 rec__tgt1 [] -> [] -> -> rec__src2 IH__src rec__tgt2 IH__tgt.
      move: rec__tgt1.
      move: (IH__src _ rec__src1) => [] <- rec__tgt1.
        by move: (IH__tgt (Return r') rec__tgt1) => [] ->.
    - move => B arr Delta Delta' r.
      move instr__eq: [tgt_for_srcs_gte B in arr :: Delta ] => instr rec1 IH1 rec2 IH2 r2 pr2.
      move: instr__eq rec1 IH1 rec2 IH2.
      case: r2 / pr2 => // B' arr' Delta__tmp Delta'__tmp r' rec1' rec2' [] -> [] -> -> rec1 IH1 rec2 IH2.
        by move: (IH1 _ rec1') (IH2 _ rec2') => [] -> [] ->.
    - move => B.
      move instr__eq: [tgt_for_srcs_gte B in [::]] => instr r2 pr2.
      move: instr__eq.
        by case: r2 / pr2.
    - move => A B1 B2 res1 res2.
      move instr__eq: [subty A of B1 \times B2] => instr rec1 IH1 rec2 IH2 r2 pr2.
      move: instr__eq rec1 IH1 rec2 IH2.
      case: r2 / pr2 => // A' B1' B2' res1' res2' rec1' rec2' [] -> [] -> -> rec1 IH1 rec2 IH2.
        by move: (IH1 _ rec1') (IH2 _ rec2') => [] -> [] ->.
    - move => A B1 B2 res1 res2.
      move instr__eq: [subty A of B1 \cap B2] => instr rec1 IH1 rec2 IH2 r2 pr2.
      move: instr__eq rec1 IH1 rec2 IH2.
      case: r2 / pr2 => // A' B1' B2' r1' r2' rec1' rec2' [] -> [] -> -> rec1 IH1 rec2 IH2.
        by move: (IH1 _ rec1') (IH2 _ rec2') => [] -> [] ->.
  Qed.

  (** Subtype request return booleans **)
  Definition normal r : bool :=
    match r with
    | Return _ => true
    | _ => false
    end.

  Lemma normalizing: forall A B r, [ subty A of B] ~~> r -> normal r.
  Proof.
    move => A B r.
    move p__eq: [ subty A of B] => p prf.
    move: p__eq.
      by case: p r / prf => //.
  Qed.

  (** The set of instructions from the domain of the subtype machine relation, i.e. { p | exists r, p ~~> r } **)
  Inductive Domain : @Instruction Constructor -> Prop :=
  | dom__Omega: forall A, Domain [subty A of Omega ]
  | dom__Ctor: forall A b B, Domain [subty (\bigcap_(A__i <- cast (Ctor b B) A) A__i) of B] -> Domain [subty A of Ctor b B]
  | dom__Arr: forall A B1 B2,
      Domain [tgt_for_srcs_gte B1 in cast (B1 -> B2) A] ->
      (forall Delta,
          [tgt_for_srcs_gte B1 in cast (B1 -> B2) A] ~~> [check_tgt Delta] ->
          Domain [subty (\bigcap_(A__i <- Delta) A__i) of B2]) ->
      Domain [subty A of (B1 -> B2)]
  | dom__chooseTgt: forall B A Delta,
      Domain [subty B of A.1] ->
      Domain [tgt_for_srcs_gte B in Delta] ->
      Domain [tgt_for_srcs_gte B in [:: A & Delta ]]
  | dom__doneTgt: forall B, Domain [tgt_for_srcs_gte B in [::]]
  | dom__Prod: forall A B1 B2,
      Domain [subty (\bigcap_(A__i <- cast (B1 \times B2) A) A__i.1) of B1] ->
      Domain [subty (\bigcap_(A__i <- cast (B1 \times B2) A) A__i.2) of B2] ->
      Domain [subty A of B1 \times B2]
  | dom__Inter: forall A B1 B2,
      Domain [subty A of B1] ->
      Domain [subty A of B2] ->
      Domain [subty A of B1 \cap B2].
  Arguments dom__Omega [A].
  Arguments dom__Ctor [A b B].
  Arguments dom__Arr [A B1 B2].
  Arguments dom__chooseTgt [B A Delta].
  Arguments dom__doneTgt [B].
  Arguments dom__Prod [A B1 B2].
  Arguments dom__Inter [A B1 B2].
  Hint Constructors Domain.

  (** The subtype machine is total, forall p, Domain p \/ exists b, p = Return b **)
  Section SubtypeMachineTotal.
    
    Fixpoint depth (A: @IT Constructor) : nat :=
      match A with
      | Omega => 1
      | Ctor _ A => 1 + depth A
      | A1 -> A2 => 1 + maxn (depth A1) (depth A2)
      | A1 \times A2 => 1 + maxn (depth A1) (depth A2)
      | A1 \cap A2 => maxn (depth A1) (depth A2)
      end.

    Definition IT_depth_rect:
      forall (P: @IT Constructor -> @IT Constructor -> Type),
        (forall A B, (forall A' B', maxn (depth A') (depth B') < maxn (depth A) (depth B) -> P A' B') -> P A B) ->
        forall A B, P A B.
    Proof.
      move => P IH A B.
      apply: (Fix_F_2 (R := fun (p1 p2 : IT * IT) => (maxn (depth p1.1) (depth p1.2) < maxn (depth p2.1) (depth p2.2))%coq_nat)).
      - move => p1 p2 prf.
        apply IH.
        move => A' B' /ltP.
          by apply prf.
      - by apply (well_founded_ltof _ (fun p : IT * IT => maxn (depth p.1) (depth p.2))).
    Defined.

    Arguments IT_depth_rect [P].
    Hint View for move / IT_depth_rect | 1.
    Hint View for apply / IT_depth_rect | 1.

    Lemma adapt_inter_depth__left: forall A B1 B2 n, n < maxn (depth A) (depth B1) -> n < maxn (depth A) (depth (B1 \cap B2)).
    Proof.
      move => A B1 B2 n size__prf.
      apply /ltP.
      apply: Nat.lt_le_trans.
      * apply /ltP; exact size__prf.
      * apply /leP.
        rewrite leq_max geq_max geq_max /= leq_maxl eq_leq //= leq_max.
        move: (leq_total (depth B1) (depth A)) => /orP [ -> | -> ] //=.
          by apply: orbT.
    Qed.
    Arguments adapt_inter_depth__left [A B1 B2 n].

    Lemma adapt_inter_depth__right: forall A B1 B2 n, n < maxn (depth A) (depth B2) -> n < maxn (depth A) (depth (B1 \cap B2)).
    Proof.
      move => A B1 B2 n size__prf.
      apply /ltP.
      apply: Nat.lt_le_trans.
      * apply /ltP; exact size__prf.
      * apply /leP.
        rewrite leq_max geq_max geq_max /= leq_maxr eq_leq //= leq_max.
        move: (leq_total (depth B2) (depth A)) => /orP [ -> | -> ] //=.
          by do 2 rewrite orbT.
    Qed.
    Arguments adapt_inter_depth__right [A B1 B2 n].

    Lemma cast_inter: forall (A1 A2 B: @IT Constructor),
        ~~isOmega B -> cast B (A1 \cap A2) = cast B A1 ++ cast B A2.
    Proof.
      move => A1 A2 B.
      repeat rewrite slow_cast_cast.
      rewrite /slow_cast /=.
        by case (isOmega B).
    Qed.

    Lemma cast_ctor_depth: forall A c C, all (fun A__i => depth A__i < depth A) (cast (Ctor c C) A).
    Proof.
      elim => //=.
      - move => a A _ c C.
        rewrite /cast.
        case: [ctor a <= c] => //=.
          by rewrite ltnSn.
      - move => A1 IH1 A2 IH2 c C.
        rewrite (cast_inter A1 A2 (Ctor c C) isT) all_cat.
        apply /andP.
        split.
        + apply (@sub_all _ (fun A => depth A < (depth A1))) => //.
          move => A size_prf.
          apply /ltP.
          apply: Nat.lt_le_trans.
          * by apply /ltP; exact size_prf.
          * by apply /leP; apply leq_maxl.
        + apply (@sub_all _ (fun A => depth A < (depth A2))) => //.
          move => A size_prf.
          apply /ltP.
          apply: Nat.lt_le_trans.
          * by apply /ltP; exact size_prf.
          * by apply /leP; apply leq_maxr.
    Qed.

    Lemma adapt_ctor_depth: forall A A' Delta,
        all (fun A__i => depth A__i < depth A) [:: A' & Delta ] ->
        depth (\bigcap_(A__i <- [:: A' & Delta ]) A__i) < depth A.
    Proof.
      move => A A' Delta.
      move: A'.
      elim: Delta.
      - rewrite /= => ?.
          by rewrite andbT.
      - move => A'' Delta IH A'.
        rewrite bigcap_cons => /andP [] size_prf1 /andP [] size_prf2 size_prf3.
        rewrite gtn_max size_prf1.
        move: (IH A'').
        rewrite /= size_prf2 /all size_prf3 /=.
          by auto.
    Qed.

    Lemma adapt_ctor_depth_max:
      forall A A' Delta b B,
        depth (\bigcap_(A__i <- [:: A' & Delta ]) A__i) < depth A ->
        maxn (depth (\bigcap_(A__i<-[::A'&Delta])A__i)) (depth B) < maxn (depth A) (depth (Ctor b B)).
    Proof.
      move => A A' Delta b B size_prf.
      rewrite gtn_max.
      apply /andP.
      split.
      - apply /ltP.
        apply: Nat.lt_le_trans.
        * apply /ltP; exact size_prf.
        * apply /leP.
            by rewrite leq_max eq_leq.
      - rewrite leq_max /= (eq_leq (erefl (depth B).+1)).
          by apply: orbT.
    Qed.
    Arguments adapt_ctor_depth_max [A A' Delta b B].

    Lemma adapt_depth_pair: forall A A' Delta,
        all (fun A__i => (depth A__i.1 < depth A) && (depth A__i.2 < depth A)) [:: A' & Delta ] ->
        (depth (\bigcap_(A__i <- [:: A' & Delta ]) A__i.1) < depth A)
          && (depth (\bigcap_(A__i <- [:: A' & Delta ]) A__i.2) < depth A).
    Proof.
      move => A A' Delta.
      move: A'.
      elim: Delta.
      - rewrite /= => ?.
          by rewrite andbT.
      - move => A'' Delta IH A'.
        rewrite bigcap_cons bigcap_cons => /andP [] /andP [] size_prf11 size_prf12 /andP [] /andP [] size_prf21 size_prf22 size_prf3.
        rewrite gtn_max gtn_max size_prf11 size_prf12.
        move: (IH A'') => /=.
        rewrite -/depth -/(map (fun x => x.2)) -/(intersect (map snd Delta)).
        move: IH => _.
        rewrite -/(all (fun A__i => (depth A__i.1 < depth A) && (depth A__i.2 < depth A))) in size_prf3.
        rewrite size_prf21 size_prf22 /= size_prf3 /=.
        move: size_prf3 => _.
        case: Delta.
        + by rewrite size_prf21; auto.
        + by auto.
    Qed.

    Lemma cast_arrow_depth:
      forall A C1 C2,
        (isOmega C2 = false) ->
        all (fun A__i => ((depth A__i.1) < depth A) && ((depth A__i.2) < depth A)) (cast (C1 -> C2) A).
    Proof.
      elim => //=.
      - move => C1 C2.
          by rewrite /cast /= => ->.
      - move => a A _ C1 C2.
          by rewrite /cast /= => ->.
      - move => A1 _ A2 _ C1 C2.
        rewrite /cast /= => ->.
        apply /andP.
        split => //.
        apply /andP.
        split.
        + by rewrite (leq_add2l 1) leq_max eq_leq.
        + rewrite (leq_add2l 1) leq_max (@eq_leq (depth A2) (depth A2)) => //.
            by apply: orbT.
      - move => A1 _ A2 _ C1 C2.
          by rewrite /cast /= => ->.
      - move => A1 IH1 A2 IH2 C1 C2.
        move: (cast_inter A1 A2 (C1 -> C2)) => /=.
        case isOmega__C2: (isOmega C2) => // split_app _.
        rewrite (split_app isT).       
        rewrite all_cat.
        apply /andP.
        split.
        + apply (@sub_all _ (fun A => (depth A.1 < (depth A1)) && (depth A.2 < (depth A1))));
            last by apply IH1; rewrite isOmega__C2.
          move => A /andP [] size_prf1 size_prf2.
          apply /andP.
          split.
          * by rewrite leq_max size_prf1.
          * by rewrite leq_max size_prf2.
        + apply (@sub_all _ (fun A => (depth A.1 < (depth A2)) && (depth A.2 < (depth A2))));
            last by apply IH2; rewrite isOmega__C2.
          move => A /andP [] size_prf1 size_prf2.
          apply /andP.
          split.
          * rewrite leq_max size_prf1.
              by apply: orbT.
          * rewrite leq_max size_prf2.
              by apply: orbT.
    Qed.

    Lemma adapt_arrow_depth_max:
      forall A A' Delta B1 B2,
        (depth (\bigcap_(A__i <- [:: A'.1 & map fst Delta ]) A__i) < depth A) &&
                                                                          (depth (\bigcap_(A__i <- [:: A'.2 & map snd Delta ]) A__i) < depth A) ->
        (maxn (depth B1) (depth (\bigcap_(A__i<-[:: A'.1 & map fst Delta]) A__i)) < maxn (depth A) (depth (B1 -> B2))) /\
        (maxn (depth (\bigcap_(A__i<-[:: A'.2 & map snd Delta]) A__i)) (depth B2) < maxn (depth A) (depth (B1 -> B2))).
    Proof.
      move => A A' Delta B1 B2 /andP [] size_prf1 size_prf2.
      rewrite gtn_max gtn_max.
      split; apply /andP; split.
      - rewrite leq_max /= (leq_add2l 1) leq_max (@eq_leq (depth B1) (depth B1)) //=.
          by apply: orbT.
      - by rewrite leq_max size_prf1.
      - by rewrite leq_max size_prf2.
      - by rewrite leq_max /= (leq_add2l 1) leq_max (@eq_leq (depth B2) (depth B2)) //= orbT orbT.
    Qed.
    Arguments adapt_arrow_depth_max [A A' Delta B1 B2].

    Lemma cast_product_depth: forall A C1 C2, all (fun A__i => (depth A__i.1 < depth A) && (depth A__i.2 < depth A)) (cast (C1 \times C2) A).
    Proof.
      elim => //=.
      - move => A1 _ A2 _ C1 C2.
        rewrite (leq_add2l 1) (leq_add2l 1).
        rewrite leq_max (@eq_leq (depth A1) (depth A1)) //=.
          by rewrite leq_max (@eq_leq (depth A2) (depth A2)) //= orbT.      
      - move => A1 IH1 A2 IH2 C1 C2.
        rewrite (cast_inter _ _ (C1 \times C2) isT).
        rewrite all_cat.
        apply /andP.
        split.
        + apply (@sub_all _ (fun A => (depth A.1 < (depth A1)) && (depth A.2 < (depth A1))));
            last by apply IH1; rewrite isOmega__C2.
          move => A /andP [] size_prf1 size_prf2.
          apply /andP.
          split.
          * by rewrite leq_max size_prf1.
          * by rewrite leq_max size_prf2.
        + apply (@sub_all _ (fun A => (depth A.1 < (depth A2)) && (depth A.2 < (depth A2))));
            last by apply IH2; rewrite isOmega__C2.
          move => A /andP [] size_prf1 size_prf2.
          apply /andP.
          split.
          * rewrite leq_max size_prf1.
              by apply: orbT.
          * rewrite leq_max size_prf2.
              by apply: orbT.
    Qed.

    Lemma adapt_product_depth_max:
      forall A A' Delta B1 B2,
        ((depth (\bigcap_(A__i <- [:: A' & Delta ]) A__i.1) < depth A)
           && (depth (\bigcap_(A__i <- [:: A' & Delta ]) A__i.2) < depth A)) ->
        (maxn (depth (\bigcap_(A__i<-[:: A' & Delta]) A__i.1)) (depth B1) < maxn (depth A) (depth (B1 \times B2))) /\
        (maxn (depth (\bigcap_(A__i<-[:: A' & Delta]) A__i.2)) (depth B2) < maxn (depth A) (depth (B1 \times B2))).
    Proof.
      move => A A' Delta B1 B2 /andP [] size_prf1 size_prf2.
      rewrite gtn_max gtn_max.
      split; apply /andP; split.
      - by rewrite leq_max size_prf1.
      - by rewrite leq_max /= (leq_add2l 1) leq_max (@eq_leq (depth B1) (depth B1)) //= orbT.
      - by rewrite leq_max size_prf2.
      - by rewrite leq_max /= (leq_add2l 1) leq_max (@eq_leq (depth B2) (depth B2)) //= orbT orbT.
    Qed.
    Arguments adapt_product_depth_max [A A' Delta B1 B2].

    Lemma choose_arrow_depth:
      forall A Delta Delta' B1,
        all (fun A__i => ((depth A__i.1) < depth A) && ((depth A__i.2) < depth A)) Delta ->
        [ tgt_for_srcs_gte B1 in Delta] ~~> [ check_tgt Delta'] ->
        ~~nilp Delta' ->
        depth (\bigcap_(A__i <- Delta') A__i) < depth A.
    Proof.
      move => A.
      elim.
      - by move => Delta' B1 _ /emptyDoneTgt ->.
      - move => A' Delta IH Delta' B1 /andP [] depth__A' depth__Delta prf.
        move: prf.
        move p1__eq: [ tgt_for_srcs_gte B1 in A'::Delta] => p1.
        move p2__eq: [ check_tgt Delta'] => p2 prf.
        move: A A' Delta B1 Delta' p1__eq p2__eq depth__A' depth__Delta IH.
        case: p1 p2 / prf => //.
        move => B1 A' Delta Delta' r _ prf2 A A'__tmp Delta__tmp B1__tmp Delta'__tmp.
        move => [] _ -> -> [] ->.
        move => /andP [] depth__A'1 depth__A'2 depth__Delta IH.
        case: r.
        + move => _.
          move: prf2.
          case: Delta' => //.
          move => A'' Delta' prf2.
            by rewrite bigcap_cons gtn_max -/depth depth__A'2 (IH _ B1 depth__Delta prf2 isT).
        + by apply: (IH Delta' B1).
    Qed.
    Arguments choose_arrow_depth [A Delta Delta' B1].

    Lemma omega__dom: forall A, Domain [subty Omega of A].
    Proof.
      elim => //.
      - move => a A p.
          by apply dom__Ctor.
      - move => A1 IH1 A2 IH2.
        apply dom__Arr.
        + rewrite /cast /=.
          case: (isOmega A2).
          * by apply dom__chooseTgt.
          * by apply dom__doneTgt.
        + move => Delta.
          move p1__eq: [tgt_for_srcs_gte A1 in cast (A1 -> A2) Omega] => p1.
          move p2__eq: [ check_tgt Delta ] => p2 prf.
          move: Delta p1__eq p2__eq IH1 IH2.
          case: p1 p2 / prf => //.
          * move => B A Delta Delta' r prf1 prf2 Delta'' [] [] ->.
            rewrite /cast /=.
            case isOmega__A2: (isOmega A2) => //=.
            move: prf2.
            case: Delta => //= prf2 [] A__eq.
            move: prf1.
            rewrite -A__eq.
            move: A A__eq => _ _ /=.
            move => prf1 [] ->.
            move: prf1.
            move p1__eq: [subty B of Omega] => p1.
            move p2__eq: (Return r) => p2 prf1.
            move: p1__eq p2__eq.
            case: p1 p2 / prf1 => // A [] -> _.
            move: prf2 => /emptyDoneTgt ->.
            case: r => //.
          * by move => ? ? _ [] ->.
      - move => B1 IH1 B2 IH2.
          by apply: dom__Prod.
      - auto.
    Qed.

    Lemma subtype_total: forall A B, Domain [subty A of B].
    Proof.
      apply: IT_depth_rect => A B.
      move: A.
      elim: B => //.
      - move => b B _ A IH.
        apply: dom__Ctor => //=.
        case cannotCast: (nilp (cast (Ctor b B) A)).
        + move /nilP: cannotCast => ->.
            by apply: omega__dom.
        + apply: IH.
          move: cannotCast (cast_ctor_depth A b B).
          case: (cast (Ctor b B) A) => // A' Delta _ depth_prf.
          apply: adapt_ctor_depth_max.
            by apply: adapt_ctor_depth.
      - move => B1 _ B2 _ A IH.
        move isOmega__B2: (isOmega B2) => b.
        move: isOmega__B2.
        case: b.
        + move => isOmega__B2.
          have cast_omega: cast (B1 -> B2) A = [:: (Omega, Omega)];
            first by  move: IH => _; case: A; rewrite /cast /= isOmega__B2.
          apply: dom__Arr;
            first by rewrite cast_omega; apply: dom__chooseTgt.
          rewrite cast_omega.
          move => Delta p.
          suff Delta__eq: (\bigcap_(A__i <- Delta) A__i) = Omega
            by rewrite Delta__eq; apply omega__dom.
          move: p.
          move p1__eq: [ tgt_for_srcs_gte B1 in [:: (Omega, Omega)]] => p1.
          move p2__eq: [ check_tgt Delta] => p2 prf.
          move: p1__eq p2__eq.
          case: p1 p2 / prf => // .
          move => B A1 Delta' Delta'' r prf1 prf2 p1__eq.
          move: p1__eq prf1 prf2 => [] <- <- <- /=.
          move p1__eq: [subty B1 of Omega] => p1.
          move p2__eq: (Return r) => p2 prf.
          move: p1__eq p2__eq.
          case: p1 p2 / prf => //.
          move => _ [] _ _ /emptyDoneTgt -> [] ->.
            by case: r.
        + move => notOmega__B2.
          move: (cast_arrow_depth A B1 B2 notOmega__B2).
          move cast__eq: (cast (B1 -> B2) A) => Delta.
          move: cast__eq.
          case: Delta.
          * move => cast__eq _.
            apply dom__Arr;
             first by rewrite cast__eq; apply: dom__doneTgt.
            rewrite cast__eq.
            move => Delta /emptyDoneTgt Delta__eq.
              by rewrite Delta__eq; apply: omega__dom.
          * move => A' Delta cast__eq depth_proofs.
            apply dom__Arr.
            ** rewrite cast__eq.
               move: cast__eq depth_proofs => _.
               move: A'.
               elim: Delta.
               *** move => A' /= depth_proof.
                   apply: dom__chooseTgt; last by apply: dom__doneTgt.
                   apply: IH.
                   move: (@adapt_arrow_depth_max A A' [::] B1 B2).
                   rewrite /=.
                   move => adapt.
                   rewrite andbT in depth_proof.
                     by move: (adapt depth_proof) => [].
               *** move => A2 Delta IH' A1 /= /andP [] depth_proof depth_proofs.
                   apply dom__chooseTgt;
                     last by apply: IH'.
                   apply: IH.
                   move: (@adapt_arrow_depth_max A A1 [::] B1 B2).
                   rewrite /=.
                   move => adapt.
                     by move: (adapt depth_proof) => [].
            ** case; first by move => _; apply omega__dom.
               move => A'' Delta' prf.
               suff A2__depth: depth (\bigcap_(A__i <- A''::Delta') A__i) < depth A.
               { apply: IH.
                rewrite gtn_max leq_max leq_max A2__depth /=.
                  by rewrite (leq_add2l 1) leq_max (eq_leq erefl) orbT orbT. }
               rewrite cast__eq in prf.
                 by apply: (choose_arrow_depth depth_proofs prf isT).
      - move => B1 _ B2 _ A IH.
        apply: dom__Prod.
        + move: (cast_product_depth A B1 B2).
          case: (cast (B1 \times B2) A);
            first by move => *; apply omega__dom.
          move => A' Delta depth_proof.
          apply: IH.
          move: (adapt_depth_pair _ _ _ depth_proof).
            by move => /(@adapt_product_depth_max _ _ _ B1 B2) [].
        + move: (cast_product_depth A B1 B2).
          case: (cast (B1 \times B2) A);
            first by move => *; apply omega__dom.
          move => A' Delta depth_proof.
          apply: IH.
          move: (adapt_depth_pair _ _ _ depth_proof).
            by move => /(@adapt_product_depth_max _ _ _ B1 B2) [].
      - move => B1 IH1 B2 IH2 A IH.
        apply: dom__Inter.
        + apply: IH1 => *.
          apply: IH.
            by apply: adapt_inter_depth__left.
        + apply: IH2 => *.
          apply: IH.
            by apply: adapt_inter_depth__right.
    Qed.

    Lemma total: forall p, Domain p.
    Proof.
      case.
      - move => [] A B; by apply: subtype_total.
      - move => [].
        move => B Delta.
        elim: Delta.
        + apply: dom__doneTgt.
        + move => A' Delta IH.
          apply: dom__chooseTgt => //.
            by apply subtype_total.
    Qed.
  End SubtypeMachineTotal.

  Section Execution.
    Let inv_dom__Ctor {A: IT} {b: Constructor} {B: IT} (ok: Domain [ subty A of Ctor b B]):
      Domain [ subty (\bigcap_(A__i <- cast (Ctor b B) A) A__i) of B].
    Proof.
      move: ok.
      move p__eq: [ subty A of Ctor b B] => p ok.
      move: p__eq.
      case: ok => //.
        by move => ? ? ? ? [] -> -> ->.
    Qed.

    Let inv_dom__Arr1 {A B1 B2: @IT Constructor} (ok: Domain [ subty A of B1 -> B2]):
      Domain [ tgt_for_srcs_gte B1 in cast (B1 -> B2) A].
    Proof.
      move: ok.
      move p__eq: [ subty A of B1 -> B2] => p ok.
      move: p__eq.
      case: ok => //.
        by move => ? ? ? ? ? [] -> [] -> ->.
    Qed.

    Let inv_dom__Arr2 {A B1 B2: @IT Constructor} {Delta: seq (@IT Constructor)} (ok: Domain [ subty A of B1 -> B2]): 
      [ tgt_for_srcs_gte B1 in cast (B1 -> B2) A] ~~> [ check_tgt Delta] ->
      Domain [ subty (\bigcap_(A__i <- Delta) A__i) of B2].
    Proof.
      move: ok.
      move p1__eq: [ subty A of B1 -> B2] => p1 prf.
      move: p1__eq.
      case: p1 / prf => // A'' B1' B2' prf' IH [] -> [] -> -> prf.
        by apply: IH.
    Qed.

    Let inv_dom__Prod1 {A B1 B2: @IT Constructor} (ok: Domain [ subty A of B1 \times B2]):
      Domain [ subty (\bigcap_(A__i <- cast (B1 \times B2) A) A__i.1) of B1].
    Proof.
      move: ok.
      move p1__eq: [ subty A of B1 \times B2] => p1 ok.
      move: p1__eq.
        by case: p1 / ok => // ? ? ? ? ? [] -> [] -> ->.
    Qed.

    Let inv_dom__Prod2 {A B1 B2: @IT Constructor} (ok: Domain [ subty A of B1 \times B2]):
      Domain [ subty (\bigcap_(A__i <- (cast (B1 \times B2) A)) A__i.2) of B2].
    Proof.
      move: ok.
      move p1__eq: [ subty A of B1 \times B2] => p1 ok.
      move: p1__eq.
        by case: p1 / ok => // ? ? ? ? ? [] -> [] -> ->.
    Qed.

    Let inv_dom__Inter1 {A B1 B2: @IT Constructor} (ok: Domain [ subty A of B1 \cap B2]):
      Domain [ subty A of B1].
    Proof.
      move: ok.
      move p1__eq: [ subty A of B1 \cap B2] => p1 ok.
      move: p1__eq.
        by case: p1 / ok => // ? ? ? ? ? [] -> [] ->.
    Qed.

    Let inv_dom__Inter2 {A B1 B2: @IT Constructor} (ok: Domain [ subty A of B1 \cap B2]):
      Domain [ subty A of B2].
    Proof.
      move: ok.
      move p1__eq: [ subty A of B1 \cap B2] => p1 ok.
      move: p1__eq.
        by case: p1 / ok => // ? ? ? ? ? [] -> [] _ ->.
    Qed.

    Let inv_dom__chooseTgt1 {B: @IT Constructor} {A: IT*IT} {Delta: seq (IT*IT)} (ok: Domain [tgt_for_srcs_gte B in [:: A & Delta ]]):
      Domain [subty B of A.1].
    Proof.
      move: ok.
      move p1__eq: [ tgt_for_srcs_gte B in A :: Delta] => p1 ok.
      move: p1__eq.
        by case: p1 / ok => // ? ? ? ? ? [] -> ->.
    Qed.

    Let inv_dom__chooseTgt2 {B: @IT Constructor} {A: IT*IT} {Delta: seq (IT*IT)} (ok: Domain [tgt_for_srcs_gte B in [:: A & Delta ]]):
      Domain [tgt_for_srcs_gte B in Delta].
    Proof.
      move: ok.
      move p1__eq: [ tgt_for_srcs_gte B in A :: Delta] => p1 ok.
      move: p1__eq.
        by case: p1 / ok => // ? ? ? ? ? [] -> _ ->.
    Qed.

    Let subtyp_return_value (r: @Result Constructor): bool :=
      match r with
      | Return b => b
      | _ => false
      end.

    Lemma inv_subtyp_return {A B: @IT Constructor} {r: Result}: [subty A of B] ~~> r -> r = Return (subtyp_return_value r).
    Proof.
      move p1__eq: [ subty A of B] => p1 prf.
      move: p1__eq.
        by case: p1 r /prf.
    Qed.

    Let tgt_for_srcs_gte_return_value (r: @Result Constructor): seq (@IT Constructor) :=
      match r with
      |[ check_tgt Delta] => Delta
      | _ => [::]
      end.

    Lemma inv_tgt_for_srcs_gte_check_tgt {B} {Delta} {r: Result}:
      [ tgt_for_srcs_gte B in Delta] ~~> r -> r = [ check_tgt (tgt_for_srcs_gte_return_value r)].
    Proof.
      move p1__eq: [ tgt_for_srcs_gte B in Delta] => p1 prf.
      move: p1__eq.
        by case: p1 r / prf.
    Qed.

    Fixpoint subtype_machine_rec (p: Instruction) (ok: Domain p) {struct ok}: { r | p ~~> r} :=
      match p as p' return Domain p' -> { r | p' ~~> r } with
      | [ subty A of Omega] => fun _ => exist _ (Return true) step__Omega
      | [ subty A of Ctor b B] =>
        fun ok =>
          let: casted := cast (Ctor b B) A in
          let: canCast := ~~nilp casted in
          let: (exist R Prf) := subtype_machine_rec [subty (\bigcap_(A__i <- casted) A__i) of B] (inv_dom__Ctor ok) in
          let: prf := (rew inv_subtyp_return Prf in Prf) in
          let: r := subtyp_return_value R in
          exist _ (Return (canCast && r)) (step__Ctor prf)
      | [ subty A of B1 -> B2] =>
        fun ok =>
          let: (exist R1 Prf__src) := subtype_machine_rec [ tgt_for_srcs_gte B1 in cast (B1 -> B2) A]
                                                        (inv_dom__Arr1 ok) in
          let: prf__src := (rew inv_tgt_for_srcs_gte_check_tgt Prf__src in Prf__src) in
          let: Delta := tgt_for_srcs_gte_return_value R1 in
          let: (exist R2 Prf__tgt) := subtype_machine_rec [ subty (\bigcap_(A__i <- Delta) A__i) of B2]
                                                        (inv_dom__Arr2 ok prf__src)  in
          let: prf__tgt := (rew inv_subtyp_return Prf__tgt in Prf__tgt) in
          let: r := (subtyp_return_value R2) in
          exist _ (Return (isOmega B2 || r)) (step__Arr prf__src prf__tgt)
      | [ subty A of B1 \times B2] =>
        fun ok =>
          let: casted := cast (B1 \times B2) A in
          let: canCast := ~~ nilp casted in
          let: (exist R1 Prf1) := subtype_machine_rec [ subty (\bigcap_(A__i <- casted) (fst A__i)) of B1]
                                                      (inv_dom__Prod1 ok) in
          let: (exist R2 Prf2) := subtype_machine_rec [ subty (\bigcap_(A__i <- casted) (snd A__i)) of B2]
                                                      (inv_dom__Prod2 ok) in
          let: prf1 := (rew inv_subtyp_return Prf1 in Prf1) in
          let: r1 := subtyp_return_value R1 in
          let: prf2 := (rew inv_subtyp_return Prf2 in Prf2) in
          let: r2 := subtyp_return_value R2 in
          exist _ (Return (canCast && r1 && r2 )) (step__Prod prf1 prf2)
      | [ subty A of B1 \cap B2] =>
        fun ok =>
          let: (exist R1 Prf1) := subtype_machine_rec [ subty A of B1] (inv_dom__Inter1 ok) in
          let: (exist R2 Prf2) := subtype_machine_rec [ subty A of B2] (inv_dom__Inter2 ok) in
          let: prf1 := (rew inv_subtyp_return Prf1 in Prf1) in
          let: r1 := subtyp_return_value R1 in
          let: prf2 := (rew inv_subtyp_return Prf2 in Prf2) in
          let: r2 := subtyp_return_value R2 in
          exist _ (Return (r1 && r2)) (step__Inter prf1 prf2)
      | [ tgt_for_srcs_gte B1 in [:: A & Delta]] =>
        fun ok =>
          let: (exist R1 Prf1) := subtype_machine_rec [ subty B1 of A.1] (inv_dom__chooseTgt1 ok) in
          let: prf1 := (rew inv_subtyp_return Prf1 in Prf1) in
          let: r := subtyp_return_value R1 in
          let: (exist R2 Prf2) := subtype_machine_rec [ tgt_for_srcs_gte B1 in Delta]
                                                      (inv_dom__chooseTgt2 ok) in
          let: prf2 := (rew inv_tgt_for_srcs_gte_check_tgt Prf2 in Prf2) in
          let: Delta' := tgt_for_srcs_gte_return_value R2 in
          exist _ [ check_tgt if r then [:: A.2 & Delta'] else Delta']
                (step__chooseTgt prf1 prf2)
      | [ tgt_for_srcs_gte B1 in [::]] =>
        fun _ => exist _ [ check_tgt [::]] step__doneTgt
      end ok.
  
    Definition subtype_machine (p: Instruction): { r | p ~~> r } := subtype_machine_rec p (total p).
  End Execution.

  Section BCDRules.
    Implicit Type A B C: @IT Constructor.
    Lemma subty__Omega: forall A B, isOmega B -> [ subty A of B] ~~> Return true.
    Proof.
      move => A B.
      move: A.
      elim: B => //.
      - move => B1 IH1 B2 IH2 A isOmega__B2.
        have: exists Delta, [ tgt_for_srcs_gte B1 in cast (B1 -> B2) A] ~~> [ check_tgt Delta].
        + move: (subtype_machine [ tgt_for_srcs_gte B1 in cast (B1 -> B2) A]) => [] r.
          move p__eq: [ tgt_for_srcs_gte B1 in cast (B1 -> B2) A] => p prf.
          move: p__eq.
          case: p r / prf => //; by eauto.
        + move => [] A' prf.
          move: (step__Arr prf (IH2 _ isOmega__B2)).
            by rewrite orbT.
      - move => B1 IH1 B2 IH2 A /andP [] prf1 prf2.
          by apply: (step__Inter (IH1 _ prf1) (IH2 _ prf2)).
    Qed.
   
    Lemma all_omega: forall A B1 B2, isOmega A -> all (@isOmega _) (map snd (cast (B1 -> B2) A)).
    Proof.
      elim => //.
      - move => B1 B2 /=.
        rewrite /cast /=.
          by case: (isOmega B2).
      - move => A1 IH1 A2 IH2 B1 B2 /= isOmega__A2.
        rewrite /cast /=.
        case: (isOmega B2) => //=.
          by rewrite isOmega__A2.
      - move => A1 IH1 A2 IH2 B1 B2 /andP [] isOmega__A1 isOmega__A2 /=.
        case notOmega__B2: (~~isOmega B2);
          last by move: notOmega__B2; rewrite /cast /=; case (isOmega B2) => //.
        rewrite (cast_inter A1 A2 (B1 -> B2) notOmega__B2).
          by rewrite map_cat all_cat (IH1 _ _ isOmega__A1) (IH2 _ _ isOmega__A2).
    Qed.

    Lemma bigcap_omega: forall Delta, all (@isOmega Constructor) Delta = isOmega (\bigcap_(A__i <- Delta) A__i).
    Proof.
      elim => // A Delta IH.
      rewrite bigcap_cons.
      move: IH.
      case: Delta => /=.
      - by rewrite andbT.
      - by move => A' Delta ->.
    Qed.

    Lemma check_tgt_subseq:
      forall Delta Delta' B1,
        [ tgt_for_srcs_gte B1 in Delta] ~~> [ check_tgt Delta'] ->
        subseq Delta' (map snd Delta).
    Proof.
      elim.
      - by move => Delta' B1 /emptyDoneTgt ->.
      - move => A' Delta IH Delta' B1.
        move p__eq: [ tgt_for_srcs_gte B1 in [:: A' & Delta]] => p.
        move r__eq: [ check_tgt Delta'] => r prf.
        move: B1 A' Delta Delta' p__eq r__eq IH.
        case: p r / prf => //.
        move => B1 A' Delta Delta' r _ prf2 B1__tmp A'__tmp Delta__tmp Delta'__tmp [] _ -> -> [] -> IH.
        case: r.
        + rewrite /=.
          move: (erefl A'.2) => /eqP ->.
            by apply: (IH _ B1).
        + apply: (subseq_trans (IH _ _ prf2)).
            by apply: subseq_cons.
    Qed.


    Lemma Omega__tgts: forall A Delta B1 B2,
        [ tgt_for_srcs_gte B1 in cast (B1 -> B2) A] ~~> [ check_tgt Delta] ->
        isOmega A ->
        all (@isOmega Constructor) Delta.
    Proof.
      move => A Delta B1 B2 prf isOmega__A.
      move: (all_omega _ B1 B2 isOmega__A) => /allP omegaPrf.
      move: (check_tgt_subseq _ _ _ prf) => /mem_subseq member_prf.
      apply /allP => A' inprf.
      apply omegaPrf.
        by apply member_prf.
    Qed.

    Lemma omega_nilp__Ctor: forall A b B, isOmega A -> nilp (cast (Ctor b B) A).
    Proof.
      elim => //=.
      move => A1 IH1 A2 IH2 b B /andP [] isOmega__A1 isOmega__A2.
      move: (IH1 b B isOmega__A1) (IH2 b B isOmega__A2).
      repeat rewrite slow_cast_cast.
        by rewrite /slow_cast /= => /nilP -> /nilP ->.
    Qed.

    Lemma omega_nilp__Prod: forall A B1 B2, isOmega A -> nilp (cast (B1 \times B2) A).
    Proof.
      elim => //=.
      move => A1 IH1 A2 IH2 B1 B2 /andP [] isOmega__A1 isOmega__A2.
      move: (IH1 B1 B2 isOmega__A1) (IH2 B1 B2  isOmega__A2).
      repeat rewrite slow_cast_cast.
        by rewrite /slow_cast /= => /nilP -> /nilP ->.
    Qed.

    Lemma Omega__subty: forall A B, [ subty A of B] ~~> Return true -> isOmega A -> isOmega B.
    Proof.
      move => A B.
      move p__eq: [ subty A of B] => p.
      move r__eq: (Return true) => r prf.
      move: A B p__eq r__eq.
      elim: p r / prf => //.
      - by move => ? ? ? [] -> ->.
      - move => A b B r _ _ ? ? [] -> _ devil isOmega__A.
        rewrite (omega_nilp__Ctor A b B isOmega__A) in devil.
        discriminate devil.
      - move => A B1 B2 Delta r prf1 _ prf2 IH A__tmp B__tmp [] -> -> r__eq isOmega__A /=.
        case isOmega__B2: (isOmega B2) => //.
        rewrite isOmega__B2 /= in r__eq.
        rewrite -isOmega__B2.
        apply: (IH _ _ erefl r__eq).
        rewrite -bigcap_omega.
        apply: (Omega__tgts _ _ _ _ prf1 isOmega__A).
      - move => A B1 B2 r1 r2 _ _ _ _ ? ? [] -> _ devil isOmega__A.
        rewrite (omega_nilp__Prod A B1 B2 isOmega__A)in devil.
        discriminate devil.
      - move => A B1 B2 r1 r2 prf1 IH1 prf2 IH2 A__tmp B__tmp [] -> -> [] /eqP /andP [] r1__true r2__true isOmega__A /=.
        rewrite r1__true in IH1.
        rewrite r2__true in IH2.
          by rewrite (IH1 _ _ erefl erefl isOmega__A) (IH2 _ _ erefl erefl isOmega__A).
    Qed.

    Lemma castsubseq__Ctor: forall A b c B C,
        [ctor b <= c] -> subseq (cast (Ctor b B) A) (cast (Ctor c C) A).
    Proof.
      elim => //.
      - move => a A IH b c B C leq__bc /=.
        rewrite /cast /=.
        case leq__ab: [ ctor a <= b].
        + move: (preorder_transitive a b c).
            by rewrite leq__ab leq__bc /= => ->.
        + by apply: sub0seq.
      - move => A1 IH1 A2 IH2 b c B C leq__bc /=.
        rewrite (cast_inter _ _ (Ctor b B) isT) (cast_inter _ _ (Ctor c C) isT).
          by apply: cat_subseq; eauto.
    Qed.

    Lemma split_cast: forall A Delta B,
        ~~isOmega B ->
        cast B (\bigcap_(A__i <- [:: A & Delta]) A__i) = cast B A ++ cast B (\bigcap_(A__i <- Delta) A__i).
    Proof.
      move => A Delta B.
      rewrite bigcap_cons.
      case: Delta.
      + rewrite /= {3}/cast.
        case (isOmega B) => //.
          by rewrite cats0.
      + move => A' Delta notOmega__B.
          by rewrite (cast_inter _ _ _ notOmega__B).
    Qed.

    Lemma castsubseq: forall Delta Delta' B,
        subseq Delta Delta' ->
        subseq (cast B (\bigcap_(A__i <- Delta) A__i)) (cast B (\bigcap_(A__i <- Delta') A__i)).
    Proof.
      move => Delta Delta' B.
      case isOmega__B: (isOmega B);
        first by rewrite /cast isOmega__B; auto using subseq_refl.
      move: Delta.
      elim: Delta'.
      - case => //.
      - move => A' Delta' IH.
        case.
        + by rewrite {1}/cast isOmega__B /=; move => ?; apply sub0seq.
        + move => A Delta.
          rewrite [subseq _ _]/=.
          case A__eq: (A == A').
          * rewrite (eqP A__eq) =>incl.
            do 2 rewrite (split_cast _ _ _ (negbT isOmega__B)) /=.
            apply: cat_subseq;
              by auto using subseq_refl, IH.
          * move => incl.
            rewrite (split_cast _ Delta' _ (negbT isOmega__B)).
            rewrite -(cat0s (cast B (\bigcap_(A__i <- [:: A & Delta]) A__i))).
            apply: cat_subseq;
              by auto using sub0seq, IH.
    Qed.

    Lemma weaken_check_tgt:
      forall Delta1 Delta1' Delta2 Delta2' B1,
        subseq Delta2 Delta1 ->
        [ tgt_for_srcs_gte B1 in Delta1] ~~> [ check_tgt Delta1'] ->
        [ tgt_for_srcs_gte B1 in Delta2] ~~> [ check_tgt Delta2'] ->
        subseq Delta2' Delta1'.
    Proof.
      elim.
      - move => Delta1' Delta2 Delta2' B1.
        rewrite subseq0 => /eqP ->.
          by move => /emptyDoneTgt -> /emptyDoneTgt ->.
      - move => A1 Delta1 IH Delta1'.
        case.
        + move => ? ? _ _ /emptyDoneTgt ->.
            by rewrite sub0seq.
        + move => A2 Delta2 Delta2' B1.
          rewrite [subseq _ _]/=.
          case A__eq: (A2 == A1).
          * move: A__eq => /eqP ->.
            move: A2 => _.
            move => incl.
            move p__eq: [ tgt_for_srcs_gte B1 in A1 :: Delta1] => p.
            move r1__eq: [ check_tgt Delta1'] => r1 prf.
            move: p__eq r1__eq.
            case: p r1 / prf => // B1__tmp A1__tmp Delta1__tmp Delta1'__tmp r1 prf11 prf12 p__eq r1__eq.
            move: p__eq r1__eq prf11 prf12 => [] <- <- <- [] -> prf11 prf12.
            move p__eq: [ tgt_for_srcs_gte B1 in A1 :: Delta2] => p.
            move r2__eq: [ check_tgt Delta2'] => r2 prf.
            move: p__eq r2__eq.
            case: p r2 /prf => // B__tmp2 A2__tmp Delta2__tmp Delta2'__tmp r2 prf21 prf22 p__eq r2__eq.
            move: p__eq r2__eq prf21 prf22 => [] <- <- <- [] -> prf21 prf22.
            have: r1 = r2
              by move: (Semantics_functional [ subty B1 of A1.1] (Return r1) (Return r2) prf11 prf21) => [] ->.
            move: prf11 prf21 => _ _ ->.
            move: (IH _ _ _ _ incl prf12 prf22).
            case: r2 => //=.
              by move: (erefl A1.2) => /eqP ->.
          * move => incl.
            move p__eq: [ tgt_for_srcs_gte B1 in A1 :: Delta1] => p.
            move r1__eq: [ check_tgt Delta1'] => r1 prf.
            move: p__eq r1__eq.
            case: p r1 / prf => // B1__tmp A1__tmp Delta1__tmp Delta1'__tmp r1 prf11 prf12 p__eq r1__eq.
            move: p__eq r1__eq prf11 prf12 => [] <- <- <- [] -> prf11 prf12 prf2.
            move: (IH _ _ _ _ incl prf12 prf2).
            move: prf11 => _.
            case: r1 => // incl'.
            apply: (subseq_trans incl').
              by apply: subseq_cons.
    Qed.

    Lemma bigcap_map_eq:
      forall (t: Type) (Delta: seq t) (f: t -> @IT Constructor),
        (\bigcap_(A__i <- Delta) (f A__i)) ==
        (\bigcap_(A__i <- map f Delta) A__i).
    Proof.
      move => t Delta f.
      elim: Delta => // A Delta.
      do 2 rewrite bigcap_cons.
        by case: Delta => // A' Delta /eqP ->.
    Qed.
    Arguments bigcap_map_eq [t Delta].

    Lemma nilp_subseq_bigcap_cast:
      forall A Delta Delta',
        subseq Delta Delta' ->
        ~~ nilp (cast A (\bigcap_(A__i <- Delta) A__i)) ->
        ~~ nilp (cast A (\bigcap_(A__i <- Delta') A__i)).
    Proof.
      move => A Delta Delta' incl /nilP not_empty.
      move: (castsubseq _ _ A incl).
      case: (cast A (\bigcap_(A__i <- Delta') A__i)) => //=.
        by move => /eqP /not_empty.
    Qed.

    Lemma subty__weaken: forall A Delta Delta',
        subseq Delta Delta' ->
        [ subty (\bigcap_(A__i <- Delta) A__i) of A] ~~> Return true ->
        [ subty (\bigcap_(A__i <- Delta') A__i) of A] ~~> Return true.
    Proof.
      move => A Delta Delta' incl.
      move p__eq: [ subty \bigcap_(A__i <- Delta) A__i of A] => p.
      move r__eq: (Return true) => r prf.
      move: A Delta p__eq r__eq  Delta' incl.
      elim: p r / prf => //.
      - by move => ? ? ? [] _ -> *; apply: step__Omega.
      - move => Delta__tmp a A r prf IH A__tmp Delta [] Delta__eq.
        rewrite -Delta__eq => -> [] r__true Delta' incl.        
        case isOmega__Delta: (isOmega (\bigcap_(A__i <- Delta) A__i)).
        + rewrite (omega_nilp__Ctor _ _ _ isOmega__Delta) in r__true.
          discriminate r__true.
        + have isOmega__Delta' : (isOmega (\bigcap_(A__i <- Delta') A__i) = false).
          * move: isOmega__Delta.
            do 2 rewrite -bigcap_omega.
            move => /allPn [] A'.
            move: (mem_subseq incl) => f /f inprf notOmega__A'.
            apply /allPn.
              by eauto.
          * have not_nilp__Delta: ~~ nilp (cast (Ctor a A) (\bigcap_(A__i <- Delta) A__i)).
            { move: r__true.
                by case eq: (~~ nilp (cast (Ctor a A) (\bigcap_(A__i <- Delta) A__i))). }
            have not_nilp_eq:
              ((~~ nilp (cast (Ctor a A) (\bigcap_(A__i <- Delta) A__i))) ==
               ~~ nilp (cast (Ctor a A) (\bigcap_(A__i <- Delta') A__i))).
            { by rewrite (nilp_subseq_bigcap_cast _ _ _ incl not_nilp__Delta) not_nilp__Delta. }
            rewrite (eqP not_nilp_eq).
            apply step__Ctor.
            rewrite not_nilp__Delta /= in r__true.
            rewrite r__true -Delta__eq in IH.
              by apply: (IH _ _ erefl erefl
                            (cast (Ctor a A) (\bigcap_(A__i <- Delta') A__i))
                            (castsubseq _ _ (Ctor a A) incl)).
      - move => Delta__tmp B1 B2 Delta1' r1 prf11 _ prf12 IH2 B__tmp Delta [] Delta__eq B__eq [] r__true Delta' incl.
        move: Delta__eq B__eq prf11 prf12 => <- -> prf11 prf12.
        rewrite -r__true.
        move: (subtype_machine [ tgt_for_srcs_gte B1 in cast (B1 -> B2) (\bigcap_(A__i <- Delta') A__i)]) => [] res21 prf21.
        move: (inv_tgt_for_srcs_gte_check_tgt prf21) => res21__eq.
        rewrite res21__eq in prf21.
        case isOmega__B2: (isOmega B2).
        + move: (subtype_machine [ subty \bigcap_(A__i <- match res21 with
                                                        | Return _ => [::]
                                                        | [ check_tgt Delta] => Delta
                                                        end) A__i of B2]) => [] res22 prf22.
          move: (inv_subtyp_return prf22) => res22__eq.
          rewrite res22__eq in prf22.
          move: (step__Arr prf21 prf22).
            by rewrite isOmega__B2.
        + rewrite isOmega__B2 /= in r__true.
          move: (IH2 _ _ erefl (f_equal (@Return _) r__true) _
                     (weaken_check_tgt (cast (B1 -> B2) (\bigcap_(A__i <- Delta') A__i)) _
                                       (cast (B1 -> B2) (\bigcap_(A__i <- Delta) A__i)) _ _
                                       (castsubseq _ _ (B1 -> B2) incl) prf21 prf11)).
          move => /(step__Arr prf21).
            by rewrite isOmega__B2 r__true.
      - move => A B1 B2 r1 r2 prf1 IH1 prf2 IH2 A__tmp Delta [] Delta__eq A__eq [] r__true Delta' incl.
        rewrite A__eq -Delta__eq.
        case isOmega__Delta: (isOmega (\bigcap_(A__i <- Delta) A__i)).
        + rewrite -Delta__eq (omega_nilp__Prod _ _ _ isOmega__Delta) /= in r__true.
          discriminate r__true.
        + have isOmega__Delta' : (isOmega (\bigcap_(A__i <- Delta') A__i) = false).
          { move: isOmega__Delta.
            do 2 rewrite -bigcap_omega.
            move => /allPn [] A'.
            move: (mem_subseq incl) => f /f inprf notOmega__A'.
            apply /allPn.
              by eauto. }
          have not_nilp__Delta: (~~ nilp (cast (B1 \times B2) (\bigcap_(A__i <- Delta) A__i))).
          { move: r__true.
            rewrite -Delta__eq.
            case: (cast (B1 \times B2) (\bigcap_(A__i <- Delta) A__i)) => //. }
          have not_nilp_eq: ((~~ nilp (cast (B1 \times B2) (\bigcap_(A__i <- Delta) A__i))) ==
                             (~~ nilp (cast (B1 \times B2) (\bigcap_(A__i <- Delta') A__i)))).
          { by rewrite (nilp_subseq_bigcap_cast _ _ _ incl not_nilp__Delta) not_nilp__Delta. }
          rewrite (eqP not_nilp_eq).
          rewrite -Delta__eq not_nilp__Delta /= in r__true.
          apply step__Prod.
          * move: r__true prf1 IH1.
            rewrite -Delta__eq.
            case: r1 => // _ prf1 IH.
            rewrite (eqP (bigcap_map_eq fst)) in IH.
            move: (IH _ (map fst (cast (B1 \times B2) (\bigcap_(A__i <- Delta) A__i)))
                      erefl erefl
                      (map fst (cast (B1 \times B2) (\bigcap_(A__i <- Delta') A__i)))
                      (map_subseq fst (castsubseq _ _ (B1 \times B2) incl))).
              by rewrite (eqP (bigcap_map_eq fst)).
          * move: r__true prf2 IH2.
            rewrite -Delta__eq.
            case: r2; last by rewrite andbF.
            move => _ prf2 IH.
            rewrite (eqP (bigcap_map_eq snd)) in IH.
            move: (IH _ (map snd (cast (B1 \times B2) (\bigcap_(A__i <- Delta) A__i)))
                      erefl erefl
                      (map snd (cast (B1 \times B2) (\bigcap_(A__i <- Delta') A__i)))
                      (map_subseq snd (castsubseq _ _ (B1 \times B2) incl))).
              by rewrite (eqP (bigcap_map_eq snd)).
      - move => A B1 B2 r1 r2 prf1 IH1 prf2 IH2 B Delta [] Delta__eq B__eq [] r__true Delta' incl.
        rewrite B__eq.
        apply step__Inter.
        + rewrite -Delta__eq in IH1.
          move: r__true IH1 prf1.
          case: r1 => // _ IH1 _.
          apply: (IH1 _ _ erefl erefl _ incl).
        + rewrite -Delta__eq in IH2.
          move: r__true IH2 prf2.
          case: r2; last by rewrite andbF.
          move => // _ IH2 _.
          apply: (IH2 _ _ erefl erefl _ incl).
    Qed.

    Lemma subty__cat: forall A Delta1 Delta2 (r1 r2: bool),
        [ subty A of \bigcap_(A__i <- Delta1) A__i] ~~> Return r1 ->
        [ subty A of \bigcap_(A__i <- Delta2) A__i] ~~> Return r2 ->
        [ subty A of \bigcap_(A__i <- Delta1 ++ Delta2) A__i] ~~> Return (r1 && r2).
    Proof.
      move => A.
      elim.
      - by move => Delta2 r1 r2 /= /(Semantics_functional _ (Return true) (Return r1) (step__Omega)) [] <-.
      - move => A1 Delta1 IH Delta2 r1 r2 prf1 prf2.
        rewrite bigcap_cons in prf1.
        move: prf1 IH.
        case: Delta1.
        + move => /= prf1.
          move: prf2.
          case: Delta2 => /=.
          * move => /(Semantics_functional _ (Return true) (Return r2) (step__Omega)) [] <-.
              by rewrite andbT.
          * move => A2 Delta2 prf2 IH.
              by apply step__Inter.
        + move => A12 Delta1 prf1 IH.
          move: prf1.
          move p__eq: [ subty A of A1 \cap \bigcap_(A__i <- (A12 :: Delta1)) A__i] => p.
          move r__eq: (Return r1) => r prf.
          move: p__eq r__eq.
          case: p r / prf => //.
          move => A__tmp B1 B2 r11 r12 prf11 prf12 [] A__eq [] B1__eq B2__eq [] r1__eq.
          rewrite r1__eq -andbA.
          apply: step__Inter.
          * by rewrite A__eq B1__eq.
          * rewrite -A__eq -B2__eq in prf12.
              by apply: (IH Delta2 r12 r2 prf12 prf2).
    Qed.

    Lemma subty__CtorTrans: forall A B c C,
    [ subty A of B] ~~> Return true ->
    [ subty \bigcap_(A__i <- cast (Ctor c C) A) A__i of \bigcap_(A__i <- cast (Ctor c C) B) A__i] ~~> Return true.
    Proof.
      move => A B c C.
      move p__eq: [ subty A of B] => p.
      move r__eq: (Return true) => r prf.
      move: A B p__eq r__eq c C.
      elim: p r / prf => //.
      - move => ? ? ? [] -> -> /= *.
          by apply subty__Omega.
      - move => A b B r prf1 IH A__tmp B__tmp [] A__eq B__eq.
        rewrite A__eq B__eq => [] [] /eqP /andP [] notOmega__A r__true c C /=.
        case leq__bc: [ctor b <= c].
        + rewrite r__true notOmega__A.
          rewrite r__true in prf1.
          rewrite /= {2}/cast leq__bc /=.
          by apply: (subty__weaken B (cast (Ctor b B) A) (cast (Ctor c C) A)
                                 (castsubseq__Ctor _ _ _ _ _ leq__bc) prf1).
        + rewrite {2}/cast leq__bc notOmega__A r__true /=.
            by apply: step__Omega.
      - move => A B1 B2 Delta r prf1 _ prf2 IH2 A__tmp B__tmp [] -> -> [] r__true c C.
        rewrite {2}/cast /= -r__true.
          by apply: step__Omega.
      - move => A B1 B2 r1 r2 prf1 _ prf2 _ A__tmp B__tmp [] -> -> r__true c C.
        rewrite {2}/cast /= -r__true.
          by apply: step__Omega.
      - move => A B1 B2 r1 r2 prf1 IH1 prf2 IH2 A__tmp B__tmp [] -> -> r__true c C.
        rewrite (slow_cast_cast _ (B1 \cap B2)).
        rewrite /slow_cast /=.
        apply: subty__cat.
        + match goal with
          |[|- [ subty _ of \bigcap_(A__i <- ?x) A__i] ~~> _ ] =>
           have: x = cast (Ctor c C) B1 by rewrite slow_cast_cast /slow_cast
          end.
          move => ->.
          apply: IH1 => //.
          move: r__true prf1.
            by case: r1.
        + match goal with
          |[|- [ subty _ of \bigcap_(A__i <- ?x) A__i] ~~> _ ] =>
           have: x = cast (Ctor c C) B2 by rewrite slow_cast_cast /slow_cast
          end.
          move => ->.
          apply: IH2 => //.
          move: r__true prf2.
          case: r2 => //.
            by rewrite andbF.
    Qed.

    Lemma omegaDoneTgt:
      forall (B: @IT Constructor) (A: @IT Constructor) Delta,
        [ tgt_for_srcs_gte B in [:: (Omega, A)]] ~~> [ check_tgt Delta] -> Delta = [:: A].
    Proof.
      move => B A Delta.
      move p__eq: [ tgt_for_srcs_gte B in [:: (Omega, A)]] => p.
      move r__eq: [ check_tgt Delta] => r prf.
      move: r__eq p__eq.
      case: p r / prf => // B__tmp A__tmp Delta1 Delta2 r prf1 prf2 [] Delta__eq [] B__eq A__eq Delta1__eq.
      rewrite -A__eq in prf1.
      move: prf1 Delta__eq => /= /(Semantics_functional _ _ _ (subty__Omega B__tmp Omega isT)) [] <- ->.
      rewrite -A__eq /=.
      apply: f_equal.
      move: prf2.
        by rewrite -Delta1__eq => /emptyDoneTgt.
    Qed.

    Lemma subty__Refl: forall A, [ subty A of A] ~~> Return true.
    Proof.
      elim.
      - by apply: step__Omega.
      - move => a A IH.
        have canCast: (true = ~~(nilp (cast (Ctor a A) (Ctor a A)))).
        { by rewrite /cast /= preorder_reflexive. }
        rewrite -(andbT true) [T in T && true]canCast.
        apply step__Ctor.
          by rewrite /cast /= preorder_reflexive /=.
      - move => A1 IH1 A2 IH2.
        case isOmega__A2: (isOmega A2).
        + by apply: (subty__Omega (A1 -> A2) (A1 -> A2) isOmega__A2).
        + rewrite -(orFb true) -isOmega__A2.
          apply: (step__Arr (Delta := [:: A2])) => //.
          rewrite /cast /= isOmega__A2.
            by apply: (step__chooseTgt (Delta' := [::]) (r := true)).
      - move => A1 IH1 A2 IH2.
        have canCast: (true = ~~(nilp (cast (A1 \times A2) (A1 \times A2)))).
        { by rewrite /cast /=. }
        rewrite -(andbT true) [T in T && true]canCast -(andbT true) andbA.
          by apply step__Prod.
      - move => A1 IH1 A2 IH2.
        rewrite -(andbT true).
        apply: step__Inter.
        + apply: (fun incl => subty__weaken _ [:: A1] [:: A1; A2] incl IH1).
            by rewrite /= eq_refl.
        + apply: (fun incl => subty__weaken _ [:: A2] [:: A1; A2] incl IH2).
            by apply: subseq_cons.
    Qed.

    Lemma split_tgts_for_srcs_gte: forall A Delta1 Delta2 Delta1' Delta2',
        [ tgt_for_srcs_gte A in Delta1] ~~> [ check_tgt Delta1'] ->
        [ tgt_for_srcs_gte A in Delta2] ~~> [ check_tgt Delta2'] ->
        [ tgt_for_srcs_gte A in Delta1 ++ Delta2] ~~> [ check_tgt Delta1' ++ Delta2'].
    Proof.
      move => A.
      elim.
      - by move => Delta2 Delta1' Delta2' /emptyDoneTgt ->.
      - move => A1 Delta1 IH Delta2 Delta1' Delta2'.
        move p__eq: [ tgt_for_srcs_gte A in A1 :: Delta1] => p.
        move r__eq: [ check_tgt Delta1'] => r prf.
        move: p__eq r__eq.
        case: p r / prf => //.
        move => A__tmp A1__tmp Delta1__tmp Delta1'__tmp r.
        case r__eq: r => prf11 prf12 [] A__eq [] A1__eq Delta1__eq [] Delta1'__eq prf2.
        + rewrite Delta1'__eq -A1__eq.
          rewrite -A1__eq -A__eq in prf11.
          apply: (step__chooseTgt (r := true)) => //.
          apply: IH => //.
            by rewrite A__eq Delta1__eq.
        + rewrite Delta1'__eq.
          rewrite -A1__eq -A__eq in prf11.
          apply: (step__chooseTgt (r := false)) => //.
          apply: IH => //.
            by rewrite A__eq Delta1__eq.
    Qed.
    Arguments split_tgts_for_srcs_gte [A Delta1 Delta2 Delta1' Delta2'].

    Lemma cast_eq__Arr: forall A B1 B2 C1 C2,
        isOmega B2 = isOmega C2 ->
        cast (B1 -> B2) A = cast (C1 -> C2) A.
    Proof.
      elim.
      - move => B1 B2 C1 C2.
        rewrite /cast /=.
          by case: (isOmega B2) => <-.
      - move => a A IH B1 B2 C1 C2.
        rewrite /cast /=.
          by case: (isOmega B2) => <-.
      - move => A1 IH1 A2 IH2 B1 B2 C1 C2.
        rewrite /cast /=.
          by case: (isOmega B2) => <- //.
      - move => A1 IH1 A2 IH2 B1 B2 C1 C2.
        rewrite /cast /=.
          by case: (isOmega B2) => <- //.
      - move => A1 IH1 A2 IH2 B1 B2 C1 C2.
        rewrite /cast /=.
          by case: (isOmega B2) => <-.
    Qed.

    Lemma subty__ArrIncl:
      forall A C1 C2,
         (forall A' B' : IT,
            maxn (depth A') (depth B') < maxn (depth A) (depth (C1 -> C2)) ->
            forall B : IT,
              [ subty A' of B] ~~> Return true ->
              [ subty B of B'] ~~> Return true -> [ subty A' of B'] ~~> Return true) ->
         forall B1 B2 Delta1 Delta2,
           (isOmega C2) = false -> (isOmega B2) = false ->
           [ tgt_for_srcs_gte C1 in cast (C1 -> C2) A] ~~> [ check_tgt Delta1] ->
           [ tgt_for_srcs_gte B1 in cast (B1 -> B2) A] ~~> [ check_tgt Delta2] ->
           [subty C1 of B1] ~~> Return true ->           
           subseq Delta2 Delta1.
    Proof.
      move => A C1 C2 IH__rec B1 B2 Delta1 Delta2 notOmega__C2 notOmega__B2.
      rewrite (cast_eq__Arr A B1 B2 C1 C2 (etrans notOmega__B2 (esym notOmega__C2))).
      move: (cast_arrow_depth A C1 C2 notOmega__C2).
      move: (cast (C1 -> C2) A).
      have:
        (forall A' B' : IT,
            maxn (depth A') (depth B') < maxn (depth A) ((depth C1).+1) ->
            forall B : IT,
              [ subty A' of B] ~~> Return true ->
              [ subty B of B'] ~~> Return true -> [ subty A' of B'] ~~> Return true).
      { move => A' B' depth_prf.
        apply: IH__rec.
        move: depth_prf.
        rewrite leq_max /= leq_max ltnS ltnS leq_max.
        move => /orP [].
        - by move => ->.
        - by move => ->; rewrite orbT. }
      rewrite /=.
      move: C2 B2 notOmega__B2 notOmega__C2 IH__rec => _ _ _ _ _.
      move => IH__rec Delta.
      move: A C1 B1 IH__rec Delta1 Delta2.
      elim: Delta.
      - by move => ? ? ? ? ? ? ? /emptyDoneTgt -> /emptyDoneTgt -> _.
      - move => A' Delta IH A C1 B1 IH__rec Delta1 Delta2 depth_prf prf1 prf2.
        move: prf2 prf1.
        move p__eq: [ tgt_for_srcs_gte B1 in A' :: Delta] => p.
        move r__eq: [ check_tgt Delta2] => r prf.
        move: p__eq r__eq.
        case: p r / prf => //.
        move => B1__tmp A'__tmp Delta__tmp Delta1__tmp r prf21 prf22 [] B1__eq A'__eq Delta__eq [] Delta2__eq prf1 prf.
        move: Delta2__eq prf21.
        case: r.
        + move => Delta2__eq prf21.
          have prf__C1: [ subty C1 of A'.1] ~~> Return true.
          * rewrite -A'__eq -B1__eq in prf21.
            apply: (fun prf' => IH__rec C1 A'.1 prf' _ prf prf21).
            rewrite gtn_max leq_max leq_max ltnS leqnn orbT /=.
              by move: depth_prf => /andP [] /andP [] ->.
          * move: prf1.
            move p__eq: [ tgt_for_srcs_gte C1 in A' :: Delta] => p.
            move r__eq: [ check_tgt Delta1] => r prf1.
            move: p__eq r__eq.
            case: p r / prf1 => //.
            move => C1__tmp A''__tmp Delta'__tmp Delta2__tmp r prf'__C1 prf12 [] C1__eq A'__eq' Delta__eq'.
            rewrite -C1__eq -Delta__eq' in prf12.
            rewrite -A'__eq' -C1__eq in prf'__C1.
            move: (Semantics_functional _ _ _ prf__C1 prf'__C1) => [] <- [] ->.
            rewrite Delta2__eq -A'__eq' -A'__eq /=.
            rewrite (eq_refl A'.2).
            move: depth_prf => /andP [] _ depth_prf.
            rewrite -B1__eq -Delta__eq in prf22.
              by apply: (IH A C1 B1).
        + move: prf1.
          move p__eq: [ tgt_for_srcs_gte C1 in A' :: Delta] => p.
          move r__eq: [ check_tgt Delta1] => r prf1.
          move: p__eq r__eq.
          case: p r / prf1 => //.
          move => C1__tmp A''__tmp Delta'__tmp Delta2__tmp r prf__C1 prf12 [] C1__eq A'__eq' Delta__eq'.
          move: prf__C1.
          case: r.
          * move => _ [] Delta1__eq Delta2__eq _.
            rewrite Delta1__eq Delta2__eq.
            apply (fun prf => subseq_trans prf (subseq_cons Delta2__tmp A''__tmp.2)).
            move: depth_prf => /andP [] _ depth_prf.
            rewrite -B1__eq -Delta__eq in prf22.
            rewrite -C1__eq -Delta__eq' in prf12.
              by apply: (IH A C1 B1).
          * move => _ [] Delta1__eq Delta2__eq _.
            rewrite Delta1__eq Delta2__eq.
            rewrite -B1__eq -Delta__eq in prf22.
            rewrite -C1__eq -Delta__eq' in prf12.
            move: depth_prf => /andP [] _ depth_prf.
              by apply: (IH A C1 B1).
    Qed.

    Lemma subty__ArrTrans:
      forall A C1 C2,
        (forall A' B' : IT,
            maxn (depth A') (depth B') < maxn (depth A) (depth (C1 -> C2)) ->
            forall B : IT,
              [ subty A' of B] ~~> Return true ->
              [ subty B of B'] ~~> Return true -> [ subty A' of B'] ~~> Return true) ->
        forall B Delta1 Delta2,
          [ subty A of B] ~~> Return true ->
          [ tgt_for_srcs_gte C1 in cast (C1 -> C2) A] ~~> [ check_tgt Delta1] ->
          [ tgt_for_srcs_gte C1 in cast (C1 -> C2) B] ~~> [ check_tgt Delta2] ->
          [ subty \bigcap_(A__i <- Delta1) A__i of \bigcap_(A__i <- Delta2) A__i] ~~> Return true.
    Proof.
      move => A C1 C2 IH__rec B Delta1 Delta2.
      move p__eq: [ subty A of B] => p.
      move r__eq: (Return true) => r prf.
      move: C1 C2 A IH__rec B p__eq r__eq Delta1 Delta2.
      elim: p r / prf => //.
      - move => A C1 C2 A__tmp _ B [] -> -> _ Delta1 Delta2 ? prf1.
        move: (Omega__tgts _ _ _ _ prf1 isT).
        rewrite bigcap_omega.
          by apply subty__Omega.
      - move => A b B r prf IH C1 C2 A__tmp IH__rec B__tmp [] -> -> [] r__true Delta1 Delta2 prf1.
        rewrite /cast /=.
        case isOmega__C2: (isOmega C2).
        + move => /(omegaDoneTgt _ _ _) -> /=.
          rewrite -r__true.
            by apply: step__Omega.
        + move => /emptyDoneTgt -> /=.
          rewrite -r__true.
            by apply: step__Omega.
      - move => A B1 B2 Delta r prf1 _ prf2 IH C1 C2 A__tmp IH__rec B__tmp [] A__eq B__eq [] r__true Delta1 Delta2.
        rewrite B__eq A__eq.
        case isOmega__C2: (isOmega C2).
        + rewrite /cast /= isOmega__C2 /=.
          move => _ /(omegaDoneTgt _ _ _) -> /=.
          rewrite -r__true.
            by apply: step__Omega.
        + move => prf11.
          rewrite /cast /= isOmega__C2.
          move p__eq: [ tgt_for_srcs_gte C1 in [:: (B1, B2)]] => p.
          move r1__eq: [ check_tgt Delta2] => r1 prf.
          move: p__eq r1__eq.
          case: p r1 / prf => //.
          move => C1__tmp B__tmp2 Delta__tmp Delta'__tmp r2 prf21 prf22 [] C1__eq B12__eq Delta__eq [] Delta2__eq.
          rewrite -Delta__eq in prf22.
          move: prf22 => /emptyDoneTgt Delta'__eq.
          rewrite Delta'__eq in Delta2__eq.
          move: Delta2__eq prf21.
          case: r2;
            last by move => -> _; rewrite -r__true; apply step__Omega.
          move => ->.
          rewrite -B12__eq /= -C1__eq.
          case isOmega__B2: (isOmega B2);
            first by move => /= _; apply subty__Omega.
          rewrite isOmega__B2 /= in r__true.
          rewrite -r__true /=.
          move => prf21.
          rewrite -r__true in prf2.
          suff: subseq Delta Delta1
            by move => incl; apply: (subty__weaken _ _ _ incl).
          rewrite A__eq in IH__rec.
            by apply: (subty__ArrIncl _ _ _ IH__rec _ _ _ _ isOmega__C2 isOmega__B2 prf11 prf1 prf21).
      - move => A B1 B2 r1 r2 prf1 IH1 prf2 IH2 C1 C2 A__tmp IH__rec B__tmp [] -> -> [] r__true Delta1 Delta2 prf1'.
        rewrite /cast /=.
        case isOmega__C2: (isOmega C2).
        + move => /(omegaDoneTgt _ _ _) -> /=.
          rewrite -r__true.
            by apply: step__Omega.
        + move => /emptyDoneTgt -> /=.
          rewrite -r__true.
            by apply: step__Omega.
      - move => A B1 B2 r1 r2 prf1 IH1 prf2 IH2 C1 C2
                 A__tmp IH__rec B__tmp [] A__eq B__eq [] /eqP /andP [] r1__true r2__true Delta1 Delta2 prf1'.
        rewrite A__eq in prf1'.
        rewrite B__eq.
        case isOmega__C2: (isOmega C2).
        + rewrite /cast /= isOmega__C2.
          move => /(omegaDoneTgt _ _ _) -> /=.
          rewrite r1__true r2__true.
            by apply: step__Omega.
        + rewrite (split_cast B1 [:: B2] (C1 -> C2) (negbT isOmega__C2)).
          move: (subtype_machine [ tgt_for_srcs_gte C1 in cast (C1 -> C2) B1]) => [] r11 prf11.
          move: (inv_tgt_for_srcs_gte_check_tgt prf11) => r11__eq.
          rewrite r11__eq in prf11.
          rewrite A__eq in IH__rec.
          move: (IH1 _ _ _ IH__rec _ erefl (esym (f_equal (@Return Constructor) r1__true)) Delta1 _ prf1' prf11) => prf21.
          move: (subtype_machine [ tgt_for_srcs_gte C1 in cast (C1 -> C2) B2]) => [] r12 prf12.
          move: (inv_tgt_for_srcs_gte_check_tgt prf12) => r12__eq.
          rewrite r12__eq in prf12.
          move: (IH2 _ _ _ IH__rec _ erefl (esym (f_equal (@Return Constructor) r2__true)) Delta1 _ prf1' prf12) => prf22.
          move: (split_tgts_for_srcs_gte prf11 prf12) => combined1 combined2.
          move: (Semantics_functional _ _ _ combined1 combined2) => [] <-.
            by apply: subty__cat.
    Qed.

    Lemma depth_gt0: forall (A: @IT Constructor), (0 < depth A)%N.
    Proof.
      elim => //.
      move => A IH1 B IH2 /=.
        by rewrite leq_max IH1.
    Qed.

    Lemma subty__left: forall A B1 B2,
        [ subty A of B1 \cap B2] ~~> Return true ->
        [ subty A of B1] ~~> Return true.
    Proof.
      move => A B1 B2.
      move p__eq: [ subty A of B1 \cap B2] => p.
      move r__eq: (Return true) => r prf.
      move: p__eq r__eq.
      case: p r / prf => //.
      move => A' B1' B2' r1 r2 prf1 _ [] -> [] -> _ [] r__eq.
      rewrite -r__eq.
      move: r__eq prf1.
        by case: r1 => //.
    Qed.
    Arguments subty__left [A B1 B2].

    Lemma subty__right: forall A B1 B2,
        [ subty A of B1 \cap B2] ~~> Return true ->
        [ subty A of B2] ~~> Return true.
    Proof.
      move => A B1 B2.
      move p__eq: [ subty A of B1 \cap B2] => p.
      move r__eq: (Return true) => r prf.
      move: p__eq r__eq.
      case: p r / prf => //.
      move => A' B1' B2' r1 r2 _ prf2 [] -> [] _ -> [] r__eq.
      rewrite -r__eq.
      move: r__eq prf2.
        by case: r2 => //; rewrite andbF.
    Qed.
    Arguments subty__right [A B1 B2].

    Lemma cast_eq__Prod: forall A C1 C2 B1 B2, cast (C1 \times C2) A = cast (B1 \times B2) A.
    Proof. by case. Qed.

    Lemma subty__ProdTrans: forall A B C1 C2,
    [ subty A of B] ~~> Return true ->
    [ subty \bigcap_(A__i <- cast (C1 \times C2) A) A__i.1 of \bigcap_(A__i <- cast (C1 \times C2) B) A__i.1] ~~> Return true /\
    [ subty \bigcap_(A__i <- cast (C1 \times C2) A) A__i.2 of \bigcap_(A__i <- cast (C1 \times C2) B) A__i.2] ~~> Return true.
    Proof.
      move => A B C1 C2.
      move p__eq: [ subty A of B] => p.
      move r__eq: (Return true) => r prf.
      move: A B p__eq r__eq C1 C2.
      elim: p r / prf => //.
      - move => ? ? ? [] -> -> /= *.
          by split; apply subty__Omega.
      - move => A b B r prf1 IH A__tmp B__tmp [] A__eq B__eq.
        rewrite A__eq B__eq => [] [] /eqP /andP [] notOmega__A r__true C1 C2 /=.
        rewrite r__true notOmega__A.
          by split; apply subty__Omega.
      - move => A B1 B2 Delta r prf1 _ prf2 IH2 A__tmp B__tmp [] -> -> [] r__true C1 C2.
        rewrite {2}/cast /= -r__true.
          by split; apply: step__Omega.
      - move => A B1 B2 r1 r2 prf1 IH1 prf2 IH2 A__tmp B__tmp [] -> -> r__true C1 C2.
        move: r__true => [] /eqP /andP [] [] /andP [] notOmega__A r1__true r2__true.
        rewrite notOmega__A /=.
        split.
        + by rewrite (cast_eq__Prod A C1 C2 B1 B2) r2__true andbT.
        + by rewrite (cast_eq__Prod A C1 C2 B1 B2) r1__true.
      - move => A B1 B2 r1 r2 prf1 IH1 prf2 IH2 A__tmp B__tmp [] -> -> r__true C1 C2.
        rewrite {2 4}/cast /=.
        move: r__true => [] /eqP /andP [] r1__true r2__true.
        move: (IH1 _ _ erefl (esym (f_equal (@Return Constructor) r1__true)) C1 C2) => [] prf11 prf12.
        rewrite [X in [ subty _ of X]](eqP (bigcap_map_eq fst)) in prf11.
        rewrite [X in [ subty _ of X]](eqP (bigcap_map_eq snd)) in prf12.
        move: (IH2 _ _ erefl (esym (f_equal (@Return Constructor) r2__true)) C1 C2) => [] prf21 prf22.
        rewrite [X in [ subty _ of X]](eqP (bigcap_map_eq fst)) in prf21.
        rewrite [X in [ subty _ of X]](eqP (bigcap_map_eq snd)) in prf22.
        split.
        + match goal with
          |[ |- [subty _ of \bigcap_(A__i <- ?x) A__i.1] ~~> _] =>
           have: x = slow_cast (C1 \times C2) (B1 \cap B2) by rewrite -slow_cast_cast /cast /=
          end.
          move => ->.
          repeat rewrite slow_cast_cast in prf11, prf21.
          move: (subty__cat (\bigcap_(A__i <- slow_cast (C1 \times C2) A) A__i.1)
                          (map fst (slow_cast (C1 \times C2) B1))
                          (map fst (slow_cast (C1 \times C2) B2))
                          r1 r2 prf11 prf21).
          rewrite slow_cast_cast.
            by rewrite {2 3}/slow_cast /= -map_cat -(eqP (bigcap_map_eq fst)).
        + match goal with
          |[ |- [subty _ of \bigcap_(A__i <- ?x) A__i.2] ~~> _] =>
           have: x = slow_cast (C1 \times C2) (B1 \cap B2) by rewrite -slow_cast_cast /cast /=
          end.
          move => ->.
          repeat rewrite slow_cast_cast in prf12, prf22.
          move: (subty__cat (\bigcap_(A__i <- slow_cast (C1 \times C2) A) A__i.2)
                          (map snd (slow_cast (C1 \times C2) B1))
                          (map snd (slow_cast (C1 \times C2) B2))
                          r1 r2 prf12 prf22).
          rewrite slow_cast_cast.
            by rewrite {2 3}/slow_cast /= -map_cat -(eqP (bigcap_map_eq snd)).
    Qed.

    Lemma can_cast_trans__Ctor:
      forall A B C c, ~~ nilp (cast (Ctor c C) B) -> [ subty A of B] ~~> Return true -> ~~ nilp (cast (Ctor c C) A).
    Proof.
      move => A B c C canCast prf.
      move: prf c C canCast.
      move p__eq: [ subty A of B] => p.
      move r__eq: (Return true) => r prf.
      move: A B p__eq r__eq.
      elim: p r / prf => //.
      - move => A A__tmp B [] A__eq -> _ C.
          by rewrite /cast /=.
      - move => A__tmp b B' r _ _ A B [] -> ->.
        case: r; last by rewrite andbF.
        rewrite andbT.
        move => [] canCast__A C c.
        rewrite {1}/cast /=.
        case leq__bc: [ ctor b <= c] => //.
        move: (castsubseq__Ctor A__tmp b c B' C leq__bc).
        case: (cast (Ctor c C) A__tmp) => //.
        move: canCast__A => /eqP /nilP.
          by case: (cast (Ctor b B') A__tmp).
      - move => ? ? ? ? ? ? _ _ _ ? ? [] -> ->.
          by rewrite /cast /=.
      - move => A__tmp B1 B2 r1 r2 prf1 IH1 prf2 IH2 A B [] -> -> r__true c C.
          by rewrite /cast /=.
      - move => A__tmp B1 B2 r1 r2 prf1 IH1 prf2 IH2 A B [] -> -> [] /eqP /andP [] r1__true r2__true c C.
        rewrite cast_inter => //.
        rewrite r1__true in IH1.
        rewrite r2__true in IH2.
        move: (IH1 _ _ erefl erefl c C).
        move: (IH2 _ _ erefl erefl c C).
          by case: (cast (Ctor C c) B1).
    Qed.

    Lemma can_cast_trans__Prod:
      forall A B C1 C2, ~~ nilp (cast (C1 \times C2) B) -> [ subty A of B] ~~> Return true -> ~~ nilp (cast (C1 \times C2) A).
    Proof.
      move => A B C1 C2 canCast prf.
      move: prf C1 C2 canCast.
      move p__eq: [ subty A of B] => p.
      move r__eq: (Return true) => r prf.
      move: A B p__eq r__eq.
      elim: p r / prf => //.
      - move => A A__tmp B [] A__eq -> _ C.
          by rewrite /cast /=.
      - move => ? ? ? ? ? ? ? ? [] -> ->.
          by rewrite /cast /=.
      - move => ? ? ? ? ? ? _ _ _ ? ? [] -> ->.
          by rewrite /cast /=.
      - move => A__tmp B1 B2 r1 r2 _ _ _ _ A B [] -> -> [] /eqP /andP [] /andP [] result _ _ C1 C2.
          by rewrite (cast_eq__Prod A__tmp C1 C2 B1 B2).
      - move => A__tmp B1 B2 r1 r2 prf1 IH1 prf2 IH2 A B [] -> -> [] /eqP /andP [] r1__true r2__true C1 C2.
        rewrite cast_inter => //.
        rewrite r1__true in IH1.
        rewrite r2__true in IH2.
        move: (IH1 _ _ erefl erefl C1 C2).
        move: (IH2 _ _ erefl erefl C1 C2).
          by case: (cast (C1 \times C2) B1).
    Qed.

    Lemma subty__trans: forall A B C,
        [ subty A of B] ~~> Return true ->
        [ subty B of C] ~~> Return true ->
        [ subty A of C] ~~> Return true.
    Proof.
      move => A B C.
      move: B.
      apply: (fun IH => IT_depth_rect
                       (fun A C =>
                          forall B, [ subty A of B] ~~> Return true ->
                               [ subty B of C] ~~> Return true ->
                               [ subty A of C] ~~> Return true) IH A C).
      move: A C => _ _ A C.
      move: A.
      elim: C => //.
      - move => c C _ A IH B prf1 prf2.
        move: prf2 prf1 IH.
        move p__eq: [ subty B of Ctor c C] => p.
        move r'__eq: (Return true) => r' prf.
        move: p__eq r'__eq.
        case: p r' / prf => //.
        move => B__tmp c__tmp C__tmp r' prf1 eqprf.
        move: eqprf prf1 => [] <- [] <- <- prf2 [] /eqP /andP [] canCast__B r'__eq.
        rewrite canCast__B r'__eq.
        move => prf1 IH.
        rewrite -{1}(can_cast_trans__Ctor _ _ _ _ canCast__B prf1).
        apply: step__Ctor.
        rewrite r'__eq in prf2.
        apply: (fun depthprf prf => IH _ _ depthprf _ prf prf2);
          last by apply: subty__CtorTrans.
        move: (cast_ctor_depth A c C).
        case: (cast (Ctor c C) A).
        + move => _ //=.
            by rewrite leq_max (gtn_max (1 + depth C)) ltnSn ltnS depth_gt0 /= orbT.
        + move => A' Delta /adapt_ctor_depth.
          apply: adapt_ctor_depth_max.
      - move => C1 IH1 C2 IH2 A IH__rec B prf1 prf2.
        rewrite -(orTb (isOmega C2)).
        move: (subtype_machine [ tgt_for_srcs_gte C1 in cast (C1 -> C2) A]) => [] r p.
        move: p (inv_tgt_for_srcs_gte_check_tgt p).
        case: r => // Delta' prf _.
        rewrite -(orTb (isOmega C2)) orbC.
        apply: (@step__Arr Constructor A C1 C2 Delta' true prf).
        move: (subtype_machine [ tgt_for_srcs_gte C1 in cast (C1 -> C2) B]) => [] r p.
        move: p (inv_tgt_for_srcs_gte_check_tgt p).
        case: r => // Delta'' prf' _.
        case isOmega__C2: (isOmega C2);
         first by apply: subty__Omega.
        apply: (fun prf => IH2 _ prf (\bigcap_(A__i <- Delta'') A__i)).
        + move => A' C' depthprf.
          apply: IH__rec.
          move: prf depthprf.
          move: (cast_arrow_depth A C1 C2 isOmega__C2).
          case: Delta'.
          * move => /=.
            rewrite gtn_max gtn_max leq_max leq_max
                    (ltnNge (depth A')) (depth_gt0 A')
                    (ltnNge (depth C')) (depth_gt0 C') /=.
            move => _ _ /andP [] /ltnW depth__A' /ltnW depth__C'.
            rewrite leq_max leq_max ltnS ltnS leq_max leq_max depth__A' depth__C'.
              by repeat rewrite orbT.
          * move => A'' Delta' depth_prf prf1'.
            move: (choose_arrow_depth _ _ _ _ depth_prf prf1' isT) => depth__A depth_prf'.
            apply: (ltn_trans depth_prf').
              by rewrite gtn_max leq_max leq_max /= ltnS ltnS leq_maxr orbT leq_max depth__A.
        + move: prf1 prf prf'.
            by apply: subty__ArrTrans.
        + move: prf2.
          move p__eq: [ subty B of C1 -> C2] => p.
          move r__eq: (Return true) => r prf2.
          move: p__eq r__eq.
          case: p r / prf2 => //.
          move => B__tmp C1' C2' B__tmp' r prf__tmp prf__result [] B__eq C1__eq C2__eq [] r__eq.
          rewrite -C1__eq -C2__eq -B__eq in prf__tmp.
          move: (Semantics_functional _ _ _ prf' prf__tmp) => [] ->.
          rewrite C2__eq.
          case isOmega__C2': (isOmega C2').
          * by apply subty__Omega.
          * by rewrite orFb.
      - move => C1 IH1 C2 IH2 A IH__rec B prf1 prf2.
        move: prf2.
        move p__eq: [ subty B of C1 \times C2] => p.
        move r2__eq: (Return true) => r2 prf2.
        move: p__eq r2__eq.
        case: p r2 / prf2 => //.
        move => B__tmp C1__tmp C2__tmp r1 r2 prf21 prf22 [] B__eq [] C1__eq C2__eq []
                    /eqP /andP [] [] /andP [] canCast__B r1__true r2__true.
        rewrite -B__eq in canCast__B.
        move: (can_cast_trans__Prod _ _ _ _ canCast__B prf1).
        rewrite -B__eq canCast__B => <-.
        rewrite -B__eq -C1__eq -C2__eq r1__true in prf21.
        rewrite -B__eq -C1__eq -C2__eq r2__true in prf22.
        move: (subty__ProdTrans A B C1 C2 prf1) => [] prf11 prf12.
        rewrite -C1__eq -C2__eq r1__true r2__true.
        apply: step__Prod.
        + apply: (fun prf => IH1 _ prf _ prf11 prf21).
          move => A' B' depth_prf.
          apply: IH__rec.
          move: depth_prf.
          move: (cast_product_depth A C1 C2).
          case: (cast (C1 \times C2) A).
          * rewrite /=.
            rewrite gtn_max gtn_max leq_max leq_max /= leq_max leq_max
                    (ltnNge (depth A')) (depth_gt0 A') /=
                    (ltnNge (depth B')) (depth_gt0 B') /=
                    ltnS ltnS leq_max leq_max.
            move => _ /andP [] /ltnW -> /ltnW ->.
              by rewrite orbT orbT.
          * move => A1 Delta /adapt_depth_pair /andP [] depth__A1 depth__A2.
            rewrite gtn_max gtn_max leq_max leq_max leq_max leq_max.
            move => /andP [] depth_prf1 depth_prf2.
            apply /andP.
            split.
            ** move: depth_prf1 => /orP [] depth_prf1.
               *** by rewrite (ltn_trans depth_prf1 depth__A1).
               *** by rewrite /= ltnS leq_max (ltnW depth_prf1) orbT.
            ** move: depth_prf2 => /orP [] depth_prf2.
               *** by rewrite (ltn_trans depth_prf2 depth__A1).
               *** by rewrite /= ltnS leq_max (ltnW depth_prf2) orbT.
        + apply: (fun prf => IH2 _ prf _ prf12 prf22).
          move => A' B' depth_prf.
          apply: IH__rec.
          move: depth_prf.
          move: (cast_product_depth A C1 C2).
          case: (cast (C1 \times C2) A).
          * rewrite /=.
            rewrite gtn_max gtn_max leq_max leq_max /= leq_max leq_max
                    (ltnNge (depth A')) (depth_gt0 A') /=
                    (ltnNge (depth B')) (depth_gt0 B') /=
                    ltnS ltnS leq_max leq_max.
            move => _ /andP [] /ltnW -> /ltnW ->.
              by rewrite orbT orbT orbT orbT.
          * move => A1 Delta /adapt_depth_pair /andP [] depth__A1 depth__A2.
            rewrite gtn_max gtn_max leq_max leq_max leq_max leq_max.
            move => /andP [] depth_prf1 depth_prf2.
            apply /andP.
            split.
            ** move: depth_prf1 => /orP [] depth_prf1.
               *** by rewrite (ltn_trans depth_prf1 depth__A2).
               *** by rewrite /= ltnS leq_max (ltnW depth_prf1) orbT orbT.
            ** move: depth_prf2 => /orP [] depth_prf2.
               *** by rewrite (ltn_trans depth_prf2 depth__A2).
               *** by rewrite /= ltnS leq_max (ltnW depth_prf2) orbT orbT.
      - move => C1 IH1 C2 IH2 A IH__rec B prf1 prf2.
        rewrite -(andbT true).
        apply step__Inter.
        + apply: (fun prf => IH1 A prf B prf1 (subty__left prf2)).
          move => A' B' depthprf.
          apply: (IH__rec A' B').
          apply /ltP.
          apply: (@Nat.lt_le_trans _ (maxn (depth A) (depth C1)) _);
            first by apply: ltP.
          apply /leP.
            by rewrite leq_max geq_max geq_max leqnn /= leq_max leq_max leqnn /= andbT orbA leq_total.
        + apply: (fun prf => IH2 A prf B prf1 (subty__right prf2)).
          move => A' B' depthprf.
          apply: (IH__rec A' B').
          apply /ltP.
          apply: (@Nat.lt_le_trans _ (maxn (depth A) (depth C2)) _);
            first by apply: ltP.
          apply /leP.
            by rewrite leq_max geq_max geq_max leqnn /=
                       leq_max leq_max leqnn /=
                       andbC orbT /=
                       orbC -orbA leq_total orbT.
    Qed.

    Lemma subty__CtorDist: forall a A1 A2, [ subty (Ctor a A1 \cap Ctor a A2) of Ctor a (A1 \cap A2)] ~~> Return true.
    Proof.
      move => a A1 A2.
      rewrite -(andbT true).
      have canCast: true = ~~nilp (cast (Ctor a (A1 \cap A2)) (Ctor a A1 \cap Ctor a A2)).
      { by rewrite /cast preorder_reflexive. }
      rewrite {1}canCast.
      apply step__Ctor.
      rewrite /cast /= preorder_reflexive /=.
      apply: subty__Refl.
    Qed.

    Lemma subty__Idem: forall A, [ subty A \cap A of A] ~~> Return true.
    Proof.
      move => A.
      apply: (subty__weaken A [:: A] [:: A; A]).
      - by apply: subseq_cons.
      - by apply: subty__Refl.
    Qed.

    Lemma bcd_bigcap_cat_f: forall (T: Type) (f: T -> @IT Constructor) (Delta1 Delta2: seq T),
        [ bcd ((\bigcap_(A__i <- Delta1) (f A__i)) \cap (\bigcap_(A__i <- Delta2) (f A__i))) <=
          \bigcap_(A__i <- Delta1 ++ Delta2) (f A__i)].
    Proof.
      move => T f.
      elim => //.
      move => A Delta1.
      rewrite bigcap_cons.
      case: Delta1.
      - rewrite [\bigcap_(A__i <- [::]) A__i]/=.
        move => IH Delta2.
        rewrite bigcap_cons.
          by case: Delta2.
      - move => A2 Delta1 IH Delta2.
        rewrite [\bigcap_(A__i <- ([:: A, _ & _ ] ++ _)) (f A__i)]bigcap_cons -/cat.
        apply: BCD__Glb.
        + by apply: (BCD__Trans (f A \cap \bigcap_(A__i <- (A2 :: Delta1)) (f A__i))).
        + apply: (BCD__Trans ((\bigcap_(A__i <- (A2 :: Delta1)) (f A__i)) \cap \bigcap_(A__i <- Delta2) (f A__i))).
          * apply: BCD__Glb => //.
              by apply: (BCD__Trans (f A \cap \bigcap_(A__i <- (A2 :: Delta1)) (f A__i))).
          * by apply: IH.
    Qed.



    Lemma bcd_bigcap_cat: forall (Delta1 Delta2: seq (@IT Constructor)),
        [ bcd ((\bigcap_(A__i <- Delta1) A__i) \cap (\bigcap_(A__i <- Delta2) A__i)) <=
          \bigcap_(A__i <- Delta1 ++ Delta2) A__i].
    Proof. by apply (bcd_bigcap_cat_f _ id). Qed.

    Lemma bcd_cat_bigcap_f: forall (T: Type) (f: T -> @IT Constructor) (Delta1 Delta2: seq T),
        [ bcd (\bigcap_(A__i <- Delta1 ++ Delta2) (f A__i)) <=
          ((\bigcap_(A__i <- Delta1) (f A__i)) \cap (\bigcap_(A__i <- Delta2) (f A__i))) ].
    Proof.
      move => T f.
      elim.
      - by move => Delta2; rewrite /=; apply BCD__Glb.
      - move => A Delta1.
        case: Delta1.
        + move => IH Delta2.
          case: Delta2 => //=.
            by apply: BCD__Glb.
        + move => A1 Delta1 IH Delta2.
          rewrite [\bigcap_(A__i <- ([:: A, _ & _] ++ _)) (f A__i)]bigcap_cons -/cat.
          rewrite [\bigcap_(A__i <- ([:: A, _ & _])) (f A__i)]bigcap_cons -/cat.
          apply (BCD__Trans (f A \cap \bigcap_(A__i <- (A1 :: Delta1)) (f A__i) \cap \bigcap_(A__i <- Delta2) (f A__i))).
          * apply: BCD__Glb => //.
            apply (BCD__Trans (\bigcap_(A__i <- (A1 :: Delta1 ++ Delta2)) (f A__i))) => //.
              by apply IH.
          * apply: BCD__Glb.
            ** apply: BCD__Glb => //.
                 by apply: (BCD__Trans (\bigcap_(A__i <- (A1 :: Delta1)) (f A__i) \cap \bigcap_(A__i <- Delta2) (f A__i))).
            ** by apply: (BCD__Trans (\bigcap_(A__i <- (A1 :: Delta1)) (f A__i) \cap \bigcap_(A__i <- Delta2) (f A__i))).
    Qed.

    Lemma bcd_cat_bigcap: forall (Delta1 Delta2: seq (@IT Constructor)),
        [ bcd (\bigcap_(A__i <- Delta1 ++ Delta2) A__i) <=
          ((\bigcap_(A__i <- Delta1) A__i) \cap (\bigcap_(A__i <- Delta2) A__i)) ].
    Proof. by apply: (bcd_cat_bigcap_f _ id). Qed.
      
    Lemma bcd_cast__ctor: forall A b B,
        ~~nilp (cast (Ctor b B) A) ->
        [ bcd A <= Ctor b (\bigcap_(A__i <- cast (Ctor b B) A) A__i)].
    Proof.
      elim => /=.
      - by move => ? ?; rewrite /cast /=.
      - move => a A IH b B.
        rewrite /cast /=.
        case prf: [ ctor a <= b] => //.
        move => _; by apply: BCD__CAx.
      - by move => ? _ ? _; rewrite /cast /=.
      - by move => ? _ ? _; rewrite /cast /=.
      - move => A1 IH1 A2 IH2 b B /nilP canCast.
        apply: (BCD__Trans ((Ctor b (\bigcap_(A__i <- cast (Ctor b B) A1) A__i))
                            \cap (Ctor b (\bigcap_(A__i <- cast (Ctor b B) A2) A__i)))).
        + apply BCD__Glb.
          * move: canCast.
            case cast__eq: (cast (Ctor b B) A1).
            ** move: cast__eq.
               repeat rewrite slow_cast_cast.
               rewrite /slow_cast /=.
               move => -> /= canCast__A2.
               apply: (BCD__Trans A2) => //.
               apply: (BCD__Trans (Ctor b (\bigcap_(A__i <- cast (Ctor b B) A2) A__i))).
               *** apply: IH2.
                   rewrite slow_cast_cast.
                   rewrite /slow_cast /=.
                     by move: canCast__A2 => /nilP.
               *** apply: BCD__CAx => //.
                   apply: preorder_reflexive.
            ** rewrite -cast__eq.
               move => _.
               apply: (BCD__Trans A1) => //.
               apply: IH1.
                 by rewrite cast__eq.
          * move: canCast.
            case cast__eq: (cast (Ctor b B) A2).
            ** move: cast__eq.
               repeat rewrite slow_cast_cast.
               rewrite /slow_cast /=.
               move => -> /= canCast__A1.
               rewrite cats0 in canCast__A1.
               apply: (BCD__Trans A1) => //.
               apply: (BCD__Trans (Ctor b (\bigcap_(A__i <- cast (Ctor b B) A1) A__i))).
               *** apply: IH1.
                   rewrite slow_cast_cast /slow_cast /=.
                     by move: canCast__A1 => /nilP.
               *** apply: BCD__CAx => //.
                   apply: preorder_reflexive.
            ** rewrite -cast__eq.
               move => _.
               apply: (BCD__Trans A2) => //.
               apply: IH2.
                 by rewrite cast__eq.
        + apply: (BCD__Trans
                    (Ctor b ((\bigcap_(A__i <- cast (Ctor b B) A1) A__i)
                               \cap (\bigcap_(A__i <- cast (Ctor b B) A2) A__i)))) => //.
          rewrite slow_cast_cast /slow_cast /=.
          apply: BCD__CAx.
          * by apply: preorder_reflexive.
          * repeat rewrite slow_cast_cast.
              by apply bcd_bigcap_cat.
    Qed.

    Lemma bcd__omega: forall A B, isOmega B -> [ bcd A <= B].
    Proof.
      move => A B.
      move: A.
      elim: B => //.
      - move => B1 _ B2 IH A /= isOmega__B2.
        apply: (BCD__Trans Omega) => //.
        apply: (BCD__Trans (Omega -> Omega)) => //.
        apply: (BCD__Sub) => //.
          by apply: IH.
      - move => B1 IH1 B2 IH2 A /andP [] isOmega__A1 isOmega__A2.
        apply BCD__Glb.
        + by apply: IH1.
        + by apply: IH2.
    Qed.

    Lemma bcd_cast__Arr: forall A B1 B2,
        [ bcd A <= \bigcap_(A__i <- cast (B1 -> B2) A) (A__i.1 -> A__i.2)].
    Proof.
      move => A B1 B2.
      case isOmega__B2: (isOmega B2);
        first by rewrite /cast /= isOmega__B2; apply bcd__omega.
      rewrite slow_cast_cast /slow_cast /= isOmega__B2 /=.
      elim: A; auto using bcd__omega.
      move => A1 IH1 A2 IH2.
      apply: BCD__Trans;
        last by apply: (bcd_bigcap_cat_f _ (fun A__i => A__i.1 -> A__i.2)).
      apply: BCD__Glb.
      + by apply: (BCD__Trans A1).
      + by apply: (BCD__Trans A2).
    Qed.

    Lemma bcd__Arr: forall A1 B1 A2 B2,
        [ bcd ((A1 -> B1) \cap (A2 -> B2)) <= (A1 \cap A2) -> (B1 \cap B2)].
    Proof.
      move => A1 B1 A2 B2.
      apply: (BCD__Trans ((A1 \cap A2 -> B1) \cap (A1 \cap A2 -> B2))).
      - apply: BCD__Glb.
        + apply: BCD__Trans; first by apply: BCD__Lub1.
            by apply: BCD__Sub.
        + apply: BCD__Trans; first by apply: BCD__Lub2.
            by apply: BCD__Sub.
      - by apply: BCD__Dist.
    Qed.

    Lemma bcd_cast__Prod: forall A B1 B2,
        [ bcd A <= \bigcap_(A__i <- cast (B1 \times B2) A) (A__i.1 \times A__i.2)].
    Proof.
      move => A B1 B2.
      elim: A => //=.
      move => A1 IH1 A2 IH2.
      rewrite slow_cast_cast /slow_cast /=.
      rewrite slow_cast_cast in IH1.
      rewrite slow_cast_cast in IH2.
      apply: BCD__Trans; last by apply: bcd_bigcap_cat_f.
      apply: BCD__Glb.
      - by apply: BCD__Trans; first by apply BCD__Lub1.
      - by apply: BCD__Trans; first by apply BCD__Lub2.
    Qed.

    Lemma bcd__ProdDist: forall (Delta: seq (@IT Constructor * @IT Constructor)),
        ~~nilp Delta ->
        [ bcd
            (\bigcap_(A__i <- Delta) (A__i.1 \times A__i.2))
          <= (\bigcap_(A__i <- Delta) A__i.1) \times (\bigcap_(A__i <- Delta) A__i.2)].
    Proof.
      elim => // A1 Delta.
      case: Delta => //.
      move => A2 Delta /(fun f => f isT) IH _.
      rewrite bigcap_cons
              [\bigcap_(A__i <- [:: A1, _ & _ ]) _]bigcap_cons
              [\bigcap_(A__i <- [:: A1, _ & _ ]) _]bigcap_cons.
      apply: BCD__Trans; last by apply BCD__ProdDist.
      apply: BCD__Glb; first by apply: BCD__Lub1.
      apply: BCD__Trans; first by apply: BCD__Lub2.
      done.
    Qed.  

    Lemma subty__sound: forall A B, [ subty A of B] ~~> Return true -> [ bcd A <= B].
    Proof.
      apply: IT_depth_rect.
      move => A B IH.
      move p__eq: [ subty A of B] => p.
      move r__eq: (Return true) => r prf.
      move: A B p__eq r__eq IH.
      elim: p r / prf => //.
      - by move => ? ? ? [] _ -> _ _; apply: BCD__omega.
      - move => A b B r prf IH A__tmp B__tmp [] A__eq B__eq [] /eqP /andP [] canCast__A r__true IH__rec.
        rewrite A__eq B__eq.
        apply: (BCD__Trans (Ctor b (\bigcap_(A__i <- cast (Ctor b B) A) A__i))).
        + by apply: bcd_cast__ctor.
        + apply: BCD__CAx; first by rewrite preorder_reflexive.
          apply (IH _ _ erefl);
            first by rewrite r__true.
          move => A' B' depth_prf.
          apply: IH__rec.
          rewrite A__eq B__eq.
          apply: (ltn_trans depth_prf).
          move: (cast_ctor_depth A b B).
          move: canCast__A.
          case: (cast (Ctor b B) A) => // A1 Delta _ /adapt_ctor_depth.
          apply: adapt_ctor_depth_max.
      - move => A B1 B2 Delta r prf1 _ prf2 IH A__tmp B [] A__eq B__eq [] r__true IH__rec.
        rewrite A__eq B__eq.
        move: r__true.
        case isOmega__B2: (isOmega B2);
          first by move => _; apply: (bcd__omega A (B1 -> B2) isOmega__B2).
        move => /= r__true.
        rewrite A__eq B__eq in IH__rec.
        apply: (BCD__Trans (\bigcap_(A__i <- filter (fun A => sval (subtype_machine [subty B1 of A]) == Return true)
                                      (map fst (cast (B1 -> B2) A))) A__i -> \bigcap_(A__i <- Delta) A__i)).
        + apply: (BCD__Trans (\bigcap_(A__i <- cast (B1 -> B2) A) (A__i.1 -> A__i.2)));
            first by apply: bcd_cast__Arr.
          have IH__rec': (forall A' B' : IT,
                           maxn (depth A') (depth B') < maxn (depth A) (depth B1) ->
                           [ subty A' of B'] ~~> Return true -> [ bcd (A') <= B']).
          { move => A' B'.
            rewrite gtn_max leq_max leq_max => /andP [] depth__A' depth__B'.
            apply: IH__rec.
            rewrite gtn_max leq_max leq_max /= ltnS ltnS leq_max leq_max orbA orbA.
            case: (orP depth__A');
              last move => /ltnW; move => ->; (case (orP depth__B'); last move => /ltnW); move => ->; by repeat rewrite orbT. }
          move: (cast_arrow_depth A B1 B2 isOmega__B2).
          move: prf1 IH__rec'.
          move: (cast (B1 -> B2) A) => /= Delta'.
          clear...
          move p__eq: [ tgt_for_srcs_gte B1 in Delta'] => p.
          move r__eq: [ check_tgt Delta] => r prf.
          move: A B1 Delta' Delta p__eq r__eq.
          elim: p r / prf => //;
            last by move => B A B1 Delta' Delta [] B__eq Delta__eq [] -> *; apply bcd__omega.
          move => B1 A1 Delta Delta' r prf1 _ prf2 IH A B1__tmp Delta__tmp Delta'__tmp
                    [] B1__eq Delta__eq [] Delta'__eq.
          rewrite Delta'__eq Delta__eq B1__eq [filter _ _]/=.
          move => IH__rec /andP [] /andP [] depth__A11 depth__A12 depth_prf.
          rewrite (Semantics_functional _ _ _ (proj2_sig (subtype_machine [ subty B1 of A1.1])) prf1).
          move: (IH A B1 Delta Delta' erefl erefl IH__rec depth_prf).
          have: (Delta = [::] -> Delta' = [::])%type.
          { move => Delta__eq'.
            move: Delta__eq' prf2 => ->.
              by apply: emptyDoneTgt. }
          clear prf1 Delta'__eq prf2 IH Delta__eq depth_prf.
          case: r.
          * rewrite (eq_refl (Return true)).
            case: Delta;
              first by rewrite /= => /(fun x => x erefl) -> /=.
            move => A2 Delta _. 
            case: Delta' => //.
            ** move => _.
               apply: BCD__Trans; first by apply: BCD__Lub1.
               apply: BCD__Sub => //.
               case: (filter (fun A => sval (subtype_machine [ subty B1 of A]) == Return true)
                             (map fst [:: A2 & Delta])) => //.
                 by move => *; apply: BCD__Lub1.
            ** move => A2' Delta'.
               case: (filter (fun A => sval (subtype_machine [ subty B1 of A]) == Return true)
                             (map fst [:: A2 & Delta])).
               *** rewrite [\bigcap_(A__i <- [::]) A__i]/=.
                   move => prf.
                   rewrite bigcap_cons
                           [\bigcap_(A__i <- [:: A1.1]) A__i]/=
                           [\bigcap_(A__i <- [:: A1.2 , A2' & Delta']) A__i]bigcap_cons.
                   apply: BCD__Trans; last by apply: BCD__Dist.
                   apply: BCD__Glb => //.
                   apply: BCD__Trans; first by apply: BCD__Lub2.
                   apply: BCD__Trans; first by exact prf.
                     by apply: BCD__Sub.
               *** move => A1' Delta1 prf.
                   rewrite bigcap_cons.
                   rewrite [\bigcap_(A__i <- [:: A1.1 & _ ]) A__i]bigcap_cons.
                   rewrite [\bigcap_(A__i <- [:: A1.2 & _ ]) A__i]bigcap_cons.
                   apply: BCD__Trans; last by apply: bcd__Arr.
                   apply: BCD__Glb => //.
                   apply: BCD__Trans; first by apply: BCD__Lub2.
                   done.
          * rewrite /=.
            case: Delta;
              first by rewrite /= => /(fun x => x erefl) -> _; by apply: bcd__omega.
            move => A2 Delta prf.
            apply: BCD__Trans; by apply: BCD__Lub2.
        + apply: BCD__Sub.
          * move: IH__rec (cast_arrow_depth A B1 B2 isOmega__B2).
            clear...
            elim: (cast (B1 -> B2) A);
              first by move => *; apply BCD__omega.
            move => A1 Delta IH IH__rec /andP [] /andP [] depth__A11 depth__A12 depth_prf.
            have: ([ subty B1 of A1.1] ~~> Return true -> [ bcd B1 <= A1.1])%type.
            { apply: IH__rec.
                by rewrite gtn_max leq_max leq_max depth__A11 /= andbT ltnS leq_max leqnn orbT. }
            move: (subtype_machine [ subty B1 of A1.1]) => [] r.
            case: r => r; last by move => /inv_subtyp_return devil; discriminate devil.
            move => prf /=.
            rewrite (Semantics_functional _ _ _ (proj2_sig (subtype_machine [ subty B1 of A1.1])) prf).
            move: prf.
            move: (IH IH__rec depth_prf).
            case: r => //.
            move => res_prf hd_prf hd_prf_bcd /=.
            move: (hd_prf_bcd hd_prf) res_prf.
            case: (filter (fun A => sval (subtype_machine [subty B1 of A]) == Return true)
                             (map fst Delta)) => //=.
            move => *. by apply: BCD__Glb.
          * rewrite r__true in IH, IH__rec.
            apply: IH => //.
            move => A' B' depth_prf.
            apply: IH__rec.
            apply (ltn_trans depth_prf).
            have: (~~nilp Delta).
            { move: isOmega__B2 prf2.
              rewrite -r__true.
              clear...
              case: Delta => //=.
              move => isOmega__B2 /Omega__subty /(fun f => f isT).
                by rewrite isOmega__B2. }
            move => /(choose_arrow_depth _ _ _ _ (cast_arrow_depth A B1 B2 isOmega__B2) prf1) depth__A.
              by rewrite gtn_max leq_max leq_max depth__A /= ltnS leq_max leqnn orbT orbT.
      - move => A B1 B2 r1 r2 prf1 IH1 prf2 IH2 A__tmp B__tmp [] A__eq B__eq
                 [] /eqP /andP [] /andP [] canCast__A r1__true r2__true IH__rec.
        rewrite A__eq B__eq.
        rewrite A__eq B__eq in IH__rec.
        apply: BCD__Trans; first by apply: bcd_cast__Prod.
        apply: BCD__Trans; first by apply: (bcd__ProdDist _ canCast__A).
        apply: BCD__ProdSub.
        + rewrite r1__true in IH1.
          apply (IH1 _ _ erefl erefl).
          move => A' B' depth__prf.
          apply: IH__rec.
          apply: (ltn_trans depth__prf).
          move: (cast_product_depth A B1 B2).
          move: canCast__A.
          case: (cast (B1 \times B2) A) => //.
          move => ? ? _.
          move => /adapt_depth_pair prf.
            by apply: (proj1 (adapt_product_depth_max _ _ _ _ _ prf)).
        + rewrite r2__true in IH2.
          apply (IH2 _ _ erefl erefl).
          move => A' B' depth__prf.
          apply: IH__rec.
          apply: (ltn_trans depth__prf).
          move: (cast_product_depth A B1 B2).
          move: canCast__A.
          case: (cast (B1 \times B2) A) => //.
          move => ? ? _.
          move => /adapt_depth_pair prf.
            by apply: (proj2 (adapt_product_depth_max _ _ _ _ _ prf)).
      - move => A B1 B2 r1 r2 prf1 IH1 prf2 IH2 A__tmp B__tmp [] A__eq B__eq
                 [] /eqP /andP [] r1__true r2__true IH__rec.
        rewrite A__eq B__eq.
        apply: BCD__Glb.
        + rewrite r1__true in IH1.
          apply: IH1 => //.
          rewrite A__eq B__eq in IH__rec.
          move => A' B'.
          rewrite gtn_max leq_max leq_max => /andP [] depth__A' depth__B'.
          apply: IH__rec.
            by rewrite gtn_max leq_max leq_max /= leq_max leq_max orbA depth__A' orbA depth__B'.
        + rewrite r2__true in IH2.
          apply: IH2 => //.
          rewrite A__eq B__eq in IH__rec.
          move => A' B'.
          rewrite gtn_max leq_max leq_max => /andP [] depth__A' depth__B'.
          apply: IH__rec.
          rewrite gtn_max leq_max leq_max /= leq_max leq_max.
          rewrite [X in (_ < depth A) || X]orbC orbA depth__A'.
            by rewrite [X in (_ < depth A) || X]orbC orbA depth__B'.
    Qed.
        
    Lemma subty_complete: forall A B, [ bcd A <= B] -> [ subty A of B] ~~> Return true.
    Proof.
      move => A B prf.
      elim: A B / prf.
      - move => a b A B prf__ab prf IH.
        rewrite -(andbT true).
        have canCast: ~~nilp (cast (Ctor b B) (Ctor a A))
          by rewrite /cast /= prf__ab.
        rewrite -[X in X && true]canCast.
        apply: step__Ctor.
        rewrite /cast /= prf__ab.
          by exact IH.
      - by move => *; apply: step__Omega.
      - by move => *; apply: subty__CtorDist.
      - by move => *; apply: subty__Omega.
      - move => A1 A2 B1 B2 _ IH1 _ IH2.
        rewrite -(orbT (isOmega B2)).
        case isOmega__B2: (isOmega B2).
        + by apply: subty__Omega.
        + rewrite -[X in X || true]isOmega__B2.
          apply: (step__Arr (Delta := [:: A2]) (r := true)) => //.
          rewrite /cast /= isOmega__B2.
            by apply: (step__chooseTgt (A := (A1, A2)) IH1 (step__doneTgt)).
      - move => A B1 B2.
        rewrite -(orbT (isOmega (B1 \cap B2))).
        case isOmega__B1B2: (isOmega (B1 \cap B2)).
        + by apply: subty__Omega.
        + rewrite -[X in X || true]isOmega__B1B2.
          apply: (step__Arr (Delta := [:: B1; B2]) (r := true)).
          * rewrite /cast /= -/(isOmega (B1 \cap B2)) isOmega__B1B2.
            apply: (step__chooseTgt (A := (A, B1)) (Delta' := [:: B2]) (subty__Refl A)).
              by apply: (step__chooseTgt (A := (A, B2)) (subty__Refl A) (step__doneTgt)).
          * by apply: subty__Refl.
      - move => A1 A2 B1 B2 _ IH1 _ IH2.
        have canCast: (true = ~~nilp (cast (B1 \times B2) (A1 \times A2)))
          by rewrite /cast /=.
        rewrite -(andbT true) -(andbT true) [X in X && _](canCast) andbA.
          by apply step__Prod.
      - move => A1 A2 B1 B2.
        have canCast: (true = ~~nilp (cast ((A1 \cap B1) \times (A2 \cap B2)) (A1 \times A2 \cap B1 \times B2)))
          by rewrite /cast /=.
        rewrite -(andbT true) -(andbT true) [X in X && _](canCast) andbA.
          by apply: step__Prod => //=; apply: subty__Refl.
      - move => A.
        apply: subty__Refl.
      - move => A B C _ IH1 _ IH2.
          by apply: (subty__trans _ _ _ IH1 IH2).
      - move => *.
        rewrite -(andbT true).
          by apply step__Inter.
      - move => A B; apply: (subty__weaken A [:: A] [:: A; B]).
        + by rewrite /= eq_refl.
        + by apply: subty__Refl.
      - move => A B; apply: (subty__weaken B [:: B] [:: A; B]).
        + by apply: subseq_cons.
        + by apply: subty__Refl.
    Qed.

    Theorem subtype_machine_correct: forall A B, [ bcd A <= B] <-> sval (subtype_machine [ subty A of B]) = Return true.
    Proof.
      move => A B.
      split.
      - move => /subty_complete /Semantics_functional prf.
        move: (subtype_machine [ subty A of B]) => [] r rel.
          by rewrite (prf r rel).
      - move: (subtype_machine [ subty A of B]) => [] r rel /= r_eq.
        move: r_eq rel => ->.
        apply: subty__sound.
    Qed.

    Definition checkSubtypes (A B: @IT Constructor): bool :=
      if subtype_machine [ subty A of B] is exist (Return true) _ then true else false.

    Lemma subtypeMachineP: forall A B, reflect [bcd A <= B] (checkSubtypes A B).
    Proof.
      move => A B.
      rewrite /checkSubtypes.
      move: (subtype_machine_correct A B).
      case (subtype_machine [subty A of B]) => result prf.
      move: (inv_subtyp_return prf) => result__eq.
      move: prf.
      rewrite result__eq.
      move: result__eq => _.
      case result => //=.
      + case.
        * move => /subty__sound prf _.
            by apply: ReflectT.
        * move => _ disprf.
          apply: ReflectF.
          move => /disprf prf.
            by discriminate prf.
      +  move => _ _ disprf.
         apply: ReflectF.
         move => /disprf prf.
           by discriminate prf.
    Qed.
  End BCDRules.

  Section Runtime.

    Inductive Domain_n : nat -> @Instruction Constructor -> Prop :=
    | dom_n__Omega: forall A, Domain_n 1 [subty A of Omega ]
    | dom_n__Ctor: forall A b B n,
        Domain_n n [subty (\bigcap_(A__i <- cast (Ctor b B) A) A__i) of B] ->
        Domain_n (n + 1) [subty A of Ctor b B]
    | dom_n__Arr: forall A B1 B2 m n,
        Domain_n m [tgt_for_srcs_gte B1 in cast (B1 -> B2) A] ->
        (forall Delta,
            [tgt_for_srcs_gte B1 in cast (B1 -> B2) A] ~~> [check_tgt Delta] ->
            Domain_n n [subty (\bigcap_(A__i <- Delta) A__i) of B2]) ->
        Domain_n (m + n + 1) [subty A of (B1 -> B2)]
    | dom_n__chooseTgt: forall B A Delta n m,
        Domain_n m [subty B of A.1] ->
        Domain_n n [tgt_for_srcs_gte B in Delta] ->
        Domain_n (m + n + 1) [tgt_for_srcs_gte B in [:: A & Delta ]]
    | dom_n__doneTgt: forall B, Domain_n 1 [tgt_for_srcs_gte B in [::]]
    | dom_n__Prod: forall A B1 B2 m n ,
        Domain_n m [subty (\bigcap_(A__i <- cast (B1 \times B2) A) A__i.1) of B1] ->
        Domain_n n [subty (\bigcap_(A__i <- cast (B1 \times B2) A) A__i.2) of B2] ->
        Domain_n (m + n + 1) [subty A of B1 \times B2]
    | dom_n__Inter: forall A B1 B2 m n,
        Domain_n m [subty A of B1] ->
        Domain_n n [subty A of B2] ->
        Domain_n (m + n + 1) [subty A of B1 \cap B2].

    Fixpoint size (A: @IT Constructor): nat :=
      match A with
      | Omega => 1
      | Ctor _ A' => 1 + size A'
      | A1 -> A2 => 1 + size A1 + size A2
      | A1 \times A2 => 1 + size A1 + size A2
      | A1 \cap A2 => 1 + size A1 + size A2
      end.

    Lemma size_min: forall A, 0 < size A.
    Proof. by case => //=. Qed.

    Definition cost (p: Instruction): nat :=
      match p with
      | [ subty A of B] => 2 * size A * size B
      | [ tgt_for_srcs_gte B in Delta] =>
        1 + size B * sumn (map (fun x => 1 + 2 * size (x.1)) Delta)
      end.

    Lemma bigcap_size: forall (Delta1 Delta2: seq (@IT Constructor)),
        size (\bigcap_(A__i <- (Delta1 ++ Delta2)) A__i) <= 1 + size (\bigcap_(A__i <- Delta1) A__i) + size (\bigcap_(A__i <- Delta2) A__i).
    Proof.
      elim => //=.
      - move => Delta2.
        rewrite -addnA add1n add1n.
        apply: leqW.
        apply: leqW.
          by apply: leqnn.
      - move => A Delta1.
        case: Delta1.
        + move => IH Delta2 /=.
          case: Delta2 => //=.
            by rewrite -addnA addn1 add1n leqW.
        + move => A1 Delta1 IH Delta2.
          rewrite (leq_add2l 1) -/size -/Nat.add -addn1 plusE -addnAC (addnC _ 1) (addnA 1) (addnC 1).
          rewrite  -(addnA (size A)) -(addnA (size A)) (leq_add2l (size A)).
            by apply: IH.
    Qed.

    Lemma ctor_cast_size_lt: forall A b B, ~~nilp (cast (Ctor b B) A) -> size (\bigcap_(A__i <- (cast (Ctor b B) A)) A__i) < size A.
    Proof.
      elim => //=.
      - move => a A IH b B.
        rewrite /cast /=.
        case: [ ctor a <= b] => //.
      - move => A1 IH1 A2 IH2 b B.
        rewrite (cast_inter A1 A2 (Ctor b B) isT).
        move => canCast.
        apply: leq_ltn_trans; first by apply: bigcap_size.
        rewrite (ltn_add2l 1) -/Nat.add plusE.
        move: (IH1 b B) canCast.
        case: (cast (Ctor b B) A1).
        + move => _ /(IH2 b B) prf /=.
          apply: (leq_ltn_trans (n := (size A1) + (size (\bigcap_(A__i <- cast (Ctor b B) A2) A__i)))).
          * rewrite (leq_add2r (size (\bigcap_(A__i <- cast (Ctor b B) A2) A__i))).
              by apply: size_min.
          * by rewrite (ltn_add2l (size A1)).
        + move => A1' Delta1 IH1'.
          move: (IH2 b B).
          case: (cast (Ctor b B) A2).
          * move => _ _.
            apply: (leq_ltn_trans (n := size (\bigcap_(A__i <- [:: A1' & Delta1]) A__i) + size A2)).
            ** rewrite leq_add2l.
                 by apply: size_min.
            ** rewrite ltn_add2r.
                 by apply: IH1'.
          * move => A2' Delta2 IH2' _.
            apply: (leq_ltn_trans (n := size (\bigcap_(A__i <- [:: A1' & Delta1]) A__i) + size A2)).
            ** rewrite leq_add2l.
               apply: ltnW.
                 by apply: IH2'.
            ** rewrite ltn_add2r.
                 by apply: IH1'.
    Qed.

    Lemma ctor_cast_size_le: forall A b B, size (\bigcap_(A__i <- (cast (Ctor b B) A)) A__i) <= size A.
    Proof.
      move => A b B.
      move: (ctor_cast_size_lt A b B).
      case canCast: (nilp (cast (Ctor b B) A)).
      - move: canCast => /nilP -> _.
          by apply: size_min.
      - by move => /(fun x => ltnW (x isT)).
    Qed.

    Lemma prod_cast_size_le1: forall A B1 B2, size (\bigcap_(A__i <- cast (B1 \times B2) A) A__i.1) <= size A.
    Proof.
      elim; try by move => *; rewrite /cast.
      - move => A1 _ A2 _ B1 B2 /=.
        apply: leq_trans; last by apply: leq_addr.
        apply: leq_trans; last by apply: leq_addl.
          by apply: leqnn.
      - move => A1 IH1 A2 IH2 B1 B2.
        rewrite cast_inter => //.
        rewrite (eqP (bigcap_map_eq _ _ (fun x => x.1))) map_cat.
        apply: (leq_trans (bigcap_size _ _)).
        rewrite -(addnA 1) /= -(addnA 1) leq_add2l.
        do 2 rewrite -(eqP (bigcap_map_eq _ _ (fun x => x.1))).
          by apply: leq_add.
    Qed.

    Lemma prod_cast_size_le2: forall A B1 B2, size (\bigcap_(A__i <- cast (B1 \times B2) A) A__i.2) <= size A.
    Proof.
      elim; try by move => *; rewrite /cast.
      - move => A1 _ A2 _ B1 B2 /=.
        apply: leq_trans; last by apply: leq_addl.
          by apply: leqnn.
      - move => A1 IH1 A2 IH2 B1 B2.
        rewrite cast_inter => //.
        rewrite (eqP (bigcap_map_eq _ _ (fun x => x.2))) map_cat.
        apply: (leq_trans (bigcap_size _ _)).
        rewrite -(addnA 1) /= -(addnA 1) leq_add2l.
        do 2 rewrite -(eqP (bigcap_map_eq _ _ (fun x => x.2))).
          by apply: leq_add.
    Qed.

    Lemma arrow_cast_size1: forall A B1 B2,
        ~~ (isOmega B2) -> sumn (map (fun x => 1 + 2 * size (x.1)) (cast (B1 -> B2) A)) <= 2 * size A.
    Proof.
      move => A B1 B2.
      elim: A; try by rewrite /cast /=; case (isOmega B2) => //.
      + move => A1 _ A2 _ /=.
        rewrite /cast /=.
        case (isOmega B2) => //= _.
        rewrite addn0 mulnDr mulnDr -(addnA (2 * 1)).
        apply: leq_add => //.
        apply: leq_trans; last by apply leq_addr.
        apply: leq_pmul2r; apply: size_min.
      + move => A1 IH1 A2 IH2 notOmega__B2.
        rewrite (cast_inter A1 A2 (B1 -> B2) notOmega__B2).
        rewrite map_cat sumn_cat /= mulnDr mulnDr -(addnA (2 * 1)).
        apply: leq_trans; last by apply leq_addl.
        apply: leq_add.
        * by apply: IH1.
        * by apply: IH2.
    Qed.

    Fixpoint width (A: @IT Constructor): nat :=
      match A with
      | A1 \cap A2 => width A1 + width A2
      | _ => 1
      end.

    Lemma width_size: forall A, width A <= size A.
    Proof.
      elim => //=.
      move => A1 IH1 A2 IH2 /=.
      rewrite -(addnA 1).
      apply: leq_trans; last by apply: leq_addl.
        by apply: leq_add.
    Qed.

    Lemma width_size_quot: forall A, width A %/ size A <= 1.
    Proof.
      move => A.
      apply: (leq_trans (leq_div2r (size A) (width_size A))).
      rewrite -[X in X %/ _ <= _](mul1n (size A)) mulnK => //.
      apply size_min.
    Qed.

    Lemma subseq_split {aT: eqType}:
    forall {s s1 s2: seq aT},
      subseq s (s1 ++ s2) ->
      { ss: seq aT * seq aT | s = ss.1 ++ ss.2 /\ subseq ss.1 s1 /\ subseq ss.2 s2 }.
    Proof.
      move => s s1.
      move: s.
      elim: s1.
      - move => s s2 s__incl.
        exists ([::], s); by repeat split.
      - move => a s1 IH s.
        case: s.
        + move => s2 _.
          exists ([::], [::]); repeat split.
            by apply: sub0seq.
        + move => a' s' /=.
          move a'a__eq:  (a' == a) => eq.
          move: a'a__eq.
          case eq => a'a__eq s2.
          * case /(IH _ _) => ss [] s'__eq [] ss__incl1 ss__incl2.
            exists ([:: a & ss.1], ss.2); repeat split.
            { rewrite /= s'__eq.
                by move: a'a__eq => /(_ =P _) ->. }
            { by rewrite /= eq_refl. }
            { done. }
          * case /(IH (a'::s') s2) => ss [] s'__eq [] ss__incl1 ss__incl2.
            exists (ss.1, ss.2); repeat split => //=.
            move: ss__incl1 s'__eq.
            case: ss.1 => //.
            move => a'' ss1' a'ss1'__incl [] p.
            move: a'ss1'__incl.
            rewrite -p.
              by rewrite a'a__eq.
    Qed.

    
    Lemma arrow_cast_size2: forall A B1 B2 Delta,
        subseq Delta (map snd (cast (B1 -> B2) A)) ->
        size (\bigcap_(A__i <- Delta) A__i) <= size A.
    Proof.
      move => A B1 B2.
      case isOmega__B2: (isOmega B2).
      - rewrite /cast /= isOmega__B2 /=.
        case.
        + move => _ /=.
            by apply: size_min.
        + case => //.
          rewrite eq_refl => Delta /eqP -> /=.
            by apply: size_min.
      - elim: A;
          try by rewrite /cast /= isOmega__B2; repeat (move => ? /= /eqP -> //= || move => ?).
        + move => A1 _ A2 _ /=.
          rewrite /cast /= isOmega__B2 /=.
          case => //.
          move => A2'.
          case A2__eq: (A2' == A2) => //.
          move: A2__eq => /eqP -> Delta /eqP -> /=.
          apply: leq_trans; last by apply leq_addl.
          apply: leqnn.
        + move => A1 IH1 A2 IH2.
          rewrite (cast_inter A1 A2 (B1 -> B2));
            last by move: isOmega__B2 => /= ->.
          move => Delta.
          rewrite map_cat => Delta__incl.
          move: (subseq_split Delta__incl) => [] [] Delta1 Delta2 /= [] Delta__eq []Delta1__incl Delta2__incl.
          rewrite Delta__eq.
          apply: (leq_trans (bigcap_size _ _)).
          rewrite -(addnA 1) -(addnA 1).
          apply: leq_add => //.
          apply: leq_add.
          * by apply: IH1.
          * by apply: IH2.
    Qed.

    Lemma choose_tgt_subseq:
      forall (B: @IT Constructor) Delta Delta',
        ([ tgt_for_srcs_gte B in Delta] ~~> [ check_tgt Delta']) -> subseq Delta' (map snd Delta).
    Proof.
      move => B Delta Delta'.
      move p__eq: [ tgt_for_srcs_gte B in Delta] => p.
      move r__eq: [ check_tgt Delta'] => r prf.
      move: Delta Delta' p__eq r__eq.
      elim: p r / prf => //.
      - move => B_tmp A Delta1 Delta' r prf1 _ prf2 IH Delta_tmp Delta'_tmp eq1 eq2.
        move: eq1 eq2 prf1 prf2 IH => [] <- -> [] -> _ _ /(fun x => x Delta1 Delta' erefl erefl) IH.
        case: r.
        + by rewrite /= eq_refl.
        + rewrite [map _ _]/=.
          apply: subseq_trans; first by exact: IH.
            by apply: subseq_cons.
      - by move => ? ? ? [] _ -> [] ->.
    Qed.

    Lemma tgts_omega_size: forall B m, Domain_n m [ tgt_for_srcs_gte B in [:: (Omega, Omega)]] -> m = 3.
    Proof.
      move => B m.
      move p__eq: [ tgt_for_srcs_gte B in [:: (Omega, Omega)]] => p prf.
      move: p__eq.
      case: m p / prf => //.
      move => B1 A Delta m n prf1 prf2 eq.
      move: eq prf1 prf2 => [] _ <- <- /=.
      move p__eq: [ subty B1 of Omega] => p prf.
      move: p__eq.
      case: n p / prf => //.
      move => _ _.
      move p__eq: [ tgt_for_srcs_gte B1 in [::]] => p prf.
      move: p__eq.
        by case: m p / prf.
    Qed.

    Lemma Domain_Domain_n: forall p, Domain p -> exists n, Domain_n n p.
    Proof.
      move => p dom.
      elim: p / dom.
      - move => A.
        exists 1; by apply: dom_n__Omega.
      - move => A b B dom1 [] n IH.
        exists (n + 1); by apply: dom_n__Ctor.
      - move => A B1 B2 dom1 [] m IH1 dom2 IH2.
        move: (subtype_machine [ tgt_for_srcs_gte B1 in cast (B1 -> B2) A]) => [] r prf.
        move: (inv_tgt_for_srcs_gte_check_tgt prf) => r__eq.
        rewrite r__eq in prf.
        move: (IH2 _ prf) => [] n IH2'.
        exists (m + n + 1).
        apply: dom_n__Arr => //.
          by move => Delta' /(Semantics_functional _ _ _ prf) [] <-.
      - move => B A Delta dom1 [] m IH1 dom2 [] n IH2.
        exists (m + n + 1); by apply: dom_n__chooseTgt.
      - move => B.
        exists 1; by apply: dom_n__doneTgt.
      - move => A B1 B2 dom1 [] m IH1 dom2 [] n IH2.
        exists (m + n + 1); by apply: dom_n__Prod.
      - move => A B1 B2 dom1 [] m IH1 dom2 [] n IH2.
        exists (m + n + 1); by apply: dom_n__Inter.
    Qed.        

    Lemma Domain_size: forall p n, Domain_n n p -> n <= cost p.
    Proof.
      move => p.
      move: (total p) => dom.
      elim: p / dom.
      - move => A n.
        move p__eq: [ subty A of Omega] => p prf.
        move: p__eq.
        case: n p / prf => * //=.
        rewrite muln1 muln_gt0 /=.
          by apply: size_min.
      - move => A b B dom IH n.
        move p__eq: [ subty A of Ctor b B] => p prf.
        move: p__eq.
        case: n p / prf => //= A_tmp b_tmp B_tmp n prf p__eq.
        move: p__eq prf => [] <- <- <- prf.
        move: (IH n prf) => /= IH'.
        move: (ctor_cast_size_le A b B) => cast_size.
        rewrite mulnDr muln1 -(addnC 1).
        apply: leq_add.
        + rewrite muln_gt0 /=.
            by apply: size_min.
        + apply: (leq_trans IH').
          rewrite leq_mul2r.
          case: (size B == 0) => //=.
            by apply: leq_mul.
      - move => A B1 B2 dom1 IH1 dom2 IH2 n.
        move p__eq: [ subty A of B1 -> B2] => p prf.
        move: p__eq.
        case: n p / prf => //= A_tmp B1_tmp B2_tmp m n prf1 prf2 eq.
        move: eq prf1 prf2 => [] <- <- <- prf1 prf2.
        move: (IH1 m prf1) => IH1'.
        move: (subtype_machine [ tgt_for_srcs_gte B1 in cast (B1 -> B2) A]) => [] r prf.
        move: (inv_tgt_for_srcs_gte_check_tgt prf) => r__eq.
        rewrite r__eq in prf.
        move: (IH2 _ prf n (prf2 _ prf)) => IH2'.
        rewrite /= in IH1', IH2'.
        do 2 rewrite mulnDr.
        rewrite muln1 [X in _ <= X + _ + _](mul2n (size A)) -addnn.
        rewrite -(addnC 1) -(addnA (size A + _)) -(addnA (size A)).
        apply: leq_add.
        + by apply size_min.
        + rewrite addnA.
          apply: leq_add.
          * move: IH1'.
            case isOmega__B2: (isOmega B2).
            ** move => _.
               move: prf1.
               rewrite /cast /= isOmega__B2 => /tgts_omega_size ->.
               apply: (leq_trans (n := 1 + 2)) => //.
               apply: leq_add.
               *** apply: size_min.
               *** rewrite -(mulnA).
                   apply: leq_pmulr.
                   rewrite muln_gt0; by do 2 rewrite size_min.
            ** move => IH1'.
               apply: (leq_trans IH1').
               apply: leq_add.
               *** by apply: size_min.
               *** rewrite (mulnC) leq_pmul2r; last by apply: size_min.
                   apply: arrow_cast_size1.
                     by rewrite isOmega__B2.
          * apply: (leq_trans IH2').
            rewrite leq_mul2r.
            rewrite leq_mul2l.
            rewrite (arrow_cast_size2 A B1 B2) /=;
                    first by rewrite orbT.
            by apply: (choose_tgt_subseq _ _ _ prf).            
      - move => B A Delta dom1 IH1 dom2 IH2 n.
        move p__eq: [ tgt_for_srcs_gte B in A :: Delta] => p prf.
        move: p__eq.
        case: n p / prf => //=  B__tmp A_tmp Delta__tmp m n prf1 prf2 eq.
        move: eq prf1 prf2 => [] <- <- <- prf1 prf2.
        move: (IH1 n prf1) (IH2 m prf2) => /= IH1' IH2'.
        rewrite -(addnC 1) (leq_add2l).
        do 2 rewrite mulnDr.
        rewrite muln1 (addnAC (size B)) (addnC n).
        apply: leq_add.
        + apply: (leq_trans IH2').
          rewrite leq_add2r.
            by apply: size_min.
        + by rewrite mulnC -mulnA -(mulnC (size B)) mulnA.
      - move => B n.
        move p__eq: [ tgt_for_srcs_gte B in [::]] => p prf.
        move: p__eq.
        case: n p / prf => //= B__tmp [] <-.
      - move => A B1 B2 dom1 IH1 dom2 IH2 n.
        move p__eq: [ subty A of B1 \times B2] => p prf.
        move: p__eq.
        case: n p / prf => //= A_tmp B1_tmp B2_tmp m n prf1 prf2 eq.
        move: eq prf1 prf2 => [] <- <- <- prf1 prf2.
        move: (IH1 m prf1) (IH2 n prf2) => /= IH1' IH2'.
        rewrite mulnDr mulnDr -(addnC 1) muln1 -(addnA (_ * size A)).
        apply: leq_add.
        + by rewrite muln_gt0 /=; apply size_min.
        + apply: leq_add.
          * apply: (leq_trans IH1').
            rewrite -(mulnA _ (size _)) -(mulnA _ (size _)).
            rewrite leq_pmul2l => //.
            rewrite leq_pmul2r.
            ** by apply: prod_cast_size_le1.
            ** by apply: size_min.
          * apply: (leq_trans IH2').
            rewrite -(mulnA _ (size _)) -(mulnA _ (size _)).
            rewrite leq_pmul2l => //.
            rewrite leq_pmul2r.
            ** by apply: prod_cast_size_le2.
            ** by apply: size_min.
      - move => A B1 B2 dom1 IH1 dom2 IH2 n.
        move p__eq: [ subty A of B1 \cap B2] => p prf.
        move: p__eq.
        case: n p / prf => //= A_tmp B1_tmp B2_tmp m n prf1 prf2 eq.
        move: eq prf1 prf2 => [] <- <- <- prf1 prf2.
        move: (IH1 m prf1) (IH2 n prf2) => /= IH1' IH2'.
        rewrite mulnDr mulnDr -(addnC 1) muln1 -(addnA (_ * size A)).
        apply: leq_add.
        + by rewrite muln_gt0 /=; apply size_min.
        + by apply: leq_add.
    Qed.
  End Runtime.
End SubtypeMachineSpec.

Arguments checkSubtypes [Constructor].

Section SubtypeMachineInversion.
  Variable Constructor: ctor.

  Definition SubtypeMachine_inv {p: @Instruction Constructor} {r: @Result Constructor} (prf: p ~~> r) :=
    let diag p r : Prop :=
        match p, r with
        | [subty A of Omega], Return true =>
          forall (X: @Instruction Constructor -> @Result Constructor -> Prop),
            X [subty A of Omega] (Return true) ->
            X [subty A of Omega] (Return true)

        | [subty A of Ctor b B], Return r =>
          forall (X: @Instruction Constructor -> @Result Constructor -> Prop),
            (forall r', [subty (\bigcap_(A__i <- cast (Ctor b B) A) A__i) of B] ~~> Return r' ->
                   X [subty A of Ctor b B] (Return (~~nilp (cast (Ctor b B) A) && r'))) ->
            X [subty A of Ctor b B] (Return r)
        | [subty A of B1 -> B2], Return r =>
          forall (X: @Instruction Constructor -> @Result Constructor -> Prop),
            (forall Delta r',
                [tgt_for_srcs_gte B1 in cast (B1 -> B2) A] ~~> [check_tgt Delta] ->
                [subty (\bigcap_(A__i <- Delta) A__i) of B2] ~~> Return r' ->
                X [subty A of B1 -> B2] (Return (isOmega B2 || r'))) ->
            X [subty A of B1 -> B2] (Return r)
        | [tgt_for_srcs_gte B in [:: A & Delta ]], [check_tgt Delta'] =>
          forall (X: @Instruction Constructor -> @Result Constructor -> Prop),
            (forall Delta' r,
                [subty B of A.1] ~~> Return r ->
                [tgt_for_srcs_gte B in Delta] ~~> [check_tgt Delta'] ->
                X [tgt_for_srcs_gte B in [:: A & Delta ]] [check_tgt if r then [:: A.2 & Delta'] else Delta' ]) ->
            X [tgt_for_srcs_gte B in [:: A & Delta ]] [check_tgt Delta']
        | [tgt_for_srcs_gte B in [::]], [check_tgt [::]] =>
          forall (X: @Instruction Constructor -> @Result Constructor -> Prop),
            X [tgt_for_srcs_gte B in [::]] [check_tgt [::]] ->
            X [tgt_for_srcs_gte B in [::]] [check_tgt [::]]
        | [subty A of B1 \times B2], Return r =>
          forall (X: @Instruction Constructor -> @Result Constructor -> Prop),
            (forall r1 r2,
               [subty (\bigcap_(A__i <- cast (B1 \times B2) A) A__i.1) of B1] ~~> Return r1 ->
               [subty (\bigcap_(A__i <- cast (B1 \times B2) A) A__i.2) of B2] ~~> Return r2 ->
               X [subty A of B1 \times B2] (Return (~~nilp (cast (B1 \times B2) A) && r1 && r2))) ->
            X [subty A of B1 \times B2] (Return r)
        | [subty A of B1 \cap B2], Return r =>
          forall (X: @Instruction Constructor -> @Result Constructor -> Prop),
            (forall r1 r2,
                [subty A of B1] ~~> Return r1 ->
                [subty A of B2] ~~> Return r2 ->
                X [subty A of B1 \cap B2] (Return (r1 && r2))) ->
            X [subty A of B1 \cap B2] (Return r)
        | _, _ => False
        end in
    match prf in p' ~~> r' return diag p' r' with
    | step__Omega A => fun X k => k
    | step__Ctor A b B r prf => fun X k => k r prf
    | step__Arr A B1 B2 Delta r prf1 prf2 => fun X k => k Delta r prf1 prf2
    | step__chooseTgt B A Delta Delta' r prf1 prf2 => fun X k => k Delta' r prf1 prf2
    | step__doneTgt B => fun X k => k
    | step__Prod A B1 B2 r1 r2 prf1 prf2 => fun X k => k r1 r2 prf1 prf2
    | step__Inter A B1 B2 r1 r2 prf1 prf2 => fun X k => k r1 r2 prf1 prf2
    end.

End SubtypeMachineInversion.

Arguments SubtypeMachine_inv [Constructor] [p] [r].

Section PrimalityDefinitions.
  Variable Constructor: ctor.

  Inductive PrimeComponent: @IT Constructor -> Prop :=
  | PrimeComponent__omega: PrimeComponent Omega
  | PrimeComponent__Ctor: forall c A, PrimeComponent A -> PrimeComponent (Ctor c A)
  | PrimeComponent__ProductL: forall A, PrimeComponent A -> PrimeComponent (A \times Omega)
  | PrimeComponent__ProductR: forall A, PrimeComponent A -> PrimeComponent (Omega \times A)
  | PrimeComponent__Arr: forall A B, PrimeComponent B -> PrimeComponent (A -> B).

  Fixpoint isPrimeComponent (A: @IT Constructor): bool :=
    match A with
    | Omega => true
    | Ctor _ A => isPrimeComponent A
    | Omega \times A => isPrimeComponent A
    | A \times Omega => isPrimeComponent A
    | _ -> B => isPrimeComponent B
    | _ => false
    end. 

End PrimalityDefinitions.

Arguments PrimeComponent [Constructor].
Arguments PrimeComponent__omega [Constructor].
Arguments PrimeComponent__Ctor [Constructor] c [A].
Arguments PrimeComponent__ProductL [Constructor] [A].
Arguments PrimeComponent__ProductR [Constructor] [A].
Arguments PrimeComponent__Arr [Constructor] [A B].
Arguments isPrimeComponent [Constructor].
Hint Constructors PrimeComponent.
Hint Resolve PrimeComponent__omega.

Section PrimalityLemmas.
  Variable Constructor: ctor.

  Definition PrimeComponent_inv {A: @IT Constructor} (pc: PrimeComponent A) :=
    let diag (A: @IT Constructor): Prop :=
        match A return Prop with
        | Omega => forall (X: @IT Constructor -> Prop), X Omega -> X Omega
        | Ctor c A => forall (X: IT -> Prop), (PrimeComponent A -> X (Ctor c A)) -> X (Ctor c A)
        | A \times B =>
          forall (X: @IT Constructor -> Prop),
            (PrimeComponent A -> X (A \times Omega)) ->
            (PrimeComponent B -> X (Omega \times B)) ->
            X (A \times B)
        | A -> B => forall (X: IT -> Prop), (PrimeComponent B -> X (A -> B)) -> X (A -> B)
        | _ => False
        end in
    match pc in PrimeComponent A' return diag A' with
    | PrimeComponent__omega => fun X k => k
    | PrimeComponent__Ctor c A prf => fun X k => k prf
    | PrimeComponent__ProductL A prf => fun X k1 k2 => k1 prf
    | PrimeComponent__ProductR A prf => fun X k1 k2 => k2 prf
    | PrimeComponent__Arr A B prf => fun X k => k prf
    end.

  Lemma isPrimeComponentSound: forall (A: @IT Constructor), isPrimeComponent A -> PrimeComponent A.
  Proof.
    elim => //; last 1 [ idtac  ] || by auto.
    move => A prime__A B prime__B.
    move: prime__A prime__B.
    case: A; case B => //; auto.
  Qed.

  Lemma isPrimeComponentComplete: forall (A: @IT Constructor), PrimeComponent A -> isPrimeComponent A.
  Proof.
    elim => //.
    - move => c A IH /PrimeComponent_inv prime__A.
      apply prime__A => //.
    - move => ? _ B IH /PrimeComponent_inv prime__B.
      eapply prime__B => //.
    - move => A IH__A B IH__B /PrimeComponent_inv prf.
      have: (A = Omega /\ isPrimeComponent B) \/
            (B = Omega /\ isPrimeComponent A).
      
      { apply: (prf (fun C => match C with
                           | (A \times B) =>
                             (A = Omega /\ isPrimeComponent B) \/
                             (B = Omega /\ isPrimeComponent A)
                           | _ => True
                           end)); by move => ?; tauto. }
      case.
      + by move => [] -> // ->.
      + move => [] -> //= ->.
          by move: A IH__A prf => [].
    - by move => ? ? ? ? /PrimeComponent_inv.
  Qed.    

  Lemma isPrimeComponentP: forall (A: @IT Constructor), reflect (PrimeComponent A) (isPrimeComponent A).
  Proof.
    move => A.
    apply: (equivP (P := isPrimeComponent A));
      first by apply: idP.
    split.
    - by apply: isPrimeComponentSound.
    - by apply: isPrimeComponentComplete.
  Qed.

  Lemma primeComponentPrimeSubty:
    forall (A B C: @IT Constructor),
      [subty (A \cap B) of C ] ~~> Return true ->
      PrimeComponent C ->
      [subty A of C ] ~~> Return true \/ [subty B of C ] ~~> Return true.
  Proof.
    move => A B C prf /isPrimeComponentP.
    move: A B prf.
    elim: C.
    - by move => *; left; auto.
    - move => c C IH A B /SubtypeMachine_inv prf /= prime__C.
      apply: (prf (fun (p: @Instruction Constructor)  (r: @Result Constructor) =>
                     match p, r return Prop with
                     | [ subty A \cap B of Ctor c C], (Return true) =>
                       [ subty A of Ctor c C] ~~> Return true \/ [ subty B of Ctor c C] ~~> Return true
                     | _, _ => True
                     end)).
      move => []; last by rewrite andbF.
      move canCast: (~~ nilp (cast (Ctor c C) (A \cap B))) => [] //=.
      move: canCast.
      rewrite (cast_inter _ A B (Ctor c C) isT).
      rewrite /nilp size_cat -lt0n addn_gt0.
      move /orP.
      rewrite lt0n lt0n.
      move => [] canCast
                /subty__sound /(BCD__Trans _ (bcd_bigcap_cat _ _ _)) /subty_complete /IH /(fun f => f prime__C)
                [].
      + by move => /step__Ctor; rewrite canCast; move => *; left.
      + move canCast__B: (nilp (cast (Ctor c C) B)) => [].
        * rewrite (nilP canCast__B) /=.
          move => omega__C.
          left.
          rewrite -(andbT true) -[X in X && _]canCast.
          apply: step__Ctor.
            by apply: (subty__trans _ _ Omega).
        * by move => /step__Ctor; rewrite canCast__B; move => *; right.
      + move canCast__A: (nilp (cast (Ctor c C) A)) => [].
        * rewrite (nilP canCast__A) /=.
          move => omega__C.
          right.
          rewrite -(andbT true) -[X in X && _]canCast.
          apply: step__Ctor.
            by apply: (subty__trans _ _ Omega).
        * by move => /step__Ctor; rewrite canCast__A; move => *; left.
      + by move => /step__Ctor; rewrite canCast; move => *; right.
    - move => C1 IH__C1 C2 IH__C2 A B /SubtypeMachine_inv prf /= prime__C.
      apply: (prf (fun (p: @Instruction Constructor)  (r: @Result Constructor) =>
                     match p, r return Prop with
                     | [ subty A \cap B of C1 -> C2], (Return true) =>
                       [ subty A of C1 -> C2] ~~> Return true \/ [ subty B of C1 -> C2] ~~> Return true
                     | _, _ => True
                     end)).
      move isOmega__C2: (isOmega C2) => [] //=; first by move => *; left; apply: subty__Omega.
      move => Delta [] //.
      move: (subtype_machine _ [ tgt_for_srcs_gte C1 in cast (C1 -> C2) A] ).
      move => [] [ ? | Delta1 ];
               first move => /SubtypeMachine_inv;
               move castA__eq: (cast (C1 -> C2) A) => Delta__A; first by case Delta__A.
      move: (subtype_machine _ [ tgt_for_srcs_gte C1 in cast (C1 -> C2) B] ).
      move => [] [ ? | Delta2 ];
               first move => /SubtypeMachine_inv;
               move castB__eq: (cast (C1 -> C2) B) => Delta__B; first by case Delta__B.
      move: (cast_inter _ A B (C1 -> C2)).
      rewrite /isOmega -/(isOmega C2) isOmega__C2 /(~~ false).
      move => /(fun f => f isT) -> prf__Delta2 prf__Delta1.
      move: (split_tgts_for_srcs_gte _ _ _ _ _ _ prf__Delta1 prf__Delta2).
      rewrite castA__eq castB__eq.
      move => prf__Delta12 prf__Delta.
      move: (Semantics_functional _ _ _ _ prf__Delta prf__Delta12) => [] Delta__eq.
      rewrite Delta__eq.
      move => /subty__sound /(BCD__Trans _ (bcd_bigcap_cat _ _ _)) /subty_complete.
      move => /IH__C2 /(fun f => f prime__C) [].
      + move: castA__eq prf__Delta1 => <-.
        move => /step__Arr mkR /mkR.
        rewrite isOmega__C2 //=.
          by left.
      + move: castB__eq prf__Delta2 => <-.
        move => /step__Arr mkR /mkR.
        rewrite isOmega__C2 //=.
          by right.
    - move => C1 IH__C1 C2 IH__C2 A B /SubtypeMachine_inv prf /isPrimeComponentP /PrimeComponent_inv prime__C.
      move: prf (prf (fun (p: @Instruction Constructor)  (r: @Result Constructor) =>
                        match p, r return Prop with
                        | [ subty A \cap B of C1 \times C2], (Return true) =>
                          [ subty A of C1 \times C2] ~~> Return true \/
                          [ subty B of C1 \times C2] ~~> Return true
                        | _, _ => True
                        end)) => _.
      apply: (prime__C
                (fun ty =>
                   match ty with
                   | C1 \times C2 =>
                     forall _ : (forall _ : (forall r1 r2 : bool,
                          [ subty \bigcap_(A__i <- cast (C1 \times C2) (A \cap B)) A__i.1 of C1] ~~> Return r1 ->
                          [ subty \bigcap_(A__i <- cast (C1 \times C2) (A \cap B)) A__i.2 of C2] ~~> Return r2 ->
                          if ~~ nilp (cast (C1 \times C2) (A \cap B)) && r1 && r2
                          then [ subty A of C1 \times C2] ~~> Return true \/ [ subty B of C1 \times C2] ~~> Return true
                          else True),
                      [ subty A of C1 \times C2] ~~> Return true \/
                      [ subty B of C1 \times C2] ~~> Return true),
                       ([ subty A of C1 \times C2] ~~> Return true \/
                        [ subty B of C1 \times C2] ~~> Return true)%type
                   | _ => True
                   end)).
      + move => prime__C1 k.
        apply: k.
        do 2 (move => []; last by rewrite andbF).
        do 2 rewrite andbT.
        rewrite (cast_inter _ _ _ (C1 \times Omega) isT).
        case canCast: (~~ nilp (cast (C1 \times Omega) A ++ cast (C1 \times Omega) B)) => [] //.
        move => /subty__sound /(BCD__Trans _ (bcd_bigcap_cat_f _ _ _ _ _)) /subty_complete /IH__C1
                /(fun f => f (isPrimeComponentComplete _ prime__C1)) [] prf _.
        * move: canCast.
          rewrite /nilp size_cat -lt0n addn_gt0.
           move /orP.
           rewrite lt0n lt0n.
           move => canCast.
           move canCast__A: (~~(nilp (cast (C1 \times Omega) A))) => [].
          ** left.
             rewrite -(andbT true) -(andbT (true && true)).
             rewrite -[X in X && _ && _ ]canCast__A.
               by apply step__Prod.
          ** right.
             move: canCast.
             rewrite -/(nilp (cast (C1 \times Omega) A)) canCast__A.
             move => /orP //= canCast__B.
             rewrite -(andbT true) -(andbT (true && true)).
             rewrite -[X in X && _ && _ ]canCast__B.
             apply step__Prod => //.
             move: canCast__A prf.
             rewrite /nilp.
             move => /negbFE /eqP cannotCast__A.    
             rewrite (size0nil cannotCast__A) /=.
               by apply: subty__trans.
        * move: canCast.
          rewrite /nilp size_cat -lt0n addn_gt0.
           move /orP.
           rewrite lt0n lt0n.
           move => canCast.
           move canCast__B: (~~(nilp (cast (C1 \times Omega) B))) => [].
          ** right.
             rewrite -(andbT true) -(andbT (true && true)).
             rewrite -[X in X && _ && _ ]canCast__B.
               by apply step__Prod.
          ** left.
             move: canCast.
             rewrite -/(nilp (cast (C1 \times Omega) B)) canCast__B.
             move => /orP //= canCast__A.
             rewrite -(andbT true) -(andbT (true && true)).
             rewrite -[X in X && _ && _ ]canCast__A orbF.
             apply step__Prod => //.
             move: canCast__B prf.
             rewrite /nilp.
             move => /negbFE /eqP cannotCast__B.
             rewrite (size0nil cannotCast__B) /=.
               by apply: subty__trans.
      + move => prime__C2 k.
        apply: k.
        do 2 (move => []; last by rewrite andbF).
        do 2 rewrite andbT.
        rewrite (cast_inter _ _ _ (Omega \times C2) isT).
        case canCast: (~~ nilp (cast (Omega \times C2) A ++ cast (Omega \times C2) B)) => [] //.
        move => _ /subty__sound /(BCD__Trans _ (bcd_bigcap_cat_f _ _ _ _ _)) /subty_complete /IH__C2
                /(fun f => f (isPrimeComponentComplete _ prime__C2)) [] prf.
        * move: canCast.
          rewrite /nilp size_cat -lt0n addn_gt0.
           move /orP.
           rewrite lt0n lt0n.
           move => canCast.
           move canCast__A: (~~(nilp (cast (Omega \times C2) A))) => [].
          ** left.
             rewrite -(andbT true) -(andbT (true && true)).
             rewrite -[X in X && _ && _ ]canCast__A.
               by apply step__Prod.
          ** right.
             move: canCast.
             rewrite -/(nilp (cast (Omega \times C2) A)) canCast__A.
             move => /orP //= canCast__B.
             rewrite -(andbT true) -(andbT (true && true)).
             rewrite -[X in X && _ && _ ]canCast__B.
             apply step__Prod => //.
             move: canCast__A prf.
             rewrite /nilp.
             move => /negbFE /eqP cannotCast__A.    
             rewrite (size0nil cannotCast__A) /=.
               by apply: subty__trans.
        * move: canCast.
          rewrite /nilp size_cat -lt0n addn_gt0.
           move /orP.
           rewrite lt0n lt0n.
           move => canCast.
           move canCast__B: (~~(nilp (cast (Omega \times C2) B))) => [].
          ** right.
             rewrite -(andbT true) -(andbT (true && true)).
             rewrite -[X in X && _ && _ ]canCast__B.
               by apply step__Prod.
          ** left.
             move: canCast.
             rewrite -/(nilp (cast (Omega \times C2) B)) canCast__B.
             move => /orP //= canCast__A.
             rewrite -(andbT true) -(andbT (true && true)).
             rewrite -[X in X && _ && _ ]canCast__A orbF.
             apply step__Prod => //.
             move: canCast__B prf.
             rewrite /nilp.
             move => /negbFE /eqP cannotCast__B.
             rewrite (size0nil cannotCast__B) /=.
               by apply: subty__trans.
    - done.
  Qed.

  Lemma primeComponentPrime:
    forall (A B C: @IT Constructor),
      [bcd (A \cap B) <= C] ->
      PrimeComponent C ->
      [bcd A <= C] \/ [bcd B <= C].
  Proof.
    move => A B C /subty_complete prf prime__C.
    case: (primeComponentPrimeSubty A B C prf prime__C).
    - by left; apply: subty__sound.
    - by right; apply: subty__sound.
  Qed.

  Lemma primeComponentPrime_seq:
    forall (A: @IT Constructor) Delta,
      ~~isOmega A ->
      PrimeComponent A ->
      [bcd (\bigcap_(A__i <- Delta) A__i) <= A] ->
      has (fun B => checkSubtypes B A) Delta.
  Proof.
    move => A.
    elim.
    - move => //= notOmega__A _ /subty_complete /(fun prf => Omega__subty _ Omega _ prf isT).
        by move: notOmega__A => /negP.
    - move => B Delta IH notOmega__A prime__A.
      move => /(BCD__Trans _ (bcd_bigcap_cat _ [:: B] Delta)).
      move => /(fun prf => primeComponentPrime _ _ _ prf prime__A) [] //=.
      + by move => /subtypeMachineP ->.
      + move => /(IH notOmega__A prime__A) ->.
          by rewrite orbT.
  Qed.

  Fixpoint addAndFilter
           (Delta: seq (@IT Constructor))
           (A: @IT Constructor) :=
    match Delta with
    | [::] => [:: A]
    | [:: B & Delta] =>
      if checkSubtypes B A
      then [:: B & Delta]
      else
        if checkSubtypes A B
        then addAndFilter Delta A
        else [:: B & addAndFilter Delta A]
    end.

  Fixpoint primeFactors_rec
           (A: @IT Constructor)
           (contextualize: @IT Constructor -> @IT Constructor)
           (Delta: seq (@IT Constructor)): seq (@IT Constructor) :=
    match A with
    | Omega =>
      let P := contextualize Omega in
      if isOmega P then Delta else addAndFilter Delta P
    | Ctor a A => primeFactors_rec A (fun B => contextualize (Ctor a B)) Delta
    | A1 -> A2 => primeFactors_rec A2 (fun B => contextualize (A1 -> B)) Delta
    | A1 \times A2 =>
      primeFactors_rec A2 (fun B => contextualize (Omega \times B))
                       (primeFactors_rec A1 (fun B => contextualize (B \times Omega)) Delta)
    | A1 \cap A2 =>
      primeFactors_rec A2 contextualize
                       (primeFactors_rec A1 contextualize Delta)
    end.

  Lemma addAndFilterLeq__A: forall A Delta, has (fun B => checkSubtypes B A) (addAndFilter Delta A).
  Proof.
    move => A.
    elim => //=.
    - rewrite orbF.
        by apply /subtypeMachineP.
    - move => B Delta IH.
      move check__BA: (checkSubtypes B A) => [] //=.
      + by rewrite check__BA.
      + case: (checkSubtypes A B) => //=.
          by rewrite IH orbT.
  Qed.

  Lemma addAndFilterLeq__DeltaA: forall C A Delta,
      has (fun B => checkSubtypes B C) (addAndFilter Delta A) <->
      has (fun B => checkSubtypes B C) Delta \/ checkSubtypes A C.
  Proof.
    move => C A.
    elim => //=.
    - rewrite orbF.
      split; first by move => ->; right.
        by move => [] //.
    - move => B Delta IH.
      move le__BA: (checkSubtypes B A) => [] //=.
      + split; first by move => ?; left.
        move => [] //.
          by move: le__BA => /subtypeMachineP /(BCD__Trans) mkPrf /subtypeMachineP /mkPrf /subtypeMachineP ->.
      + move le__AB: (checkSubtypes A B) => [] //=.
        * split.
          ** move => /IH [] ->; last by right.
               by rewrite orbT; left.
          ** move => [].
             *** move => /orP [].
                 **** move => /subtypeMachineP le__BC.
                      apply: sub_has; last by apply: addAndFilterLeq__A.
                      move: le__AB.
                        by move => /subtypeMachineP le__AB D /subtypeMachineP /(BCD__Trans)
                                   /(fun f => f le__AB) /(BCD__Trans) /(fun f => f le__BC) /subtypeMachineP.
                 **** move => /(or_introl) prf.
                        by move: ((proj2 IH) (prf _)).
             *** move => /or_intror prf.
                   by move: ((proj2 IH) (prf _)).
        * split.
          ** move => /orP []; first by move => ->; left.
             move => /IH [] ->; last by right.
               by rewrite orbT; left.
          ** case.
             *** move => /orP []; first by move => -> //=.
                 move => /or_introl prf.
                 move: ((proj2 IH) (prf _)) => ->.
                   by rewrite orbT.
             *** move => /or_intror prf.
                 move: ((proj2 IH) (prf _)) => ->.
                   by rewrite orbT.
  Qed.
  

  Lemma has_subseq:
    forall {a: eqType} P (Delta Delta': seq a),
      subseq Delta Delta' -> has P Delta -> has P Delta'.
  Proof.
    move => a P Delta Delta' /mem_subseq shift_in /hasP [] x /shift_in inprf prf.
    apply /hasP.
      by exists x.
  Qed.

  Lemma addAndFilter_has_le_weaken:
    forall A B Delta' Delta,
      subseq Delta Delta' ->
      has (fun D => checkSubtypes D B) (addAndFilter Delta A) ->
      has (fun D => checkSubtypes D B) (addAndFilter Delta' A).
  Proof.
    move => A B.
    elim.
    - move => Delta.
      rewrite subseq0.
        by move => /eqP ->.
    - move => C Delta' IH /=.
      case => //=.
      + move => _ le__AB.
        move: (IH [::] (sub0seq Delta') le__AB) => prf.
        move le__CA: (checkSubtypes C A) => [].
        * apply /orP; left.
          apply /subtypeMachineP.
          apply: (BCD__Trans A); apply /subtypeMachineP => //.
            by rewrite orbF in le__AB.
        * case: (checkSubtypes A C) => //=.
            by rewrite prf orbT.
      + move => C'.
        case eq__CC': (C' == C) => [].
        * move => Delta subseq__DeltaDelta'.
          rewrite (eqP eq__CC').
          case: (checkSubtypes A C).
          ** case: (checkSubtypes C A); last by apply: IH.
             apply: has_subseq.
               by apply: (cat_subseq (subseq_refl [:: C])).
          ** case: (checkSubtypes C A).
             *** apply: has_subseq.
                   by apply: (cat_subseq (subseq_refl [:: C])).
             *** move => //= /orP []; first by move => ->.
                 move => /(IH _ subseq__DeltaDelta') ->.
                   by rewrite orbT.
        * move => Delta.
          move => /IH mkPrf /mkPrf.
          case le__CA: (checkSubtypes C A).
          ** move => /addAndFilterLeq__DeltaA [] //=; first by move ->; rewrite orbT.
               by move: le__CA => /subtypeMachineP /(BCD__Trans) mkPrf' /subtypeMachineP
                                /mkPrf' /subtypeMachineP ->.
          ** case (checkSubtypes A C) => //= ->.
               by rewrite orbT.
  Qed.

  Lemma addAndFilterLeq__Delta:
    forall A Delta, all (fun B => has (fun C => checkSubtypes C B) (addAndFilter Delta A)) Delta .
  Proof.
    move => A.
    elim.
    - done.
    - move => B Delta IH.
      rewrite /all -/(all _ Delta).
      apply /andP.
      split.
      + apply /addAndFilterLeq__DeltaA.
        left => //=.
          by move: (@BCD__Refl _ B) => /subtypeMachineP ->.
      + apply: sub_all; last by apply: IH.
        move => C prf.
        apply: addAndFilter_has_le_weaken; last by exact prf.
          by apply: subseq_cons.
  Qed.

  Lemma addAndFilter_in:
    forall B A Delta, B \in addAndFilter Delta A -> B = A \/ B \in Delta.
  Proof.
    move => B A.
    elim.
    - rewrite (mem_seq1 B A) => /eqP ?; by left.
    - move => C Delta IH //=.
      case (checkSubtypes C A); first by move => ?; right.
      case (checkSubtypes A C).
      + move => /IH.
        rewrite in_cons.
        move => [] ->; first by left.
          by rewrite orbT; right.
      + rewrite in_cons in_cons.
        move => /orP []; first by move => ->; right.
        move => /IH [] ->; first by left.
          by rewrite orbT; right.
  Qed.

  Lemma bigcap_has_le: forall (A: @IT Constructor) Delta,
      has (fun B => checkSubtypes B A) Delta ->
      [bcd (\bigcap_(A__i <- Delta) A__i) <= A].
  Proof.
    move => A.
    elim => //= B Delta IH /orP [].
    - move: IH => _ /subtypeMachineP.
      case: Delta => //=.
      move => ? ? le__BA.
        by apply: BCD__Trans; first by apply: BCD__Lub1.
    - move => /IH.
      move: IH => _.
      case: Delta.
      + by move => /(BCD__Trans _ (@BCD__omega _ B)).
      + move => *.
          by apply: BCD__Trans; first by apply: BCD__Lub2.
  Qed.

  Lemma addAndFilter_monotonic: forall A Delta,
      [bcd (\bigcap_(A__i <- addAndFilter Delta A) A__i) <= \bigcap_(A__i <- Delta) A__i].
  Proof.
    move => A Delta.
    move: (addAndFilterLeq__Delta A Delta).
    elim: Delta => //= B Delta IH /andP [].
    move le__BA: (checkSubtypes B A) => [] //=.
    move le__AB: (checkSubtypes A B) => [].
    - move => prf__B /IH.
      move: IH prf__B => _.
      case: Delta.
      + by move => /andP [] /subtypeMachineP prf__B _ _ //=.
      + move => ? ? /bigcap_has_le *.
          by apply: BCD__Glb.
    - move => _ _.
      move: (addAndFilterLeq__Delta A Delta) => /IH.
      move: IH => _.
      case: Delta; first by rewrite //=.
      move => B2 Delta prf.
      apply: BCD__Trans; first by apply: (bcd_cat_bigcap _ [:: B] _).
      apply: BCD__Glb.
      * apply: BCD__Lub1.
      * by apply: BCD__Trans; first by apply: BCD__Lub2.
  Qed.

  Lemma primeFactors_rec_prime:
    forall A Delta contextualize,
      all (fun B => isPrimeComponent B) Delta ->
      (forall A, isPrimeComponent A -> isPrimeComponent (contextualize A)) ->
      all (fun B => isPrimeComponent B) (primeFactors_rec A contextualize Delta).
  Proof.
    elim.
    - move => Delta contextualize Delta__Ok contextualize__Ok //=.
      case: (isOmega (contextualize Omega)) => //.
      apply /allP => A /addAndFilter_in [].
      + move => ->.
          by apply contextualize__Ok.
      + by move: (allP Delta__Ok) => prf /(fun x => prf x).
    - move => c A IH Delta contextualize Delta__Ok contextualize__Ok //=.
      apply: IH => //=.
      move => B prf.
        by apply: contextualize__Ok.
    - move => A _ B IH Delta contextualize Delta__Ok contextualize__Ok //=.
      apply: IH => //.
      move => C prf.
        by apply: contextualize__Ok.
    - move => A IH__A B IH__B Delta contextualize Delta__Ok contextualize__Ok //=.
      apply: IH__B.
      + apply: IH__A => //.
        move => C prf.
        apply: contextualize__Ok => //=.
        rewrite prf.
          by case C.
      + move => C prf.
          by apply: contextualize__Ok => //=.
    - move => A IH__A B IH__B Delta contextualize Delta__Ok contextualize__Ok //=.
      apply: IH__B.
      + by apply: IH__A.
      + move => C prf.
          by apply: contextualize__Ok.
  Qed.

  Lemma primeFactors_monotonic: forall A Delta contextualize,
      [bcd (\bigcap_(P__i <- primeFactors_rec A contextualize Delta) P__i) <= \bigcap_(A__i <- Delta) A__i].
  Proof.
    elim.
    - move => Delta contextualize //=.
      case: (isOmega (contextualize Omega)) => //=.
        by apply: addAndFilter_monotonic.
    - move => ? ? IH ? ?.
        by apply: IH.
    - move => A _ B IH ? ?.
        by apply: IH.
    - move => A IH__A B IH__B ? ?.
      apply: BCD__Trans; first by apply: IH__B.
        by apply: IH__A.
    - move => A IH__A B IH__B ? ?.
      apply: BCD__Trans; first by apply: IH__B.
        by apply: IH__A.
  Qed.

  Lemma primeFactors_rec_leq: forall A Delta contextualize,
      (forall B C, [bcd B <= C] -> [bcd (contextualize B) <= (contextualize C)]) ->
      (forall B C, [bcd ((contextualize B) \cap (contextualize C)) <= (contextualize (B \cap C)) ]) ->
      [bcd (\bigcap_(P__i <- primeFactors_rec A contextualize Delta) P__i) <= contextualize A].
  Proof.
    elim.
    - move => Delta contextualize _ _ //=.
      case isOmega__ctxt: (isOmega (contextualize Omega)).
      + apply: subty__sound.
          by apply: subty__Omega.
      + move: (addAndFilterLeq__A (contextualize Omega) Delta).
        elim: (addAndFilter Delta (contextualize Omega)) => //.
        move => P Delta' IH /orP [].
        * move => /subtypeMachineP prf //=.
          move: IH => _.
          case: Delta' => //= P2 Delta'.
            by apply: BCD__Trans; first by apply BCD__Lub1.
        * move => /IH.
          move: IH => _.
          case: Delta' => //=.
          ** move => prf.
              by apply: BCD__Trans; last by exact prf.
          ** move => P1 Delta' prf.
               by apply: BCD__Trans; first by apply BCD__Lub2.
    - move => c A IH Delta contextualize prf dist //=.
      apply: IH.
      move => B C le__BC.
      apply: prf.
      + apply: BCD__CAx => //.
        apply: preorder_reflexive.
      + move => B C.
        apply: BCD__Trans; first by apply dist.
        apply: prf.
          by apply: BCD__CDist.
    - move => A _ B IH Delta contextualize prf dist.
      apply: IH.
      move => C D le__CD.
      apply: prf;
        first by apply: BCD__Sub.
      move => C D.
      apply: BCD__Trans; first by apply dist.
      apply: prf.
        by apply: BCD__Dist.
    - move => A IH__A B IH__B Delta contextualize prf dist.
      apply: (BCD__Trans
                ((contextualize (Omega \times B))
                   \cap (contextualize (A \times Omega)))); last first.
      + apply: (BCD__Trans (contextualize ((Omega \cap A) \times (B \cap Omega)))); last first.
        * apply: prf.
          apply: BCD__ProdSub.
          ** by apply: BCD__Lub2.
          ** by apply: BCD__Lub1.
        * apply: (BCD__Trans (contextualize ((Omega \times B) \cap (A \times Omega)))).
          ** by apply: dist.
          ** apply prf.
              by apply: BCD__ProdDist.
      + apply: BCD__Glb.
        * apply: IH__B.
          ** move => C D le__CD.
             apply: prf.
               by apply: BCD__ProdSub.
          ** move => C D.
             apply: BCD__Trans; first by apply: dist.
             apply: prf.
             apply: BCD__Trans; first by apply: BCD__ProdDist.
               by apply: BCD__ProdSub.
        * rewrite /=.
          apply: BCD__Trans; first by apply: primeFactors_monotonic.
          apply: IH__A.
          ** move => C D le__CD.
             apply: prf.
               by apply: BCD__ProdSub.
          ** move => C D.
             apply: BCD__Trans; first by apply: dist.
             apply: prf.
             apply: BCD__Trans; first by apply: BCD__ProdDist.
               by apply: BCD__ProdSub.
    - move => A IH__A B IH__B Delta contextualize prf dist.
      rewrite /=.
      apply: BCD__Trans; last by apply: dist.
      apply: BCD__Glb.
      + apply: BCD__Trans; first by apply: primeFactors_monotonic.
          by apply: IH__A.
      + by apply: IH__B.
  Qed.

  Lemma addAndFilterGeq__Delta: forall A Delta,
      all (fun B => has (fun C => checkSubtypes C B) [:: A & Delta]) (addAndFilter Delta A).
  Proof.
    move => A.
    elim => //=.
    - rewrite andbT orbF.
        by apply /subtypeMachineP.
    - move => B Delta IH.
      move le__BA: (checkSubtypes B A) => [] //=.
      + apply /andP.
        split.
        * apply /orP; right; apply /orP; left.
            by apply /subtypeMachineP.
        * apply: (sub_all (a1 := fun B => has (fun C => checkSubtypes C B) Delta)).
          ** move => ? ->.
               by do 2 rewrite orbT.
          ** clear...
             elim: Delta => //= A Delta IH.
             apply /andP.
             split.
             *** by apply /orP; left; apply /subtypeMachineP.
             *** apply: sub_all; last by exact IH.
                 move => ? ->.
                   by rewrite orbT.
      + move leq__AB: (checkSubtypes A B) => [].
        * apply: sub_all; last by exact IH.
          move => ? /orP [] ->;
            by repeat rewrite orbT.
        * apply /andP.
          split.
          ** apply /orP; right; apply /orP; left.
               by apply /subtypeMachineP.
          ** apply: sub_all; last by exact IH.
             move => ? /orP [] ->;
               by repeat rewrite orbT.
  Qed.

  Lemma bcd_all_ge: forall (Delta1 Delta2 : seq (@IT Constructor)),
      all (fun B => has (fun C => checkSubtypes C B) Delta1) Delta2 ->
      [bcd (\bigcap_(A__i <- Delta1) A__i) <= \bigcap_(A__i <- Delta2) A__i].
  Proof.
    move => Delta1.
    elim => //= A Delta2 IH /andP [] prf /IH prfs.
    apply: BCD__Trans; last by apply: (bcd_bigcap_cat _ [:: A]).
    apply: BCD__Glb => //=.
      by apply: bigcap_has_le.
  Qed.

  Lemma addAndFilterGeq: forall A Delta,
      [bcd (\bigcap_(A__i <- [:: A & Delta]) A__i) <= \bigcap_(A__i <- addAndFilter Delta A) A__i].
  Proof.
    move => A Delta.
    apply: bcd_all_ge.
      by apply: addAndFilterGeq__Delta.
  Qed.

  Lemma primeFactors_rec_geq: forall A Delta contextualize,
      (forall B C, [bcd B <= C] -> [bcd (contextualize B) <= (contextualize C)]) ->
      [bcd (\bigcap_(A__i <- [:: contextualize A & Delta]) A__i) <=
       (\bigcap_(P__i <- primeFactors_rec A contextualize Delta) P__i) ].
  Proof.
    elim.
    - move => Delta contextualize _ //=.
      apply: BCD__Trans; first by apply: (bcd_cat_bigcap _ [:: contextualize Omega]).
      case: (isOmega (contextualize Omega)) => //=.
      apply: BCD__Trans; last by apply: addAndFilterGeq.
        by apply: (bcd_bigcap_cat _ [:: contextualize Omega]).
    - move => ? ? IH ? ? prf.
      apply: IH.
      move => B C le__BC.
      apply: prf.
      apply: BCD__CAx => //.
        by apply: preorder_reflexive.
    - move => A _ B IH Delta contextualize prf.
      apply: IH.
      move => C D le__CD.
      apply: prf.
        by apply: BCD__Sub.
    - move => A IH__A B IH__B Delta contextualize prf.
      rewrite [primeFactors_rec _ _]/=.
      apply: (BCD__Trans (\bigcap_(A__i <- [:: contextualize (Omega \times B),
                                        contextualize (A \times Omega) &
                                        Delta ]) A__i)).
      + apply: (BCD__Trans (\bigcap_(A__i <- [:: contextualize ((Omega \times B) \cap (A \times Omega)) &
                                        Delta ]) A__i)).
        * apply: BCD__Trans; first by apply: (bcd_cat_bigcap _ [:: contextualize (A \times B)]).
          apply: BCD__Trans; last by apply: (bcd_bigcap_cat _ [:: contextualize _]).
          apply: BCD__Glb => //.
          apply: BCD__Trans; first by apply: BCD__Lub1.
          apply: prf.
          apply: (BCD__Trans ((A \cap Omega) \times (Omega \cap B))).
          ** apply: BCD__ProdSub; by apply: BCD__Glb.
          ** apply: BCD__Glb; by apply: BCD__ProdSub.
        * apply: BCD__Trans; first by apply: (bcd_cat_bigcap _ [:: contextualize _]).
          apply: BCD__Trans;
            last by apply: (bcd_bigcap_cat _ [:: contextualize (Omega \times B);
                                              contextualize (A \times Omega)]).
          apply: BCD__Glb => //.
          apply: BCD__Trans; first by apply: BCD__Lub1.
          apply: BCD__Glb; by apply: prf.
      + apply: BCD__Trans; last apply: IH__B.
        * apply: BCD__Trans; first by apply: (bcd_cat_bigcap _ [:: contextualize _]).
          apply: BCD__Trans; last by apply: (bcd_bigcap_cat _ [:: contextualize _]).
          apply: BCD__Glb => //.
          apply: BCD__Trans; first by apply: BCD__Lub2.
          apply: IH__A.
          move => C D le__CD.
          apply: prf.
            by apply: BCD__ProdSub.
        * move => C D le__CD.
          apply: prf.
            by apply: BCD__ProdSub.
    - move => A IH__A B IH__B Delta contextualize prf.
      rewrite [primeFactors_rec _ _]/=.
      apply: (BCD__Trans (\bigcap_(A__i <- [:: contextualize B,
                                        contextualize A &
                                        Delta ]) A__i)).
      + apply: BCD__Trans; last by apply: (bcd_bigcap_cat _ [:: contextualize B; contextualize A]).
        apply: BCD__Glb.
        * apply: BCD__Trans; first by apply: (bcd_cat_bigcap _ [:: contextualize _]).
          apply: BCD__Trans; first by apply: BCD__Lub1.
          apply: BCD__Glb; by apply: prf.
        * by apply: BCD__Trans; first by apply: (bcd_cat_bigcap _ [:: contextualize _]).
      + apply: BCD__Trans; last by apply: IH__B.
        apply: BCD__Trans; last by apply: (bcd_bigcap_cat _ [:: contextualize _]).
        apply: BCD__Trans; first by apply: (bcd_cat_bigcap _ [:: contextualize _]).
        apply: BCD__Glb => //.
        apply: BCD__Trans; first by apply: BCD__Lub2.
          by apply: IH__A.
  Qed.

  Fixpoint nosubdub (Delta: seq (@IT Constructor)): bool :=
    match Delta with
    | [::] => true
    | [:: A & Delta'] =>
      all (fun B => ~~ (checkSubtypes B A || checkSubtypes A B)) Delta' && nosubdub Delta'
    end.

  Lemma addAndFilter_nosubdub: forall A Delta,
      nosubdub Delta ->
      nosubdub (addAndFilter Delta A).
  Proof.
    move => A.
    elim => //= B Delta IH prf.
    move le__BA: (checkSubtypes B A) => [] //.
    move: prf => /andP [] prfB prfDelta.
    move le__AB: (checkSubtypes A B) => [] //=.
    - by apply: IH.
    - rewrite (IH prfDelta) andbT.
      apply /allP => C /addAndFilter_in [].
      + move => ->.
          by rewrite le__AB le__BA.
      + by move: prfB => /allP disprf /(disprf C).
  Qed.

  Lemma primeFactors_nosubdub: forall A Delta contextualize,
      nosubdub Delta ->
      nosubdub (primeFactors_rec A contextualize Delta).
  Proof.
    elim.
    - move => Delta contextualize prf //=.
      case: (isOmega (contextualize Omega)) => //.
        by apply: addAndFilter_nosubdub.
    - move => ? ? IH *; by apply: IH.
    - move => A _ B IH *.
        by apply: IH.
    - move => A IH__A B IH__B Delta contextualize prf.
      apply: IH__B.
        by apply: IH__A.
    - move => A IH__A B IH__B Delta contextualize prf.
      apply: IH__B.
        by apply: IH__A.
  Qed.

  Lemma primeFactors__notOmega: forall A Delta contextualize,
      all (fun B => ~~ checkSubtypes Omega B) Delta ->
      all (fun B => ~~ checkSubtypes Omega B) (primeFactors_rec A contextualize Delta).
  Proof.
    elim.
    - move => Delta contextualize prf //=.
      case isOmega__A: (isOmega (contextualize Omega)) => [] //=.
      apply /allP => B /addAndFilter_in [].
      + move => ->.
        apply /subtypeMachineP => /subty_complete /Omega__subty devil.
        move: (devil isT).
          by rewrite isOmega__A.
      + by move: prf => /allP prf /prf.
    - move => ? ? IH ? ?.
        by apply: IH.
    - move => ? _ ? IH *.
        by apply: IH.
    - move => ? IH__A ? IH__B *.
      apply: IH__B.
        by apply: IH__A.
    - move => ? IH__A ? IH__B *.
      apply: IH__B.
        by apply: IH__A.
  Qed.
  
  Fixpoint desubdub (Delta: seq (@IT Constructor)): seq (@IT Constructor) :=
    match Delta with
    |[::] => [::]
    |[:: A & Delta'] => if ~~isOmega A then addAndFilter (desubdub Delta') A else desubdub Delta'
    end.

  Lemma desubdub_nosubdub: forall Delta, nosubdub (desubdub Delta).
  Proof.
    elim => //= A Delta IH.
    case: (isOmega A) => //=.
      by apply: addAndFilter_nosubdub.
  Qed.

  Lemma desubdub_all:
    forall Delta p, all p Delta -> all p (desubdub Delta).
  Proof.
    elim => //= A Delta IH p /andP [] pA all__Delta.
    case: (isOmega A) => //=.
    - by apply: IH.
    - apply /allP => B /addAndFilter_in [].
      + by move ->.
      + by move: (IH p all__Delta) => /allP prf /prf.
  Qed.

  Lemma desubdub_leq:
    forall Delta, [bcd (\bigcap_(A__i <- desubdub Delta) A__i) <= \bigcap_(A__i <- Delta) A__i].
  Proof.
    elim => // A Delta IH.
    rewrite /desubdub -/desubdub.
    apply: BCD__Trans; last by apply: (bcd_bigcap_cat _ [:: A]).
    apply: BCD__Glb.
    - case omega__A: (isOmega A).
      + by apply: bcd__omega.
      + apply: bigcap_has_le.
          by apply: addAndFilterLeq__A.
    - case: (isOmega A) => //=.
      apply: BCD__Trans; last by exact IH.
        by apply: addAndFilter_monotonic.
  Qed.

  Lemma desubdub_geq:
    forall Delta, [bcd (\bigcap_(A__i <- Delta) A__i) <= (\bigcap_(A__i <- desubdub Delta) A__i)].
  Proof.
    elim => // A Delta IH.
    rewrite /desubdub -/desubdub.
    case omega__A: (isOmega A).
    - apply: BCD__Trans; first by apply: (bcd_cat_bigcap _ [:: A]).
      by apply: BCD__Trans; first by apply: BCD__Lub2.
    - apply: BCD__Trans; last by apply: addAndFilterGeq.
      apply: BCD__Trans; last by apply: (bcd_bigcap_cat _ [:: A]).
      apply: BCD__Trans; first by apply: (bcd_cat_bigcap _ [:: A]).
      apply: BCD__Glb => //.
        by apply: BCD__Trans; first by apply: BCD__Lub2.
  Qed.

  Lemma addAndFilter_size: forall A Delta,
      seq.size (addAndFilter Delta A) <= seq.size [:: A & Delta].
  Proof.
    move => A.
    elim => //= B Delta IH.
    case: (checkSubtypes B A) => //=.
    case: (checkSubtypes A B) => //=.
      by apply: leq_trans; first by exact IH.
  Qed.

  Lemma desubdub_size: forall Delta, seq.size (desubdub Delta) <= seq.size Delta.
  Proof.
    elim => //= A Delta IH.
    case: (isOmega A).
    - by apply: leq_trans.
    - by apply: leq_trans; first by apply: addAndFilter_size.
  Qed.

  Lemma desubdubb_notOmega:
    forall Delta, all (fun A => ~~isOmega A) (desubdub Delta).
  Proof.
    elim => //= A Delta IH.
    case omega__A: (isOmega A) => //=.
    apply /allP => B /addAndFilter_in [].
    - move => ->.
      by rewrite omega__A.
    - by move: IH => /allP IH /IH.
  Qed.

  Lemma bcd_prime_ge_all:  forall Delta1 Delta2 : seq (@IT Constructor),
      [ bcd (\bigcap_(A__i <- Delta1) A__i) <= \bigcap_(A__i <- Delta2) A__i] ->
      all (fun A => isPrimeComponent A) Delta2 ->
      all (fun A => ~~isOmega A) Delta2 ->
      all (fun B  =>  has (fun A => checkSubtypes A B) Delta1) Delta2.
  Proof.
    move => Delta1.
    elim => // A Delta2 IH.
    move => /(fun prf => BCD__Trans _ prf (bcd_cat_bigcap _ [:: A] Delta2)) prf.
    move: (BCD__Trans _ prf BCD__Lub1)(BCD__Trans _ prf BCD__Lub2) => lprf rprf.
    move => /= /andP [] /isPrimeComponentP prime__A prime__Delta2.
    move => /= /andP [] notOmega__A notOmega__Delta2.
    rewrite (primeComponentPrime_seq _ _ notOmega__A prime__A lprf).
      by rewrite (IH rprf prime__Delta2 notOmega__Delta2).
  Qed.

  Lemma prime_filter_le: forall Delta__prime Delta : seq (@IT Constructor),
      all (fun B => isPrimeComponent B) Delta__prime ->
      all (fun B => ~~isOmega B) Delta__prime ->
      [bcd (\bigcap_(A__i <- Delta) A__i) <= \bigcap_(A__i <- Delta__prime) A__i] ->
      [bcd (\bigcap_(A__i <- [seq A <- Delta | has (fun B => checkSubtypes A B) Delta__prime]) A__i) <= \bigcap_(A__i <- Delta__prime) A__i].
  Proof.
    move => Delta__prime Delta prime notOmega /(fun prf => bcd_prime_ge_all _ _ prf prime notOmega) prf.
    apply: bcd_all_ge.
    suff: {in Delta__prime,
                (fun A => has (fun B => checkSubtypes B A) Delta)
                =1 (fun A => has (fun B => checkSubtypes B A) [seq A <- Delta | has (fun B => checkSubtypes A B) Delta__prime] ) };
      first by move => /eq_in_all <-.
    move => B inprf__B.
    do 2 rewrite has_filter.
    rewrite -filter_predI.
    do 2 rewrite -has_filter.
    suff: {in Delta,
                (fun A => checkSubtypes A B)
                =1 (predI (fun A => checkSubtypes A B) (fun A : IT => has (fun B => checkSubtypes A B) Delta__prime)) };
      first by move => /eq_in_has <-.
    move => A inprf /=.
    move le__AB: (checkSubtypes A B) => [] //=.
    apply /sameP; last by exact hasP.
    apply: introP => // _.
      by exists B.
  Qed.

  Lemma nosubdub_unique: forall (Delta: seq (@IT Constructor)),
      nosubdub Delta ->
      forall A B, A \in Delta -> B \in Delta -> [bcd A <= B] -> A = B.
  Proof.
    elim => // C Delta IH /andP [] nodub__C nodubsub__Delta A B /orP [] prf__A /orP [] prf__B le__AB.
    - by rewrite (eqP prf__A) (eqP prf__B).
    - move: (allP nodub__C B prf__B).
      rewrite -(eqP prf__A).
      move: le__AB => /subtypeMachineP ->.
        by rewrite orbT.
    - move: (allP nodub__C A prf__A).
      rewrite -(eqP prf__B).
        by move: le__AB => /subtypeMachineP ->.
    - by apply: IH.
  Qed.

  Lemma nosubdub_prime_injective:
    forall Delta1 Delta2 : seq (@IT Constructor),
      nosubdub Delta1 ->
      nosubdub Delta2 ->
      all (fun A => isPrimeComponent A) Delta1 ->
      all (fun A => ~~isOmega A) Delta1 ->
      [bcd (\bigcap_(A__i <- Delta2) A__i) <= (\bigcap_(A__i <- Delta1) A__i)] ->
      forall A1 A2 B,
        A1 \in Delta1 -> A2 \in Delta1 -> B \in Delta2 -> [bcd A1 <= B] -> [bcd A2 <= B] -> A1 = A2.
  Proof.
    move => Delta1 Delta2 nosubdub__Delta1 nosubdub__Delta2 prime__Delta1 notOmega__Delta1 le21.
    move => A1 A2 B inprf__A1 inprf__A2 inprf__B le__AB le__BA.
    have: [bcd B <= A2].
    { move: (bcd_prime_ge_all _ _ le21 prime__Delta1 notOmega__Delta1) => /allP /(fun prf => prf A2 inprf__A2) /hasP [] B2 inprf__B2.
      move => /subtypeMachineP le__B2A2.
      move: (BCD__Trans _ le__B2A2 le__BA).
        by move => /(nosubdub_unique _ nosubdub__Delta2 _ _ inprf__B2 inprf__B) <-. }
    move => /(BCD__Trans _ le__AB).
      by move => /(nosubdub_unique _ nosubdub__Delta1 _ _ inprf__A1 inprf__A2).
  Qed.

  Lemma nosubdub_prime_bijective:
    forall Delta1 Delta2 : seq (@IT Constructor),
      nosubdub Delta1 ->
      nosubdub Delta2 ->
      all (fun A => isPrimeComponent A) Delta2 ->
      all (fun A => ~~isOmega A) Delta2 ->
      [bcd (\bigcap_(A__i <- Delta2) A__i) <= (\bigcap_(A__i <- Delta1) A__i)] ->
      [bcd (\bigcap_(A__i <- Delta1) A__i) <= (\bigcap_(A__i <- Delta2) A__i)] ->
      forall A B,
        A \in Delta1 -> B \in Delta2 -> [bcd B <= A] -> [bcd A <= B].
  Proof.
    move => Delta1 Delta2 nosubdub__Delta1 nosubdub__Delta2 prime__Delta2 notOmega__Delta2 le21 le12.
    move => A B inprf__A inprf__B le__BA.
    move: (bcd_prime_ge_all _ _ le12 prime__Delta2 notOmega__Delta2) => /allP /(fun prf => prf B inprf__B) /hasP [] A2 inprf__A2.
    move => /subtypeMachineP le__A2B.
    move: (BCD__Trans _ le__A2B le__BA).
      by move => /(nosubdub_unique _ nosubdub__Delta1 _ _ inprf__A2 inprf__A) <-.
  Qed.

  Inductive PermUpToSubtyping: seq (@IT Constructor) -> seq (@IT Constructor) -> Prop :=
  | PermNil : PermUpToSubtyping [::] [::]
  | PermCons : forall A B Delta1 Delta21 Delta22,
      [bcd A <= B] -> [bcd B <= A] -> PermUpToSubtyping Delta1 (Delta21 ++ Delta22) ->
      PermUpToSubtyping [:: A & Delta1] (Delta21 ++ [:: B & Delta22]).

  Fixpoint splitcat_rec (A: Type) (p: pred A) (xs: seq A) (prefix: seq A):
    option (seq A * A * seq A) :=
    if xs is [:: x & xs]
    then if p x then some (prefix, x, xs) else splitcat_rec A p xs (rcons prefix x)
    else None.

  Definition splitcat {A: Type} p xs := splitcat_rec A p xs [::].

  Lemma splitcat_rec_eq: forall {A} p (xs: seq A) prefix,
      has p xs ->
      omap (fun ys => ys.1.1 ++ [:: ys.1.2 & ys.2]) (splitcat_rec A p xs prefix)
      = some (prefix ++ xs).
  Proof.
    move => A p.
    elim => // x xs IH prefix /=.
    case (p x) => //= /(IH (rcons prefix x)) ->.
      by rewrite cat_rcons.
  Qed.

  Lemma splitcat_rec_p: forall {A} p (xs: seq A) (prefix: seq A),
      if (splitcat_rec A p xs prefix) is Some (ys1, y, ys2) then p y else ~~ has p xs.
  Proof.
    move => A p.
    elim => //= x xs IH prefix //=.
      by move px: (p x) => [].
  Qed.

  Lemma splitcat_eq: forall {A} p (xs: seq A),
      has p xs ->
      omap (fun ys => ys.1.1 ++ [:: ys.1.2 & ys.2]) (splitcat p xs) = some xs.
  Proof. by move => *; apply: splitcat_rec_eq. Qed.

  Lemma splitcat_p: forall {A} p (xs: seq A),
      has p xs ->
      if (splitcat p xs) is Some (ys1, y, ys2) then p y else ~~ has p xs.
  Proof. by move => *; apply: splitcat_rec_p. Qed.

  Lemma nosubdub_weaken: forall Delta1 Delta2,
      subseq Delta1 Delta2 ->
      nosubdub Delta2 -> nosubdub Delta1.
  Proof.
    move => Delta1 Delta2.
    move: Delta1.
    elim: Delta2.
    - move => Delta1.
        by rewrite subseq0 => /eqP ->.
    - move => // B Delta2 IH [] // A Delta1.
      rewrite /subseq -/subseq.
      case AB__eq: (A == B).
      + move: AB__eq => /eqP -> subseq__12.
        move: (IH _ subseq__12) => prf /andP [] notin__B /prf /= ->.
        rewrite andbT.
        apply /allP => x inprf.
        move: (mem_subseq subseq__12 inprf).
          by move: notin__B => /allP notin__B /notin__B.
      + by move => /IH prf /andP [] _ /prf.
  Qed.

  Lemma bcd_prime_strengthen:
    forall Delta11 (A: @IT Constructor) Delta12 Delta2,
      all (fun B => isPrimeComponent B) Delta2 ->
      all (fun B => ~~checkSubtypes A B) Delta2 ->
      [bcd (\bigcap_(A_i <- Delta11 ++ [:: A & Delta12]) A_i) <= \bigcap_(A_i <- Delta2) A_i] ->
      [bcd (\bigcap_(A_i <- Delta11 ++ Delta12) A_i) <= \bigcap_(A_i <- Delta2) A_i].
  Proof.
    move => Delta11 A Delta12 Delta2 prime__Delta2 notle__ADelta2 le12.
    have: [bcd (A \cap \bigcap_(A_i <- Delta11 ++ Delta12) A_i) <= \bigcap_(A_i <- Delta2) A_i].
    { apply: BCD__Trans; last by apply le12.
      apply: BCD__Trans; last by apply bcd_bigcap_cat.
      apply: BCD__Glb.
      - apply: BCD__Trans; last by apply: (BCD__Lub2).
        apply: BCD__Glb => //.
        apply: BCD__Trans; first by apply: BCD__Lub2.
          by apply: BCD__Trans; first by apply: bcd_cat_bigcap.
      - apply: BCD__Trans; last by apply: (bcd_bigcap_cat _ [:: A]).
        apply: BCD__Glb => //.
        apply: BCD__Trans; first by apply: BCD__Lub2.
          by apply: BCD__Trans; first by apply: bcd_cat_bigcap. }
    move: le12 prime__Delta2 notle__ADelta2 => _.
    elim: Delta2.
    - rewrite //=.
    - move => B Delta2 IH prime__BDelta2 notle__ABDelta2.
      move => /(fun prf => BCD__Trans _ prf (bcd_cat_bigcap _ [:: B] Delta2)) le12.
      apply: BCD__Trans; last by apply: (bcd_bigcap_cat _ [:: B]).
      apply: BCD__Glb.
      + move: prime__BDelta2 => /andP [] /isPrimeComponentP prime__B _.
        move: le12 => /(fun prf => BCD__Trans _ prf BCD__Lub1).
        move => /(fun prf => primeComponentPrime _ _ _ prf prime__B) [] //.
          by move: notle__ABDelta2 => /andP [] /subtypeMachineP.
      + apply: IH => //.
        * by move: prime__BDelta2 => /andP [].
        * by move: notle__ABDelta2 => /andP [].
        * by apply: BCD__Trans; first by exact le12.
  Qed.

  Lemma nosubdub_everywhere:
    forall Delta1 A Delta2,
      nosubdub (Delta1 ++ [:: A & Delta2]) ->
      all (fun B => ~~ ((checkSubtypes B A) || (checkSubtypes A B))) (Delta1 ++ Delta2).
  Proof.
    elim.
    - by move => A Delta2 /andP [].
    - move => B Delta1 IH A Delta2 /= /andP [] /allP prf /IH ->.
      rewrite andbT.
      move: (prf A).
      rewrite mem_cat mem_head orbT.
      move => /(fun prf => prf isT) /norP []  notAB notBA.
      apply /norP.
      rewrite notAB notBA.
        by apply /andP.
  Qed.

  Lemma nosubdub_prime_perm:
    forall Delta1 Delta2 : seq (@IT Constructor),
      nosubdub Delta1 ->
      nosubdub Delta2 ->
      all (fun A => isPrimeComponent A) Delta1 ->
      all (fun A => isPrimeComponent A) Delta2 ->
      all (fun A => ~~isOmega A) Delta1 ->
      all (fun A => ~~isOmega A) Delta2 ->
      [bcd (\bigcap_(A__i <- Delta1) A__i) <= (\bigcap_(A__i <- Delta2) A__i)] ->
      [bcd (\bigcap_(A__i <- Delta2) A__i) <= (\bigcap_(A__i <- Delta1) A__i)] ->
      PermUpToSubtyping Delta1 Delta2.
  Proof.
    elim.
    - move => Delta2 _ nosubdub__Delta2 _ prime__Delta2 _ notOmega__Delta2.
      move => /(fun prf => bcd_prime_ge_all _ _ prf prime__Delta2 notOmega__Delta2).
      clear ...
      case Delta2 => // *.
      apply: PermNil.
    - move => A Delta1 IH Delta2.
      move => nosubdub__Delta1 nosubdub__Delta2 prime__Delta1 prime__Delta2
                            notOmega__Delta1 notOmega__Delta2.
      move => le__A12 le__2A1.
      move: (bcd_prime_ge_all _ _ le__2A1 prime__Delta1  notOmega__Delta1) => /andP [] has__ADelta2.
      move: (splitcat_p _ Delta2 has__ADelta2).
      move: (splitcat_eq _ Delta2 has__ADelta2).
      case: (splitcat (fun B => checkSubtypes B A) Delta2) => // [] [] [] Delta21 B Delta22 [] eq__Delta2.
      rewrite -eq__Delta2.
      move => /subtypeMachineP le__BA all__Delta1.
      apply: PermCons => //.
      + apply: (nosubdub_prime_bijective [:: A & Delta1] Delta2) => //.
        * by rewrite in_cons eq_refl.
        * by rewrite -eq__Delta2 mem_cat in_cons eq_refl orbT.
      + apply: IH.
        * by move: nosubdub__Delta1 => /andP [].
        * move: nosubdub__Delta2.
          rewrite -eq__Delta2.
          move => /(nosubdub_weaken (Delta21 ++ Delta22)) prf.
          apply: prf.
          apply: cat_subseq => //.
            by apply subseq_cons.
        * by move: prime__Delta1 => /andP [].
        * move: prime__Delta2.
          rewrite -eq__Delta2  all_cat all_cat.
          move => /andP [] -> /andP [] _.
          rewrite /all.
            by move => ->.
        * by move: notOmega__Delta1 => /andP [].
        * move: notOmega__Delta2.
          rewrite -eq__Delta2  all_cat all_cat.
          move => /andP [] -> /andP [] _.
          rewrite /all.
            by move => ->.
        * apply: (bcd_prime_strengthen [::] A Delta1).
          ** move: prime__Delta2.
             rewrite -eq__Delta2  all_cat all_cat.
             move => /andP [] -> /andP [] _.
             rewrite /all.
               by move => ->.
          ** move: nosubdub__Delta2.
             rewrite -eq__Delta2.
             move => /(nosubdub_everywhere) /sub_all prf.
             apply: prf => C /norP [] _ /negP disprf.
             apply /negP => /subtypeMachineP prf.
             apply disprf.
               by move: (BCD__Trans _ le__BA prf) => /subtypeMachineP.
          ** apply: BCD__Trans; first by exact le__A12.
             rewrite -eq__Delta2.
             apply: BCD__Trans; last by apply: bcd_bigcap_cat.
             apply: BCD__Trans; first by apply: bcd_cat_bigcap.
             apply: BCD__Glb => //.
             apply: BCD__Trans; first by apply: BCD__Lub2.
               by apply: BCD__Trans; first by apply: (bcd_cat_bigcap _ [:: B]).
        * apply: (bcd_prime_strengthen Delta21 B Delta22).
          ** by move: prime__Delta1 => /andP [].
          ** have: [bcd A <= B].
             { apply: (nosubdub_prime_bijective [:: A & Delta1] Delta2) => //.
               - by apply: mem_head.
               - by rewrite -eq__Delta2 mem_cat mem_head orbT. }
             move: nosubdub__Delta1 => /andP [] prf _ le__AB.
             apply: sub_all; last by exact prf.
             move => C /norP [] nle__CA /negP nle__AC.
             apply /negP => /subtypeMachineP le__BC.
             apply nle__AC.
             apply /subtypeMachineP.
               by apply: BCD__Trans; first by exact le__AB.
          ** rewrite eq__Delta2.
             apply: BCD__Trans; first by exact le__2A1.
               by apply: BCD__Trans; first by apply: (bcd_cat_bigcap _ [:: A]).
  Qed.

  Lemma PermUpToSubtyping_size: forall Delta1 Delta2,
      PermUpToSubtyping Delta1 Delta2 -> seq.size Delta1 = seq.size Delta2.
  Proof.
    move => Delta1 Delta2.
    elim => // A B Delta Delta21 Delta22 _ _ _ IH.
    rewrite size_cat /= addnS -size_cat.
      by apply: (f_equal (fun x => x.+1)).
  Qed.

  Definition primeFactors (A: @IT Constructor): seq (@IT Constructor) :=
    primeFactors_rec A id [::].

  Lemma primeFactors_geq: forall A, [bcd A <= \bigcap_(P__i <- primeFactors A) P__i ].
  Proof.
    move => A.
    rewrite /primeFactors.
      by apply: (primeFactors_rec_geq A [::]).
  Qed.

  Lemma primeFactors_leq: forall A, [bcd (\bigcap_(P__i <- primeFactors A) P__i) <= A ].
  Proof.
    move => A.
    rewrite /primeFactors.
      by apply: (primeFactors_rec_leq A [::]).
  Qed.

  Lemma primeFactors_prime:
    forall A, all (fun B => isPrimeComponent B) (primeFactors A).
  Proof.
    move => A.
    rewrite /primeFactors.
      by apply: (primeFactors_rec_prime A [::]).
  Qed.

  Lemma primeFactors_minimal:
    forall A Delta,
      all (fun B => isPrimeComponent B) Delta ->
      [bcd (\bigcap_(A_i <- Delta) A_i) <= A] ->
      [bcd A <= (\bigcap_(A_i <- Delta) A_i)] ->
      seq.size (primeFactors A) <= seq.size Delta.
  Proof.
    move => A Delta prime__Delta le__DeltaA le__ADelta.
    apply: leq_trans; last by apply: desubdub_size.
    apply: eq_leq.
    apply: PermUpToSubtyping_size.
    apply: nosubdub_prime_perm.
    - by apply: primeFactors_nosubdub.
    - by apply: desubdub_nosubdub.
    - by apply: primeFactors_prime.
    - by apply: desubdub_all.
    - rewrite /primeFactors.
      apply: sub_all; last by apply: (primeFactors__notOmega A [::] id isT).
      move => B /negP notOmega.
      apply /negP => omega__B.
        by move: (bcd__omega _ Omega B omega__B) => /subtypeMachineP.
    - by apply: desubdubb_notOmega.
    - apply: BCD__Trans; first by apply: primeFactors_leq.
        by apply: BCD__Trans; last by apply: desubdub_geq.
    - apply: BCD__Trans; last by apply: primeFactors_geq.
        by apply: BCD__Trans; first by apply: desubdub_leq.
  Qed.
End PrimalityLemmas.

Arguments PrimeComponent [Constructor].
Arguments isPrimeComponent [Constructor].
Arguments isPrimeComponentP [Constructor] [A].
Arguments primeFactors [Constructor].
Arguments primeFactors_leq [Constructor].
Arguments primeFactors_geq [Constructor].
Arguments primeFactors_prime [Constructor].
Arguments primeFactors_minimal [Constructor].


(*




  Inductive Cover : Type :=
  | SplitCover 
      (splits : seq (MultiArrow * seq (@IT Constructor)))
      (toCover : seq (@IT Constructor))
      (currentResult : option MultiArrow)
      (delta: seq MultiArrow) : Cover
  | ContinueToCover (task: Cover)
                    (continue: seq MultiArrow -> Cover): Cover
  | CoverResult (delta: seq MultiArrow): Cover.

  Definition paritionCover
             (covered: seq (@IT Constructor))
             (toCover: seq (@IT Constructor)): seq (@IT Constructor) * seq (@IT Constructor) :=
    foldr (fun A s =>
                 if A \in covered
                 then ([:: A & s.1], s.2)
                 else (s.1, [:: A & s.2])) ([::], [::]) toCover.

  Definition changedCover
             (covered: seq (@IT Constructor))
             (toCover: seq (@IT Constructor)): option (seq (@IT Constructor)) :=
    let (coveredFresh, uncovered) := paritionCover covered toCover in
    if coveredFresh is [::] then None else Some uncovered.

  

  Definition mergeMultiArrow
             (arrow: MultiArrow)
             (srcs: seq (@IT Constructor))
             (tgt: @IT Constructor): MultiArrow :=
      (map (fun src => src.1 \cap src.2) (zip srcs arrow.1), tgt \cap arrow.2).

  Fixpoint cover (splits : seq (MultiArrow * seq (@IT Constructor)))
           (toCover : seq (@IT Constructor))
           (currentResult : option MultiArrow)
           (Delta: seq MultiArrow): seq MultiArrow :=
    if splits is [:: (srcs, tgt, covered) & splits]
    then
      match changedCover covered toCover, currentResult with
      | Some [::], None =>
        [:: (srcs, tgt) & cover splits toCover currentResult Delta]
      | Some [::], Some result =>
        [:: (mergeMultiArrow result srcs tgt) & cover splits toCover currentResult Delta]
      | Some remaining, Some (currentSources, currentTarget) =>
        if all (fun AB => checkSubtypes _ AB.1 AB.2) (zip currentSources srcs)
        then cover splits remaining (Some (currentSources, tgt \cap currentTarget)) Delta
        else
          cover splits remaining
                       (Some (mergeMultiArrow (currentSources, currentTarget) srcs tgt))
                       (cover splits toCover currentResult Delta)
      | Some remaining, None =>
        cover splits remaining (Some (srcs, tgt))
              (cover splits toCover currentResult Delta)
      | None, _ =>
        cover splits toCover currentResult Delta
      end
    else Delta.

  Lemma partitionCover_filter:
    forall covered toCover,
      paritionCover covered toCover = (filter (fun A => A \in covered) toCover,
                                       filter (fun A => A \notin covered) toCover).
  Proof.
    move => covered toCover.
    rewrite /paritionCover.
    rewrite -[X in _ = (X, _)](cats0) -[X in _ = (_, X)](cats0).
    set l := (X in foldr _ (X, _) _ = (_ ++ X, _)).
    set r := (X in foldr _ (_, X) _ = (_, _ ++ X)).
    move: l r.
    elim: toCover => //= A toCover IH l r.
    rewrite (IH l r).
      by case: (A \in covered).
  Qed.        

  Lemma changedCover_le:
    forall covered toCover A B,
      [bcd A <= \bigcap_(A_i <- covered) A_i] ->
      [bcd B <= \bigcap_(A_i <- if changedCover covered toCover is Some remaining then remaining else toCover) A_i] ->
      [bcd (if changedCover covered toCover is Some _ then (A \cap B) else B) <= \bigcap_(A_i <- toCover) A_i].
  Proof.
    move => covered toCover.
    rewrite /changedCover partitionCover_filter.
    move => A B le__Acovered le__Brest.
    apply: BCD__Trans;
      last apply: (bcd_all_ge _ (filter (fun A => A \in covered) toCover ++ filter (fun A => A \notin covered) toCover)).
    - apply: BCD__Trans; last by apply: bcd_bigcap_cat.
      apply: BCD__Glb.
      + move: le__Acovered le__Brest.
        case filter_eq: (filter (fun A => A \in covered) toCover); first by rewrite /=.
        rewrite -filter_eq.
        move => le__Acovered _.
        apply: BCD__Trans; first by apply: BCD__Lub1.
        apply: BCD__Trans; first by exact le__Acovered.
        apply: bcd_all_ge.
        apply /allP => C inprf.
          apply /hasP.
          exists C.
          ** move: inprf.
               by rewrite mem_filter => /andP [].
          ** by apply /subtypeMachineP.
      + move: le__Brest.
        case: (filter (fun A => A \in covered) toCover).
        * move => le__Brest.
          apply: BCD__Trans; first by exact le__Brest.
          apply: bcd_all_ge.
          apply /allP => C inprf.
          apply /hasP.
          exists C.
          ** move: inprf.
               by rewrite mem_filter => /andP [].
          ** by apply /subtypeMachineP.
        * move => *.
            by apply: BCD__Trans; first by apply: BCD__Lub2.
    - apply /allP => C inprf.
      apply /hasP.
      exists C; last by apply /subtypeMachineP.
        by rewrite mem_cat mem_filter mem_filter inprf andbT andbT orbN.
  Qed.


  Lemma cover_current_le_tgt_or_inDelta:
    forall splits toCover currentResult Delta,
      all (fun A => checkSubtypes _ A.2 currentResult.2 || (A \in Delta))
          (cover splits toCover (Some currentResult) Delta).
  Proof.
    elim.
    - move => /= _ ? Delta.
      apply: sub_all; last by (apply /allP => x inprf; exact inprf).
      move => ? ->.
        by rewrite orbT.
    - move => [] [] srcs tgt covered splits IH toCover.
      case;
        rewrite /=; case (changedCover covered toCover).
      + case.
        * move => ? currentTgt Delta.
          rewrite /=.
          move: (@BCD__Lub2 _ tgt currentTgt) => /subtypeMachineP -> /=.
            by apply: IH.
        * move => A remaining currentSrcs currentTgt Delta.
          case: (all (fun AB => checkSubtypes Constructor AB.1 AB.2) (zip currentSrcs srcs)).
          ** apply: sub_all; last by apply: IH.
             move => B /orP [].
             *** by move => /subtypeMachineP /(fun prf => BCD__Trans _ prf BCD__Lub2) /subtypeMachineP ->.
             *** by move => ->; rewrite orbT.
          ** apply: sub_all; last by apply: IH.
             move => B /orP [].
             *** by move => /subtypeMachineP /(fun prf => BCD__Trans _ prf BCD__Lub2) /subtypeMachineP ->.
             *** move: B.
                 apply: allP.
                   by apply: IH.
      + move => *.
          by apply: IH.
  Qed.

  Lemma cover_le:
    forall splits toCover currentResult Delta,
      all (fun split => checkSubtypes _ split.1.2 (\bigcap_(A_i <- split.2) A_i)) splits ->
      all (fun A => checkSubtypes _ A.2 (\bigcap_(A_i <- toCover) A_i)) Delta ->
      all (fun A => checkSubtypes _ A.2 (\bigcap_(A_i <- toCover) A_i))
          (cover splits toCover currentResult Delta).
  Proof.
    elim => // [] [] [] srcs tgt covered splits IH toCover.
    have le__toCoverRemaining:
      (if changedCover covered toCover is Some remaining
       then [bcd (\bigcap_(A_i <- toCover) A_i) <= (\bigcap_(A_i <- remaining) A_i)]
       else true).
    { rewrite /changedCover partitionCover_filter.
      case filter_eq: (filter (fun A => A \in covered) toCover) => //.
      apply: bcd_all_ge.
      apply /allP => C inprf.
      apply /hasP.
      exists C; last by apply /subtypeMachineP.
      move: inprf.
        by rewrite mem_filter => /andP [] _ ->. }
    move => currentResult Delta /andP [] /subtypeMachineP le__Acovered le__splits le__Delta.
    have:
      (if changedCover covered toCover is Some remaining
       then all (fun A => checkSubtypes Constructor A.2 (\bigcap_(A_i <- remaining) A_i))
                Delta
       else true).
    { move: le__toCoverRemaining.
      rewrite /changedCover partitionCover_filter.
      case filter_eq: (filter (fun A => A \in covered) toCover) => //.
      move => le__toCoverRemaining.
      apply: sub_all; last by exact le__Delta.
      move => AB /subtypeMachineP prf.
      apply /subtypeMachineP.
        by apply: BCD__Trans; first by exact prf. }
    case: currentResult.
    - move => A.
      move: (fun B => changedCover_le covered toCover tgt B  le__Acovered).
      rewrite /cover -/cover.
      move: le__toCoverRemaining.
      case: (changedCover covered toCover).
      + case.
        * move => _ /(fun prf => prf A.2 BCD__omega) /subtypeMachineP /= -> /= _.
            by apply: IH.
        * move: A le__Acovered => [] srcs__A tgt__A le__Acovered.
          case: (all (fun AB => checkSubtypes Constructor AB.1 AB.2) (zip srcs__A srcs)).
          ** move => B remaining _ prf le__Deltaremaining.
             apply /allP => AB inprf.
             move: (IH [:: B & remaining] (Some (srcs__A, tgt \cap tgt__A)) Delta le__splits le__Deltaremaining).
             move => /allP /(fun prf => prf AB inprf) /subtypeMachineP /(prf _) le__tgtB.
             move: (cover_current_le_tgt_or_inDelta splits [:: B & remaining] (srcs__A, tgt \cap tgt__A) Delta).
             move => /allP /(fun prf => prf AB inprf) /orP [].
             *** move => /subtypeMachineP /= le__ABtgt.
                 apply /subtypeMachineP.
                 apply: BCD__Trans; last by exact le__tgtB.
                 apply: BCD__Glb => //.
                   by apply: BCD__Trans; first by exact le__ABtgt.
             *** by move: le__Delta => /allP /(fun prf => prf AB).
          ** move => B remaining le__toCoverRemaining prf le__Deltaremaining.
             apply /allP => AB inprf.
             move: (cover_current_le_tgt_or_inDelta splits
                                                    [:: B & remaining]
                                                    (mergeMultiArrow (srcs__A, tgt__A) srcs tgt)
                                                    (cover splits toCover (Some (srcs__A, tgt__A)) Delta)).
             move: (IH toCover (Some (srcs__A, tgt__A)) Delta le__splits le__Delta).
             move => le__Delta2.
             move => /allP /(fun prf => prf AB inprf) /orP [].
             *** move => /subtypeMachineP /= le__ABtgt.
                 apply /subtypeMachineP.
                 have: all (fun AB => checkSubtypes _ AB.2 (\bigcap_(A_i <- [:: B & remaining]) A_i))
                           (cover splits toCover (Some (srcs__A, tgt__A)) Delta).
                 { apply: sub_all; last by exact le__Delta2.
                   move => CD /subtypeMachineP prf2.
                   apply /subtypeMachineP.
                     by apply: BCD__Trans; first by exact prf2. }
                 move => /(IH [:: B & remaining]
                             (Some (mergeMultiArrow (srcs__A, tgt__A) srcs tgt))
                             (cover splits toCover (Some (srcs__A, tgt__A)) Delta)
                             le__splits).
                 move => /allP /(fun prf => prf AB inprf) /subtypeMachineP /(prf _) le__tgtB.
                 apply: BCD__Trans; last by exact le__tgtB.
                 apply: BCD__Glb => //.
                   by apply: BCD__Trans; first by exact le__ABtgt.
             *** by move => /(allP le__Delta2 AB).
      + move => *; by apply IH.
    - move: (fun B => changedCover_le covered toCover tgt B  le__Acovered).
      rewrite /cover -/cover.
      move: le__toCoverRemaining.
      case: (changedCover covered toCover).
      + case.
        * move => _ /(fun prf => prf Omega BCD__Refl) /(BCD__Trans _ (BCD__Glb BCD__Refl BCD__omega)) /subtypeMachineP /= -> /= _.
            by apply: IH.
        * move => B remaining le__toCoverRemaining prf le__Deltareamaining.
          apply /allP => AB inprf.
          move: (cover_current_le_tgt_or_inDelta splits
                                                 [:: B & remaining]
                                                 (srcs, tgt)
                                                 (cover splits toCover None Delta)).
          move: (IH toCover None Delta le__splits le__Delta).
          move => le__Delta2.
          move => /allP /(fun prf => prf AB inprf) /orP [].
          ** move => /subtypeMachineP /= le__ABtgt.
             apply /subtypeMachineP.
             have: all (fun AB => checkSubtypes _ AB.2 (\bigcap_(A_i <- [:: B & remaining]) A_i))
                       (cover splits toCover None Delta).
             { apply: sub_all; last by exact le__Delta2.
               move => CD /subtypeMachineP prf2.
               apply /subtypeMachineP.
                 by apply: BCD__Trans; first by exact prf2. }
             move => /(IH [:: B & remaining]
                         (Some (srcs, tgt))
                         (cover splits toCover None Delta)
                         le__splits).
             move => /allP /(fun prf => prf AB inprf) /subtypeMachineP /(prf _) le__tgtB.
             apply: BCD__Trans; last by exact le__tgtB.
               by apply: BCD__Glb.
          ** by move => /(allP le__Delta2 AB).
      + move => *; by apply /IH .
  Qed.

  Definition splitMultiArrow (arr: MultiArrow): option (MultiArrow * MultiArrow) :=
    foldr (fun src res =>
             match src with
             | A \cap B => omap (fun r => (([:: A & r.1.1], r.1.2), ([:: B & r.2.1], r.2.2))) res
             | _ => None
             end)
          (match arr.2 with
           | A \cap B => Some (([::], A), ([::], B))
           | _ => None
           end)
          arr.1.

  Fixpoint isMultiArrowSelection (splits: seq MultiArrow) (arr: MultiArrow): bool :=
    match splits with
    | [::] => false
    | [:: (srcs, tgt) & splits] =>
      ((srcs, tgt) == arr)
      || if splitMultiArrow arr is Some (arr1, arr2)
        then
          (arr1.2 == tgt)
            && ((arr1.1 == srcs) && isMultiArrowSelection splits arr2)
                || ((all (fun AB => checkSubtypes _ AB.1 AB.2) (zip srcs arr1.1)) && isMultiArrowSelection splits (arr.1, arr2.2))
        else false
    end.

  Definition mkArrow (B: @IT Constructor) (srcs: seq (@IT Constructor)): @IT Constructor :=
    foldr (fun A B => A -> B) B srcs.

  Lemma isMultiArrowSelection_ge:
    forall splits arr,
      \bigcap_(A_i <- splits) (mkArrow 

  Definition cover_naive
           (splits : seq (MultiArrow * seq (@IT Constructor)))
           (toCover : seq (@IT Constructor)) :=
    [set selection in powerset [set: seq_sub splits] |  [set: seq_sub toCover] \subset (imset (fun B => [set: seq_sub B.2])
                                                                                              selection)].


  Lemma cover_complete:
    forall splits toCover currentResult Delta selection,
      subseq selection splits ->

      has (fun AB => checkSubtypes (mkArrow AB.2 AB.1) () ) (cover splits toCover currentResult Delta)

  Fixpoint rightAssocIntersectionOf (A: @IT Constructor) (Delta: seq (@IT Constructor)): bool :=
    match A with
    | A \cap B => (A \in Delta) && rightAssocIntersectionOf B Delta
    | A => A \in Delta
    end.

  Definition mkArrow (B: @IT Constructor) (srcs: seq (@IT Constructor)): @IT Constructor :=
    foldr (fun A B => A -> B) B srcs.

  Definition joinedArrowOf (A: MultiArrow) (Delta: seq MultiArrow) :=
    rightAssocIntersectionOf (mkArrow A.2 A.1) (map (fun A => mkArrow A.2 A.1) Delta).

  Definition SoundArrow
             (splits: seq MultiArrow)
             (toCover: seq (@IT Constructor))
             (A: MultiArrow): bool :=
    (checkSubtypes _ A.2 (\bigcap_(A_i <- toCover) A_i))
      && joinedArrowOf A splits.

  Lemma joinedArrowOf_nil: forall A, joinedArrowOf A [::] = false.
  Proof.
    case => srcs tgt.
    rewrite /joinedArrowOf /=.
    elim: srcs => //=.
      by elim: tgt.
  Qed.


  Lemma cover_sound:
    forall splits toCover currentResult Delta,
      all (SoundArrow (map (fun x => x.1) splits) toCover) Delta ->
      if currentResult is Some A
      then
        joinedArrowOf A (map (fun x => x.1) splits)
        -> all (SoundArrow [:: A & map (fun x => x.1) splits] toCover) (cover splits toCover (Some A) Delta)
      else all (SoundArrow (map (fun x => x.1) splits) toCover) (cover splits toCover None Delta).
  Proof.
    elim.
    - move => toCover [] A //.
      case => //= [] [] srcs tgt Delta.
        by rewrite joinedArrowOf_nil.
    - move => [] [] srcs tgt covered splits IH toCover [].
      + 
      

  Lemma splitTy_le: forall A B srcs Delta,
      subseq Delta (nth [::] (splitTy A) (length srcs)) ->
      [bcd A <= mkArrow B srcs] ->
      [bcd (\bigcap_(A_i <- Delta) (mkArrow A_i.2 A_i.1)) <= mkArrow B srcs].
  Proof.



  (**)
End Split. *)

Section NatConstructors.
  Lemma leq_transb: forall (m n p: nat), (m <= n) && (n <= p) ==> (m <= p).
  Proof.
    move => m n p.
    move: (@leq_trans n m p).
    case (m <= n) => //=.
    case (n <= p) => //= prf.
      by apply: prf.
  Qed.

  Definition nat_ctorMixin :=
    Constructor.Mixin nat_countType
                      leq leqnn leq_transb.
  Canonical nat_ctorType := Eval hnf in CtorType nat_countType nat_ctorMixin.
End NatConstructors.

Section PrimeFactorTest.
  Definition A := Ctor 1 Omega -> Ctor 1 Omega.
  Definition B := Ctor 1 Omega.
  Definition C := Ctor 2 Omega -> Ctor 0 Omega.
  Definition D := Ctor 3 (A \times C).

  Example test := primeFactors (A \cap B \cap C \cap D).
End PrimeFactorTest.

Require Extraction.
Extraction Language Ocaml.
Recursive Extraction subtype_machine.

Extraction Language Haskell.
Recursive Extraction subtype_machine.
Recursive Extraction test.

(*
    Variable k1 k2 k3 k4 k5 k6 k7 k8 k9 : nat.
    Variable k1_gt0: k1 > 0.
    Variable k2_gt0: k2 > 0.
    Variable k3_gt0: k3 > 0.
    Variable k4_gt0: k4 > 0.
    Variable k5_gt0: k5 > 0.
    Variable k6_gt0: k6 > 0.
    Variable k7_gt0: k7 > 0.
    Variable k8_gt0: k8 > 0.
    Variable k9_gt0: k9 > 0.

    Fixpoint length (A: @IT Constructor): nat :=
      match A with
      | A1 -> A2 => 1 + length A2
      | A1 \cap A2 => (length A1) + (length A2)
      | _ => 1
      end.

    Fixpoint breadth (A: @IT Constructor): nat :=
      match A with
      | A1 \cap A2 => breadth A1 + breadth A2
      | _ => 1
      end.

    Reserved Notation "A '~~>[' n ']' B" (at level 70, no associativity).
    Inductive CostIndexedSemantics : @Instruction Constructor -> @Result Constructor -> nat -> Prop :=
    | istep__Omega : forall A, [subty A of Omega ] ~~>[1] Return true
    | istep__Ctor: forall A b B (r: bool) n,
        [subty (\bigcap_(A__i <- cast (Ctor b B) A) A__i) of B] ~~>[n] Return r ->
        [subty A of Ctor b B] ~~>[(k1 * (breadth A + length (Ctor b B)) + k2 * (breadth A) + k3) + n] Return (~~nilp (cast (Ctor b B) A) && r)
    | istep__Arr: forall A B1 B2 Delta (r: bool) m n,
        [tgt_for_srcs_gte B1 in cast (B1 -> B2) A] ~~>[m] [check_tgt Delta] ->
        [subty (\bigcap_(A__i <- Delta) A__i) of B2] ~~>[n] Return r ->
        [subty A of B1 -> B2] ~~>[(k1 * (breadth A + length (B1 -> B2)) + k4 * breadth A + k5 * (length B2)) + (m + n)] Return (isOmega B2 || r)
    | istep__chooseTgt: forall B A Delta Delta' (r: bool) m n,
        [subty B of A.1] ~~>[m] Return r ->
        [tgt_for_srcs_gte B in Delta] ~~>[n] [check_tgt Delta'] ->
        [tgt_for_srcs_gte B in [:: A & Delta ]] ~~>[k6 + (m + n)] [check_tgt if r then [:: A.2 & Delta'] else Delta' ]
    | istep__doneTgt: forall B, [tgt_for_srcs_gte B in [::]] ~~>[1] [check_tgt [::]]
    | istep__Prod: forall A B1 B2 (r1 r2: bool) m n,
        [subty (\bigcap_(A__i <- cast (B1 \times B2) A) A__i.1) of B1] ~~>[m] Return r1 ->
        [subty (\bigcap_(A__i <- cast (B1 \times B2) A) A__i.2) of B2] ~~>[n] Return r2 ->
        [subty A of B1 \times B2] ~~>[(k1 * (breadth A + length (B1 \times B2)) + 2 * k7 * breadth A + k8) + (m + n)] Return (~~nilp (cast (B1 \times B2) A) && r1 && r2)
    | istep__Inter: forall A B1 B2 (r1 r2: bool) m n,
        [subty A of B1] ~~>[m] Return r1 ->
        [subty A of B2] ~~>[n] Return r2 ->
        [subty A of B1 \cap B2] ~~>[k9 + (m + n)] Return (r1 && r2)
    where "p '~~>[' n ']' r" := (CostIndexedSemantics p r n).

    Definition c1 := k1 + k2 + k3 + k4 + k5 + k6 + k7 + k8 + k9.

    Lemma length_size: forall A, length A <= size A.
    Proof.
      elim => //.
      - move => A1 _ A2 IH /=.
        rewrite -[X in _ <= X](addnAC 1) -(addnA).
        rewrite leq_add2l.
        apply: leq_trans; first by exact IH.
          by apply: leq_addr.
      - move => A1 IH1 A2 IH2 /=.
        rewrite -[X in _ <= X](addnAC 1) -(addnA).
        apply: leq_trans; last by apply: leq_addl.
        rewrite addnC.
          by apply: leq_add.
    Qed.

    Lemma breadth_size: forall A, breadth A <= size A.
    Proof.
      elim => //=.
      move => A1 IH1 A2 IH2.
      apply: leq_add => //.
        by apply: leq_trans; last by apply leq_addl.
    Qed.

    Lemma c1_gt0: c1 > 0.
    Proof.
      rewrite /c1.
      apply: ltn_addl.
      apply: k9_gt0.
    Qed.

    Lemma k1_leq: k1 <= c1.
    Proof.
      rewrite /c1.
      do 7 rewrite -(addnA k1).
      apply: leq_addr.
    Qed.

    Lemma k2_leq: k2 <= c1.
      rewrite /c1.
      do 7 rewrite -(addnA k1).
      apply: leq_trans; last by apply: leq_addl.
      do 6 rewrite -(addnA k2).
      apply: leq_addr.
    Qed.

    Lemma k3_leq: k3 <= c1.
      rewrite /c1.
      do 7 rewrite -(addnA k1).
      apply: leq_trans; last by apply: leq_addl.
      do 6 rewrite -(addnA k2).
      apply: leq_trans; last by apply: leq_addl.
      do 5 rewrite -(addnA k3).
      apply: leq_addr.
    Qed.

    Ltac kn_leq k :=
      rewrite /c1;
      do 7 rewrite -(addnA k1);
      try (by apply: leq_addr)
      || (apply: leq_trans; last by apply: leq_addl;
         do 6 rewrite -(addnA k2);
         try (by apply: leq_addr )
         || (apply: leq_trans; last by apply: leq_addl;
            do 5 rewrite -(addnA k3);
            try (by apply: leq_addr)
            || (apply: leq_trans; last by apply: leq_addl;
               do 4 rewrite -(addnA k4);
               try (by apply: leq_addr)
               || (apply: leq_trans; last by apply: leq_addl;
                  do 3 rewrite -(addnA k5);
                  try (by apply: leq_addr)
                  || (apply: leq_trans; last by apply: leq_addl;
                     do 2 rewrite -(addnA k6);
                     try (by apply: leq_addr)
                     || (apply: leq_trans; last by apply: leq_addl;
                        rewrite -(addnA k7);
                        try (by apply: leq_addr)
                        || apply: leq_trans; last by apply: leq_addl;
                          try (by apply leq_addr) || by apply leq_addl)))))).

    Lemma cost_l: forall p,
      match p with
      | [ subty A of Omega] => 1 <= c1 * (breadth A + length Omega)
      | [ subty A of Ctor b B] => k1 * (breadth A + length (Ctor b B)) + k2 * (breadth A) + k3 <= c1 * (breadth A + length (Ctor b B))
      | [ subty A of B1 -> B2] => (k1 * (breadth A + length (B1 -> B2)) + k4 * breadth A + k5) <= c1 * (breadth A + length (B1 -> B2))
      | [tgt_for_srcs_gte B in [:: A & Delta ]] => k6 <= c1
      | [tgt_for_srcs_gte B in [::]] => 1 <= c1
      | [subty A of B1 \times B2] => k1 * (breadth A + length (B1 \times B2)) + 2 * k7 * breadth A + k8 <= c1 * (breadth A + length (B1 \times B2))
      | [subty A of B1 \cap B2] => k9 <= c1 * (breadth A + length (B1 \cap B2))
      end.
    Proof.
      case.
      - move => [] A.
        case.
        + rewrite /=.
          rewrite muln_gt0 c1_gt0.
            by rewrite addn_gt0 orbT.
        + move => b B /=.
          apply: (leq_trans (n := k1 * (breadth A + 1) + k2 * (breadth A + 1) + k3 * (breadth A + 1))).
          * rewrite -(addnA (k1 * _)) -(addnA (k1 * _)) leq_add2l.
            apply: leq_add.
            ** rewrite leq_pmul2l => //.
                 by apply: leq_addr.
            ** rewrite leq_pmulr => //.
                 by rewrite addn_gt0 orbT.
          * rewrite -(mulnDl k1) -(mulnDl (k1 + k2)) (leq_pmul2r); admit.
        + move => A1 A2; admit.
        + admit.
        + admit.
      - move => [] A Delta.
        admit.
    Admitted.
(*
          apply: (leq_trans (n := k1 * (2 * size A * (1 + size B)) + k2 * (2 * size A * (1 + size B)) + k3 * (2 * size A * (1 + size B)))).
          * apply: leq_add.
            ** apply: leq_add.
               *** rewrite (mulnDr k1).
                   rewrite -(mulnA 2) [X in _ <= X](mulnC k1) -(mulnA 2) -(mulnC k1) (mul2n) -(addnn).
                   apply: leq_add.
                   **** by rewrite leq_mul2l (leq_pmulr _ (addn_gt0 1 _)) orbT.
                   **** rewrite (muln1).
                        apply leq_pmulr.
                          by rewrite muln_gt0 addn_gt0 size_min size_min.
               *** rewrite (leq_pmul2l k2_gt0) (mulnC 2) -(mulnA (size A)).
                   apply: leq_pmulr.
                     by rewrite muln_gt0 /= addn_gt0.
            ** apply: leq_pmulr.
                 by rewrite muln_gt0 /= addn_gt0 muln_gt0 size_min size_min.
          * do 5 (rewrite mulnDl; apply: leq_trans; last by apply: leq_addr).
            rewrite -(mulnDl k1) -(mulnDl (k1 + k2)).
              by apply: leqnn.
        + move => B1 B2.
          rewrite /c1.
          apply: (leq_trans (n := k1 * (2 * size A * (size (B1 -> B2))) + k4 * (2 * size A * (size (B1 -> B2))))).
          * apply: leq_add.
            ** rewrite (mulnDr k1).
               rewrite -(mulnA 2) [X in _ <= X](mulnC k1) -(mulnA 2) -(mulnC k1) (mul2n) -(addnn).
               apply: leq_add.
               *** by rewrite leq_mul2l (leq_pmulr _ (addn_gt0 1 _)) orbT.
               *** rewrite (leq_pmul2l k1_gt0).
                   apply: (leq_pmull).
                     by apply: size_min.
            ** apply: leq_pmulr.
                 by rewrite muln_gt0 /= muln_gt0 size_min addn_gt0 addn_gt0.
          * rewrite -(mulnDl k1 k4) /cost.
            rewrite leq_pmul2r.
            ** do 6 rewrite -(addnA k1).
               rewrite leq_add2l -(addnA k2) -(addnC k4) (addnA k2) -(addnC k4).
               do 5 rewrite -(addnA k4).
                 by apply: leq_addr.
            ** by rewrite muln_gt0 size_min muln_gt0 size_min.
        + move => B1 B2.
          rewrite /c1.
          apply: (leq_trans (n := k1 * (2 * size A * (size (B1 \times B2))) +
                                  k6 * (2 * size A * (size (B1 \times B2))) +
                                  k7 * (2 * size A * (size (B1 \times B2))))).
          * apply: leq_add.
             ** apply: leq_add.
                *** rewrite (leq_pmul2l k1_gt0).
                    apply (leq_trans (n := size A + size (B1 \times B2))).
                    **** by apply leq_add.
                    **** rewrite -(mulnA 2) (mul2n) -(addnn).
                         apply: leq_add.
                         ***** by apply: leq_pmulr; rewrite size_min.
                         ***** by apply: leq_pmull; rewrite size_min.
                *** rewrite -(mulnA 2) (mulnC 2) -(mulnA k6).
                    rewrite (leq_pmul2l k6_gt0).
                    rewrite -(mulnC (size (B1 \times B2))) -(mulnC 2).
                    apply: leq_pmull.
                      by apply: size_min.
             ** apply leq_pmulr.
                  by rewrite muln_gt0 muln_gt0 size_min size_min.
          * rewrite -(mulnDl k1 k6) -(mulnDl _ k7) /cost.
            rewrite leq_pmul2r.
            ** do 7 rewrite -(addnA k1).
               rewrite leq_add2l.
               do 5 rewrite -(addnA k2).
               apply: leq_trans; last by apply: leq_addl.
               do 4 rewrite -(addnA k3).
               apply: leq_trans; last by apply: leq_addl.
               do 3 rewrite -(addnA k4).
               apply: leq_trans; last by apply: leq_addl.
               do 2 rewrite -(addnA k5).
               apply: leq_trans; last by apply: leq_addl.
               rewrite -(addnA k6).
               rewrite leq_add2l.
                 by apply: leq_addr.
            ** by rewrite muln_gt0 muln_gt0 size_min size_min.
        + move => B1 B2.
          rewrite /c1.
          apply: (leq_trans (n := k8 * cost [ subty A of B1 \cap B2])).
          * apply: leq_pmulr.
              by rewrite /= muln_gt0 addn_gt0 addn_gt0 size_min size_min orbT muln_gt0 size_min.
          * rewrite leq_pmul2r.
            ** apply: leq_trans; last by apply: leq_addl.
                 by apply: leqnn.
            ** by rewrite /= muln_gt0 addn_gt0 addn_gt0 size_min size_min orbT muln_gt0 size_min.
      - move => [] B.
        case.
        + rewrite /= muln_gt0 /c1 muln0 addn0 /= leq_addr andbT.
          do 6 rewrite -(addnA k1).
          apply: ltn_addr.
            by apply: k1_gt0.
        + move => A Delta /=.
          apply: leq_trans; last apply: leq_pmulr.
          * rewrite /c1.
            do 6 rewrite -(addnA k1).
            apply: leq_trans; last by apply: leq_addl.
            do 5 rewrite -(addnA k2).
            apply: leq_trans; last by apply: leq_addl.
            do 4 rewrite -(addnA k3).
            apply: leq_trans; last by apply: leq_addl.
            do 3 rewrite -(addnA k4).
            apply: leq_trans; last by apply: leq_addl.
            do 2 rewrite -(addnA k5).
              by rewrite leq_addr.
          * by apply: leq_addr.
    Qed.
 *)

    Variable c2 : nat.
    Hypothesis c2_gtc1: c2 > c1.
    Hypothesis c2_gte2: c2 >= 2.

    Definition cost' (p: Instruction) : nat :=
      match p with
      | [ subty A of B] =>  c2 * size A * size B - c1 - size B
      | [tgt_for_srcs_gte B in Delta ] =>
        k6 + sumn (map (fun x => k6 + c2 * size B * size (x.1) - c1 - size B) Delta)
      end.

    Lemma Semantics_forget_costs: forall p r n, p ~~>[n] r -> p ~~> r.
    Proof.
      move => p r n prf.
      elim: p r n / prf; try by move => *; constructor.
      - move => A B1 B2 Delta r m n _ IH1 _ IH2.
        apply: step__Arr.
        + by exact IH1.
        + by exact IH2.
    Qed.

    Lemma arrow_cast_cost'1: forall A B1 B2,
        ~~ (isOmega B2) -> sumn (map (fun x => k6 + c2 * size B1 * size (x.1) - c1) (cast (B1 -> B2) A)) <= c2 * size A.
    Proof. Admitted.
    (*
      move => A B1 B2.
      elim: A; try by rewrite /cast /=; case (isOmega B2) => //.
      + move => A1 _ A2 _ /=.
        rewrite /cast /=.
        case (isOmega B2) => //= _.
        rewrite addn0 mulnDr mulnDr -(addnA (2 * 1)).
        apply: leq_add => //.
        apply: leq_trans; last by apply leq_addr.
        apply: leq_pmul2r; apply: size_min.
      + move => A1 IH1 A2 IH2 notOmega__B2.
        rewrite (cast_inter A1 A2 (B1 -> B2) notOmega__B2).
        rewrite map_cat sumn_cat /= mulnDr mulnDr -(addnA (2 * 1)).
        apply: leq_trans; last by apply leq_addl.
        apply: leq_add.
        * by apply: IH1.
        * by apply: IH2.
    Qed.*)


    Lemma foo: forall p n r,
        p ~~>[n] r ->
        n <= cost' p.
    Proof.
      move => p n r prf.
      elim: p r n / prf.
      - move => A /=.
        rewrite subn_gt0.
        rewrite muln1.
        admit.
        (*apply: leq_trans; first by apply: c2_gtc1.
        apply: leq_pmulr.
          by rewrite size_min.*)
      - move => A b B r n prf IH.
        rewrite /cost'.
        rewrite -(addnC n).
        apply: leq_trans; first by (erewrite leq_add2r; exact IH).
        rewrite /=.
        rewrite (mulnDr (c2 * size A)).
        rewrite -[X in _ <= X](subnDA c1).
        rewrite (addnC _ (k1 * _ + _ + _)).
        rewrite (addnC c1).
        rewrite (subnDA ) (subnDA) -(addnBA).
        + rewrite (addnBA (c2 * size A * 1)).
          * rewrite (addnC (c2 * size A * 1)).
            rewrite -(addnBA (c2 * size A * size B)).
            ** rewrite (addnC (c2 * size A * size B)).
               rewrite -(subnDA (size B)).
               rewrite -(addnBA (c2 * size A * 1 - 1)).
               *** rewrite addnC -(addnC (c2 * size A * size B - _)).
                   apply leq_add.
                   **** rewrite (addnC (size B)) (subnDA).
                        apply: leq_sub; last by apply: leqnn.
                        apply: leq_sub; last by apply: leqnn.
                        apply: leq_mul; last by apply: leqnn.
                        apply: leq_mul; first by apply: leqnn.
                          by apply ctor_cast_size_le.
                   **** admit.
               *** admit. (* add c2 > 2 * c1 *)
            ** rewrite (muln1).
                 by rewrite muln_gt0 size_min ltnW.
          * by rewrite muln_gt0 muln_gt0 size_min size_min ltnW.
        + by rewrite muln_gt0 muln_gt0 size_min size_min ltnW.
      - move => A B1 B2 Delta r m n prf1 IH1 prf2 IH2.
        apply: leq_trans.
        + apply: leq_add; first by apply: leqnn.
          apply: leq_add.
          * by apply: IH1.
          * by apply: IH2.
        + rewrite /cost' /=.
          case isOmega__B2: (isOmega B2).
          * move: prf1.
            rewrite /cast /= isOmega__B2 /=.
            move => /Semantics_forget_costs /(omegaDoneTgt) -> /=.
            do 2 rewrite (mulnDr (c2 * size A)).
            rewrite addn0 -addnBA.
            ** repeat rewrite muln1.
               rewrite (addnC (c2 * size A)) -(addnC (c2 * size A * size B2)) (addnA (c2 * size A * _)).
               rewrite -[X in _ <= X](subnDA c1).
               rewrite (addnA (c2 * size A * size B2 + _)).
               rewrite -[X in _ <= X](subnBA).
               *** 

               rewrite -(addnA k6) -(addnA k6).
               rewrite -(addnA (k1 * _)) -(addnA (k1 * _)) -(addnA (k4 * _)).
               rewrite -(addnC (c2 * _ - _ + _)).
               do 4 rewrite -(addnCA (c2 * _ - _ + _)).
               rewrite (addnA (k1 * _)) (addnA (k1 * _ + _)) (addnA (k1 * _ + _ + _)) (addnC (c2 * _ - _ + _)).
               rewrite -(addnA (c2 * size A)) -(addnBA).
               *** apply: leq_add.
                   **** admit.
                   **** apply: leq_trans.
                        { apply: leq_add.
                          - by apply: leq_subr.
                          - by apply: leqnn. }
                        { rewrite -(addnBA).
                          - apply: leq_add.
                            + rewrite -(mulnA c2) leq_pmul2l.
                              * apply: leq_pmull; by apply: size_min.
                              * by apply ltnW.
                            + apply: leq_sub2r.
                              rewrite leq_pmul2r.
                              * apply: leq_pmulr.
                                  by apply: size_min.
                              * by apply: size_min.
                          - rewrite -(muln1 c1).
                            apply: leq_mul; last by apply: size_min.
                            rewrite -(muln1 c1).
                            apply: leq_mul; last by apply: size_min.
                              by apply: ltnW. }
               *** apply: leq_trans; last by apply: leq_addr.
                   rewrite -(muln1 c1).
                   apply: leq_mul; last by apply: size_min.
                   rewrite -(muln1 c1).
                   apply: leq_mul; last by apply: size_min.
                     by apply: ltnW.
            ** rewrite muln1.
               rewrite -(muln1 c1).
               apply: leq_mul; last by apply: size_min.
                 by apply: ltnW.
          * rewrite -(addnA k6).
            rewrite -(addnC (sumn _ + _)) -(addnCA (sumn _ + _)).
            do 2 rewrite (mulnDr (c2 * size A)).
            rewrite -(addnA (c2 * _ * 1)).
            rewrite -(addnBA).
            ** rewrite (addnC (c2 * _ * 1)).
               apply: leq_add.
               *** rewrite -(addnBA).
                   **** apply: leq_add.
                        { apply: leq_trans.
                          - have notOmega__B2: (~~ isOmega B2) by move: isOmega__B2; case (isOmega B2) => //.
                            apply: (arrow_cast_cost'1 _ _ _ notOmega__B2).
                          - apply: leq_pmulr; by apply: size_min. }
                        { apply: leq_sub2r.
                          rewrite leq_pmul2r; last by apply: size_min.
                          rewrite leq_pmul2l; last by apply: ltnW.
                          apply: arrow_cast_size2.
                          apply: choose_tgt_subseq.
                          apply: Semantics_forget_costs.
                            by exact prf1. }
                   **** rewrite -(muln1 c1).
                        apply: leq_mul; last by apply: size_min.
                        rewrite -(muln1 c1).
                        apply: leq_mul; last by apply: size_min.
                          by apply: ltnW.
               *** admit.
            ** apply: leq_trans; last by apply: leq_addr.
               rewrite -(muln1 c1).
               apply: leq_mul; last by apply: size_min.
               rewrite -(muln1 c1).
               apply: leq_mul; last by apply: size_min.
                 by apply: ltnW.
      - move => B A Delta Delta' r n m prf1 IH1 prf2 IH2.
        apply: leq_trans.
        + apply leq_add; first by apply: leqnn.
          apply: leq_add.
          * by apply: IH1.
          * by apply: IH2.
        + rewrite /cost' /=.
          rewrite leq_add2l.
          rewrite -(addnBA).
          * by rewrite [X in _ <= X](addnAC k6) (addnC (c2 * _ * _ - c1)) leqnn.
          * rewrite -(muln1 c1) -(mulnA c2).
            apply: leq_mul; first by apply: ltnW.
              by rewrite muln_gt0 size_min size_min.
      - move => B /=; by rewrite addn_gt0 k6_gt0.
      - move => A B1 B2 r1 r2 m n prf1 IH1 prf2 IH2.
        apply: leq_trans.
        + apply: leq_add; first by apply: leqnn.
          apply: leq_add.
          * by apply: IH1.
          * by apply: IH2.
        + rewrite /cost' /=.
          do 2 rewrite (mulnDr (c2 * size A)).
          rewrite -(addnA (c2 * size A * 1)).
          rewrite -(addnA (k1 * _)).
          rewrite -(addnBA).
          * apply: leq_add.
            ** admit.
            ** apply: leq_trans.
               *** apply: leq_add; last by apply: leqnn.
                   apply: leq_subr.
               *** rewrite -(addnBA).
                   **** apply: leq_add.
                        { do 2 rewrite -(mulnA c2).
                          rewrite leq_pmul2l; last by apply: ltnW.
                          rewrite leq_pmul2r; last by apply: size_min.
                            by apply: prod_cast_size_le1. }
                        { apply: leq_sub2r.
                          do 2 rewrite -(mulnA c2).
                          rewrite leq_pmul2l; last by apply: ltnW.
                          rewrite leq_pmul2r; last by apply: size_min.
                            by apply: prod_cast_size_le2. }
                   **** rewrite -(muln1 c1) -(mulnA c2).
                        apply: leq_mul; first by apply: ltnW.
                          by rewrite muln_gt0 size_min size_min.
          * apply: leq_trans; last by apply: leq_addr.
            rewrite -(muln1 c1) -(mulnA c2).
            apply: leq_mul; first by apply: ltnW.
              by rewrite muln_gt0 size_min size_min.
      - move => A B1 B2 r1 r2 m n prf1 IH1 prf2 IH2.
        apply: leq_trans.
        + apply: leq_add; first by apply: leqnn.
          apply: leq_add.
          * by apply: IH1.
          * by apply: IH2.
        + rewrite /cost' /=.
          do 2 rewrite (mulnDr (c2 * size A)).
          rewrite -(addnA (c2 * size A * 1)).
          rewrite -(addnBA).
          * apply: leq_add.
            ** apply: (leq_trans (n := c1)).
               *** rewrite /c1.
                   rewrite -(addnC k9).
                     by apply: (leq_addr).
               *** rewrite muln1 -(muln1 c1).
                   apply: leq_mul; last by apply: size_min.
                     by apply: ltnW.
            ** apply: leq_trans.
               *** apply: leq_add; last by apply: leqnn.
                   apply: leq_subr.
               *** rewrite -(addnBA).
                   **** apply: leq_add; by apply: leqnn.
                   **** rewrite -(muln1 c1) -(mulnA c2).
                        apply: leq_mul; first by apply: ltnW.
                          by rewrite muln_gt0 size_min size_min.
          * apply: leq_trans; last by apply: leq_addr.
            rewrite -(muln1 c1) -(mulnA c2).
            apply: leq_mul; first by apply: ltnW.
              by rewrite muln_gt0 size_min size_min.
    Qed.


    Lemma cost_r: forall p,
      match p  return Prop with
      | [ subty A of Omega] => 0 <= cost p
      | [ subty A of Ctor b B] => cost [ subty (\bigcap_(A__i <- cast (Ctor b B) A) A__i) of B] <= cost p
      | [ subty A of B1 -> B2] =>
        forall Delta, [tgt_for_srcs_gte B1 in cast (B1 -> B2) A] ~~> [ check_tgt Delta] ->
                 cost [tgt_for_srcs_gte B1 in cast (B1 -> B2) A] + cost [subty (\bigcap_(A__i <- Delta) A__i) of B2] <= cost p
      | [tgt_for_srcs_gte B in [:: A & Delta ]] => cost [ subty B of A.1] + cost [ tgt_for_srcs_gte B in Delta] <= cost p
      | [tgt_for_srcs_gte B in [::]] => 0 <= cost p
      | [subty A of B1 \times B2] => cost [ subty A of B1] + cost [ subty A of B2] <= cost p
      | [subty A of B1 \cap B2] => cost [ subty A of B1] + cost [ subty A of B2] <= cost p
      end.
    Proof.
      (*case.
      - move => [] A.
        elim.
        + admit.
        + move => b B _.
          apply: *)
    Admitted.

    Variable c2: nat.

    Lemma bigO_costs: forall p r n,
        p
          ~~>[n] r ->
        n <= c1 * cost p + c2 * cost p.
    Proof.
      move => p r n prf.
      elim: p r n / prf.
      - move => A.
        admit.
          (*by rewrite -(mulnA 2) muln_gt0 (cost_l [ subty A of Omega]).´*)
      - move => A b B r n prf IH.
        (*rewrite -(mulnA 2) (mul2n) -(addnn).*)
        apply: leq_add.
        + by apply: (cost_l [ subty A of Ctor b B]).
        + rewrite /=.
          apply: leq_trans; first by exact IH.
          rewrite /cost /=.
        rewrite (addnA (k1 * _)).
        move: (cost_l [ subty A of (Ctor b B)]).

    Lemma cost_r: forall p,
      match p with
      | [ subty A of Omega] => 0 <= cost p
      | [ subty A of Ctor b B] => cost [ subty (\bigcap_(A__i <- cast (Ctor b B) A) A__i) B] <= cost p
      | [ subty A of B1 -> B2] => cost [tgt_for_srcs_gte B1 in cast (B1 -> B2) A] + [subty (\bigcap_(A__i <- Delta) A__i) of B2] ~~>[n] <= cost p
      | [tgt_for_srcs_gte B in [:: A & Delta ]] => k5 <= c1 * cost p
      | [tgt_for_srcs_gte B in [::]] => 1 <= c1 * cost p
      | [subty A of B1 \times B2] => k1 * size (B1 \times B2) + 2 * k6 * size A + k7 <= c1 * cost p
      | [subty A of B1 \cap B2] => k8 <= c1 * cost p
      end.

    Lemma cost_lhs: forall p, 




    Lemma bigO_costs: forall p r n,
        p ~~>[n] r ->
        n <=
        (5 * (1 +
             (k1 + k2 + 1 + k3) +
             (k1 + 1 + 1 + k4) +
             (1 + 1 + k5) +
             (k1 + 2 * k6 + 1 + 1 + k7) +
             (1 + 1 + k8))) * (cost p) - (1 +
             (k1 + k2 + 1 + k3) +
             (k1 + 1 + 1 + k4) +
             (1 + 1 + k5) +
             (k1 + 2 * k6 + 1 + 1 + k7) +
             (1 + 1 + k8)).
    Proof.
      move => p r n prf.
      match goal with
      |[|- context[ 5 * ?co * _]] =>
       set (coeff := co)
      end.
      elim: p r n / prf.
      - admit.
      - move => A b B r n prf' IH /=.
        have: (n <= 4 * coeff + 2 * (size A + (1 + size B))).
        { apply: (leq_trans IH).
          move: (ctor_

        apply: leq_trans; last first.
        + rewrite -(mulnA 5) -(mulnC (2 * _ * _)) (mulnA 5) -(mulnC (2 * _ * _)).
          

        


      move => p r.
      move: (Domain_Domain_n p (total p)) => [] m dom n prf.
      move: (Domain_size p m dom) => m_size.


      move: m_size n prf.
      elim: m p / dom.
      - move => A _ n.
        move p__eq: [ subty A of Omega] => p prf.
        move: p__eq.
        case: p r n / prf => //= ? [] <-.
        repeat rewrite mulnDl.
        repeat apply: ltn_addl.
        rewrite mulnDr.
        apply: ltn_addr.
        rewrite muln1.
          by rewrite muln_gt0 k8_gt0 size_min.
      - move => A b B n dom IH /=.
        admit.
      - move => A B1 B2 m n dom1 IH1 dom2 IH2.
        
        
        




    Lemma size_min: forall A, 0 < size A.
    Proof. by case => //=. Qed.

    Lemma bigcap_size: forall (Delta1 Delta2: seq (@IT Constructor)),
        size (\bigcap_(A__i <- (Delta1 ++ Delta2)) A__i) <= 1 + size (\bigcap_(A__i <- Delta1) A__i) + size (\bigcap_(A__i <- Delta2) A__i).
    Proof.
      elim => //=.
      - move => Delta2.
        rewrite -addnA add1n add1n.
        apply: leqW.
        apply: leqW.
          by apply: leqnn.
      - move => A Delta1.
        case: Delta1.
        + move => IH Delta2 /=.
          case: Delta2 => //=.
            by rewrite -addnA addn1 add1n leqW.
        + move => A1 Delta1 IH Delta2.
          rewrite (leq_add2l 1) -/size -/Nat.add -addn1 plusE -addnAC (addnC _ 1) (addnA 1) (addnC 1).
          rewrite  -(addnA (size A)) -(addnA (size A)) (leq_add2l (size A)).
            by apply: IH.
    Qed.

    Lemma ctor_cast_size: forall A b B, ~~nilp (cast (Ctor b B) A) -> size (\bigcap_(A__i <- (cast (Ctor b B) A)) A__i) < size A.
    Proof.
      elim => //=.
      - move => a A IH b B.
        rewrite /cast /=.
        case: [ ctor a <= b] => //.
      - move => A1 IH1 A2 IH2 b B.
        rewrite (cast_inter A1 A2 (Ctor b B) isT).
        move => canCast.
        apply: leq_ltn_trans; first by apply: bigcap_size.
        rewrite (ltn_add2l 1) -/Nat.add plusE.
        move: (IH1 b B) canCast.
        case: (cast (Ctor b B) A1).
        + move => _ /(IH2 b B) prf /=.
          apply: (leq_ltn_trans (n := (size A1) + (size (\bigcap_(A__i <- cast (Ctor b B) A2) A__i)))).
          * rewrite (leq_add2r (size (\bigcap_(A__i <- cast (Ctor b B) A2) A__i))).
              by apply: size_min.
          * by rewrite (ltn_add2l (size A1)).
        + move => A1' Delta1 IH1'.
          move: (IH2 b B).
          case: (cast (Ctor b B) A2).
          * move => _ _.
            apply: (leq_ltn_trans (n := size (\bigcap_(A__i <- [:: A1' & Delta1]) A__i) + size A2)).
            ** rewrite leq_add2l.
                 by apply: size_min.
            ** rewrite ltn_add2r.
                 by apply: IH1'.
          * move => A2' Delta2 IH2' _.
            apply: (leq_ltn_trans (n := size (\bigcap_(A__i <- [:: A1' & Delta1]) A__i) + size A2)).
            ** rewrite leq_add2l.
               apply: ltnW.
                 by apply: IH2'.
            ** rewrite ltn_add2r.
                 by apply: IH1'.
    Qed.

    Lemma gauss: forall n k, sumn (map (fun x => k * x) (iota 1 n)) = k * ((n * (n.+1))./2).
    Proof.
      move => n k.
      elim: n => //.
      move => n IH.
      rewrite -(addn1 n) (iota_add 1) map_cat sumn_cat IH.
      move: IH => _.
      case: n.
      - rewrite /= muln0 addn0 addn0 //=.
      - move => n.
        rewrite [sumn _]/= addn0.
        apply: eqP.
        rewrite -(mulnDr k) (eqn_mul2l).
        rewrite -(@mulKn (1 + n.+1) 2 isT) -divn2.
        rewrite -(divnDr); last by apply: dvdn_mulr; apply: dvdnn.
        rewrite (mulnDr 2) -[X in (2 * 1 + 2 * X)](addn1) (mulnDr 2) muln1.
        rewrite -addn1 mulnDl -addn1 mulnDl -addn1 mulnDl.
        repeat rewrite muln0.
        repeat rewrite add0n.
        repeat rewrite mul1n.
        rewrite mulnDl mul1n.
        rewrite -(addn1 (n + 1 + 1)).
        repeat rewrite mulnDr.
        repeat rewrite muln1.
        rewrite mul2n -addnn.
        repeat rewrite -addnA.
        repeat rewrite add1n.
        repeat rewrite (addnC 2).
        rewrite -add2n (addnC 2).
        rewrite addn3 addn2 addn2 addn2.
        rewrite -addn4 -(addnA n n.+2 4) addn4.
        rewrite divn2.
        rewrite (eq_refl _).
          by rewrite orbT.
    Qed.

    Lemma sumn_split_last:
      forall n k, n >= 1 -> sumn (map (fun x => k * x) (iota 1 n)) = sumn (map (fun x => k * x) (iota 1 n.-1)) + k * n.
    Proof.
      move => n k n_gt.
      have: (k * n = sumn (map (fun x => k * x) (iota (1 + n.-1) 1)))
        by rewrite -subn1 (subnKC n_gt) /= addn0.
      move => ->.
      rewrite -sumn_cat -map_cat -iota_add addn1.
        by rewrite (prednK n_gt).
    Qed.

    Lemma sumn_leq: forall m n k, m <= n -> sumn (map (fun x => k * x) (iota 1 m)) <= sumn (map (fun x => k * x) (iota 1 n)).
    Proof.
      move => m n k.
      move: m.
      elim: n.
      - case => //.
      - move => n IH m.
        rewrite leq_eqVlt => /orP.
        case.
        + by move => /eqP ->.
        + rewrite ltnS.
          move => /IH.
          rewrite (sumn_split_last n.+1); last by done.
          move => prf.
          apply: (leq_trans prf).
          rewrite /=.
            by apply leq_addr.
    Qed.

    Lemma twice_maxS: forall m n, 1 + (m + n) <= 2 * (maxn m n).+1.
    Proof.
      move => ? ?.
      rewrite (addnC 1) -(addn1 (maxn _ _)) mulnDr.
      apply: leq_add => //.
      rewrite mul2n -addnn.
      apply: leq_add.
      - apply: leq_maxl.
      - apply: leq_maxr.
    Qed.

    (*Lemma sumn_shift_upper: forall m n k,
        sumn (map (fun x => k * x) (iota 1 (m + n))) <=
        sumn (map (fun x => k * x) (iota m n)).
    Proof.
      move => m n.
      rewrite iota_add.
*)

    (*Lemma sumn_add_upper: forall m n1 n2 k,
        sumn (map (fun x => k * x) (iota 1 (m + n1))) + sumn (map (fun x => k * x) (iota 1 (m + n2))) <=
        sumn (map (fun x => k * x) (iota 1 (m + n1 + n2))).
    Proof.
      move => m n1 n2 k.
      rewrite -sumn_cat -map_cat.
      rewrite -addnA.
      rewrite (iota_add 1 m).
      rewrite (iota_add 1 m (n1 + n2)).
      rewrite (iota_add (1 + m) n1).
      do 4 rewrite map_cat.
      do 4 rewrite sumn_cat.
      rewrite -(addnA (sumn _)).
      do 2 rewrite leq_add2l.
      *)

    Record a_props {a: nat}: Type :=
      { a_gt0: a > 0;
        a_gt2c: a > 2 * c + 1
      }.

    Lemma asum: forall a m n o,
        @a_props a ->
        o < m ->
        m > 0 -> n > 0 ->
        c * (m + n) + a * o * (n - 1) < a * m * n.
    Proof.
      move => a m n o props lt_om m_gt0 n_gt0.
      rewrite mulnDr addnC -ltn_subRL -(mulnA a) -(mulnA a) -(mulnBr a).
      have m_le: m <= (m * n - o * (n - 1)).
      { apply: (leq_trans (n := m * n - m * (n - 1))).
        - by rewrite -mulnBr (subKn n_gt0) muln1.
        - rewrite mulnBr.
          rewrite subKn.
          + apply: (leq_trans (n := m * n - m * (n - 1))).
            * rewrite -mulnBr muln1.
              apply: leq_pmulr.
                by rewrite subKn.
            * apply: leq_sub2l.
                by rewrite leq_mul2r (ltnW lt_om) orbT.
          + rewrite muln1.
              by apply leq_pmulr. }
      have n_le: n <= (m * n - o * (n - 1)).
      { rewrite mulnBr (subnBA).
        - rewrite addnC -addnBA.
          + apply: (leq_trans (n := o + n)); first by rewrite leq_addl.
            rewrite muln1 leq_add2l -mulnBl.
            apply: leq_pmull.
              by rewrite subn_gt0.
          + by rewrite leq_pmul2r => //; apply: ltnW.
        - by rewrite muln1; apply: leq_pmulr. }
      rewrite -ltn_divLR.
      - apply: (leq_ltn_trans (n := (2 * c * (m * n - o * (n - 1))) %/ (m * n - o * (n - 1)))).
        + apply: leq_div2r.
          rewrite -mulnA mul2n -addnn.
            by apply: leq_add; rewrite leq_pmul2l.
        + rewrite mulnK; last by apply: leq_trans; last by apply: m_le.
          apply: ltn_trans; last by apply: a_gt2c.
            by rewrite addn1 ltnSn.
      - by apply: leq_trans; last by apply: m_le.
    Qed.

    Lemma asum': forall a m n,
        @a_props a ->
        m > 0 -> n > 0 ->
        c * (m + n) + a * (n-1) < a * m * n.
    Proof.
      move => a m n props m_gt0 n_gt0.
      apply: (leq_ltn_trans (n := c * (m + n) + a * n)).
      - rewrite leq_add2l.
        rewrite leq_pmul2l; last by apply: a_gt0.
          by apply: leq_subr.
      - rewrite -(mulnA a) -ltn_divLR.
        + rewrite mulnDr.
          have m_le: (m <= m * n) by apply: leq_pmulr.
          have n_le: (n <= m * n) by apply: leq_pmull.
          apply: leq_ltn_trans; first by apply: leq_divDl.
          rewrite (divn_small (m := a * n)).
          apply: (leq_ltn_trans (n := ((2 * c) * (m * n) + a * (m * n)) %/ (m * n))).
          * rewrite -(mulnA 2) mul2n -addnn.
            apply: leq_div2r.
            apply: leq_add.
            ** apply: leq_add.
               *** by rewrite leq_pmul2l.
               *** by rewrite leq_pmul2l.
            ** rewrite leq_pmul2l => //; last by apply: a_gt0.
          * rewrite -mulnDl mulnK.


    Lemma bound: forall a p r n,
        @a_props a ->
        p ~~>[n] r ->
        n <= match p with
            | [ subty A of B] => a * (size A * size B)
            | [ tgt_for_srcs_gte B1 in Delta ] =>
              a * sumn (map (fun x => size x.1) Delta) * size B1
            end.
    Proof.
      move => a p r n props prf.
      elim: p r n / prf.
      - move => A.
          by rewrite muln1 muln_gt0 (a_gt0 props) size_min.
      - move => A b B r n prf IH.
        apply: leq_ltn_trans.
        + by apply: (leq_add (leqnn _) IH).
        + do 2 rewrite (mulnA a).
          have: (size B = size (Ctor b B) - 1)
            by rewrite /= addnC addn1 subn1 /=.
          move => ->.
          apply: asum => //.
          *
            apply: ctor_cast_size.

        rewrite addn1 ltnS (addnC _ n).
        rewrite leq_add2r.
        apply: (leq_trans IH).


        rewrite /= mulnDr muln1.
        rewrite -addnA -(addnA (2 * _)) (addnC (2 * _)) -(addnA (size A)) -(addnA (size A)) ltn_add2l.
        do 3 rewrite -(addnA 1).
        rewrite ltn_add2l.
        rewrite -(addnA (size B)) ltn_add2l.
        apply: (leq_ltn_trans IH).
        rewrite ltn_add2r.
        admit.

      - move => A B1 B2 Delta r m n prf1 IH1 prf2 IH2. 
        (*rewrite (sumn_split_last); last by done.
        rewrite -(addn1) (addnC _ 1) addnA (addnC (sumn _)).
        apply: leq_add; first by apply: twice_maxS.
        apply: (leq_trans IH).
        apply: sumn_leq.
        rewrite /= leq_max gtn_max gtn_max.
        move: (ctor_cast_size A b B).
        case canCast: (cast (Ctor b B) A).
        + move => _ /=.
            by rewrite add1n ltnSn ltnS size_min /= orbT.
        + move => /(fun f => f isT) size_prf.
          rewrite size_prf add1n ltnSn andbT [_ && _]/=.
          rewrite ltnS.
          move: (leq_total (size A) (size B)) => /orP.
          case.
          * move => /(leq_trans size_prf) /ltnW ->.
              by rewrite orbT.
          * rewrite leq_eqVlt => /orP.
            case.
            ** move => /eqP ->.
                 by rewrite (ltnW size_prf) orbT.
            ** by move => ->.*)
        admit.
      - move => B A Delta Delta' r m n prf1 IH1 prf2 IH2.
        rewrite -(addn1)  (leq_add2r 1) /=.
        apply leq_add.
        (*rewrite (sumn_split_last); last by done.
        rewrite -(addn1) (addnC _ 1) addnA addnA -addnA (addnC (sumn _)).
        apply: leq_add; first by apply: twice_maxS.
        rewrite /=.*)
        admit.
      - admit.
      - move => A B1 B2 r1 r2 m n prf1 IH1 prf2 IH2.

        (*rewrite (sumn_split_last); last by done.
        rewrite -(addn1) (addnC _ 1) addnA addnA -addnA (addnC (sumn _)).
        apply: leq_add.
        + admit.
        + rewrite /=.
          apply: leq_trans.
          * apply leq_add.
            ** by apply: IH1.
            ** by apply: IH2.
          * rewrite gauss gauss gauss. *)
        admit.
      - move => A B1 B2 r1 r2 m n prf1 IH1 prf2 IH2.
        rewrite (sumn_split_last); last by done.
        rewrite -(addn1) (addnC _ 1) addnA addnA -addnA (addnC (sumn _)) -/size.
        apply: leq_add.
        + admit.
        + apply: leq_trans.
          * apply leq_add.
            ** by apply: IH1.
            ** by apply: IH2.
          * 


*)

