From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".
Require Import Types.

 (** Instructions for a machine to determine recursive inhabitation targets **)
Section RecursiveTargetsMachineInstuctions.
  Variable Constructor: ctor.

  Inductive Instruction: Type :=
  | AddSplitsWithSrcsToCtxt of (@IT Constructor * seq (@IT Constructor) * seq (seq (seq (@IT Constructor) * @IT Constructor)))
  | SplitType of (@IT Constructor).      

  Inductive Result: Type :=
  | LengthGroupedSourceTargetPairs of seq (seq (seq (@IT Constructor) * @IT Constructor)).

  (** Enable mathcomp functionalities on instructions **)
  Section InstructionMathcompInstances.
    Fixpoint Instruction2tree (i: Instruction):
      GenTree.tree (@IT Constructor + (seq (@IT Constructor) + seq (seq (seq (@IT Constructor) * @IT Constructor)))) :=
      match i with
      | AddSplitsWithSrcsToCtxt (A, Srcs, Ctxt) =>
        GenTree.Node 0 [:: GenTree.Leaf (inl A);
                          GenTree.Leaf (inr (inl Srcs));
                          GenTree.Leaf (inr (inr Ctxt))]
      | SplitType A => GenTree.Node 1 [:: GenTree.Leaf (inl A) ]
      end.

    Fixpoint Result2tree (r: Result): GenTree.tree (seq (seq (seq (@IT Constructor) * @IT Constructor))) :=
      match r with
      | LengthGroupedSourceTargetPairs Ctxt => GenTree.Node 0 [:: (GenTree.Leaf Ctxt) ]
      end.

    Fixpoint tree2Instruction (t: GenTree.tree (@IT Constructor + (seq (@IT Constructor) + seq (seq (seq (@IT Constructor) * @IT Constructor))))): option Instruction :=
      match t with
      | GenTree.Node n args =>
        match n, args with
        | 0, [:: GenTree.Leaf (inl A); GenTree.Leaf (inr (inl Srcs)); GenTree.Leaf (inr (inr Ctxt))] =>
          Some (AddSplitsWithSrcsToCtxt (A, Srcs, Ctxt))
        | 1, [:: GenTree.Leaf (inl A)] => Some (SplitType A)
        | _, _ => None
        end
      | _ => None
      end.

    Fixpoint tree2Result (t: GenTree.tree (seq (seq (seq (@IT Constructor) * @IT Constructor)))): option Result :=
      match t with
      | GenTree.Node n args =>
        match n, args with
        | 0, [:: GenTree.Leaf Ctxt] => Some (LengthGroupedSourceTargetPairs Ctxt)
        | _, _ => None
        end
      | _ => None
      end.

    Lemma pcan_Instructiontree: pcancel Instruction2tree tree2Instruction.
    Proof. by case => //= [] [] [] //=. Qed.

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
End RecursiveTargetsMachineInstuctions.

Arguments Instruction [Constructor].
Arguments AddSplitsWithSrcsToCtxt [Constructor].
Arguments SplitType [Constructor].
Hint Constructors Instruction.

Arguments Result [Constructor].
Arguments LengthGroupedSourceTargetPairs [Constructor].
Hint Constructors Result.

Notation "[ 'split' A ]" := (SplitType A) (at level 0): it_scope.
Notation "[ 'add_splits_with_srcs' Srcs => A  'to' Ctxt ]" :=
  (AddSplitsWithSrcsToCtxt (A, Srcs, Ctxt)) (at level 0): it_scope.
Notation "[ 'splits' Delta ]" := (LengthGroupedSourceTargetPairs Delta) (at level 0): it_scope.

(** A machine to determine recursive inhabitation targets **)
Reserved Notation "A '~~>' B" (at level 70, no associativity).
Section RecursiveTargetsMachine.
  Variable Constructor: ctor.

  Definition addToHead {T: Type} (x: T) (xss: seq (seq T)): seq (seq T) :=
    match xss with
    | [::] => [:: [:: x]]
    | [:: xs & xss] => [:: [:: x & xs] & xss]
    end.




  (** Semantics of the recursive target machine **)
  Inductive Semantics : @Instruction Constructor -> @Result Constructor -> Prop :=
  | step__split : forall A Delta,
      [add_splits_with_srcs [::] => A to [:: [::]] ] ~~> [splits Delta ] ->
      [split A ] ~~> [splits Delta ]
  | step__splitCtor : forall c A Gamma Delta,
      [add_splits_with_srcs Gamma => Ctor c A to Delta ] ~~> [splits (addToHead (Gamma, Ctor c A) Delta) ]
  | step__splitProd : forall A B Gamma Delta,
      [add_splits_with_srcs Gamma => A \times B to Delta ] ~~> [splits (addToHead (Gamma, A \times B) Delta) ]
  | step__splitArr : forall A B Gamma Delta Delta',
      [add_splits_with_srcs [:: A & Gamma] => B to Delta ] ~~> [splits Delta' ] ->
      [add_splits_with_srcs Gamma => A -> B to Delta ]
        ~~> [splits if isOmega B then Delta else [:: [:: (Gamma, A -> B)] & Delta'] ]
  | step__splitOmega: forall Gamma Delta,
      [add_splits_with_srcs Gamma => Omega to Delta ] ~~> [splits Delta ]
  | step__splitInterCtor: forall c A B Gamma Delta Delta',
      [add_splits_with_srcs Gamma => B to Delta ] ~~> [splits Delta' ] ->
      [add_splits_with_srcs Gamma => (Ctor c A) \cap B to Delta ]
        ~~> [splits (addToHead (Gamma, Ctor c A) Delta') ]
  | step__splitInterProd: forall A1 A2 B Gamma Delta Delta',
      [add_splits_with_srcs Gamma => B to Delta ] ~~> [splits Delta' ] ->
      [add_splits_with_srcs Gamma => (A1 \times A2) \cap B to Delta ]
        ~~> [splits (addToHead (Gamma, A1 \times A2) Delta') ]
  | step__splitInterArr: forall A1 A2 B Gamma Gamma' Delta1 Delta2 Delta3,
      [add_splits_with_srcs Gamma => B to Delta1 ] ~~> [splits [:: Gamma' & Delta2] ] ->
      [add_splits_with_srcs [:: A1 & Gamma] => A2 to Delta2 ] ~~> [splits Delta3 ] ->
      [add_splits_with_srcs Gamma => (A1 -> A2) \cap B to Delta1 ]
        ~~> [splits if isOmega A2 then [:: Gamma' & Delta2] else [:: [:: (Gamma, A1 -> A2) & Gamma'] & Delta3] ]
  | step__splitInterAssoc: forall A1 A2 B Gamma Delta Delta',
      [add_splits_with_srcs Gamma => A1 \cap (A2 \cap B) to Delta ] ~~> [splits Delta' ] ->
      [add_splits_with_srcs Gamma => (A1 \cap A2) \cap B to Delta ] ~~> [splits Delta' ]
  | step__splitInterOmega: forall B Gamma Delta Delta',
      [add_splits_with_srcs Gamma => B to Delta ] ~~> [splits Delta' ] ->
      [add_splits_with_srcs Gamma => Omega \cap B to Delta ] ~~> [splits Delta' ]
  where "p1 ~~> p2" := (Semantics p1 p2).

  Definition premisses_Semantics {i} {p} (s: i ~~> p) :=
    let diag i p :=
        match i, p with
        | [split A], [splits Delta]  =>
          forall (X: Result -> Prop),
            (forall Delta', [add_splits_with_srcs [::] => A to [:: [::]] ] ~~> [splits Delta' ] ->
                          X [splits Delta']) ->
            X [splits Delta]
        | [add_splits_with_srcs Gamma => Ctor c A to Delta ], [splits Delta'] =>
          forall (X: Result -> Prop),
            X [splits (addToHead (Gamma, Ctor c A) Delta) ] ->
            X [splits Delta']
        | [add_splits_with_srcs Gamma => A \times B to Delta ], [splits Delta] =>
          forall (X: Result -> Prop),
            X [splits (addToHead (Gamma, A \times B) Delta) ] ->
            X [splits Delta]
        | [add_splits_with_srcs Gamma => A -> B to Delta ], [splits Delta] =>

            ~~> [splits if isOmega B then Delta else [:: [:: (Gamma, A -> B)] & Delta'] ]
        | [add_splits_with_srcs Gamma => Omega to Delta ] ~~> [splits Delta ]
        | [add_splits_with_srcs Gamma => (Ctor c A) \cap B to Delta ]
            ~~> [splits (addToHead (Gamma, Ctor c A) Delta') ]
        | [add_splits_with_srcs Gamma => (A1 \times A2) \cap B to Delta ]
            ~~> [splits (addToHead (Gamma, A1 \times A2) Delta') ]
        | [add_splits_with_srcs Gamma => (A1 -> A2) \cap B to Delta1 ]
            ~~> [splits if isOmega A2 then [:: Gamma' & Delta2] else [:: [:: (Gamma, A1 -> A2) & Gamma'] & Delta3] ]
        |  [add_splits_with_srcs Gamma => (A1 \cap A2) \cap B to Delta ] ~~> [splits Delta' ]
        | [add_splits_with_srcs Gamma => Omega \cap B to Delta ] ~~> [splits Delta' ]
        | _, _  => True
        end in
    match s in i ~~> p return diag i p with
    | step__split A Delta prf => fun X k => k Delta prf
    | step__splitCtor c A Gamma Delta => fun X k => k
    | _ => I
    end.

End RecursiveTargetsMachine.

Arguments Semantics [Constructor].
Arguments step__split [Constructor A Delta].
Arguments step__splitCtor [Constructor c A Gamma Delta].
Arguments step__splitProd [Constructor A B Gamma Delta].
Arguments step__splitArr [Constructor A B Gamma Delta Delta'].
Arguments step__splitOmega [Constructor Gamma Delta].
Arguments step__splitInterCtor [Constructor c A B Gamma Delta Delta'].
Arguments step__splitInterProd [Constructor A1 A2 B Gamma Delta Delta'].
Arguments step__splitInterArr [Constructor A1 A2 B Gamma Gamma' Delta1 Delta2 Delta3].
Arguments step__splitInterAssoc [Constructor A1 A2 B Gamma Delta Delta'].
Arguments step__splitInterOmega [Constructor B Gamma Delta Delta'].
Hint Constructors Semantics.
Notation "p1 ~~> p2" := (Semantics p1 p2).

Arguments premisses_Semantics [Constructor] [i p].

Ltac foo :=
  match goal with
  |[ x : Result |- _ ~~> ?x -> _] =>
   let stp := fresh "step" in
   let r := fresh "result" in
   move: x => [] r stp; apply: (premisses_Semantics stp); eauto; move: r
  | [|- _ ~~> _ -> _] =>
    let stp := fresh "step" in
    move => stp; apply: (premisses_Semantics stp); eauto; move: stp
  | [|- forall _, _] =>
    let x := fresh "x" in
    move => x; foo; move: x
  | [|- _] => idtac
  end.


Section RecursiveTargetsMachineSpec.
  Variable Constructor: ctor.
  Implicit Type p: @Instruction Constructor.
  Implicit Type r: @Result Constructor.

  Lemma Semantics_functional: forall p r1 r2, p ~~> r1 -> p ~~> r2 -> r1 = r2.
  Proof.
    move => p r1 r2 pr1.
    move: r2.
    elim: p r1 / pr1 => //.
    - foo.
    - foo.
    - foo.
      move => ?.
      move => ?.
      move => ?.move => ?.
      move => [] r stp.
      apply: (premisses_Semantics stp).

      move => ? ? ? ? [] ? pr2.
        by apply: (premisses_Semantics pr2); eauto.
    - move => ? ? ? ? [] ? pr2.
        by apply: (premisses_Semantics pr2).
    - 
    - 


