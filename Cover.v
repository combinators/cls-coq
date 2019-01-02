Require Import PeanoNat.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Relations.Relation_Operators.
From mathcomp Require Import all_ssreflect.
Require Import Types.

Set Bullet Behavior "Strict Subproofs".

Delimit Scope it_scope with IT.
Open Scope it_scope.

Import EqNotations.

Section Split.
  Variable Constructor: ctor.

  Definition MultiArrow: Type := seq (@IT Constructor) * (@IT Constructor).

  Definition safeSplit (Delta: seq (seq MultiArrow)): seq MultiArrow * seq (seq MultiArrow) :=
    match Delta with
    | [::] => ([::], [:: [::]])
    | [:: Delta ] => (Delta, [::[::]])
    | [:: Delta1 & Delta2 ] => (Delta1, Delta2)
    end.

  Fixpoint splitRec
           (A: @IT Constructor)
           (srcs: seq (@IT Constructor))
           (Delta: seq (seq MultiArrow)):
    seq (seq MultiArrow) :=
    if isOmega A
    then Delta
    else match A with
         | Arrow A B =>
           let (Delta1, Delta2) := safeSplit Delta in
           [:: [:: ([:: A & srcs], B) & Delta1] & splitRec A [:: A & srcs] Delta2]
         | A \cap B =>
           splitRec A srcs (splitRec B srcs Delta)
         | _ => Delta
         end.

  Definition splitTy (A: @IT Constructor): seq (seq MultiArrow) :=
    if isOmega A
    then [::]
    else splitRec A [::] [:: [:: ([::], A)]].

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
Hint Constructors Instruction.

Definition dcap {Constructor: ctor} (A B: @IT Constructor): @IT Constructor :=
  if checkSubtypes A B
  then A
  else if checkSubtypes B A
       then B
       else A \cap B.
Notation "A \dcap B" := (Inter A B) (at level 80, right associativity) : it_scope.

(** A machine a machine covering paths with multi arrows **)
Section CoverMachine.
  Variable Constructor: ctor.

  Fixpoint partitionCover
             (covered: seq (@IT Constructor))
             (toCover: seq (@IT Constructor)): seq (@IT Constructor) * seq (@IT Constructor) :=
    match toCover with
    | [::] => ([::], [::])
    | [:: A & Delta ] =>
      let (coveredFresh, uncovered) := partitionCover covered Delta in
      if A \in covered
      then ([:: A & coveredFresh], uncovered)
      else (coveredFresh, [:: A & uncovered])
    end. 

  Definition mergeMultiArrow
             (arrow: MultiArrow)
             (srcs: seq (@IT Constructor))
             (tgt: @IT Constructor): MultiArrow :=
    (map (fun src => src.1 \dcap src.2) (zip srcs arrow.1), tgt \cap arrow.2).

  (** Small step semantics of the cover machine **)
  Inductive StepSemantics:
    @State Constructor * seq (@Instruction Constructor) ->
    @State Constructor * seq (@Instruction Constructor) -> Prop :=
  | step__done: forall s toCover p,
      (s, [:: Cover [::] toCover & p]) ~~> (s, p)
  | step__doneContinue: forall s toCover currentResult p,
      (s, [:: ContinueCover [::] toCover currentResult & p]) ~~> (s, p)
  | step__skip: forall s srcs tgt covered splits toCover p,
      ((partitionCover covered toCover).1 == [::]) ->
      (s, [:: Cover [:: (srcs, tgt, covered) & splits] toCover & p])
        ~~> (s, [:: Cover splits toCover & p])
  | step__skipContinue: forall s srcs tgt covered splits toCover currentResult p,
      ((partitionCover covered toCover).1 == [::]) ->
      (s, [:: ContinueCover [:: (srcs, tgt, covered) & splits] toCover currentResult & p])
        ~~> (s, [:: ContinueCover splits toCover currentResult & p])
  | step__addDone: forall s srcs tgt covered splits toCover p,
      ((partitionCover covered toCover).1 != [::]) ->
      ((partitionCover covered toCover).2 == [::]) ->
      (s, [:: Cover [:: (srcs, tgt, covered) & splits] toCover & p])
        ~~> ([:: (srcs, tgt) & s], [:: Cover splits toCover & p])
  | step__mergeDone:
      forall s srcs tgt covered splits toCover currentResult p,
      ((partitionCover covered toCover).1 != [::]) ->
      ((partitionCover covered toCover).2 == [::]) ->
      (s, [:: ContinueCover [:: (srcs, tgt, covered) & splits] toCover currentResult & p])
        ~~> ( [:: mergeMultiArrow currentResult srcs tgt & s]
            , [:: ContinueCover splits toCover currentResult & p])
  | step__continue:
      forall s srcs tgt covered splits toCover p,
        ((partitionCover covered toCover).1 != [::]) ->
        ((partitionCover covered toCover).2 != [::]) ->
        (s, [:: Cover [:: (srcs, tgt, covered) & splits] toCover & p])
          ~~> ( s
              , [:: ContinueCover splits (partitionCover covered toCover).2 (srcs, tgt)
                 , Cover splits toCover 
                   & p])
  | step__continueMergeAlways:
      forall s srcs tgt covered splits toCover currentResult p,
        ((partitionCover covered toCover).1 != [::]) ->
        ((partitionCover covered toCover).2 != [::]) ->
        ((mergeMultiArrow currentResult srcs tgt).1 == currentResult.1) ->
        (s, [:: ContinueCover [:: (srcs, tgt, covered) & splits] toCover currentResult & p])
          ~~> (s
             , [:: ContinueCover
                   splits (partitionCover covered toCover).2
                   (mergeMultiArrow currentResult srcs tgt)
                & p])
  | step__continueMergeOptions:
      forall s srcs tgt covered splits toCover currentResult p,
        ((partitionCover covered toCover).1 != [::]) ->
        ((partitionCover covered toCover).2 != [::]) ->
        ((mergeMultiArrow currentResult srcs tgt).1 != currentResult.1) ->
        (s, [:: ContinueCover [:: (srcs, tgt, covered) & splits] toCover currentResult & p])
          ~~> (s
             , [:: ContinueCover
                   splits (partitionCover covered toCover).2
                   (mergeMultiArrow currentResult srcs tgt)
                , ContinueCover splits toCover currentResult
                & p])
  where "p1 ~~> p2" := (StepSemantics p1 p2).

  Definition Semantics := clos_trans_1n _ StepSemantics.
End CoverMachine.


Arguments partitionCover [Constructor].
Arguments mergeMultiArrow [Constructor].

Arguments StepSemantics [Constructor].
Arguments step__done [Constructor s toCover p].
Arguments step__doneContinue [Constructor s toCover currentResult p].
Arguments step__skip [Constructor s srcs tgt covered splits toCover p].
Arguments step__skipContinue [Constructor s srcs tgt covered splits toCover currentResult p].
Arguments step__addDone [Constructor s srcs tgt covered splits toCover p].
Arguments step__mergeDone [Constructor s srcs tgt covered splits toCover currentResult p].
Arguments step__continue [Constructor s srcs tgt covered splits toCover p].
Arguments step__continueMergeAlways [Constructor s srcs tgt covered splits toCover currentResult p].
Arguments step__continueMergeOptions [Constructor s srcs tgt covered splits toCover currentResult p].
Hint Constructors StepSemantics.

Arguments Semantics [Constructor].

Notation "p1 ~~> p2" := (StepSemantics p1 p2).
Notation "p1 '~~>[+]' p2" := (Semantics p1 p2) (at level 70, no associativity) : it_scope.

(** Small step inversion for the cover machine **)
Section CoverMachineInversion.
  Variable Constructor: ctor.

  Definition CoverMachine_inv
             {sp1 sp2: @State Constructor * seq (@Instruction Constructor)}
             (prf: sp1 ~~> sp2)
             (X: @State Constructor * seq (@Instruction Constructor) ->
                 @State Constructor * seq (@Instruction Constructor) -> Prop) :=
    let diag (x y: @State Constructor *  seq (@Instruction Constructor)): Prop :=
        let (s1, p1) := x in
        let (s2, p2) := y in
        match p1 return Prop with
        |  [:: Cover [::] toCover & p1] =>
           (X (s1, [:: Cover [::] toCover & p1]) (s1, p1) ->
            X (s1, [:: Cover [::] toCover & p1]) (s2, p2))%type
        | [:: ContinueCover [::] toCover currentResult & p1] =>
          (X (s1, [:: ContinueCover [::] toCover currentResult & p1]) (s1, p1) ->
           X (s1, [:: ContinueCover [::] toCover currentResult & p1]) (s2, p2))%type
        | [:: Cover [:: (srcs, tgt, covered) & splits] toCover & p1] =>
          ((((partitionCover covered toCover).1 == [::]) ->
            X (s1, [:: Cover [:: (srcs, tgt, covered) & splits] toCover & p1])
              (s1, [:: Cover splits toCover & p1])) ->
           (((partitionCover covered toCover).1 != [::]) ->
            ((partitionCover covered toCover).2 == [::]) ->
            X (s1, [:: Cover [:: (srcs, tgt, covered) & splits] toCover & p1])
              ([:: (srcs, tgt) & s1], [:: Cover splits toCover & p1])) ->
           (((partitionCover covered toCover).1 != [::]) ->
            ((partitionCover covered toCover).2 != [::]) ->
            X (s1, [:: Cover [:: (srcs, tgt, covered) & splits] toCover & p1])
              (s1, [:: ContinueCover splits (partitionCover covered toCover).2 (srcs, tgt)
                    , Cover splits toCover 
                      & p1])) ->
           X (s1, [:: Cover [:: (srcs, tgt, covered) & splits] toCover & p1]) (s2, p2))%type
        | [:: ContinueCover [:: (srcs, tgt, covered) & splits] toCover currentResult & p1] =>
          ((((partitionCover covered toCover).1 == [::]) ->
            X (s1, [:: ContinueCover [:: (srcs, tgt, covered) & splits] toCover currentResult & p1])
              (s1, [:: ContinueCover splits toCover currentResult & p1])) ->
           (((partitionCover covered toCover).1 != [::]) ->
            ((partitionCover covered toCover).2 == [::]) ->
            X (s1, [:: ContinueCover [:: (srcs, tgt, covered) & splits] toCover currentResult & p1])
              ([:: mergeMultiArrow currentResult srcs tgt & s1]
               , [:: ContinueCover splits toCover currentResult & p1])) ->
           (((partitionCover covered toCover).1 != [::]) ->
            ((partitionCover covered toCover).2 != [::]) ->
            ((mergeMultiArrow currentResult srcs tgt).1 == currentResult.1) ->
            X (s1, [:: ContinueCover [:: (srcs, tgt, covered) & splits] toCover currentResult & p1])
              (s1
               , [:: ContinueCover
                     splits (partitionCover covered toCover).2
                     (mergeMultiArrow currentResult srcs tgt)
                  & p1])) ->
           (((partitionCover covered toCover).1 != [::]) ->
            ((partitionCover covered toCover).2 != [::]) ->
            ((mergeMultiArrow currentResult srcs tgt).1 != currentResult.1) ->
            X (s1, [:: ContinueCover [:: (srcs, tgt, covered) & splits] toCover currentResult & p1])
              (s1
               , [:: ContinueCover
                     splits (partitionCover covered toCover).2
                     (mergeMultiArrow currentResult srcs tgt)
                  , ContinueCover splits toCover currentResult
                    & p1])) ->
           X (s1, [:: ContinueCover [:: (srcs, tgt, covered) & splits] toCover currentResult & p1]) (s2, p2))%type
        | _ => False
        end in
    match prf in x ~~> y return diag x y with
    | step__done s toCover p =>
      fun k => k
    | step__doneContinue s toCover currentResult p =>
      fun k => k
    | step__skip s srcs tgt covered splits toCover p noFresh =>
      fun k _ _ => k noFresh
    | step__skipContinue s srcs tgt covered splits toCover currentResult p noFresh =>
      fun k _ _ _ => k noFresh
    | step__addDone s srcs tgt covered splits toCover p fresh noLeft =>
      fun _ k _ => k fresh noLeft
    | step__mergeDone s srcs tgt covered splits toCover currentResult p fresh noLeft =>
      fun _ k _ _ => k fresh noLeft
    | step__continue s srcs tgt covered splits toCover p fresh someLeft =>
      fun _ _ k => k fresh someLeft
    | step__continueMergeAlways s srcs tgt covered splits toCover currentResult p fresh someLeft redundant =>
      fun _ _ k _ => k fresh someLeft redundant
    | step__continueMergeOptions s srcs tgt covered splits toCover currentResult p fresh someLeft notRedundant =>
      fun _ _ _ k => k fresh someLeft notRedundant
    end.

End CoverMachineInversion.

Arguments CoverMachine_inv [Constructor] [sp1 sp2].

Section CoverMachineProperties.
  Variable Constructor: ctor.
  Implicit Type p: seq (@Instruction Constructor).
  Implicit Type s: @State Constructor.
  Implicit Type sp: @State Constructor * seq (@Instruction Constructor).

  Lemma coverMachineFunctional_step:
    forall sp sp1 sp2, sp ~~> sp1 -> sp ~~> sp2 -> sp1 = sp2.
  Proof.
    move => [] s p [] s1 p1 [] s2 p2 prf1.
    move: (CoverMachine_inv prf1 (fun x y => (x ~~> (s2, p2) -> y = (s2, p2))%type)).
    move: prf1 => _.
    case: p => //=.
    case => //=.
    case => //=.
    - move => toCover p res.
      apply: res.
      move => /CoverMachine_inv res'.
        by apply: (res' (fun x y => (s, p) = y)%type).
    - move => [] [] srcs tgt covered splits toCover p res.
      apply: res.
      + move => noFresh.
        move => /CoverMachine_inv res'.
        apply: (res' (fun x y => _ = y)%type) => //;
          by rewrite noFresh.
      + move => fresh noLeft.
        move => /CoverMachine_inv res'.
        apply: (res' (fun x y => _ = y)%type) => //.
        * move => noFresh.
          move: fresh.
            by rewrite noFresh.
        * by rewrite noLeft.
      + move => fresh someLeft.
        move => /CoverMachine_inv res'.
        apply: (res' (fun x y => _ = y)%type) => //.
        * move => noFresh.
          move: fresh.
            by rewrite noFresh.
        * move => _ noLeft.
          move: someLeft.
            by rewrite noLeft.
    - case.
      + move => toCover currentResult p res.
        apply: res.
        move => /CoverMachine_inv res'.
          by apply: (res' (fun x y => (s, p) = y)%type).
      + move => [] [] srcs tgt covered splits toCover currentResult p res.
        apply: res.
        * move => noFresh.
          move => /CoverMachine_inv res'.
          apply: (res' (fun x y => _ = y)%type) => //;
            by rewrite noFresh.
        * move => fresh noLeft.
          move => /CoverMachine_inv res'.
          apply: (res' (fun x y => _ = y)%type) => //; try by rewrite noLeft.
          move => noFresh.
          move: fresh.
            by rewrite noFresh.
        * move => fresh someLeft redundant.
          move => /CoverMachine_inv res'.
          apply: (res' (fun x y => _ = y)%type) => //.
          ** move => noFresh.
             move: fresh.
               by rewrite noFresh.
          ** move => _ noLeft.
             move: someLeft.
               by rewrite noLeft.
          ** by rewrite redundant.
        * move => fresh someLeft notRedundant.
          move => /CoverMachine_inv res'.
          apply: (res' (fun x y => _ = y)%type) => //.
          ** move => noFresh.
             move: fresh.
               by rewrite noFresh.
          ** move => _ noLeft.
             move: someLeft.
               by rewrite noLeft.
          ** move => _ _ redundant.
             move: notRedundant.
               by rewrite redundant.
  Qed.

  Reserved Notation "p1 '~~>[' n ']' p2" (at level 70, no associativity).
  Inductive nStepSemantics:
    nat -> 
    @State Constructor * seq (@Instruction Constructor) ->
    @State Constructor * seq (@Instruction Constructor) -> Prop :=
  | LastStep: forall sp1 sp2,
      sp1 ~~> sp2 ->
      sp1 ~~>[1] sp2
  | MoreSteps: forall n sp1 sp2 sp3,
      sp1 ~~> sp2 ->
      sp2 ~~>[n.+1] sp3 ->
      sp1 ~~>[n.+2] sp3
  where "sp1 '~~>[' n ']' sp2" := (nStepSemantics n sp1 sp2).
  Hint Constructors nStepSemantics.

  Lemma nStepSemantics_sound: forall n s1 p1 s2 p2,
      (s1, p1) ~~>[n] (s2, p2) ->
      (s1, p1) ~~>[+] (s2, p2).
  Proof.
    move => n s1 p1 s2 p2.
    elim.
    - move => *.
        by apply: t1n_step.
    - move => ? ? ? ? prf *.
        by apply: t1n_trans; first by exact prf.
  Qed.

  Lemma nStepSemantics_complete:
    forall sp1 sp2,
      sp1 ~~>[+] sp2 ->
      exists n, sp1 ~~>[n] sp2.
  Proof.
    move => sp1 sp2 prf.
    elim: sp1 sp2 / prf.
    - move => sp1 sp2 prf.
      exists 1.
        by apply LastStep.
    - move => sp1 sp2 sp3 prf _ [] n prfs.
      exists (n.+1).
      move: prf.
      case: n sp2 sp3 / prfs.
      + move => ? ? ? prf.
        apply: MoreSteps; first by exact prf.
          by apply: LastStep.
      + move => ? ? ? ? prf1 ? prf2.
        apply: MoreSteps; first by exact prf2.
          by apply: MoreSteps; first by exact prf1.
  Qed.

  Definition nStepSemantics_inv n sp1 sp2 (prf: sp1 ~~>[n] sp2)
             (X: nat ->
                 @State Constructor * seq (@Instruction Constructor) ->
                 @State Constructor * seq (@Instruction Constructor) -> Prop) :=
    let diag n sp1 sp2 :=
        match n return Prop with
        | 0 => False
        | 1 =>
          ((sp1 ~~> sp2 -> X 1 sp1 sp2) -> X 1 sp1 sp2)%type
        | n.+2 =>
          (((forall sp3, sp1 ~~> sp3 -> sp3 ~~>[n.+1] sp2 -> X (n.+2) sp1 sp2)%type) ->
           X (n.+2) sp1 sp2)%type
        end in
    match prf in sp1 ~~>[n] sp2 return diag n sp1 sp2 with
    | LastStep _ _ prf => fun k => k prf
    | MoreSteps _ _ _ _ prf1 prf2 =>
      fun k => k _ prf1 prf2
    end.
  
  Lemma coverMachineFunctional:
    forall n sp sp1 sp2, sp ~~>[n] sp1 -> sp ~~>[n] sp2 -> sp1 = sp2.
  Proof.
    move => n sp sp1 sp2 prf1.
    move: sp2.
    elim: n sp sp1 / prf1.
    - move => sp1 sp2 prf1 sp3 /nStepSemantics_inv res.
      apply: (res (fun _ _ sp3 => sp2 = sp3)) => prf2.
        by apply: coverMachineFunctional_step; first by exact prf1.
    - move => n sp1 sp2 sp3 prf prfs IH sp4 /nStepSemantics_inv res.
      apply: (res (fun _ _ sp4 => sp3 = sp4)).
        by move => sp2' /(coverMachineFunctional_step _ _ _ prf) <- /IH.
  Qed.

  (** The set of instructions from the domain of the cover machine relation,
       i.e. { (s, p) | exists s', (s, p) ~~>[+] (s', [::]) } **)
  Inductive Domain: @State Constructor * seq (@Instruction Constructor) -> Prop :=
  | dom__doneEmpty: forall s toCover,
      Domain (s, [:: Cover [::] toCover])
  | dom__done: forall s toCover p,
      Domain (s, p) ->
      Domain (s, [:: Cover [::] toCover & p])
  | dom__doneContinueEmpty: forall s toCover currentResult,
      Domain (s, [:: ContinueCover [::] toCover currentResult ])
  | dom__doneContinue: forall s toCover currentResult p,
      Domain (s, p) ->
      Domain (s, [:: ContinueCover [::] toCover currentResult & p])
  | dom__skip: forall s srcs tgt covered splits toCover p,
      ((partitionCover covered toCover).1 == [::]) ->
      Domain (s, [:: Cover splits toCover & p]) ->
      Domain (s, [:: Cover [:: (srcs, tgt, covered) & splits] toCover & p])
  | dom__skipContinue: forall s srcs tgt covered splits toCover currentResult p,
      ((partitionCover covered toCover).1 == [::]) ->
      Domain (s, [:: ContinueCover splits toCover currentResult & p]) ->
      Domain (s, [:: ContinueCover [:: (srcs, tgt, covered) & splits] toCover currentResult & p])
  | dom__addDone: forall s srcs tgt covered splits toCover p,
      ((partitionCover covered toCover).1 != [::]) ->
      ((partitionCover covered toCover).2 == [::]) ->
      Domain ([:: (srcs, tgt) & s], [:: Cover splits toCover & p]) ->
      Domain (s, [:: Cover [:: (srcs, tgt, covered) & splits] toCover & p])
  | dom__mergeDone:
      forall s srcs tgt covered splits toCover currentResult p,
      ((partitionCover covered toCover).1 != [::]) ->
      ((partitionCover covered toCover).2 == [::]) ->
      Domain ([:: mergeMultiArrow currentResult srcs tgt & s]
              , [:: ContinueCover splits toCover currentResult & p]) ->
      Domain (s, [:: ContinueCover [:: (srcs, tgt, covered) & splits] toCover currentResult & p])
  | dom__continue:
      forall s srcs tgt covered splits toCover p,
        ((partitionCover covered toCover).1 != [::]) ->
        ((partitionCover covered toCover).2 != [::]) ->
        Domain ( s
                 , [:: ContinueCover splits (partitionCover covered toCover).2 (srcs, tgt)
                    , Cover splits toCover 
                      & p]) ->
        Domain (s, [:: Cover [:: (srcs, tgt, covered) & splits] toCover & p])
  | dom__continueMergeAlways:
      forall s srcs tgt covered splits toCover currentResult p,
        ((partitionCover covered toCover).1 != [::]) ->
        ((partitionCover covered toCover).2 != [::]) ->
        ((mergeMultiArrow currentResult srcs tgt).1 == currentResult.1) ->
        Domain (s
                , [:: ContinueCover
                      splits (partitionCover covered toCover).2
                      (mergeMultiArrow currentResult srcs tgt)
                   & p]) ->
        Domain (s, [:: ContinueCover [:: (srcs, tgt, covered) & splits] toCover currentResult & p])
  | dom__continueMergeOptions:
      forall s srcs tgt covered splits toCover currentResult p,
        ((partitionCover covered toCover).1 != [::]) ->
        ((partitionCover covered toCover).2 != [::]) ->
        ((mergeMultiArrow currentResult srcs tgt).1 != currentResult.1) ->
        Domain (s
                , [:: ContinueCover
                      splits (partitionCover covered toCover).2
                      (mergeMultiArrow currentResult srcs tgt)
                   , ContinueCover splits toCover currentResult
                     & p]) ->
        Domain (s, [:: ContinueCover [:: (srcs, tgt, covered) & splits] toCover currentResult & p]).

  Arguments dom__doneEmpty [s toCover].
  Arguments dom__done [s toCover p].
  Arguments dom__doneContinueEmpty [s toCover currentResult].
  Arguments dom__doneContinue [s toCover currentResult p].
  Arguments dom__skip [s srcs tgt covered splits toCover p].
  Arguments dom__skipContinue [s srcs tgt covered splits toCover currentResult p].
  Arguments dom__addDone [s srcs tgt covered splits toCover p].
  Arguments dom__mergeDone [s srcs tgt covered splits toCover currentResult p].
  Arguments dom__continue [s srcs tgt covered splits toCover p].
  Arguments dom__continueMergeAlways [s srcs tgt covered splits toCover currentResult p].
  Arguments dom__continueMergeOptions [s srcs tgt covered splits toCover currentResult p].
  Hint Constructors Domain.

  Definition splitsOf (i: @Instruction Constructor) :=
    match i with
    | Cover splits _ => splits
    | ContinueCover splits _ _ => splits
    end.

  Definition sumOfSplits p : nat :=
    \sum_(i <- p) ((seq.size (splitsOf i)).+1).

  Lemma coverMachine_total: forall s i p, Domain (s, [:: i & p]).
  Proof.
    move => s i p.
    move: s.
    apply: (fun res => induction_ltof1 _
                                    (fun ip => sumOfSplits [:: ip.1 & ip.2])
                                    (fun ip => forall s, Domain (s, [:: ip.1 & ip.2]))
                                    res (i, p)).
    move: i p => _ _ [] [] [].
    - move => toCover [] //= i p IH s.
      apply: dom__done.
      apply: (IH (i, p)).
        by rewrite /ltof /sumOfSplits unlock //=.
    - move => [] [] srcs tgt covered splits toCover p IH s.
      case fresh: (partitionCover covered toCover).1.
      + apply: dom__skip; first by rewrite fresh.
        apply: (IH (_, p)).
          by rewrite /ltof /sumOfSplits unlock //=.
      + case left: (partitionCover covered toCover).2.
        * apply: dom__addDone.
          ** by rewrite fresh.
          ** by rewrite left.
          ** apply: (IH (_, p)).
               by rewrite /ltof /sumOfSplits unlock //=.
        * apply: dom__continue.
          ** by rewrite fresh.
          ** by rewrite left.
          ** rewrite /=.
             apply: (IH (_, p)).
               by rewrite /ltof /sumOfSplits unlock //=.



  
    

