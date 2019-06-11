Require Import PeanoNat.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Relations.Relation_Operators.
From mathcomp Require Import all_ssreflect.
Require Import PreOrders.
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

Definition dcap {Constructor: ctor} (A B: @IT Constructor): @IT Constructor :=
  if checkSubtypes A B
  then A
  else if checkSubtypes B A
       then B
       else A \cap B.
Notation "A \dcap B" := (dcap A B) (at level 80, right associativity) : it_scope.

Fixpoint dintersect {Constructor: ctor} (xs: seq (@IT Constructor)) : IT :=
    match xs with
    | [::] => Omega
    | [:: A] => A
    | [:: A & Delta] => A \dcap (dintersect Delta)
    end.

Notation "\bigdcap_ ( i <- xs ) F" :=
  (dintersect (map (fun i => F) xs)) (at level 41, F at level 41, i, xs at level 50,
                          format "'[' \bigdcap_ ( i <- xs ) '/ ' F ']'") : it_scope.

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

  Definition stillPossible
             (splits: seq (@MultiArrow Constructor * seq (@IT Constructor)))
             (toCover: seq (@IT Constructor)): bool :=
    all (fun A => has (fun covered => A \in covered) (map snd splits)) toCover.

  Definition mergeMultiArrow
             (arrow: MultiArrow)
             (srcs: seq (@IT Constructor))
             (tgt: @IT Constructor): MultiArrow :=
    (map (fun src => src.1 \dcap src.2) (zip srcs arrow.1), tgt \cap arrow.2).

  (** Small step semantics of the cover machine **)
  Inductive StepSemantics:
    @State Constructor * seq (@Instruction Constructor) ->
    @State Constructor * seq (@Instruction Constructor) -> Prop :=
  | step__checkPrune: forall s splits toCover p,
      ~~(stillPossible splits toCover) ->
      (s, [:: CheckCover splits toCover & p]) ~~> (s, p)
  | step__checkContinuePrune: forall s splits toCover currentResult p,
      ~~(stillPossible splits toCover) ->
      (s, [:: CheckContinueCover splits toCover currentResult & p]) ~~> (s, p)
  | step__checkOk: forall s splits toCover p,
      stillPossible splits toCover ->
      (s, [:: CheckCover splits toCover & p]) ~~> (s, [:: Cover splits toCover & p])
  | step__checkContinueOk: forall s splits toCover currentResult p,
      stillPossible splits toCover ->
      (s, [:: CheckContinueCover splits toCover currentResult & p])
        ~~> (s, [:: ContinueCover splits toCover currentResult & p])
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
        ~~> ([:: (srcs, tgt) & s], [:: CheckCover splits toCover & p])
  | step__mergeDone:
      forall s srcs tgt covered splits toCover currentResult p,
      ((partitionCover covered toCover).1 != [::]) ->
      ((partitionCover covered toCover).2 == [::]) ->
      (s, [:: ContinueCover [:: (srcs, tgt, covered) & splits] toCover currentResult & p])
        ~~> ( [:: mergeMultiArrow currentResult srcs tgt & s]
            , [:: CheckContinueCover splits toCover currentResult & p])
  | step__continue:
      forall s srcs tgt covered splits toCover p,
        ((partitionCover covered toCover).1 != [::]) ->
        ((partitionCover covered toCover).2 != [::]) ->
        (s, [:: Cover [:: (srcs, tgt, covered) & splits] toCover & p])
          ~~> ( s
              , [:: ContinueCover splits (partitionCover covered toCover).2 (srcs, tgt)
                 , CheckCover splits toCover 
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
                , CheckContinueCover splits toCover currentResult
                & p])
  where "p1 ~~> p2" := (StepSemantics p1 p2).

  Definition Semantics := clos_refl_trans_1n _ StepSemantics.
End CoverMachine.


Arguments partitionCover [Constructor].
Arguments mergeMultiArrow [Constructor].
Arguments stillPossible [Constructor].

Arguments StepSemantics [Constructor].
Arguments step__checkPrune [Constructor s splits toCover p].
Arguments step__checkContinuePrune [Constructor s splits toCover currentResult p].
Arguments step__checkOk [Constructor s splits toCover p].
Arguments step__checkContinueOk [Constructor s splits toCover currentResult p].
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
Notation "p1 '~~>[*]' p2" := (Semantics p1 p2) (at level 70, no associativity) : it_scope.

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
        | [:: CheckCover splits toCover & p1] =>
          ((~~(stillPossible splits toCover) ->
            X (s1, [:: CheckCover splits toCover & p1]) (s1, p1)) ->
           (stillPossible splits toCover ->
            X (s1, [:: CheckCover splits toCover & p1]) (s1, [:: Cover splits toCover & p1])) ->
           X (s1, [:: CheckCover splits toCover & p1]) (s2, p2))%type
        | [:: CheckContinueCover splits toCover currentResult & p1] =>
          ((~~(stillPossible splits toCover) ->
            X (s1, [:: CheckContinueCover splits toCover currentResult & p1]) (s1, p1)) ->
           (stillPossible splits toCover ->
            X (s1, [:: CheckContinueCover splits toCover currentResult & p1])
              (s1, [:: ContinueCover splits toCover currentResult & p1])) ->
           X (s1, [:: CheckContinueCover splits toCover currentResult & p1]) (s2, p2))%type
        | [:: Cover [::] toCover & p1] =>
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
              ([:: (srcs, tgt) & s1], [:: CheckCover splits toCover & p1])) ->
           (((partitionCover covered toCover).1 != [::]) ->
            ((partitionCover covered toCover).2 != [::]) ->
            X (s1, [:: Cover [:: (srcs, tgt, covered) & splits] toCover & p1])
              (s1, [:: ContinueCover splits (partitionCover covered toCover).2 (srcs, tgt)
                    , CheckCover splits toCover 
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
               , [:: CheckContinueCover splits toCover currentResult & p1])) ->
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
                  , CheckContinueCover splits toCover currentResult
                    & p1])) ->
           X (s1, [:: ContinueCover [:: (srcs, tgt, covered) & splits] toCover currentResult & p1]) (s2, p2))%type
        | _ => False
        end in
    match prf in x ~~> y return diag x y with
    | step__checkPrune s splits toCover p impossible =>
      fun k _ => k impossible
    | step__checkContinuePrune s splits toCover currentResult p impossible =>
      fun k _ => k impossible
    | step__checkOk s splits toCover p ok =>
      fun _ k => k ok
    | step__checkContinueOk s splits toCover currentResult p ok =>
      fun _ k => k ok
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
    - move => splits toCover p res.
      apply: res.
      + move => impossible /CoverMachine_inv res'.
        apply: (res' (fun x y => _ = y)%type) => //.
          by rewrite (negbTE impossible).
      + move => ok /CoverMachine_inv res'.
        apply: (res' (fun x y => _ = y)%type) => //.
          by rewrite ok.
    - move => splits toCover continueCover p res.
      apply: res.
      + move => impossible /CoverMachine_inv res'.
        apply: (res' (fun x y => _ = y)%type) => //.
          by rewrite (negbTE impossible).
      + move => ok /CoverMachine_inv res'.
        apply: (res' (fun x y => _ = y)%type) => //.
          by rewrite ok.
  Qed.

  Reserved Notation "p1 '~~>[' n ']' p2" (at level 70, no associativity).
  Inductive nStepSemantics:
    nat -> 
    @State Constructor * seq (@Instruction Constructor) ->
    @State Constructor * seq (@Instruction Constructor) -> Prop :=
  | Done: forall sp, sp ~~>[0] sp
  | MoreSteps: forall n sp1 sp2 sp3,
      sp1 ~~> sp2 ->
      sp2 ~~>[n] sp3 ->
      sp1 ~~>[n.+1] sp3
  where "sp1 '~~>[' n ']' sp2" := (nStepSemantics n sp1 sp2).
  Hint Constructors nStepSemantics.

  Lemma nStepSemantics_sound: forall n s1 p1 s2 p2,
      (s1, p1) ~~>[n] (s2, p2) ->
      (s1, p1) ~~>[*] (s2, p2).
  Proof.
    move => n s1 p1 s2 p2.
    elim.
    - move => *.
        by apply: rt1n_refl.
    - move => ? ? ? ? prf *.
      by apply: rt1n_trans; first by exact prf.
  Qed.

  Lemma nStepSemantics_complete:
    forall sp1 sp2,
      sp1 ~~>[*] sp2 ->
      exists n, sp1 ~~>[n] sp2.
  Proof.
    move => sp1 sp2 prf.
    elim: sp1 sp2 / prf.
    - move => sp.
      exists 0. by apply Done.
    - move => sp1 sp2 sp3 prf _ [] n prfs.
      exists (n.+1).
        by apply: MoreSteps; first by exact prf.
  Qed.

  Definition nStepSemantics_inv n sp1 sp2 (prf: sp1 ~~>[n] sp2)
             (X: nat ->
                 @State Constructor * seq (@Instruction Constructor) ->
                 @State Constructor * seq (@Instruction Constructor) -> Prop) :=
    let diag n sp1 sp2 :=
        match n return Prop with
        | 0 => (X 0 sp1 sp1 -> X 0 sp1 sp2)%type
        | n.+1 =>
          (((forall sp3, sp1 ~~> sp3 -> sp3 ~~>[n] sp2 -> X (n.+1) sp1 sp2)%type) ->
           X (n.+1) sp1 sp2)%type
        end in
    match prf in sp1 ~~>[n] sp2 return diag n sp1 sp2 with
    | Done _ => fun k => k
    | MoreSteps _ _ _ _ prf1 prf2 =>
      fun k => k _ prf1 prf2
    end.

  Lemma nStepSemantics_split_last: forall n sp1 sp2, sp1 ~~>[n.+1] sp2 -> exists sp3, sp1 ~~>[n] sp3 /\ sp3 ~~> sp2.
  Proof.
    elim.
    - move => sp1 sp2 prf.
      exists sp1. split; first by done.
      move: (nStepSemantics_inv _ _ _ prf) => /(fun prf => prf (fun n sp1 sp2 => sp1 ~~> sp2)) res.
      apply: res.
        by move => sp3 res /nStepSemantics_inv /(fun prf => prf (fun n sp1 sp2 => sp1 = sp2)) /(fun prf => prf Logic.eq_refl) <-.
    - move => n IH sp1 sp2 /nStepSemantics_inv /(fun prf => prf (fun n sp1 sp2 => exists sp3, sp1 ~~> sp3 /\ sp3 ~~>[n.-1] sp2)) /=.
      move => /(fun prf => prf (fun sp3 step steps => ex_intro (fun x => sp1 ~~> x /\ x ~~>[n.+1] sp2) sp3 (conj step steps))).
      case => sp3 [] step /IH [] sp4 [] steps step'.
      exists sp4; split; last by exact step'.
        by apply: MoreSteps; first by exact step.
  Qed.

  Lemma nStepSemantincs_inv_ind:
    forall (P: nat ->
          @State Constructor * seq (@Instruction Constructor) ->
          @State Constructor * seq (@Instruction Constructor) -> Prop),
      (forall sp, P 0 sp sp) ->
      (forall n sp1 sp2 sp3, sp1 ~~>[n] sp2 -> sp2 ~~> sp3 -> P n sp1 sp2 -> P (n.+1) sp1 sp3) ->
      forall n sp1 sp2, sp1 ~~>[n] sp2 -> P n sp1 sp2.
  Proof.
    move => P case__done case__step.
    elim.
    - move => sp1 sp2 /(nStepSemantics_inv) /(fun prf => prf (fun n sp1 sp2 => P n sp1 sp2)) res.
        by apply: res.
    - move => n IH sp1 sp2 /nStepSemantics_split_last [] sp3 [] steps step.
      apply: (case__step _ _ _ _ steps step).
        by apply: IH.
  Qed.

  Lemma coverMachineFunctional:
    forall n sp sp1 sp2, sp ~~>[n] sp1 -> sp ~~>[n] sp2 -> sp1 = sp2.
  Proof.
    move => n sp sp1 sp2 prf1.
    move: sp2.
    elim: n sp sp1 / prf1.
    - move => sp1 sp2 /nStepSemantics_inv res.
        by apply: (res (fun _ sp1 sp2 => sp1 = sp2)).
    - move => n sp1 sp2 sp3 prf prfs IH sp4 /nStepSemantics_inv res.
      apply: (res (fun _ _ sp4 => sp3 = sp4)).
        by move => sp2' /(coverMachineFunctional_step _ _ _ prf) <- /IH.
  Qed.

  Definition splitsOf (i: @Instruction Constructor) :=
    match i with
    | Cover splits _ => splits
    | ContinueCover splits _ _ => splits
    | CheckCover splits _ => splits
    | CheckContinueCover splits _ _ => splits
    end.

  Definition isChecked (i: @Instruction Constructor): bool :=
    match i with
    | Cover _ _ => true
    | ContinueCover _ _ _ => true
    | _ => false
    end.

  Definition measure (i: @Instruction Constructor): nat :=
    if isChecked i
    then 2 ^ (2 * (seq.size (splitsOf i)))
    else (2 ^ (2 * (seq.size (splitsOf i)))).+1.

  Lemma add2mul: forall m, m + m = 2 * m.
  Proof.
    move => m.
      by rewrite mulnC -iter_addn_0 /= addn0.
  Qed.

  Lemma ltn_add:
    forall (m n o p: nat),
      m < n -> o <= p -> m + o < n + p.
  Proof.
    move => m n o p prf1 prf2.
    apply: (@leq_ltn_trans (m + p)).
    - by rewrite leq_add2l.
    - by rewrite ltn_add2r.
  Qed.

  Lemma stepSize:
    forall sp1 sp2,
      sp1 ~~> sp2 ->
      (\sum_(i <- sp2.2) (measure i)) < \sum_(i <- sp1.2) (measure i).
  Proof.
    move => sp1 sp2 /CoverMachine_inv.
    move => /(fun res => res (fun sp1 sp2 =>
                            (\sum_(i <- sp2.2) (measure i))
                             < \sum_(i <- sp1.2) (measure i))).
    case: sp1 => s1 p1.
    case: sp2 => s2 p2.
    case: p1 => // i p1.
    case: i => //.
    - case.
      + move => toCover res.
        apply: res => //.
        rewrite unlock /=.
          by rewrite -[X in X < _]add0n ltn_add2r.
      + move => [] [] srcs tgt covered splits toCover res.
        apply: res => //.
        * rewrite unlock /= ltn_add2r /measure /= ltn_exp2l => //.
            by rewrite ltn_pmul2l.
        * rewrite unlock /= ltn_add2r /measure /=.
          rewrite -(add2mul (seq.size splits).+1) expnD expnS -(add2mul (2 ^ _)).
          rewrite mulnDl.
          rewrite -add2mul expnD -addn1.
          move => _ _.
          apply: ltn_add.
          ** rewrite mulnDr add2mul.
             apply: ltn_Pmull => //.
               by rewrite muln_gt0 expn_gt0.
          ** by rewrite muln_gt0 addn_gt0 expn_gt0.
        * rewrite unlock /= /= addnA ltn_add2r /measure /=.
          rewrite -(add2mul (seq.size splits).+1) expnD.
          rewrite -(add2mul (seq.size splits)) expnD.
          rewrite expnS -(add2mul).
          rewrite mulnDl.
          move => _ _.
          apply: ltn_add.
          ** rewrite ltn_mul2l expn_gt0 /= (add2mul) ltn_Pmull => //.
               by rewrite expn_gt0.
          ** rewrite ltn_mul2l expn_gt0 /= (add2mul) ltn_Pmull => //.
               by rewrite expn_gt0.
    - case.
      + move => toCover currentResult res.
        apply: res => //.
          by rewrite unlock /= -[X in X < _]add0n ltn_add2r.
      + move => [] [] srcs tgt covered splits toCover currentResult res.
        apply: res => //.
        * rewrite unlock /= ltn_add2r /measure /= ltn_exp2l => //.
            by rewrite ltn_pmul2l.
        * rewrite unlock /= ltn_add2r /measure /=.
          rewrite -(add2mul (seq.size splits).+1) expnD expnS -(add2mul (2 ^ _)).
          rewrite mulnDl.
          rewrite -add2mul expnD -addn1.
          move => _ _.
          apply: ltn_add.
          ** rewrite mulnDr add2mul.
             apply: ltn_Pmull => //.
               by rewrite muln_gt0 expn_gt0.
          ** by rewrite muln_gt0 addn_gt0 expn_gt0.
        * rewrite unlock /= ltn_add2r /measure /= ltn_exp2l => //.
            by rewrite ltn_pmul2l.
        * rewrite unlock /= /measure /= addnA ltn_add2r.
          rewrite -(add2mul (seq.size splits).+1) expnD.
          rewrite -(add2mul (seq.size splits)) expnD.
          rewrite expnS -(add2mul).
          rewrite mulnDl.
          move => _ _ _.
          apply: ltn_add.
          ** rewrite ltn_mul2l expn_gt0 /= (add2mul) ltn_Pmull => //.
               by rewrite expn_gt0.
          ** rewrite ltn_mul2l expn_gt0 /= (add2mul) ltn_Pmull => //.
               by rewrite expn_gt0.
    - move => splits toCover res.
      apply: res.
      + move => _.
          by rewrite unlock /= /measure /= -[X in X < _](add0n (reducebig _ _ _)) ltn_add2r.
      + move => _.
          by rewrite unlock /= /measure /= ltn_add2r ltnS.
    - move => splits toCover currentResult res.
      apply: res.
      + move => _.
          by rewrite unlock /= /measure /= -[X in X < _](add0n (reducebig _ _ _)) ltn_add2r.
      + move => _.
          by rewrite unlock /= /measure /= ltn_add2r ltnS.
  Qed.

  Lemma maxSteps:
    forall n sp1 sp2, sp1 ~~>[n] sp2 -> n <= \sum_(i <- sp1.2) (measure i).
  Proof.
    move => n sp1 sp2 prf.
    elim: n sp1 sp2 / prf.
    - case => s p /=.
        by case p.
    - move => n sp1 sp2 sp3 prf1 prf2 IH.
      apply: leq_ltn_trans; first by exact IH.
        by apply: stepSize.
  Qed.

  Definition step (sp1: (@State Constructor * seq (@Instruction Constructor))): (sp1.2 = [::]) + { sp2 | sp1 ~~> sp2 } :=
    match sp1 as sp1 return (sp1.2 = [::]) + { sp2 | sp1 ~~> sp2 } with
    | (s1, [::]) => inl (Logic.eq_refl _)
    | (s1, [:: CheckCover splits toCover & p1 ]) =>
      match boolP (stillPossible splits toCover) with
      | AltTrue ok => inr (exist _ (s1, [:: Cover splits toCover & p1]) (step__checkOk ok))
      | AltFalse impossible => inr (exist _ (s1, p1) (step__checkPrune impossible))
      end
    | (s1, [:: CheckContinueCover splits toCover currentResult & p1 ]) =>
      match boolP (stillPossible splits toCover) with
      | AltTrue ok => inr (exist _ (s1, [:: ContinueCover splits toCover currentResult & p1])
                                (step__checkContinueOk ok))
      | AltFalse impossible => inr (exist _ (s1, p1) (step__checkContinuePrune impossible))
      end
    | (s1, [:: Cover [::] toCover  & p1 ]) => inr (exist _ (s1, p1) step__done)
    | (s1, [:: ContinueCover [::] toCover currentResult  & p1 ]) => inr (exist _ (s1, p1) step__doneContinue)
    | (s1, [:: Cover [:: (srcs, tgt, covered) & splits ] toCover  & p1 ]) =>
      inr (let pc := partitionCover covered toCover in
           match boolP (pc.1 == [::]) with
           | AltTrue noFresh =>
             exist _ (s1, [:: Cover splits toCover & p1]) (step__skip noFresh)
           | AltFalse fresh =>
             match boolP (pc.2 == [::]) with
             | AltTrue noLeft =>
               exist _ ([:: (srcs, tgt) & s1],
                        [:: CheckCover splits toCover & p1]) (step__addDone fresh noLeft)
             | AltFalse someLeft =>
               exist _ (s1, [:: ContinueCover splits pc.2 (srcs, tgt), CheckCover splits toCover & p1])
                     (step__continue fresh someLeft)
             end
           end)
    | (s1, [:: ContinueCover [:: (srcs, tgt, covered) & splits ] toCover currentResult  & p1 ]) =>
      inr (let pc := partitionCover covered toCover in
           match boolP (pc.1 == [::]) with
           | AltTrue noFresh =>
             exist _ (s1, [:: ContinueCover splits toCover currentResult & p1]) (step__skipContinue noFresh)
           | AltFalse fresh =>
             match boolP (pc.2 == [::]) with
             | AltTrue noLeft =>
               exist _ ([:: mergeMultiArrow currentResult srcs tgt & s1],
                        [:: CheckContinueCover splits toCover currentResult & p1]) (step__mergeDone fresh noLeft)
             | AltFalse someLeft =>
               let ma := (mergeMultiArrow currentResult srcs tgt) in
               match boolP (ma.1 == currentResult.1) with
               | AltTrue redundant =>
                 exist _ (s1, [:: ContinueCover splits pc.2 ma & p1])
                       (step__continueMergeAlways fresh someLeft redundant)
               | AltFalse notRedundant =>
                 exist _ (s1, [:: ContinueCover splits pc.2 ma, CheckContinueCover splits toCover currentResult & p1])
                       (step__continueMergeOptions fresh someLeft notRedundant)
               end
             end
           end)
    end.

  (** The set of instructions from the domain of the cover machine relation,
       i.e. { (s1, p1) | exists s2, (s1, p1) ~~>[*] (s2, [::]) } **)
  Inductive Domain: @State Constructor * seq (@Instruction Constructor) -> Prop :=
  | Dom__done: forall s, Domain (s, [::])
  | Dom__step: forall sp1 sp2, sp1 ~~> sp2 -> Domain sp2 -> Domain sp1.
  Arguments Dom__done [s].
  Arguments Dom__step [sp1 sp2].
  Hint Constructors Domain.

  Lemma Domain_total: forall sp, Domain sp.
  Proof.
    move => sp1.
    suff: exists n s2, sp1 ~~>[n] (s2, [::]).
    { case: sp1 => s1 p1.
      move => [] n [].
      move: s1 p1.
      elim: n.
      - by move => s1 p1 s2 /(nStepSemantics_inv) /(fun res => res (fun _ sp1 sp2 => sp1 = sp2)) ->.
      - move => n IH s1 p1 s3 /(nStepSemantics_inv).
        move => /(fun res => res (fun k sp1 sp2 => exists sp3, sp1 ~~> sp3 /\ sp3 ~~>[k.-1] sp2)).
        move => /(fun res => res (fun sp3 prf prfs => ex_intro _ sp3 (conj prf prfs))).
        move => [] [] s4 p4 [] prf prfs.
        apply: Dom__step; first by exact prf.
        apply: IH.
        exact prfs. }
    move: (fun n => maxSteps n sp1).
    move: (\sum_(i <- sp1.2) (measure i)) => k.
    move: sp1.
    apply: (fun start step => nat_rect
                             (fun k =>
                                (forall sp1,
                                    (forall n sp2, (sp1 ~~>[ n] sp2 -> n <= k)%type) ->
                                    exists (n : nat) (s2 : State), sp1 ~~>[ n] (s2, [::]))%type)
                             start step k).
    - move => [] s1 p1 limit.
      exists 0, s1.
      case: (step (s1, p1)).
      + by move => /= ->.
      + by move => [] sp2 /(fun prf => MoreSteps 0 _ _ _ prf (Done _)) /limit.
    - move: k => _ k IH [] s1 p1 limit.
      case: (step (s1, p1)).
      + move => /= ->.
          by exists 0, s1.
      + move => [] sp2 prf.
        suff: (exists n s2, sp2 ~~>[n] (s2, [::])).
        { move => [] n [] s2 prfs.
          exists n.+1, s2.
            by apply: MoreSteps; first by exact prf. }
        apply: IH.
          by move => n sp3 /(MoreSteps _ _ _ _ prf) /limit.
  Qed.

  Lemma step_last: forall sp, sp.2 = [::] -> sp ~~>[*] (sp.1, [::]).
  Proof.
    move => [] s p <-.
      by apply: rt1n_refl.
  Qed.

  Lemma Domain_continue: forall sp1 sp2, Domain sp1 -> sp1 ~~> sp2 -> Domain sp2.
  Proof.
    move => sp1 [] s2 p2.
    case.
    - by move => s /CoverMachine_inv /(fun res => res (fun _ _ => True)).
    - move => [] s3 p3 [] s4 p4 prf1 res prf2.
        by rewrite -(coverMachineFunctional_step _ _ _ prf1 prf2).
  Defined.

  Lemma step_next: forall sp1 sp2 s3, sp1 ~~> sp2 -> sp2 ~~>[*] (s3, [::]) -> sp1 ~~>[*] (s3, [::]).
  Proof.
    move => [] s1 p1 [] s2 p2 s3 prf prfs.
      by apply: rt1n_trans; first by exact prf.
  Qed.

  Fixpoint coverMachine_rec (sp1 : (State * seq Instruction)) (dom: Domain sp1) {struct dom}: { s | sp1 ~~>[*] (s, [::])} :=
    match step sp1 return { s | sp1 ~~>[*] (s, [::])} with
    | inl prf => exist _ sp1.1 (step_last sp1 prf)
    | inr (exist sp2 prf) =>
      let (s, prfs) := coverMachine_rec sp2 (Domain_continue _ _ dom prf) in
      exist _ s (step_next _ sp2 _ prf prfs)
    end.

  Definition coverMachine sp : { s | sp ~~>[*] (s, [::])} := coverMachine_rec sp (Domain_total sp).

  Section StepInvariants.
    Fixpoint suffix {A: eqType} (s1 s2: seq A) {struct s2}: bool :=
      (s1 == s2)
      || if s2 is [:: _ & s2'] then suffix s1 s2' else false.

    Lemma suffixP {A: eqType} (s1 s2: seq A): reflect (exists (s: seq A), s2 == s ++ s1) (suffix s1 s2).
    Proof.
      elim: s2.
      - rewrite /= orbF.
        case: s1.
        + rewrite eq_refl.
          constructor.
            by (exists [::]).
        + move => x s1.
          rewrite /(_ == _) /=.
          constructor.
            by move => [] [].
      - move => y s2 /=.
        case s1__eq: (s1 == [:: y & s2]).
        +  move => _.
           constructor.
           exists [::].
             by move: s1__eq => /eqP ->.
        + rewrite /=.
          case (suffix s1 s2).
          * move => /rwP [] _ /(fun prf => prf isT) prf.
            constructor.
            case: prf => s /eqP ->.
              by (exists [:: y & s]).
          * move => /rwP [] disprf _.
            constructor.
            move => [] [].
            ** move: s1__eq => /eqP.
               rewrite eq_sym /=.
                 by move => devil /eqP /devil.
            ** move => x s /eqP [] _ /eqP prf.
                 by move: (disprf (ex_intro _ s prf)).
    Qed.

    Lemma suffix_empty {A: eqType}: forall (s: seq A), suffix [::] s.
    Proof. by elim. Qed.

    Lemma empty_suffix {A: eqType}: forall (s: seq A), suffix s [::] -> s = [::].
    Proof. by case. Qed.

    Lemma suffix_refl {A: eqType}: forall (s: seq A), suffix s s.
    Proof. by move => [] //= *; rewrite eq_refl. Qed.

    Lemma suffix_behead {A: eqType}: forall (s1 s2: seq A), suffix s1 s2 -> suffix (behead s1) s2.
    Proof.
      move => s1 s2.
      move: s1.
      elim: s2.
      - by move => _ /empty_suffix ->.
      - move => y s2 IH s1 /orP [].
        + move => /eqP -> /=.
            by rewrite suffix_refl orbT.
        + move => /IH /= ->.
            by rewrite orbT.
    Qed.

    Lemma suffix_trans {A: eqType}: forall (s1 s2 s3: seq A),
        suffix s1 s2 -> suffix s2 s3 -> suffix s1 s3.
    Proof.
      move => s1 s2.
      move: s1.
      elim: s2.
      - by move => s1 s3 /empty_suffix -> _; apply suffix_empty.
      - move => y s2 IH s1 s3 /orP [].
        + by move => /eqP ->.
        + rewrite -/suffix.
            by move => /IH prf /suffix_behead /prf.
    Qed.
    
    Lemma step_programStack:
      forall s1 p1 s2 p2, (s1, p1) ~~> (s2, p2) -> suffix (behead p1) p2.
    Proof.
      move => s1.
      case.
      - by move => *; apply: suffix_empty.
      - move => i p1 s2 p2 /(fun prf => CoverMachine_inv prf (fun sp1 sp2 => suffix (behead sp1.2) (sp2.2))).
        case: i => [] [].
        + move => ? prf.
          apply: prf.
            by apply: suffix_refl.
        + move => [] [] srcs tgt covered splits toCover prf.
          apply: prf; by move => *; rewrite /= suffix_refl; repeat rewrite orbT.
        + move => ? ? prf.
          apply: prf.
            by apply: suffix_refl.
        + move => [] [] srcs tgt covered splits toCover currentResult prf.
          apply: prf; by move => *; rewrite /= suffix_refl; repeat rewrite orbT.
        + move => ? prf.
          apply: prf.
          * move => _.
              by apply: suffix_refl.
          * move => _.
              by rewrite /= suffix_refl orbT.
        + move => ? ? ? prf.
          apply: prf.
          * move => _.
              by apply: suffix_refl.
          * move => _.
              by rewrite /= suffix_refl orbT.
        + move => ? ? prf.
          apply: prf.
          * move => _.
              by apply: suffix_refl.
          * move => _.
              by rewrite /= suffix_refl orbT.
        + move => ? ? ? ? prf.
          apply: prf.
          * move => _.
              by apply: suffix_refl.
          * move => _.
              by rewrite /= suffix_refl orbT.
    Qed.

    Lemma step_stateMonotonic:
      forall s1 p1 s2 p2, (s1, p1) ~~> (s2, p2) -> suffix s1 s2.
    Proof.
      move => s1.
      case.
      - by move => s2 p2 /(fun prf => CoverMachine_inv prf (fun _ _ => true)).
      - move => i p1 s2 p2 /(fun prf => CoverMachine_inv prf (fun sp1 sp2 => suffix (sp1.1) (sp2.1))).
        case: i => [] [].
        + move => ? prf.
          apply: prf.
            by apply: suffix_refl.
        + move => [] [] srcs tgt covered splits toCover prf.
          apply: prf; by move => *; rewrite /= suffix_refl; repeat rewrite orbT.
        + move => ? ? prf.
          apply: prf.
            by apply: suffix_refl.
        + move => [] [] srcs tgt covered splits toCover currentResult prf.
          apply: prf; by move => *; rewrite /= suffix_refl; repeat rewrite orbT.
        + move => ? prf.
          apply: prf; by move => _; apply: suffix_refl.
        + move => ? ? ? prf.
          apply: prf; by move => _; apply: suffix_refl.
        + move => ? ? prf.
          apply: prf; by move => _; apply: suffix_refl.
        + move => ? ? ? ? prf.
          apply: prf; by move => _; apply: suffix_refl.
    Qed.

    Lemma steps_stateMonotonic:
      forall sp1 sp2,  sp1 ~~>[*] sp2 -> suffix sp1.1 sp2.1.
    Proof.
      move => sp1 sp2 prf.
      elim: sp1 sp2 / prf.
      - by move => ?; apply: suffix_refl.
      - by move => [] s1 p1 [] s2 p2 sp3 /step_stateMonotonic /suffix_trans prf _ /prf.
    Qed.

    Fixpoint subseqs {A: Type} (xs: seq A): seq (seq A) :=
      if xs is [:: x & xs]
      then
        let rest := subseqs xs in
        (map (cons x) rest) ++ rest
      else [:: [::]].

    Lemma subseqs_subseq: forall {A: eqType} (xs ys: seq A), (ys \in subseqs xs) -> (subseq ys xs).
    Proof.
      move => A.
      elim.
      - by case.
      - move => x xs IH ys.
        rewrite /subseqs -/subseqs mem_cat.
        move => /orP [].
        + move: IH.
          elim: (subseqs xs) => // z zs IH1 IH2 /orP [].
          * move: IH1 => _.
            case: ys => // y ys /eqP [] -> ->.
            apply: (@cat_subseq _ [:: x] _ [:: x]) => //.
            apply: IH2.
              by rewrite in_cons eq_refl.
          * move => /IH1 IH.
            apply: IH.
            move => ? prf.
            apply: IH2.
              by rewrite in_cons prf orbT.
        + move => /IH prf.
          apply: subseq_trans; first by exact prf.
            by apply: subseq_cons.
    Qed.

    Lemma subseqs_empty: forall {A: eqType} (xs: seq A), [::] \in subseqs xs.
    Proof.
      move => A.
      elim => // x xs IH.
        by rewrite /= mem_cat IH orbT.
    Qed.

    Lemma subseq_subseqs: forall {A: eqType} (xs ys: seq A), subseq ys xs -> (ys \in subseqs xs).
    Proof.
      move => A.
      elim.
      - by case.
      - move => x xs IH.
        case.
        + move => _.
            by apply: subseqs_empty.
        + move => y ys.
          rewrite /=.
          case y__eq: (y == x).
          * move: y__eq => /eqP -> prf.
            rewrite mem_cat (introT orP) //=.
            left.
            move: (IH _ prf).
            move: IH => _ res.
              by rewrite mem_map => // xs1 xs2 [].
          * move => /IH prf.
              by rewrite mem_cat prf orbT.
    Qed.

    Definition mergeMultiArrows (ms: seq (@MultiArrow Constructor)): MultiArrow :=
      if ms is [:: m & ms]
      then foldl (fun m__s m => mergeMultiArrow m__s m.1 m.2) m ms
      else ([::], Omega).

    Fixpoint filterMergeMultiArrows (ms: seq (seq (@MultiArrow Constructor))): seq (@MultiArrow Constructor) :=
      match ms with
      | [::] => [::]
      | [:: [::] & mss ] => filterMergeMultiArrows mss
      | [:: [:: m & ms] & mss ] =>
        [:: mergeMultiArrows [:: m & ms] & filterMergeMultiArrows mss]
      end.

    Definition mergeComponentsOf (i: @Instruction Constructor): seq (@MultiArrow Constructor) :=
      match i with
      | Cover splits _ => map fst splits
      | ContinueCover splits _ currentResult => [:: currentResult & map fst splits]
      | CheckCover splits _ => map fst splits
      | CheckContinueCover splits _ currentResult => [:: currentResult & map fst splits]
      end.

    Lemma cat_prefix {A: eqType}: forall (s1 s2 s: seq A), s1 ++ s = s2 ++ s -> s1 = s2.
    Proof.
      elim.
      - move => s2 s prf.
        symmetry.
        apply: size0nil.
        move: prf => /(f_equal seq.size).
        rewrite size_cat size_cat /=.
          by move => /addIn ->.
      - move => x s1 IH [].
        + move => s prf.
          apply: size0nil.
          move: prf => /(f_equal seq.size).
          rewrite /= size_cat -[X in ((_ = X) -> _)%type](add0n (seq.size s)) -addn1 addnC addnA.
          move => /addIn.
            by rewrite add1n.
        + by move => y s2 s /= [] -> /IH ->.
    Qed.

    Lemma filterMergeMultiArrows_cat: forall mss1 mss2,
        filterMergeMultiArrows (mss1 ++ mss2) =
        filterMergeMultiArrows mss1 ++ filterMergeMultiArrows mss2.
    Proof.
      elim => //= ms mss1 IH mss2.
      case ms.
      - by apply: IH.
      - move => *; by rewrite IH.
    Qed.

    Lemma filterMergeMultiArrows_subseq: forall mss1 mss2,
        subseq mss1 mss2 -> subseq (filterMergeMultiArrows mss1) (filterMergeMultiArrows mss2).
    Proof.
      move => mss1 mss2.
      move: mss1.
      elim: mss2.
      - move => ?.
          by rewrite subseq0 => /eqP ->.
      - move => ms2 mss2 IH [].
        + by move => ?; apply: sub0seq.
        + move => ms1 mss1 /=.
          case ms__eq: (ms1 == ms2).
          * move => /IH.
            move: ms__eq => /eqP ->.
            case: ms2 => //= ? ?.
              by rewrite eq_refl.
          * move /IH.
            move: ms__eq.
            case: ms2 => // *.
              by apply: subseq_trans; last by apply: subseq_cons.
    Qed.

    Lemma all_nested_tl {A: eqType}:
      forall (P: A -> A -> bool) (x: A) (xs: seq A),
        all (fun y => all (P y) [:: x & xs]) [:: x & xs] ->
        all (fun x => all (P x) xs) xs.
    Proof.
      move => P x xs /allP prf.
      apply /allP.
      move => y inprf.
      move: (prf y).
      rewrite in_cons inprf orbT.
        by move => /(fun x => x isT) /andP [].
    Qed.

    Lemma all_nested_subseq {A: eqType}:
      forall (P: A -> A -> bool) (xs ys: seq A),
        subseq ys xs ->
        all (fun x => all (P x) xs) xs ->
        all (fun x => all (P x) ys) ys.
    Proof.
      move => P xs ys /mem_subseq subprf /allP prf.
      apply /allP.
      move => x /subprf /prf /allP res.
      apply /allP.
        by move => y /subprf /res.
    Qed.

    Lemma step_mergeComponents:
      forall s1 i p1 s2 p2,
        (s1, [:: i & p1]) ~~> (s2, p2) ->
        all (fun x => x \in filterMergeMultiArrows (subseqs (mergeComponentsOf i)))
            (take (seq.size s2 - seq.size s1) s2).
    Proof.
      move => s1 i p1 s2 p2 prf.
      move: (step_stateMonotonic _ _ _ _ prf) => /suffixP [] prefix /eqP eq_prf.
      rewrite eq_prf size_cat addnK take_size_cat; last by reflexivity.
      move: prefix eq_prf.
      move: prf => /(fun prf =>
                      CoverMachine_inv
                        prf
                        (fun sp1 sp2 =>
                           forall prefix, sp2.1 = prefix ++ sp1.1 ->
                                     all (fun x =>
                                            x \in filterMergeMultiArrows
                                                    (subseqs (mergeComponentsOf (head i sp1.2))))
                                         prefix)).
      case: i => [] [].
      - move => toCover res prefix /res prf.
        apply: prf.
        move => prefix' /=.
        rewrite -[X in (X = _ -> _)%type]cat0s.
          by move => /cat_prefix <-.
      - move => [] [] srcs tgt covered splits toCover res prefix /res prf.
        apply: prf.
        + move => _ prefix' /=.
          rewrite -[X in (X = _ -> _)%type]cat0s.
            by move => /cat_prefix <-.
        + move => _ _ prefix'.
          rewrite /= -cat1s.
          move => /cat_prefix <- //=.
          rewrite filterMergeMultiArrows_cat mem_cat andbT.
          apply: (introT orP).
          left.
          apply: (@mem_subseq _ (filterMergeMultiArrows [:: [:: (srcs, tgt)]])).
          * apply: filterMergeMultiArrows_subseq.
            have: ([:: [:: (srcs, tgt)]] = map (fun ms => [:: (srcs, tgt) & ms]) [:: [::]]) => // ->.
            apply: map_subseq.
            rewrite sub1seq.
              by apply: subseqs_empty.
          * by rewrite //= mem_seq1 eq_refl.
        + move => _ _ prefix' /=.
          rewrite -[X in (X = _ -> _)%type]cat0s.
            by move => /cat_prefix <-.
      - move => toCover currentResult res prefix /res prf.
        apply: prf.
        move => prefix' /=.
        rewrite -[X in (X = _ -> _)%type]cat0s.
          by move => /cat_prefix <-.
      - move => [] [] srcs tgt covered splits toCover currentResult res prefix /res prf.
        apply: prf.
        + move => _ prefix' /=.
          rewrite -[X in (X = _ -> _)%type]cat0s.
            by move => /cat_prefix <-.
        + move => _ _ prefix'.
          rewrite /= -cat1s.
          move => /cat_prefix <- //=.
          rewrite filterMergeMultiArrows_cat mem_cat andbT.
          apply: (introT orP).
          left.
          rewrite map_cat filterMergeMultiArrows_cat mem_cat.
          apply: (introT orP).
          left.
          rewrite -map_comp.
          apply: (@mem_subseq _ (filterMergeMultiArrows [:: [:: currentResult; (srcs, tgt)]])).
          * apply: filterMergeMultiArrows_subseq.
            have: ([:: [:: currentResult; (srcs, tgt)]] =
                   map (cons currentResult \o cons (srcs, tgt)) [:: [::]]) => // ->.
            apply: map_subseq.
            rewrite sub1seq.
              by apply: subseqs_empty.
          * by rewrite //= mem_seq1 eq_refl.
        + move => _ _ _ prefix' /=.
          rewrite -[X in (X = _ -> _)%type]cat0s.
            by move => /cat_prefix <-.
        + move => _ _ _ prefix' /=.
          rewrite -[X in (X = _ -> _)%type]cat0s.
            by move => /cat_prefix <-.
      - move => ? prf.
        apply: prf.
        + move => _ prefix' /=.
          rewrite -[X in (X = _ -> _)%type]cat0s.
            by move => /cat_prefix <-.
        + move => _ prefix' /=.
          rewrite -[X in (X = _ -> _)%type]cat0s.
            by move => /cat_prefix <-.
      - move => ? ? ? prf.
        apply: prf.
        + move => _ prefix' /=.
          rewrite -[X in (X = _ -> _)%type]cat0s.
            by move => /cat_prefix <-.
        + move => _ prefix' /=.
          rewrite -[X in (X = _ -> _)%type]cat0s.
            by move => /cat_prefix <-.
      - move => ? ? prf.
        apply: prf.
        + move => _ prefix' /=.
          rewrite -[X in (X = _ -> _)%type]cat0s.
            by move => /cat_prefix <-.
        + move => _ prefix' /=.
          rewrite -[X in (X = _ -> _)%type]cat0s.
            by move => /cat_prefix <-.
      - move => ? ? ? ? prf.
        apply: prf.
        + move => _ prefix' /=.
          rewrite -[X in (X = _ -> _)%type]cat0s.
            by move => /cat_prefix <-.
        + move => _ prefix' /=.
          rewrite -[X in (X = _ -> _)%type]cat0s.
            by move => /cat_prefix <-.
    Qed.

    Definition sound s p :=
      all (fun x => x \in flatten (map (fun i => filterMergeMultiArrows (subseqs (mergeComponentsOf i))) p)) s.

    Lemma step_sound:
      forall sp1 sp2, sp1 ~~> sp2 -> sound (take (seq.size sp2.1 - seq.size sp1.1) sp2.1) sp1.2.
    Proof.
      move => [] s1 p1 [] s2 p2.
      rewrite /= /sound.
      case: p1.
      - by move => /CoverMachine_inv  /(fun x => x (fun _ _ => true)).
      - move => i p1 prf.
        rewrite map_cons /=.
        apply: (introT allP).
        move => x inprf.
        rewrite mem_cat.
          by move: (step_mergeComponents _ _ _ _ _ prf) => /allP ->.
    Qed.

    Lemma step_splitsTail:
      forall s1 i1 p1 s2 p2,
        (s1, [:: i1 & p1]) ~~> (s2, p2) ->
        all (fun i2 => if isChecked i1 then splitsOf i2 == behead (splitsOf i1) else true)
            (take (seq.size p2 - seq.size p1) p2).
    Proof.
      move => s1 i1 p1 s2 p2 /CoverMachine_inv.
      move => /(fun prf => prf (fun sp1 sp2 =>
                              if sp1.2 is [:: i1 & p1]
                              then all (fun i2 => splitsOf i2 == behead (splitsOf i1))
                                       (take (seq.size sp2.2 - seq.size p1) sp2.2)
                              else true)).
      case: i1.
      - case.
        + move => toCover /= prf.
          apply: prf.
            by rewrite subnn take0.
        + move => [] [] srcs tgt covered splits toCover /= prf.
          apply: prf;
            move => *.
          * by rewrite -addn1 addnC addnK take0 /= andbT.
          * by rewrite -addn1 addnC addnK take0 /= andbT.
          * by rewrite -addn2 addnC addnK take0 /= andbT eq_refl.
      - case.
        + move => toCover currentResult /= prf.
          apply: prf.
            by rewrite subnn take0.
        + move => [] [] srcs tgt covered splits toCover currentResult /= prf.
          apply: prf; move => *.
          * by rewrite -addn1 addnC addnK take0 /= andbT.
          * by rewrite -addn1 addnC addnK take0 /= andbT.
          * by rewrite -addn1 addnC addnK take0 /= andbT.
          * by rewrite -addn2 addnC addnK take0 /= andbT eq_refl.
      - move => * /=.
          by apply: all_predT.
      - move => * /=.
          by apply: all_predT.
    Qed.

    Lemma step_mergeComponents_in:
      forall s1 i1 p1 s2 p2,
        (s1, [:: i1 & p1]) ~~> (s2, p2) ->
        all (fun i2 =>
               match i2 with
               | ContinueCover _ _ currentResult =>
                 currentResult \in filterMergeMultiArrows (subseqs (mergeComponentsOf i1))
               | CheckContinueCover _ _ currentResult =>
                 currentResult \in filterMergeMultiArrows (subseqs (mergeComponentsOf i1))
               | _ => true
               end) (take (seq.size p2 - seq.size p1) p2).
    Proof.
      move => s1 i1 p1 s2 p2 /CoverMachine_inv.
      move => /(fun prf => prf (fun sp1 sp2 =>
                              if sp1.2 is [:: i1 & p1]
                              then all (fun i2 =>
                                          match i2 with
                                          | ContinueCover _ _ currentResult =>
                                            currentResult \in filterMergeMultiArrows (subseqs (mergeComponentsOf i1))
                                          | CheckContinueCover _ _ currentResult =>
                                            currentResult \in filterMergeMultiArrows (subseqs (mergeComponentsOf i1))
                                          | _ => true
                                          end)
                                       (take (seq.size sp2.2 - seq.size p1) sp2.2)
                              else true)).
      case: i1.
      - case.
        + move => toCover /= prf.
          apply: prf.
            by rewrite subnn take0.
        + move => [] [] srcs tgt covered splits toCover /= prf.
          apply: prf;
            move => *.
          * by rewrite -addn1 addnC addnK take0.
          * by rewrite -addn1 addnC addnK take0.
          * rewrite -addn2 addnC addnK take0 /= andbT filterMergeMultiArrows_cat mem_cat.
            apply: (introT orP).
            left.
            apply: (@mem_subseq _ (filterMergeMultiArrows [:: [:: (srcs, tgt)]])).
            ** apply: filterMergeMultiArrows_subseq.
               have: ([:: [:: (srcs, tgt)]] = map (fun ms => [:: (srcs, tgt) & ms]) [:: [::]]) => // ->.
               apply: map_subseq.
               rewrite sub1seq.
                 by apply: subseqs_empty.
            ** by rewrite //= mem_seq1 eq_refl.
      - case.
        + move => toCover currentResult /= prf.
          apply: prf.
            by rewrite subnn take0.
        + move => [] [] srcs tgt covered splits toCover currentResult /= prf.
          apply: prf; move => *.
          * rewrite -addn1 addnC addnK take0 /= andbT filterMergeMultiArrows_cat mem_cat.
            apply: (introT orP).
            left.
            apply: (@mem_subseq _ (filterMergeMultiArrows [:: [:: currentResult]])).
            ** apply: filterMergeMultiArrows_subseq.
               have: ([:: [:: currentResult]] = map (fun ms => [:: currentResult & ms]) [:: [::]]) => // ->.
               apply: map_subseq.
                 by rewrite sub1seq mem_cat subseqs_empty orbT.
            ** by rewrite //= mem_seq1 eq_refl.
          * rewrite -addn1 addnC addnK take0 /= andbT filterMergeMultiArrows_cat mem_cat.
            apply: (introT orP).
            left.
            apply: (@mem_subseq _ (filterMergeMultiArrows [:: [:: currentResult]])).
            ** apply: filterMergeMultiArrows_subseq.
               have: ([:: [:: currentResult]] = map (fun ms => [:: currentResult & ms]) [:: [::]]) => // ->.
               apply: map_subseq.
                 by rewrite sub1seq mem_cat subseqs_empty orbT.
            ** by rewrite //= mem_seq1 eq_refl.
          * rewrite -addn1 addnC addnK take0 /= andbT filterMergeMultiArrows_cat mem_cat.
            apply: (introT orP).
            left.
            apply: (@mem_subseq _ (filterMergeMultiArrows [:: [:: currentResult; (srcs, tgt)]])).
            ** apply: filterMergeMultiArrows_subseq.
               have: ([:: [:: currentResult; (srcs, tgt)]] =
                      map (cons currentResult \o cons (srcs, tgt)) [:: [::]]) => // ->.
               rewrite map_cat.
               apply: subseq_trans; last by apply: prefix_subseq.
               rewrite -(map_comp (cons currentResult) (cons (srcs, tgt))).
               apply: map_subseq.
               rewrite sub1seq.
                 by apply: subseqs_empty.
            ** by rewrite //= mem_seq1 eq_refl.
          * rewrite -addn2 addnC addnK take0 /= andbT filterMergeMultiArrows_cat.
            apply: (introT andP).
            split; rewrite mem_cat map_cat filterMergeMultiArrows_cat mem_cat; apply (introT orP); left.
            ** apply: (introT orP).
               left.
               apply: (@mem_subseq _ (filterMergeMultiArrows [:: [:: currentResult; (srcs, tgt)]])).
               *** apply: filterMergeMultiArrows_subseq.
                   have: ([:: [:: currentResult; (srcs, tgt)]] =
                          map (cons currentResult \o cons (srcs, tgt)) [:: [::]]) => // ->.
                   rewrite -(map_comp (cons currentResult) (cons (srcs, tgt))).
                   apply: map_subseq.
                   rewrite sub1seq.
                     by apply: subseqs_empty.
               *** by rewrite //= mem_seq1 eq_refl.
            ** apply: (introT orP).
               right.
               apply: (@mem_subseq _ (filterMergeMultiArrows [:: [:: currentResult]])).
               *** apply: filterMergeMultiArrows_subseq.
                   have: ([:: [:: currentResult]] = map (fun ms => [:: currentResult & ms]) [:: [::]]) => // ->.
                   apply: map_subseq.
                     by rewrite sub1seq subseqs_empty.
               *** by rewrite //= mem_seq1 eq_refl.
      - move => splits toCover prf.
        apply: prf => /=.
        + by rewrite subnn take0.
        + by rewrite -addn1 addnC addnK take0.
      - move => splits toCover currentResult prf.
        apply: prf => /=.
        + by rewrite subnn take0.
        + rewrite -addn1 addnC addnK take0 all_seq1.
          move => _.
          apply: (@mem_subseq _ (filterMergeMultiArrows [:: [:: currentResult]])).
          * apply: filterMergeMultiArrows_subseq.
            have: ([:: [:: currentResult]] = map (fun ms => [:: currentResult & ms]) [:: [::]]) => // ->.
            apply: subseq_trans; last by apply: prefix_subseq.
            apply: map_subseq.
              by rewrite sub1seq subseqs_empty.
          * by rewrite //= mem_seq1 eq_refl.
    Qed.

    Lemma filterMergeMultiArrows_map_cons:
      forall m1 srcs tgt ms,
        filterMergeMultiArrows [seq mergeMultiArrow m1 srcs tgt :: i | i <- ms] =
        filterMergeMultiArrows [seq [:: m1, (srcs, tgt) & i] | i <- ms].
    Proof.
      move => m1 srcs tgt.
      elim => // m2 ms IH.
      do 2 rewrite map_cons.
        by rewrite /= IH.
    Qed.
    
    Lemma sound_reverse:
      forall s1 i p1 s2 p2 splits,
        (s1, [:: i & p1]) ~~> (s2, p2) ->
        sound splits p2 ->
        sound splits [:: i & p1].
    Proof.
      move => s1 i p1 s2 p2 splits prf.
      move: (step_splitsTail _ _ _ _ _ prf).
      move: (step_programStack _ _ _ _ prf) => stackPrf.
      move: stackPrf prf =>  /suffixP [] prefix /eqP -> prf.
      rewrite /= size_cat addnK take_cat subnn take0 cats0 ltnn /sound.
      move => splits__prfs /allP soundness.
      apply: (introT allP).
      move => s inprf.
      rewrite map_cons /= mem_cat.
      move: (soundness s inprf).
      rewrite map_cat flatten_cat /= mem_cat.
      move => /orP.
      case.
      - move => inPrefix.
        apply: (introT orP).
        left.
        rewrite /mergeComponentsOf.
        move: soundness prf splits__prfs => _.
        case: i.
        + move => splits1 toCover /CoverMachine_inv.
          case: splits1.
          * move => /(fun res => res (fun sp1 sp2 => behead sp1.2 = sp2.2)) /= /(fun res => res Logic.eq_refl) /(f_equal seq.size) /=.
            rewrite size_cat addnC -[X in (X = _ -> _)%type]addn0 => /eqP.
            rewrite eqn_add2l eq_sym => /nilP prefix__nil.
            move: inPrefix.
              by rewrite prefix__nil.
          * move => [] [] srcs tgt covered splits1 /= res.
            have: ((prefix = [:: Cover splits1 toCover]) \/
                   (prefix = [:: CheckCover splits1 toCover]) \/
                   (prefix = [:: ContinueCover splits1 (partitionCover covered toCover).2 (srcs, tgt) ; CheckCover splits1 toCover])).
            { move: res.
              move => /(fun res =>
                         res (fun sp1 sp2 =>
                                let prefix := take (seq.size sp2.2 - seq.size (behead sp1.2)) sp2.2 in
                                (prefix = [:: Cover splits1 toCover]) \/
                                (prefix = [:: CheckCover splits1 toCover]) \/
                                (prefix = [:: ContinueCover splits1 (partitionCover covered toCover).2 (srcs, tgt) ;
                                           CheckCover splits1 toCover]))).
              rewrite size_cat /= addnK take_cat ltnn subnn take0 cats0.
              move => res.
              apply: res.
              - rewrite -add1n addnK take0.
                move => _.
                  by left.
              - rewrite -add1n addnK take0.
                move => _.
                  by right; left.
              - move => _ _.
                rewrite -add2n addnK take0.
                  by right; right. }
            move => prf.
            move: inPrefix.
            case: prf; last case; move ->.
            ** rewrite filterMergeMultiArrows_cat mem_cat mem_cat orbF /=.
               move => ->.
                 by rewrite orbT.
            ** rewrite filterMergeMultiArrows_cat mem_cat mem_cat orbF /=.
               move => ->.
                 by rewrite orbT.
            ** rewrite filterMergeMultiArrows_cat /= cats0 mem_cat mem_cat filterMergeMultiArrows_cat mem_cat.
                 by move => /orP [] ->; last rewrite orbT.
        + move => splits1 toCover currentResult /CoverMachine_inv.
          case: splits1.
          * move => /(fun res => res (fun sp1 sp2 => behead sp1.2 = sp2.2)) /= /(fun res => res Logic.eq_refl) /(f_equal seq.size) /=.
            rewrite size_cat addnC -[X in (X = _ -> _)%type]addn0 => /eqP.
            rewrite eqn_add2l eq_sym => /nilP prefix__nil.
            move: inPrefix.
              by rewrite prefix__nil.
          * move => [] [] srcs tgt covered splits1 /= res.
            have: ((prefix = [:: ContinueCover splits1 toCover currentResult]) \/
                   (prefix = [:: ContinueCover splits1 (partitionCover covered toCover).2
                                 (mergeMultiArrow currentResult srcs tgt)]) \/
                   (prefix = [:: CheckContinueCover splits1 toCover currentResult]) \/
                   (prefix = [:: ContinueCover splits1 (partitionCover covered toCover).2
                                 (mergeMultiArrow currentResult srcs tgt);
                              CheckContinueCover splits1 toCover currentResult])).
            { move: res.
              move => /(fun res =>
                         res (fun sp1 sp2 =>
                                let prefix := take (seq.size sp2.2 - seq.size (behead sp1.2)) sp2.2 in
                                (prefix = [:: ContinueCover splits1 toCover currentResult]) \/
                                (prefix = [:: ContinueCover splits1 (partitionCover covered toCover).2
                                              (mergeMultiArrow currentResult srcs tgt)]) \/
                                (prefix = [:: CheckContinueCover splits1 toCover currentResult]) \/
                                (prefix = [::  ContinueCover splits1 (partitionCover covered toCover).2
                                               (mergeMultiArrow currentResult srcs tgt);
                                           CheckContinueCover splits1 toCover currentResult]))).
              rewrite size_cat /= addnK take_cat ltnn subnn take0 cats0.
              move => res.
              apply: res.
              - rewrite -add1n addnK take0.
                move => _.
                  by left.
              - rewrite -add1n addnK take0.
                move => _ _.
                  by right; right; left.
              - move => _ _ _.
                rewrite -add1n addnK take0.
                  by right; left.
              - move => _ _ _.
                rewrite -add2n addnK take0.
                  by right; right; right. }
            move => prf.
            move: inPrefix.
            case: prf; last case; last case; move => ->.
            ** rewrite filterMergeMultiArrows_cat mem_cat mem_cat orbF /=.
               rewrite map_cat [X in (_ -> _ -> (_ \in X) || _)%type]filterMergeMultiArrows_cat mem_cat.
               do 2 rewrite filterMergeMultiArrows_cat mem_cat.
                 by move => /orP [] ->; repeat rewrite orbT.
            ** rewrite filterMergeMultiArrows_cat mem_cat mem_cat orbF /=.
               rewrite map_cat [X in (_ -> _ -> (_ \in X) || _)%type]filterMergeMultiArrows_cat mem_cat.
               do 2 rewrite filterMergeMultiArrows_cat mem_cat.
               move => /orP []; last by move => ->; repeat rewrite orbT.
                 by rewrite -map_comp filterMergeMultiArrows_map_cons => ->.
            ** rewrite filterMergeMultiArrows_cat mem_cat mem_cat orbF /=.
               rewrite map_cat [X in (_ -> _ -> (_ \in X) || _)%type]filterMergeMultiArrows_cat mem_cat.
               do 2 rewrite filterMergeMultiArrows_cat mem_cat.
               move => /orP []; last by move => ->; repeat rewrite orbT.
               rewrite -map_comp => ->.
                 by rewrite orbT.
            ** rewrite filterMergeMultiArrows_cat mem_cat mem_cat orbF /=.
               do 3 rewrite filterMergeMultiArrows_cat mem_cat.
               rewrite mem_cat map_cat [X in (_ -> _ -> (_ \in X) || _)%type]filterMergeMultiArrows_cat mem_cat.
               move => /orP [].
               *** move => /orP []; last by move => ->; repeat rewrite orbT.
                     by rewrite -map_comp filterMergeMultiArrows_map_cons => ->.
               *** by move => /orP [] ->; repeat rewrite orbT.
        + move => splits1 toCover /CoverMachine_inv res.
          have: (prefix = [::] \/ prefix = [:: Cover splits1 toCover]).
          { move: res.
            move => /(fun res => res (fun sp1 sp2 =>
                                    let prefix := take (seq.size sp2.2 - seq.size (behead sp1.2)) sp2.2 in
                                    (prefix = [::]) \/ (prefix = [:: Cover splits1 toCover]))).
            rewrite size_cat /= -addnBA => //.
            rewrite subnn addn0 take_cat subnn take0 cats0 ltnn.
            move => res.
            apply: res.
            - by move => _; left.
            - rewrite -addn1 addKn take0.
                by move => _; right. }
          move => prf.
          move: inPrefix.
          case: prf; move => -> //=.
            by rewrite cats0.
        + move => splits1 toCover currentResult /CoverMachine_inv res.
          have: (prefix = [::] \/ prefix = [:: ContinueCover splits1 toCover currentResult]).
          { move: res.
            move => /(fun res => res (fun sp1 sp2 =>
                                    let prefix := take (seq.size sp2.2 - seq.size (behead sp1.2)) sp2.2 in
                                    (prefix = [::]) \/ (prefix = [:: ContinueCover splits1 toCover currentResult]))).
            rewrite size_cat /= -addnBA => //.
            rewrite subnn addn0 take_cat subnn take0 cats0 ltnn.
            move => res.
            apply: res.
            - by move => _; left.
            - rewrite -addn1 addKn take0.
                by move => _; right. }
          move => prf.
          move: inPrefix.
          case: prf; move => -> //=.
            by rewrite cats0.
      - by move => ->; rewrite orbT.
    Qed.
            
    Lemma semantics_mergeComponents:
      forall sp1 sp2, sp1 ~~>[*] sp2 -> sound (take (seq.size sp2.1 - seq.size sp1.1) sp2.1) sp1.2.
    Proof.
      move => sp1 sp2 prf.
      elim: sp1 sp2 /prf => // [] [] s1 p1.
      - by rewrite subnn take0.
      - move => [] s2 p2 [] s3 p3.
        case: p1; first by move => /CoverMachine_inv  /(fun x => x (fun _ _ => true)).
        move => i p1 step.
        rewrite -/(Semantics (s2, p2) (s3, p3)) /=.
        move => steps IH.
        move: IH (step_sound _ _ step) => /=.
        move: (step_stateMonotonic _ _ _ _ step) (steps_stateMonotonic _ _ steps).
        move => /suffixP [] prefix1 /eqP ->.
        move => /suffixP [] prefix2 /eqP /= ->.
        do 2 rewrite size_cat addnK take_cat ltnn subnn take0 cats0.
        rewrite addnA addnK take_cat ltnNge leq_addr /=.
        rewrite addnC addnK take_cat ltnn subnn take0 cats0.
        rewrite {3}/sound all_cat.
        rewrite -/(sound prefix2 [:: i & p1]) -/(sound prefix1 [:: i & p1]).
        move => /sound_reverse prf ->.
        rewrite andbT.
        apply: prf.
          by exact step.
    Qed.

    Definition toCoverOf (i: @Instruction Constructor)  :=
      match i with
      | Cover _ toCover => toCover
      | ContinueCover _ toCover _ => toCover
      | CheckCover _ toCover => toCover
      | CheckContinueCover _ toCover _ => toCover
      end.

    Definition complete s (i: @Instruction Constructor) :=
      all (fun m1 =>
             (checkSubtypes m1.2 (\bigcap_(A_i <- toCoverOf i) A_i))
               ==> has (fun m2 =>
                        let (srcs, tgt) :=
                            match i with
                            | ContinueCover _ toCover currentResult
                            | CheckContinueCover _ toCover currentResult =>
                              ((mergeMultiArrow currentResult m1.1 m1.2).1,
                               currentResult.2 \cap (\bigcap_(A_i <- toCover) A_i))
                            | _ => (m1.1, \bigcap_(A_i <- toCoverOf i) A_i)
                            end in
                        [&& seq.size m2.1 == seq.size srcs,
                         all (fun AB => checkSubtypes AB.1 AB.2) (zip srcs m2.1) &
                         checkSubtypes m2.2 tgt]) s)
          (filterMergeMultiArrows (subseqs (mergeComponentsOf i))).

    Definition instruction_covered (i: @Instruction Constructor): bool :=
      all (fun mps =>
             checkSubtypes mps.1.2 (\bigcap_(A_i <- mps.2) A_i) &&
             all (fun A => (checkSubtypes mps.1.2 A) ==> (A \in mps.2)) (toCoverOf i)) (splitsOf i).

    Lemma partitionCover_subset:
      forall (covered toCover: seq (@IT Constructor)), all (fun A => A \in covered) (partitionCover covered toCover).1.
    Proof.
      move => covered.
      elim => //.
      move => A toCover /=.
      case: (partitionCover covered toCover) => [] coveredFresh uncovered IH.
      case inprf: (A \in covered) => //=.
        by rewrite inprf IH.
    Qed.

    Lemma partitionCover_notSubset:
      forall (covered toCover: seq (@IT Constructor)), all (fun A => ~~(A \in covered)) (partitionCover covered toCover).2.
    Proof.
      move => covered.
      elim => //.
      move => A toCover /=.
      case: (partitionCover covered toCover) => [] coveredFresh uncovered IH.
      case inprf: (A \in covered) => //=.
        by rewrite inprf IH.
    Qed.

    Lemma partitionCover_subseq1:
      forall (covered toCover: seq (@IT Constructor)), subseq (partitionCover covered toCover).1 toCover.
    Proof.
      move => covered.
      elim => //= A toCover.
      case: (partitionCover covered toCover) => [] coveredFresh uncovered.
      case: (A \in covered) => /=.
      - by rewrite eq_refl.
      - case: coveredFresh => // B coveredFresh.
        case: (B == A) => //.
          by move => /(subseq_trans (subseq_cons coveredFresh B)).
    Qed.

    Lemma partitionCover_subseq2:
      forall (covered toCover: seq (@IT Constructor)), subseq (partitionCover covered toCover).2 toCover.
    Proof.
      move => covered.
      elim => //= A toCover.
      case: (partitionCover covered toCover) => [] coveredFresh uncovered.
      case: (A \in covered) => /=.
      - case: uncovered => // B uncovered.
        case: (B == A) => //.
          by move => /(subseq_trans (subseq_cons uncovered B)).
      - by rewrite eq_refl.
    Qed.

    Lemma instructions_covered_step:
      forall sp1 sp2,
        sp1 ~~> sp2 ->
        all instruction_covered sp1.2 ->
        all instruction_covered sp2.2.
    Proof.
      move => [] s1 p1 [] s2 p2 /CoverMachine_inv.
      move => /(fun res => res (fun sp1 sp2 => (all instruction_covered sp1.2 -> all instruction_covered sp2.2)%type)).
      case: p1 => //.
      case.
      - case.
        + move => toCover p1 prf.
            by apply: prf.
        + move => [] [] srcs tgt covered splits toCover p1 prf.
          apply: prf.
          * move => _ /= /andP [] covered1 ->.
            move: covered1.
              by rewrite /instruction_covered /= => /andP [] _ ->.
          * move => _ _ /= /andP [] covered1 ->.
            move: covered1.
              by rewrite /instruction_covered /= => /andP [] _ ->.
          * move => _ _ /= /andP [] covered1 ->.
            move: covered1.
            rewrite /instruction_covered /= => /andP [] /= covered1 covered2.
            rewrite andbT covered2 andbT.
            apply: (introT allP) => x inprf.
            move: covered2 => /allP /(fun prf => prf x inprf) /andP [] -> /allP covered2 /=.            
            apply: (introT allP) => y inprf2.
            apply: covered2.
            move: (partitionCover_subseq2 covered toCover) => /mem_subseq res.
              by apply: res.
      - case.
        + move => toCover p1 currentResult prf.
            by apply: prf.
        + move => [] [] srcs tgt covered splits toCover currentResult p1 prf.
          apply: prf.
          * move => _ /= /andP [] covered1 ->.
            move: covered1.
              by rewrite /instruction_covered /= => /andP [] _ ->.
          * move => _ _ /= /andP [] covered1 ->.
            move: covered1.
              by rewrite /instruction_covered /= => /andP [] _ ->.
          * move => _ _ _ /= /andP [] covered1 ->.
            move: covered1.
            rewrite /instruction_covered /= => /andP [] /= covered1 covered2.
            rewrite andbT.
            apply: (introT allP) => x inprf.
            move: covered2 => /allP /(fun prf => prf x inprf) /andP [] -> /allP covered2 /=.
            apply: (introT allP) => y inprf2.
            apply: covered2.
            move: (partitionCover_subseq2 covered toCover) => /mem_subseq res.
              by apply: res.
          * move => _ _ _ /= /andP [] covered1 ->.
            move: covered1.
            rewrite /instruction_covered /= => /andP [] /= covered1 covered2.
            rewrite andbT covered2 andbT.
            apply: (introT allP) => x inprf.
            move: covered2 => /allP /(fun prf => prf x inprf) /andP [] -> /allP covered2 /=.
            apply: (introT allP) => y inprf2.
            apply: covered2.
            move: (partitionCover_subseq2 covered toCover) => /mem_subseq res.
              by apply: res.
      - move => splits toCover p1 prf.
        apply: prf => //.
          by move => _ /andP [].
      - move => splits toCover currentResult p1 prf.
        apply: prf => //.
          by move => _ /andP [].
    Qed.


    Definition not_omega_instruction (i: @Instruction Constructor): bool :=
      (toCoverOf i != [::]) && all (fun A => ~~(checkSubtypes Omega A)) (toCoverOf i).

    Lemma not_omega_instruction_step:
      forall s1 p1 s2 p2,
        (s1, p1) ~~> (s2, p2) ->
        all not_omega_instruction p1 ->
        all not_omega_instruction p2.
    Proof.
      move => s1 p1 s2 p2 /CoverMachine_inv.
      move => /(fun prf => prf (fun sp1 sp2 => (all not_omega_instruction sp1.2 -> all not_omega_instruction sp2.2)%type)).
      case: p1 => //.
      case; case.
      - by move => ? ? prf; apply: prf => /andP [].
      - move => [] [] srcs tgt covered splits toCover p1 prf.
        apply: prf => //=.
        move => _.
        rewrite /not_omega_instruction /= => ->.
        move => /andP [] /andP [] -> prf ->.
        rewrite prf.
        do 2 rewrite andbT /=.
        apply: (introT allP).
        move => A inprf.
        move: (partitionCover_subseq2 covered toCover) => /mem_subseq /(fun prf => prf A inprf).
          by move: prf => /allP  prf /prf.
      - by move => ? ? ? prf; apply: prf => /andP [].
      - move => [] [] srcs tgt covered splits toCover currentResult p1 prf.
        apply: prf => //=.
        + move => _.
          rewrite /not_omega_instruction /= => -> _ /andP [] /andP [] _ prf -> /=.
          rewrite andbT.
          apply: (introT allP).
          move => A inprf.
          move: (partitionCover_subseq2 covered toCover) => /mem_subseq /(fun prf => prf A inprf).
            by move: prf => /allP  prf /prf.
        + move => _.
          rewrite /not_omega_instruction /= => -> _ /andP [] /andP [] -> prf ->.
          rewrite prf /= andbT.
          apply: (introT allP).
          move => A inprf.
          move: (partitionCover_subseq2 covered toCover) => /mem_subseq /(fun prf => prf A inprf).
            by move: prf => /allP  prf /prf.
      - move => toCover p prf.
        apply: prf => //.
          by move => _ /andP [].
      - move => m splits toCover p prf.
        apply: prf => //.
          by move => _ /andP [].
      - move => toCover currentResult p prf.
        apply: prf => //.
          by move => _ /andP [].
      - move => m splits toCover currentResult p prf.
        apply: prf => //.
          by move => _ /andP [].
    Qed.

    Definition arity_equal (i: @Instruction Constructor): bool :=
      all (fun x => all (fun y => seq.size x.1 == seq.size y.1) (mergeComponentsOf i)) (mergeComponentsOf i).

    Lemma arity_equal_step:
      forall sp1 sp2,
        sp1 ~~> sp2 ->
        all arity_equal sp1.2 ->
        all arity_equal sp2.2.
    Proof.
      move => [] s1 p1 [] s2 p2 /CoverMachine_inv /(fun prf => prf (fun sp1 sp2 => (all arity_equal sp1.2 -> all arity_equal sp2.2)%type)).
      case: p1 => //.
      case; case.
      - move => toCover p1 res.
        apply: res.
          by move => /andP [].
      - move => [] [] srcs tgt covered splits toCover p1 res.
        apply: res.
        + move => _ /= /andP [] prf ->.
          rewrite andbT.
          apply: all_nested_tl.
            by exact prf.
        + move => _ _ /= /andP [] prf ->.
          rewrite andbT.
          apply: all_nested_tl.
            by exact prf.
        + move => _ _ /= /andP [] prf ->.
          rewrite andbT.
          move: prf.
          rewrite /arity_equal.
          move => prf.
          rewrite prf.
          apply: all_nested_tl.
            by exact prf.
      - move => toCover currentResult p1 res.
        apply: res.
          by move => /= /andP [] _.
      - move => [] [] srcs tgt covered splits toCover currentResult p1 res.
        apply: res.
        + move => _ /= /andP [] prf ->.
          rewrite andbT.
          apply: all_nested_subseq; last by exact prf.
          apply: (@cat_subseq _ [:: _] _ [:: _] _) => //.
          rewrite map_cons.
            by apply: (@suffix_subseq _ [:: _]).
        + move => _ _ /= /andP [] prf ->.
          rewrite andbT.
          apply: all_nested_subseq; last by exact prf.
          apply: (@cat_subseq _ [:: _] _ [:: _] _) => //.
          rewrite map_cons.
            by apply: (@suffix_subseq _ [:: _]).
        + move => _ _ merge_eq /= /andP [] /allP prf ->.
          rewrite andbT.
          apply /allP.
          move => x.
          rewrite in_cons.
          move => /orP [].
          * move => /eqP ->.
            rewrite (eqP merge_eq).
            apply /allP.
            move => y.
            rewrite in_cons.
            move => /orP [].
            ** move => /eqP ->.
                 by rewrite (eqP merge_eq).
            ** move: (prf currentResult (mem_head _ _)) => /allP /(fun prf => prf y).
               rewrite in_cons.
               move: prf => _ prf inprf__y.
               move: prf.
               rewrite map_cons in_cons inprf__y orbT orbT.
                 by move => /(fun prf => prf isT).
          * move => inprf__x.
            apply /allP.
            move => y.
            rewrite in_cons.
            move => /orP [].
            ** move => /eqP ->.
               rewrite (eqP merge_eq).
               move: prf => /(fun prf => prf x).
               rewrite in_cons map_cons in_cons inprf__x orbT orbT.
                 by move => /(fun prf => prf isT) /allP /(fun prf => prf currentResult (mem_head _ _)).
            ** move => inprf__y.
               move: prf => /(fun prf => prf x).
               rewrite in_cons map_cons in_cons inprf__x orbT orbT.
               move => /(fun prf => prf isT) /allP /(fun prf => prf y).
               rewrite in_cons map_cons in_cons inprf__y orbT orbT.
                 by move => /(fun prf => prf isT).
        + move => _ _ _ /= /andP [] prf ->.
          rewrite andbT.
          apply /andP.
          split.
          * apply /allP.
            move => x.
            rewrite in_cons.
            move => /orP [].
            ** move => inprf__x.
               apply /allP.
               move => y.
               rewrite in_cons.
               move => /orP [].
               *** move => /eqP ->.
                     by rewrite (eqP inprf__x).
               *** move => inprf__y.
                   rewrite (eqP inprf__x).
                   move: (prf) => /allP /(fun prf => prf currentResult (mem_head _ _)) /allP /(fun prf => prf y).
                   rewrite in_cons map_cons in_cons inprf__y orbT orbT.
                   rewrite /mergeMultiArrow size_map size_zip.
                   move: prf => /andP [] /andP [] _ /andP [] /eqP <- _ _.
                   rewrite minnn.
                     by move => /(fun prf => prf isT).
            ** move => inprf__x.
               apply /allP.
               move => y.
               rewrite in_cons.
               move => /orP [].
               *** move => /eqP ->.
                   rewrite /mergeMultiArrow size_map size_zip.
                   move: (prf) => /andP [] /andP [] _ /andP [] /eqP <- _ _.
                   rewrite minnn.
                   move: prf => /allP /(fun prf => prf x).
                   rewrite in_cons map_cons in_cons inprf__x orbT orbT.
                     by move => /(fun prf => prf isT) /allP /(fun prf => prf currentResult (mem_head _ _)).
               *** move => inprf__y.
                   move: prf => /allP /(fun prf => prf x).
                   rewrite in_cons map_cons in_cons inprf__x orbT orbT.
                   move => /(fun prf => prf isT) /allP /(fun prf => prf y).
                   rewrite in_cons map_cons in_cons inprf__y orbT orbT.
                     by move => /(fun prf => prf isT).
          * apply: all_nested_subseq; last by exact prf.
            apply: (@cat_subseq _ [:: _] _ [:: _] _) => //.
            rewrite map_cons.
              by apply: (@suffix_subseq _ [:: _]).
      - move => toCover p prf.
          by apply: prf.
      - move => m splits toCover p prf.
        apply: prf => //.
          by move => _ /andP [].
      - move => toCover currentResult p prf.
        apply: prf => //.
          by move => _ /andP [].
      - move => m splits toCover currentResult p prf.
        apply: prf => //.
          by move => _ /andP [].
    Qed.

    Lemma mergeMultiArrows_arity:
      forall ms,
        all (fun x => all (fun y => seq.size x.1 == seq.size y.1) ms) ms ->
        all (fun m => seq.size m.1 == seq.size (mergeMultiArrows ms).1) ms.
    Proof.
      rewrite /mergeMultiArrows.
      case => // m ms /allP prf.
      suff: (seq.size (foldl (fun m__s m => mergeMultiArrow m__s m.1 m.2) m ms).1 == seq.size m.1).
      { move => /eqP ->.
        apply: (introT allP).
        move => ? /prf /allP /(fun prf => prf m) res.
        apply: res.
          by apply: mem_head. }
      move: m prf.
      elim: ms => //= m2 ms IH m1 prf.
      have: (seq.size m1.1 = seq.size (mergeMultiArrow m1 m2.1 m2.2).1).
      { rewrite /mergeMultiArrow size_map size_zip.
        move: (prf m1 (mem_head _ _)) => /andP [] _ /andP [] /eqP -> _.
          by rewrite minnn. }
      move => size__eq.
      rewrite size__eq.
      apply: IH.
      move => m /orP [].
      - move => /eqP ->.
        rewrite eq_refl /andb.
        move: (prf m1 (mem_head _ _)) => /andP [] _ /andP [] _.
          by rewrite size__eq.
      - move => /(fun inprf => prf m (mem_behead (mem_behead inprf))) => /andP [] /eqP size__eq1 /andP [] /eqP size__eq2 sizes__eq.
          by rewrite {1}size__eq1 {1}size__eq eq_refl /andb.
    Qed.

    Lemma mergeMultiArrow_tgt_le:
      forall (m1 m2: @MultiArrow Constructor), [bcd ((mergeMultiArrow m1 m2.1 m2.2).2) <= m1.2 \cap m2.2].
    Proof.
      move => [] srcs1 tgt1 [] srcs2 tgt2 /=.
        by apply: BCD__Glb.
    Qed.

    Lemma mergeMultiArrow_tgt_ge:
      forall (m1 m2: @MultiArrow Constructor), [bcd (m1.2 \cap m2.2) <= ((mergeMultiArrow m1 m2.1 m2.2).2) ].
    Proof.
      move => [] srcs1 tgt1 [] srcs2 tgt2 /=.
        by apply: BCD__Glb.
    Qed.

    Lemma mergeMultiArrow_srcs_le:
      forall (m1 m2: @MultiArrow Constructor), all (fun srcs => checkSubtypes srcs.1 (srcs.2.1 \cap srcs.2.2)) (zip (mergeMultiArrow m1 m2.1 m2.2).1 (zip m1.1 m2.1)).
    Proof.
      move => [] srcs1 tgt1 [] srcs2 tgt2 /=.
      move: srcs2.
      elim: srcs1.
      - by move => [].
      - move => src1 srcs1 IH [] // src2 srcs2 /=.
        rewrite (IH srcs2) andbT /(_ \dcap _).
        move le21__eq: (checkSubtypes src2 src1) => [].
        + apply: (introT (subtypeMachineP _ _ _)).
          apply: BCD__Glb => //.
            by apply: subtypeMachineP.
        + move le12__eq: (checkSubtypes src1 src2) => [].
          * apply: (introT (subtypeMachineP _ _ _)).
            apply: BCD__Glb => //.
              by apply: subtypeMachineP.
          * apply: (introT (subtypeMachineP _ _ _)).
              by apply: BCD__Glb.
    Qed.

    Lemma mergeMultiArrow_srcs_ge:
      forall (m1 m2: @MultiArrow Constructor), all (fun srcs => checkSubtypes (srcs.2.1 \cap srcs.2.2) srcs.1) (zip (mergeMultiArrow m1 m2.1 m2.2).1 (zip m1.1 m2.1)).
    Proof.
      move => [] srcs1 tgt1 [] srcs2 tgt2 /=.
      move: srcs2.
      elim: srcs1.
      - by move => [].
      - move => src1 srcs1 IH [] // src2 srcs2 /=.
        rewrite (IH srcs2) andbT /(_ \dcap _).
        move le21__eq: (checkSubtypes src2 src1) => [].
        + apply: (introT (subtypeMachineP _ _ _)).
            by apply: BCD__Lub2. 
        + move le12__eq: (checkSubtypes src1 src2) => [].
          * apply: (introT (subtypeMachineP _ _ _)).
              by apply: BCD__Lub1.
          * apply: (introT (subtypeMachineP _ _ _)).
              by apply: BCD__Glb.
    Qed.

    Lemma mergeMultiArrows_tgt_le:
      forall ms,
        [bcd ((mergeMultiArrows ms).2) <= \bigcap_(m_i <- ms) m_i.2 ].
    Proof.
      rewrite /mergeMultiArrows.
      case => // m ms.
      move: m.
      elim: ms => // m2 ms IH m1.
      apply: BCD__Trans; first by apply: IH.
      apply: BCD__Trans; first by apply: (bcd_cat_bigcap_f _ _ (fun m => m.2) [:: (mergeMultiArrow m1 m2.1 m2.2)]).
      apply: BCD__Trans; last by apply: (bcd_bigcap_cat_f _ _ (fun m => m.2) [:: m1; m2]).
      apply: BCD__Glb => //.
      apply: BCD__Trans; last by apply: (mergeMultiArrow_tgt_le m1 m2).
        by apply: BCD__Lub1.
    Qed.

    Lemma mergeMultiArrows_tgt_ge:
      forall ms,
        [bcd ( \bigcap_(m_i <- ms) m_i.2) <= ((mergeMultiArrows ms).2) ].
    Proof.
      rewrite /mergeMultiArrows.
      case => // m ms.
      move: m.
      elim: ms => // m2 ms IH m1.
      apply: BCD__Trans; last by apply: IH.
      apply: BCD__Trans; first by apply: (bcd_cat_bigcap_f _ _ (fun m => m.2) [:: m1; m2]).
      apply: BCD__Trans; last by apply: (bcd_bigcap_cat_f _ _ (fun m => m.2) [:: (mergeMultiArrow m1 m2.1 m2.2)]).
      apply: BCD__Glb => //.
      apply: BCD__Trans; last by apply: (mergeMultiArrow_tgt_ge m1 m2).
        by apply: BCD__Lub1.
    Qed.

    Lemma mergeMultiArrows_srcs_le:
      forall ms n,
        all (fun x => all (fun y => seq.size x.1 == seq.size y.1) ms) ms ->
        [bcd (nth Omega (mergeMultiArrows ms).1 n) <= \bigcap_(m_i <- ms) (nth Omega m_i.1 n)].
    Proof.
      rewrite /mergeMultiArrows.
      case => //= m ms.
      move: m.
      elim: ms => // m2 ms IH m1 n prf.
      rewrite map_cons.
      apply: BCD__Trans; first apply: IH.
      - move: prf => /andP [] /andP [] _ /andP [] /eqP prf1 prf1__ms /andP [] /andP [] _ prf2 prf__ms.
        rewrite eq_refl [X in X && _]/andb.
        apply: (introT andP); split.
        + apply: sub_all; last by exact prf1__ms.
          move => ? /eqP <- /=.
            by rewrite size_map size_zip prf1 minnn.
        + apply: sub_all; last by exact prf__ms.
          move => m /andP [] /eqP -> /andP [] _.
          rewrite -/(all _ ms) => ->.
            by rewrite andbT /= size_map size_zip prf1 minnn.
      - apply: BCD__Trans; last by apply: (bcd_bigcap_cat_f _ _ (fun m => nth Omega m.1 n) [:: m1; m2]).
        apply: BCD__Glb.
        + move: IH prf => _ /andP [] _ /andP [] /andP [] /eqP prf _ _.
          case: ms => /=.
          * move: (mergeMultiArrow_srcs_le m1 m2) => /all_nthP /(fun prf => prf n).
            case n__lt: (n < seq.size m2.1).
            ** rewrite size_zip size_zip size_map size_zip -prf minnn minnn.
               move => /(fun prf => prf (Omega, (Omega, Omega)) n__lt) /= /subtypeMachineP.
               rewrite nth_zip /=; last by rewrite size_map size_zip size_zip minnC.
                 by (rewrite nth_zip; last by symmetry).
            ** move => _.
               repeat rewrite nth_default; first by apply: BCD__Glb.
               *** by rewrite leqNgt n__lt.
               *** by rewrite -prf leqNgt n__lt.
               *** by rewrite size_map size_zip -prf minnn leqNgt n__lt.
          * move => ? ?.
            apply: BCD__Trans; first by apply: BCD__Lub1.
            move: (mergeMultiArrow_srcs_le m1 m2) => /all_nthP /(fun prf => prf n).
            case n__lt: (n < seq.size m2.1).
            ** rewrite size_zip size_zip size_map size_zip -prf minnn minnn.
               move => /(fun prf => prf (Omega, (Omega, Omega)) n__lt) /= /subtypeMachineP.
               rewrite nth_zip /=; last by rewrite size_map size_zip size_zip minnC.
                 by (rewrite nth_zip; last by symmetry).
            ** move => _.
               repeat rewrite nth_default; first by apply: BCD__Glb.
               *** by rewrite leqNgt n__lt.
               *** by rewrite -prf leqNgt n__lt.
               *** by rewrite size_map size_zip -prf minnn leqNgt n__lt.
        + apply: BCD__Trans; first by apply: (bcd_cat_bigcap_f _ _ (fun m => nth Omega m.1 n) [:: mergeMultiArrow m1 m2.1 m2.2]).
            by apply: BCD__Lub2.
    Qed.

    Lemma mergeMultiArrows_srcs_ge:
      forall ms n,
        all (fun x => all (fun y => seq.size x.1 == seq.size y.1) ms) ms ->
        [bcd (\bigcap_(m_i <- ms) (nth Omega m_i.1 n)) <= (nth Omega (mergeMultiArrows ms).1 n) ].
    Proof.
      rewrite /mergeMultiArrows.
      case; first by move => ?; rewrite nth_nil.
      move => /= m ms.
      move: m.
      elim: ms => // m2 ms IH m1 n prf.
      rewrite map_cons.
      apply: BCD__Trans; last apply: IH.
      - apply: BCD__Trans; first by apply: (bcd_cat_bigcap_f _ _ (fun m => nth Omega m.1 n) [:: m1; m2]).
        apply: BCD__Trans; last by apply: (bcd_bigcap_cat_f _ _ (fun m => nth Omega m.1 n) [:: mergeMultiArrow m1 m2.1 m2.2]).
        apply: BCD__Glb => //.
        move: IH prf => _ /andP [] _ /andP [] /andP [] /eqP prf _ _.
        apply: BCD__Trans; first by apply: BCD__Lub1.
        move: (mergeMultiArrow_srcs_ge m1 m2) => /all_nthP /(fun prf => prf n).
        case n__lt: (n < seq.size m2.1).
        + rewrite size_zip size_zip size_map size_zip -prf minnn minnn.
          move => /(fun prf => prf (Omega, (Omega, Omega)) n__lt) /= /subtypeMachineP.
          rewrite nth_zip /=; last by rewrite size_map size_zip size_zip minnC.
            by (rewrite nth_zip; last by symmetry).
        + move => _ /=.
          repeat rewrite nth_default; first by done.
          *** by rewrite size_map size_zip -prf minnn leqNgt n__lt.
          *** by rewrite leqNgt n__lt.
          *** by rewrite -prf leqNgt n__lt.
      - move: prf => /andP [] /andP [] _ /andP [] /eqP prf1 prf1__ms /andP [] /andP [] _ prf2 prf__ms.
        rewrite eq_refl [X in X && _]/andb.
        apply: (introT andP); split.
        + apply: sub_all; last by exact prf1__ms.
          move => ? /eqP <- /=.
            by rewrite size_map size_zip prf1 minnn.
        + apply: sub_all; last by exact prf__ms.
          move => m /andP [] /eqP -> /andP [] _.
          rewrite -/(all _ ms) => ->.
            by rewrite andbT /= size_map size_zip prf1 minnn.
    Qed.

    Definition toCover_prime (i: @Instruction Constructor): bool :=
      all (@isPrimeComponent _) (toCoverOf i).

    Lemma toCover_prime_step:
      forall s1 p1 s2 p2,
        (s1, p1) ~~> (s2, p2) ->
        all toCover_prime p1 ->
        all toCover_prime p2.
    Proof.
      move => s1 p1 s2 p2.
      move => /CoverMachine_inv /(fun prf => prf (fun sp1 sp2 => (all toCover_prime sp1.2 -> all toCover_prime sp2.2)%type)).
      case: p1 => //; case; case.
      - by move => ? ? prf; apply: prf => /andP [].
      - move => [] [] srcs tgt covered splits toCover p1 prf.
        apply: prf => //=.
        move => _ _ /andP [].
        rewrite /toCover_prime /=.
        move => prf ->.
        rewrite prf andbT andbT.
        apply: (introT allP).
        move => p inprf.
        move: prf => /allP prf.
        apply: prf.
        apply: mem_subseq; last by exact inprf.
          by apply: partitionCover_subseq2.
      - by move => ? ? ? prf; apply: prf => /andP [].
      - move => [] [] srcs tgt covered splits toCover currentResult p1 prf.
        apply: prf => //=.
        + move => _ _ _ /andP [].
          rewrite /toCover_prime /=.
          move => prf ->.
          rewrite andbT.
          apply: (introT allP).
          move => p inprf.
          move: prf => /allP prf.
          apply: prf.
          apply: mem_subseq; last by exact inprf.
            by apply: partitionCover_subseq2.
        + move => _ _ _ /andP [].
          rewrite /toCover_prime /=.
          move => prf ->.
          rewrite prf andbT andbT.
          apply: (introT allP).
          move => p inprf.
          move: prf => /allP prf.
          apply: prf.
          apply: mem_subseq; last by exact inprf.
            by apply: partitionCover_subseq2.
      - move => toCover p prf.
        apply: prf => //.
          by move => _ /andP [].
      - move => m splits toCover p prf.
        apply: prf => //.
          by move => _ /andP [].
      - move => toCover currentResult p prf.
        apply: prf => //.
          by move => _ /andP [].
      - move => m splits toCover currentResult  p prf.
        apply: prf => //.
          by move => _ /andP [].
    Qed.

    Lemma bcd_subset_f {T: eqType}:
      forall (f: T -> @IT Constructor) (Delta1 Delta2: seq T),
        {subset Delta2 <= Delta1} ->
        [bcd (\bigcap_(A_i <- Delta1) (f A_i)) <=  (\bigcap_(A_i <- Delta2) (f A_i))].
    Proof.
      move => f Delta1.
      elim => //= A Delta2 IH subset_prf.
      apply: BCD__Trans; last by apply: (bcd_bigcap_cat_f _ _ f [:: A] Delta2).
      apply: BCD__Glb.
      - move: subset_prf => /(fun prf => prf A (mem_head A Delta2)).
        clear...
        elim: Delta1 => // B Delta1 IH /orP [].
        + move => /eqP ->.
            by apply: BCD__Trans; first by apply: (bcd_cat_bigcap_f _ _ f [:: B] Delta1).
        + move => /IH prf.
          apply: BCD__Trans; first by apply: (bcd_cat_bigcap_f _ _ f [:: B] Delta1).
            by apply: BCD__Trans; first by apply: BCD__Lub2.
      - apply: IH.
        move => B inprf.
        apply: subset_prf.
          by rewrite in_cons inprf orbT.
    Qed.

    Lemma partitionCover_prime:
      forall m (ms: seq (@MultiArrow Constructor)) covered toCover,
        all (@isPrimeComponent _) toCover ->
        (forall A, A \in toCover -> [bcd (m.2) <= A] -> A \in covered) ->
        [bcd (m.2) <= \bigcap_(A_i <- covered) A_i] ->
        [bcd (\bigcap_(m_i <- [:: m & ms]) m_i.2) <= \bigcap_(A_i <- toCover) A_i] ->
        [bcd (m.2) <= \bigcap_(A_i <- (partitionCover covered toCover).1) A_i] /\
        [bcd (\bigcap_(m_i <- ms) m_i.2) <= \bigcap_(A_i <- (partitionCover covered toCover).2) A_i].
    Proof.
      move => m ms covered toCover.
      move: m ms covered.
      elim: toCover => //= p toCover IH [] srcs tgt ms covered /andP [].
      move => /isPrimeComponentP /primeComponentPrime primality rest_prime.
      move: (partitionCover_subset covered [:: p & toCover]) => /allP inCovered.
      move: (partitionCover_subseq1 covered [:: p & toCover]) => /mem_subseq inpToCover.
      move => covered_complete.
      move: IH (IH (srcs, tgt) ms covered rest_prime (fun A inprf => covered_complete A (@mem_behead _ [:: p & toCover] A inprf))) => _ IH.
      move: IH inCovered inpToCover.
      rewrite [partitionCover covered [:: p & toCover]]/=.
      case: (partitionCover covered toCover) => coveredFresh uncovered.
      case inprf: (p \in covered) => [].
      - move => IH inCovered inpToCover le__covered le__ptoCover.
        rewrite /fst.
        split.
        + apply: BCD__Trans; last by apply: (bcd_bigcap_cat _ [:: p]).
          apply: BCD__Glb.
          * apply: BCD__Trans; first by exact le__covered.
            apply: bcd_subset_f.
              by move => p1 /orP [] // /eqP ->.
          * apply: BCD__Trans; first by exact le__covered.
            apply: bcd_subset_f.
            move => p1 p1_in.
            apply: inCovered.
              by rewrite /= in_cons p1_in orbT.
        + apply: (fun x => proj2 (IH le__covered x)).
          apply: BCD__Trans; first by exact le__ptoCover.
            by apply: BCD__Trans; first by apply: (bcd_cat_bigcap _ [:: p] toCover).
      - move => IH inCovered inpToCover le__covered le__ptoCover.
        rewrite /fst.
        split.
        + apply: BCD__Trans; first by exact le__covered.
          apply: bcd_subset_f.
            by move => ? /inCovered.
        + apply: BCD__Trans; last by apply: (bcd_bigcap_cat _ [:: p] uncovered).
          apply: BCD__Glb.
          * move: le__ptoCover.
            move => /(BCD__Trans _ (bcd_bigcap_cat_f _ _ snd [:: (srcs, tgt)] ms)).
            move => /(fun prf => BCD__Trans _ prf (bcd_cat_bigcap _ [:: p] toCover)).
            move => /(fun prf => BCD__Trans _ prf BCD__Lub1).
            move => /primality [] //.
            move => /(covered_complete p (mem_head _ _)).
              by rewrite inprf.
          * apply: (fun x => proj2 (IH le__covered x)).
            apply: BCD__Trans; first by exact le__ptoCover.
              by apply: BCD__Trans; first by apply: (bcd_cat_bigcap _ [:: p] toCover).
    Qed.

    Lemma filterMergedArrows_in_cons:
      forall m1 mss m,
        (m \in filterMergeMultiArrows (map (cons m1) mss)) ->
        (m == m1) || has (fun ms => (mergeMultiArrows ms \in (filterMergeMultiArrows mss))
                                  && (m == mergeMultiArrows [:: m1 & ms])) mss.
    Proof.
      move => m1.
      elim.
      - done.
      - move => ms mss IH m.
        rewrite map_cons (filterMergeMultiArrows_cat [:: [:: m1 & ms]]) mem_cat.
        move => /orP [].
        + case: ms.
          * by rewrite /= in_cons orbF => ->.
          * move => m2 ms.
            rewrite in_cons orbF.
            move => m__eq.
            apply: (introT orP); right.
            apply: (introT hasP).
            exists [:: m2 & ms]; first by apply: mem_head.
            rewrite m__eq andbT.
              by apply: mem_head.
        + move => /IH /orP [].
          * by move => ->.
          * rewrite (has_cat _ [:: ms]).
            move => /hasP [] ms2 inprf /andP [] inprf__merged m__eq.
            do 2 (apply: (introT orP); right).
            apply: (introT hasP).
            exists ms2; first by exact inprf.
              by rewrite m__eq andbT (filterMergeMultiArrows_cat [:: ms]) mem_cat inprf__merged orbT.
    Qed.

    Lemma covered_head_tgt:
      forall srcs tgt toCover covered splits,
        all (fun (mps: (@MultiArrow Constructor) * (seq (@IT Constructor))) =>
               (checkSubtypes mps.1.2 (\bigcap_(A_i <- mps.2) A_i))
                 && (all (fun A => (checkSubtypes mps.1.2 A) ==> (A \in mps.2)) toCover))
            [:: (srcs, tgt, covered) & splits] ->
      (forall A : @IT Constructor, A \in toCover -> [ bcd tgt <= A] -> A \in covered) /\
      [ bcd tgt <= \bigcap_(A_i <- covered) A_i].
    Proof.
      move => srcs tgt toCover covered splits.
      rewrite (all_cat _ [:: (srcs, tgt, covered)]) all_seq1.
      move => /andP [] /andP [] le__tgt inprf prfs.
      split.
      - move => A inprf__A /subtypeMachineP ge__A.
        move: inprf => /allP /(fun inprf => (inprf A inprf__A)).
          by rewrite ge__A.
      - by move: le__tgt => /subtypeMachineP.
    Qed.

    Lemma partitionCover_drop1:
      forall (covered toCover: seq (@IT Constructor)),
        (partitionCover covered toCover).1 == [::] ->
        (partitionCover covered toCover).2 = toCover.
    Proof.
      move => covered toCover.
      move: covered.
      elim: toCover => //=  p toCover IH covered.
      move: (IH covered).
      case: (partitionCover covered toCover) => [] coveredFresh uncovered.
      case: (p \in covered) => //.
        by move => prf /prf /= ->.
    Qed.

    Lemma partitionCover_drop2:
      forall (covered toCover: seq (@IT Constructor)),
        (partitionCover covered toCover).2 == [::] ->
        (partitionCover covered toCover).1 = toCover.
    Proof.
      move => covered toCover.
      move: covered.
      elim: toCover => //=  p toCover IH covered.
      move: (IH covered).
      case: (partitionCover covered toCover) => [] coveredFresh uncovered.
      case: (p \in covered) => //.
        by move => prf /prf /= ->.
    Qed.

    Lemma mergeMultiArrows_cons_arity:
      forall m ms,
        ~~nilp ms ->
        all (fun x => all (fun y => seq.size x.1 == seq.size y.1) [:: m & ms]) [:: m & ms] ->
        seq.size (mergeMultiArrows [:: m & ms]).1 = seq.size (mergeMultiArrows ms).1.
    Proof.
      move => m ms.
      move: m.
      elim: ms => // m1 [].
      - move => _ m _ /andP [] _ /andP [] /andP [] /eqP size_eq _ _ /=.
          by rewrite size_map size_zip size_eq minnn.
      - move => m2 ms IH m _ prf.
        rewrite (IH (mergeMultiArrow m m1.1 m1.2)) => //.
        + apply: Logic.eq_sym.
          apply: IH => //.
          apply: (@sub_all _ (fun x => all (fun y => seq.size x.1 == seq.size y.1) [:: m, m1, m2 & ms])).
          * by move => ? /andP [] _ /= ->.
          * by move: prf => /andP [] _ /= ->.
        + apply: (introT allP).
          move => x.
          rewrite in_cons.
          move => /orP [].
          * move => /eqP -> /=.
            rewrite size_map size_zip.
            move: prf => /andP [] /andP [] _ /andP [] /eqP -> /andP [] /eqP ->.
            rewrite minnn /all => ->.
              by rewrite eq_refl.
          * rewrite in_cons.
            move => /orP [].
            ** move => /eqP -> /=.
               rewrite size_map size_zip.
               move: prf => /andP [] /andP [] _ /andP [] /eqP -> /andP [] /eqP ->.
               rewrite minnn /all => ->.
                 by rewrite eq_refl.
            ** move: x.
               apply: allP.
               apply: (@sub_all _ (fun x => all (fun y => seq.size x.1 == seq.size y.1) [:: m, m1, m2 & ms])).
               *** move => x /=.
                   rewrite size_map size_zip.
                   move => /andP [] /eqP -> /andP [] /eqP -> /andP [] /eqP -> ->.
                     by rewrite minnn eq_refl.
               *** by move: prf => /andP [] _ /andP [] _ /andP [] _.
    Qed.

    Lemma zip_eq {A: eqType}:
      forall (xs: seq A) x, x \in zip xs xs -> x.1 = x.2.
    Proof.
      elim => //= x1 xs IH x.
      rewrite in_cons.
      move => /orP [].
      - by move => /eqP [] ->.
      - by apply: IH.
    Qed.

    Lemma partitionCover_complete:
      forall (covered toCover: seq (@IT Constructor)),
        {subset toCover <= (partitionCover covered toCover).1 ++ (partitionCover covered toCover).2}.
    Proof.
      move => covered.
      elim => //= A toCover IH.
      move => B.
      rewrite in_cons.
      move => /orP [].
      - move => /eqP ->.
        move: IH => _.
        case: (partitionCover covered toCover) => ? ?.
        case: (A \in covered).
        + by rewrite in_cons eq_refl.
        + by rewrite mem_cat in_cons eq_refl orbT.
      - move => /IH.
        move: IH => _.
        case: (partitionCover covered toCover) => ? ?.
        case: (A \in covered).
        + rewrite in_cons => ->.
            by rewrite orbT.
        + rewrite mem_cat mem_cat in_cons.
          move => /= /orP [] ->; by repeat rewrite orbT.
    Qed.

    Lemma partition_cover_both:
      forall (covered toCover: seq (@IT Constructor)),
        [bcd (\bigcap_(A_i <- (partitionCover covered toCover).1 ++ (partitionCover covered toCover).2) A_i) <=
         \bigcap_(A_i <- toCover) A_i].
    Proof.
      move => covered toCover.
      apply: bcd_subset_f.
        by apply: partitionCover_complete.
    Qed.

    Lemma complete_partitionCover:
      forall (A: @IT Constructor) covered toCover,
        all (fun B => (checkSubtypes A B) ==> (B \in covered)) toCover ->
        checkSubtypes A (\bigcap_(A__i <- toCover) A__i) ->
        (partitionCover covered toCover).2 = [::].
    Proof.
      move => A covered.
      elim => // B toCover IH.
      rewrite [partitionCover _ _]/=.
      move: IH.
      case: (partitionCover covered toCover) => coveredFresh uncovered IH.
      case inprf: (B \in covered).
      - move => /andP [] _ /IH prf.
        move => /subtypeMachineP /(fun prf => BCD__Trans _ prf (bcd_cat_bigcap _ [:: B] toCover)).
        move => /(fun prf => BCD__Trans _ prf BCD__Lub2).
          by move => /subtypeMachineP /prf.
      - move => /andP [] /implyP disprf _.
        move => /subtypeMachineP /(fun prf => BCD__Trans _ prf (bcd_cat_bigcap _ [:: B] toCover)).
        move => /(fun prf => BCD__Trans _ prf BCD__Lub1).
        move => /subtypeMachineP /disprf.
          by rewrite inprf.
    Qed.

    Definition currentResultNotDone (i: @Instruction Constructor): bool :=
      match i with
      | ContinueCover _ toCover currentResult
      | CheckContinueCover _ toCover currentResult =>
        all (fun A => ~~(checkSubtypes currentResult.2 A)) toCover
      | _ => true
      end.

    Lemma currentResultNotDone_step:
      forall sp1 sp2,
        sp1 ~~> sp2 ->
        all instruction_covered sp1.2 ->
        all toCover_prime sp1.2 ->
        all currentResultNotDone sp1.2 ->
        all currentResultNotDone sp2.2.
    Proof.
      move => [] s1 p1 [] s2 p2 /CoverMachine_inv.
      move => /(fun prf => prf (fun sp1 sp2 =>
                              ( all instruction_covered sp1.2 ->
                                all toCover_prime sp1.2 ->
                                all currentResultNotDone sp1.2 ->
                                all currentResultNotDone sp2.2)%type)).
      case: p1 => //.
      move => [] [].
      - move => toCover p1 prf.
        apply: prf.
          by move => /andP [].
      - move => [] [] srcs tgt covered splits toCover p1 prf.
        apply: prf.
        + by move => _ /andP [].
        + by move => _ _ /andP [].
        + move => _ notDone.
          rewrite {1}/snd (all_cat _ [:: Cover _ _]) all_seq1.
          rewrite (all_cat _ [:: ContinueCover _ _ _]) all_seq1.
          do 2 rewrite (all_cat _ [:: Cover _ _]) all_seq1.
          rewrite (all_cat _ [:: CheckCover _ _]) all_seq1.
          move => /andP [] /andP [] /andP [] tgt_covered tgt_complete _ _ _.
          move => /andP [] _  /= ->.
          rewrite andbT.
          apply: (introT allP).
          move => A inprf.
          move: (mem_subseq (partitionCover_subseq2 covered toCover) inprf).
          move => /(allP tgt_complete) /implyP inprf2.
          apply: (introT negP).
          move => /inprf2.
            by move: (allP (partitionCover_notSubset covered toCover) _ inprf) => /implyP disprf /disprf.
      - move => toCover currentResult p1 prf.
        apply: prf.
          by move => _ _ /andP [].
      - move => [] [] srcs tgt covered splits toCover currentResult p1 prf.
        apply: prf.
        + move => _ _ _.
          rewrite /snd (all_cat _ [:: ContinueCover _ _ _]) all_seq1.
          rewrite (all_cat _ [:: ContinueCover _ _ _]) all_seq1.
          move => /andP [] notDone notDoneRest.
          rewrite notDoneRest.
          move: notDone.
            by rewrite /currentResultNotDone => ->.
        + move => _ _ _ _.
          rewrite /snd (all_cat _ [:: ContinueCover _ _ _]) all_seq1.
          rewrite (all_cat _ [:: CheckContinueCover _ _ _]) all_seq1.
          move => /andP [] notDone notDoneRest.
          rewrite notDoneRest.
          move: notDone.
            by rewrite /currentResultNotDone => ->.
        + move => _ notDone _.
          rewrite {1}/snd (all_cat _ [:: ContinueCover _ _ _]) all_seq1.
          do 3 rewrite (all_cat _ [:: ContinueCover _ _ _]) all_seq1.
          move => /andP [] /andP [] /andP [] /subtypeMachineP tgt_covered tgt_complete _ _.
          move => /andP [] prime _.
          move => /andP [] current__nle /= ->.
          rewrite andbT.
          apply: (introT allP).
          move => A inprf.
          apply: (introT negP).
          have A__prime: (PrimeComponent A).
          { apply /isPrimeComponentP.
            apply: (allP prime).
              by apply: (mem_subseq (partitionCover_subseq2 covered toCover)). }
          move => /subtypeMachineP /(fun prf => primeComponentPrime _ _ _ _ prf A__prime) [].
          * move => /subtypeMachineP.
            move: (mem_subseq (partitionCover_subseq2 covered toCover) inprf).
            move => /(allP tgt_complete) /implyP prf /prf.
              by move: (allP (partitionCover_notSubset covered toCover) _ inprf) => /implyP disprf /disprf.
          * move => /subtypeMachineP.
            move: (allP current__nle _ (mem_subseq (partitionCover_subseq2 covered toCover) inprf)).
              by move => /implyP disprf /disprf.
        + move => _ notDone _.
          rewrite {1}/snd (all_cat _ [:: ContinueCover _ _ _]) all_seq1.
          do 3 rewrite (all_cat _ [:: ContinueCover _ _ _]) all_seq1.
          rewrite (all_cat _ [:: CheckContinueCover _ _ _]) all_seq1.
          move => /andP [] /andP [] /andP [] /subtypeMachineP tgt_covered tgt_complete _ _.
          move => /andP [] prime _.
          move => /andP [] current__nle /= ->.
          move: current__nle.
          rewrite /currentResultNotDone => current__nle.
          rewrite current__nle.
          rewrite andbT andbT.
          apply: (introT allP).
          move => A inprf.
          apply: (introT negP).
          have A__prime: (PrimeComponent A).
          { apply /isPrimeComponentP.
            apply: (allP prime).
              by apply: (mem_subseq (partitionCover_subseq2 covered toCover)). }
          move => /subtypeMachineP /(fun prf => primeComponentPrime _ _ _ _ prf A__prime) [].
          * move => /subtypeMachineP.
            move: (mem_subseq (partitionCover_subseq2 covered toCover) inprf).
            move => /(allP tgt_complete) /implyP prf /prf.
              by move: (allP (partitionCover_notSubset covered toCover) _ inprf) => /implyP disprf /disprf.
          * move => /subtypeMachineP.
            move: (allP current__nle _ (mem_subseq (partitionCover_subseq2 covered toCover) inprf)).
              by move => /implyP disprf /disprf.
      - move => toCover p prf.
          by apply: prf.
      - move => m splits toCover p prf.
          by apply: prf.
      - move => toCover currentResult p prf.
        apply: prf => //.
          by move => _ _ _ /andP [].
      - move => m splits toCover currentResult p prf.
        apply: prf => //.
          by move => _ _ _ /andP [].
    Qed.

    Lemma notDone_incomplete:
      forall (tgt: @IT Constructor) toCover,
        toCover != [::] ->
        all (fun A => ~~ checkSubtypes tgt A) toCover ->
        ~~(checkSubtypes tgt (\bigcap_(A_i <- toCover) A_i)).
    Proof.
      move => currentResult.
      case => // A toCover notOmega.
      move => /allP notDone.
      apply: (introT negP).
      move => /subtypeMachineP tgt__le.
      apply: (negP (notDone A (mem_head A toCover))).
      apply /subtypeMachineP.
      apply: BCD__Trans; first by exact tgt__le.
        by apply: BCD__Trans; first by apply: (bcd_cat_bigcap _ [:: A]).
    Qed.

    Lemma filterMergeMultiArrows_map_cons2:
      forall m1 m2 mss,
        filterMergeMultiArrows
          (map (fun ms => [:: m1 & ms])
               (map (fun ms => [:: m2 & ms]) mss)) =
        filterMergeMultiArrows
          (map (fun ms => [:: mergeMultiArrow m1 m2.1 m2.2 & ms]) mss).
    Proof.
      move => m1 m2.
      elim => // ms mss IH.
      repeat rewrite map_cons.
      rewrite (filterMergeMultiArrows_cat [:: [:: m1, m2 & ms]] _).
      rewrite (filterMergeMultiArrows_cat [:: [:: mergeMultiArrow m1 m2.1 m2.2 & ms]] _).
        by rewrite IH.
    Qed.

    Lemma mergeMultiArrow_srcs_monotonic:
      forall (m: @MultiArrow Constructor) srcs tgt,
        all (fun m12 => checkSubtypes m12.2 m12.1) (zip srcs (mergeMultiArrow m srcs tgt).1).
    Proof.
      move => [] srcs1 tgt1.
      elim: srcs1.
      - by move => [].
      - move => src1 srcs1 IH srcs tgt.
        case: srcs => //= src srcs.
        rewrite (IH srcs tgt) andbT.
        apply /subtypeMachineP.
        rewrite /dcap.
        case: (checkSubtypes src src1) => //.
        case prf: (checkSubtypes src1 src) => //.
        apply /subtypeMachineP.
          by rewrite prf.
    Qed.

    Lemma cap_dcap: forall (A B: @IT Constructor), [bcd (A \cap B) <= A \dcap B].
    Proof.
      move => A B.
      rewrite /dcap.
      case: (checkSubtypes A B) => [] //.
        by case: (checkSubtypes B A) => [].
    Qed.

    Lemma dcap_cap: forall (A B: @IT Constructor), [bcd (A \dcap B) <= A \cap B].
    Proof.
      move => A B.
      rewrite /dcap.
      case le__AB: (checkSubtypes A B) => [].
      - apply: BCD__Glb => //.
          by apply /subtypeMachineP.
      - case le__BA: (checkSubtypes B A) => [] //.
        apply: BCD__Glb => //.
          by apply /subtypeMachineP.
    Qed.

    Lemma mergeMultiArrow_srcs_map_zip:
      forall (currentResult: @MultiArrow Constructor) srcs tgt,
        (mergeMultiArrow currentResult srcs tgt).1 = map (fun srcs => srcs.1 \dcap srcs.2) (zip srcs currentResult.1).
    Proof.
      move => [].
        by elim.
    Qed.

    Lemma explicit_pair_fst {A B: Type}: forall (a: A) (b : B), (a, b).1 = a.
    Proof. by move => *; trivial. Qed.

    Lemma explicit_pair_snd {A B: Type}: forall (a: A) (b : B), (a, b).2 = b.
    Proof. by move => *; trivial. Qed.

    Lemma subseqs_map_cons {a: eqType}: forall (x: a) (xs ys: seq a),
        (ys \in map (cons x) (subseqs xs)) ->
        (ys \in subseqs [:: x & xs]).
    Proof.
      move => x xs ys.
      rewrite /= mem_cat.
        by move => ->.
    Qed.        

    Lemma impossible_notSubtype:
      forall splits toCover m,
        all (fun mps =>
               (checkSubtypes mps.1.2 (\bigcap_(A_i <- mps.2) A_i))
                 && all (fun A => (checkSubtypes mps.1.2 A) ==> (A \in mps.2)) toCover) splits ->
        all (fun A => isPrimeComponent A) toCover ->
        ~~(stillPossible splits toCover) ->
        (m \in filterMergeMultiArrows (subseqs (map fst splits))) ->
        ~~(checkSubtypes m.2 (\bigcap_(A_i <- toCover) A_i)).
    Proof.
      move => splits toCover ms all_covered toCover_prime.
      rewrite /stillPossible -has_predC.
      move => /hasP [] p inprf__p /=.
      rewrite -all_predC.
      move => p_not_covered.
      move: all_covered p_not_covered.
      move: toCover inprf__p toCover_prime ms.
      elim: splits => // [] [] [] srcs tgt covered splits IH toCover inprf__p toCover_prime ms.
      rewrite (all_cat _ [:: (srcs, tgt, covered)]).
      move => /andP [] covered_first covered_rest.
      rewrite (map_cat _ [:: _]) (all_cat _ [:: _]).
      move => /andP [] disprf_first disprf_rest.
      rewrite /= filterMergeMultiArrows_cat mem_cat.
      move => /orP [].
      - move => /filterMergedArrows_in_cons.
        move => /orP [].
        + move => /eqP ->.
          apply /negP.
          move => /subtypeMachineP.
          have mem_prf: {subset [:: p] <= toCover}.
          { move => p'.
            rewrite mem_seq1.
              by move => /eqP ->. }
          move => /(fun prf => BCD__Trans _ prf (bcd_subset_f id toCover [:: p] mem_prf)).
          move: covered_first.
          rewrite all_seq1.
          move => /andP [] _ /allP /(fun prf => prf p inprf__p) /implyP devil /subtypeMachineP /devil.
          move: disprf_first.
          rewrite all_seq1.
            by move => /negbTE ->.
        + move => /hasP [] ms2 inprf__ms2 /andP [].
          have prime_p_singleton: (all (fun A => isPrimeComponent A) [:: p]).
          { rewrite all_seq1.
              by move: toCover_prime => /allP /(fun prf => prf p inprf__p). }
          have p_covered:
            (all (fun mps =>
                    (checkSubtypes mps.1.2 (\bigcap_(A_i <- mps.2) A_i))
                      && (all (fun A : IT => checkSubtypes mps.1.2 A ==> (A \in mps.2))
                              [:: p])) splits).
          { apply /allP.
            move => x inprf__x.
            rewrite all_seq1.
              by move: covered_rest => /allP /(fun prf => prf x inprf__x) /andP [] -> /allP /(fun prf => prf p inprf__p) ->. }
          move => /(IH [:: p] (mem_head p _) prime_p_singleton (mergeMultiArrows ms2) p_covered disprf_rest) disprf /eqP ->.
          apply /negP.
          move => /subtypeMachineP.
          move => /(fun prf => BCD__Trans _ (mergeMultiArrows_tgt_ge _) prf).
          move => /(fun prf => BCD__Trans _ (bcd_bigcap_cat_f _ _ _ [:: _] _) prf).
          have mem_prf: {subset [:: p] <= toCover}.
          { move => p'.
            rewrite mem_seq1.
              by move => /eqP ->. }
          move => /(fun prf => BCD__Trans _ prf (bcd_subset_f id toCover [:: p] mem_prf)).
          move: toCover_prime => /allP /(fun prf => prf p inprf__p) /isPrimeComponentP prime__p.
          move => /(fun prf => primeComponentPrime _ _ _ _ prf prime__p).
          case.
          * move: covered_first.
            rewrite all_seq1.
            move => /andP [] _ /allP /(fun prf => prf p inprf__p) /implyP devil /subtypeMachineP /devil.
            move: disprf_first.
            rewrite all_seq1.
              by move => /negbTE ->.
          * move => /(fun prf => BCD__Trans _ (mergeMultiArrows_tgt_le _) prf) /subtypeMachineP.
              by apply /negP.
      - by apply: IH.
    Qed.


    Lemma complete_reverse:
      forall s s1 p1 s2 p2,
        (s1, p1) ~~> (s2, p2) ->
        suffix s2 s ->
        all arity_equal p1 ->
        all not_omega_instruction p1 ->
        all instruction_covered p1 ->
        all toCover_prime p1 ->
        all currentResultNotDone p1 ->
        all (complete s) p2 ->
        all (complete s) p1.
    Proof.
      move => s s1 p1 s2 p2 step s2_suffix.
      move => arity_equal_instructions not_omega_instructions instructions_covered.
      move => prime_instructions notDone complete__p2.
      suff: (all (complete s) (take 1 p1)).
      { move: complete__p2.
        move: (step_programStack _ _ _ _ step).
        move /suffixP => [] p3 /eqP ->.
        rewrite all_cat.
        move => /andP [] _ complete__rest complete__head.
        have: (p1 = take 1 p1 ++ behead p1) by case p1 => //= ? ?; rewrite take0.
        move => ->.
          by rewrite all_cat complete__head complete__rest. }
      move: step arity_equal_instructions instructions_covered not_omega_instructions prime_instructions notDone.
      case: p1 => //=.
      move => i1 p1 step.
      rewrite take0 /= andbT.
      move: (step_programStack _ _ _ _ step) => /suffixP [] p3 /eqP p2__eq.
      move: step complete__p2.
      rewrite p2__eq.
      move => step.
      rewrite all_cat.
      move => /andP [] complete__p3 _.
      move: p2__eq => _.
      have: ((s1, [:: i1]) ~~> (s2, p3)).
      { move: step => /CoverMachine_inv.
        move => /(fun prf => prf (fun sp1 sp2 => (sp1.1, take 1 sp1.2) ~~> (sp2.1, take (seq.size sp2.2 - seq.size (behead sp1.2)) sp2.2))).
        case: i1; case.
        - move => toCover /=.
          rewrite size_cat addnK take_cat ltnn subnn take0 subnn take0 cats0.
          move => prf.
            by apply: prf.
        - move => [] [] srcs tgt covered splits toCover /=.
          rewrite size_cat addnK take_cat ltnn subnn take0 cats0 -addn2 -addn1 (addnC _ 1) (addnC _ 2) addnK addnK /= take0.
          move => prf.
            by apply: prf; move => *; constructor.
        - move => toCover currentResult /=.
          rewrite size_cat addnK take_cat ltnn subnn take0 subnn take0 cats0.
          move => prf.
            by apply: prf.
        - move => [] [] srcs tgt covered splits toCover currentResult /=.
          rewrite size_cat addnK take_cat ltnn subnn take0 cats0 -addn2 -addn1 (addnC _ 1) (addnC _ 2) addnK addnK /= take0.
          move => prf.
            by apply: prf; move => *; constructor.
        - move => toCover /=.
          rewrite size_cat addnK -addn1 addnC -addnBA => //.
          rewrite subnn addn0 take0 take_cat subnn take0 cats0 ltnn.
          move => prf.
          apply: prf; by constructor.
        - move => m splits toCover /=.
          rewrite size_cat addnK -addn1 addnC -addnBA => //.
          rewrite subnn addn0 take0 take_cat subnn take0 cats0 ltnn.
          move => prf.
          apply: prf; by constructor.
        - move => toCover currentResult /=.
          rewrite size_cat addnK -addn1 addnC -addnBA => //.
          rewrite subnn addn0 take0 take_cat subnn take0 cats0 ltnn.
          move => prf.
          apply: prf; by constructor.
        - move => m splits toCover currentResult /=.
          rewrite size_cat addnK -addn1 addnC -addnBA => //.
          rewrite subnn addn0 take0 take_cat subnn take0 cats0 ltnn.
          move => prf.
          apply: prf; by constructor.
      }
      move: p2 step => _ _ step /andP [] arity_equal__i _ /andP [] covered__i _ /andP [] not_omega__i _.
      move => /andP [] prime__i _ /andP [] notDone__i _.
      move: p1 => _.
      move: step s2_suffix arity_equal__i covered__i not_omega__i prime__i notDone__i complete__p3.
      move => /CoverMachine_inv
              /(fun res => res (fun sp1 sp2 => (
                                 suffix sp2.1 s ->
                                 arity_equal (head i1 sp1.2) ->
                                 instruction_covered (head i1 sp1.2) ->
                                 not_omega_instruction (head i1 sp1.2) ->
                                 toCover_prime (head i1 sp1.2) ->
                                 currentResultNotDone (head i1 sp1.2) ->
                                 all (complete s) sp2.2 -> complete s (head i1 sp1.2))%type)).
      case: i1; case => /=.
      - move => toCover prf instructions_covered.
          by apply: prf.
      - move => [] [] srcs tgt covered splits toCover prf.
        apply: prf.
        + move => partition__eq _ arity_equal__i instructions_covered__i not_omega_instructions__i prime__i _.
          rewrite andbT /complete /= filterMergeMultiArrows_cat all_cat.
          move => prf.
          rewrite prf andbT.
          apply: (introT allP).
          move => m /filterMergedArrows_in_cons.
          move => /orP [].
          * move => /= /eqP -> /=.
            rewrite implybE.
            apply: (introT orP); left.
            apply: (introT negP).
            move: prf arity_equal__i prime__i instructions_covered__i partition__eq not_omega_instructions__i => _ _ _.
            case: toCover => //= path [] /=.
            ** rewrite /instruction_covered /= andbT.
                 by case: (checkSubtypes tgt path) => // /andP [] /andP [] _ /implyP /(fun prf => prf isT) -> _ /= [] /eqP /nilP.
            ** move => p toCover /andP [] /andP [] _ /andP [] disprf _ _ partition__eq not_omega.
               move => /subtypeMachineP /(fun prf => BCD__Trans _ prf (BCD__Lub1)) /subtypeMachineP prf.
               move: disprf partition__eq => /implyP /(fun disprf => disprf prf) ->.
               case: (partitionCover covered toCover).
                 by case: (p \in covered) => ? ? /= /eqP /nilP.
          * move => /hasP [] ms [] inprf /andP [] inprf__merged m__eq.
            move: prf => /allP /(fun prf => prf (mergeMultiArrows ms)) /(fun prf => prf inprf__merged).
            move => prf.
            apply: (introT implyP).
            move: m__eq => /eqP ->.
            move => /subtypeMachineP /(BCD__Trans _ (mergeMultiArrows_tgt_ge _)).
            move: instructions_covered__i => /covered_head_tgt [] prf1 prf2.
            move => /(partitionCover_prime (srcs, tgt) ms covered toCover prime__i prf1 prf2) [] _.
            move => /(BCD__Trans _ (mergeMultiArrows_tgt_le _)) /subtypeMachineP.
            rewrite (partitionCover_drop1 _ _ partition__eq).
            move => ms_tgt__le.
            have: (~~nilp ms).
            { apply: (introT negP).
              move => /nilP ms__eq.
              move: ms_tgt__le not_omega_instructions__i.
              rewrite ms__eq /not_omega_instruction /=.
              clear ...
              case: toCover => // A toCover.
              move => /subtypeMachineP /(fun prf => BCD__Trans _ prf (bcd_cat_bigcap _ [:: A] toCover)).
                by move => /(fun prf => BCD__Trans _ prf (BCD__Lub1)) /subtypeMachineP /= ->. }
            move => ms__nonEmpty.
            move: prf ms_tgt__le => /implyP prf /prf.
            apply: sub_has.
            move => y /andP [] /eqP y__size /andP [] srcs_prf ->.
            rewrite andbT.
            have arity_equal__ms: (all (fun x => all (fun y => seq.size x.1 == seq.size y.1) [:: (srcs, tgt) & ms])
                                     [:: (srcs, tgt) & ms]).
            { apply: (introT allP).
              move => x x__in.
              have: (x \in map fst [:: (srcs, tgt, covered) & splits]).
              { move: x__in.
                rewrite in_cons.
                move => /orP [].
                - move => /eqP -> /=.
                    by rewrite in_cons eq_refl.
                - move: (subseqs_subseq _ _ inprf).
                  move => /mem_subseq subprf /subprf.
                  rewrite map_cons in_cons => ->.
                    by rewrite orbT. }
              move: x__in => _.
              move: x.
              apply: allP.
              apply: sub_all; last by exact arity_equal__i.
              move => x /= /andP [] -> /allP subprf /=.
              apply: (introT allP).
              move => z z__in.
              apply: subprf.
              apply: mem_subseq; last by exact z__in.
                by apply: subseqs_subseq. }
            have y__size_srcs: (seq.size y.1 == seq.size (mergeMultiArrows ((srcs, tgt) :: ms)).1).
            { rewrite y__size eq_sym.
                by rewrite (mergeMultiArrows_cons_arity (srcs, tgt) ms ms__nonEmpty). } 
            rewrite y__size_srcs /andb.
            apply: (introT (all_nthP (Omega, Omega))).
            move => n n_lt.
            rewrite nth_zip; last by move: y__size_srcs => /eqP ->.
            move: srcs_prf n_lt => /(all_nthP (Omega, Omega)).
            rewrite size_zip size_zip -y__size.
            move: y__size_srcs => /eqP ->.
            rewrite minnn.
            move => nth__le n_lt.
            move: (nth__le n n_lt) => /subtypeMachineP /(fun prf x => BCD__Trans _ x prf).
            rewrite nth_zip; last by rewrite y__size.
            move => res.           
            apply /subtypeMachineP.
            apply: res.
            rewrite {1 3}/fst {2}/fst.
            apply: (BCD__Trans (\bigcap_(A_i <- [:: (srcs, tgt) & ms]) (nth Omega A_i.1 n))).
            ** by apply: mergeMultiArrows_srcs_le.
            ** apply: BCD__Trans; first by apply: (bcd_cat_bigcap_f _ _ (fun x => nth Omega x.1 n) [:: (srcs, tgt)]).
               apply: BCD__Trans; first by apply: (BCD__Lub2).
               apply: mergeMultiArrows_srcs_ge.
               apply: sub_all; last by (move: arity_equal__ms => /andP [] _ restprf; exact restprf).
                 by move => ? /andP [].
        + move => partition__eq1 partition__eq2 s__suffix arity_equal__i instructions_covered__i not_omega_instructions__i prime__i _.
          rewrite /complete /= filterMergeMultiArrows_cat all_cat andbT.
          move => prf.
          rewrite prf andbT.
          apply: (introT allP).
          move => m /filterMergedArrows_in_cons.
          move => /orP [].
          * move => /= /eqP -> /=.
            apply: (introT implyP).
            move => tgt__le.
            apply: (introT hasP).
            exists (srcs, tgt).
            ** move: s__suffix => /suffixP [] s__prefix /eqP ->.
                 by rewrite mem_cat mem_head orbT.
            ** rewrite eq_refl /= tgt__le andbT.
               apply: (introT allP).
               move => ? /zip_eq ->.
                     by apply /subtypeMachineP.
          * move => /hasP [] ms [] inprf /andP [] inprf__merged m__eq.
            move: prf => /allP /(fun prf => prf (mergeMultiArrows ms)) /(fun prf => prf inprf__merged).
            move => prf.
            apply: (introT implyP).
            move: m__eq => /eqP ->.
            move => le__prf.
            apply: (introT hasP).
            exists (srcs, tgt).
            ** move: s__suffix => /suffixP [] s__prefix /eqP ->.
                 by rewrite mem_cat mem_head orbT.
            **
              have arity_equal__ms: (all (fun x => all (fun y => seq.size x.1 == seq.size y.1) [:: (srcs, tgt) & ms])
                                     [:: (srcs, tgt) & ms]).
              { apply: (fun subprf => all_nested_subseq _ _ _ subprf arity_equal__i).
                rewrite /= eq_refl.
                  by apply: subseqs_subseq. }
               move: (mergeMultiArrows_arity _ arity_equal__ms) => /andP [] ->.
               rewrite /mergeComponentsOf.
               rewrite -(partitionCover_drop2 _ _ partition__eq2).
               have: [ bcd ((srcs, tgt, covered).1.2) <= \bigcap_(A_i <- (partitionCover covered toCover).1) A_i].
               { move: instructions_covered__i => /andP [] /andP [].
                 move => /subtypeMachineP /(fun prf subset => BCD__Trans _ prf (bcd_subset_f (fun x => x) covered
                                                                                       (partitionCover covered toCover).1
                                                                                       subset)).
                 move => res _ _.
                 apply: res.
                   by move: (partitionCover_subset covered toCover) => /allP. }
               rewrite {1}/fst.
               move => /subtypeMachineP ->.
               rewrite andbC andbT andbT.
               move => arity_equal__rest.
               apply: (introT (all_nthP (Omega, Omega))).
               move => n n__lt.
               rewrite nth_zip {1}/fst /snd.
               *** apply /subtypeMachineP.
                   apply: BCD__Trans; first by apply: (mergeMultiArrows_srcs_le _ n arity_equal__ms).
                     by apply: BCD__Trans; first by apply: (bcd_cat_bigcap_f _ _ (fun x => nth Omega x.1 n) [:: (srcs, tgt)] ms).
               *** by move: (mergeMultiArrows_arity _ arity_equal__ms) => /andP [] /eqP <-.
        + move => partition__eq1 partition__eq2 s__suffix arity_equal__i instructions_covered__i not_omega_instructions__i prime__i _.
          rewrite /complete /= filterMergeMultiArrows_cat all_cat all_cat andbT.
          move => /andP [] prf1 prf2.
          rewrite prf2 andbT.
          move: prf2 prf1 => _.
          move => /andP [] prf _.
          apply: (introT allP).
          move => m inprf.
          move: (filterMergedArrows_in_cons _ _ _ inprf).
          move => /orP [].
          * move => /eqP ->.
            apply: (introT implyP).
            move: instructions_covered__i => /andP [] /andP [] _.
            move => /(complete_partitionCover _ _ _) disprf _ /disprf.
              by move: partition__eq2 => /eqP partition__eq2 /partition__eq2.
          * move => /hasP [] ms inprf__ms /andP [] inprf__merged /eqP m__eq.
            move: prf inprf.
            rewrite m__eq.
            move => /allP /(fun prf => @prf (mergeMultiArrows [:: (srcs, tgt) & ms])).
            move => prf /prf.
            move: prf => _.
            move => /implyP prf.
            apply: (introT implyP).
            have partition_subset: {subset (partitionCover covered toCover).2 <= toCover}.
            { move: (partitionCover_subseq2 covered toCover).
                by move => /mem_subseq. }
            move => /subtypeMachineP /(fun prf => BCD__Trans _ prf (bcd_subset_f id _ _ partition_subset)).
            move => /subtypeMachineP /prf.
            apply: sub_has.
            move => A /andP [] arity_equal__A /andP [] srcs__ge tgt__le.
            have arity_equal_srcsms:
              (all
                 (fun x => all (fun y => seq.size x.1 == seq.size y.1) ((srcs, tgt) :: ms))
                 ((srcs, tgt) :: ms)).
            { apply: (fun subprf => all_nested_subseq _ _ _ subprf arity_equal__i).
              rewrite /= eq_refl.
                by apply: subseqs_subseq. }
            have arity_equal__srcs: (seq.size (mergeMultiArrows [:: (srcs, tgt) & ms]).1 == seq.size srcs).
            { rewrite eq_sym.
                by apply: (fun prf => (proj1 (andP (mergeMultiArrows_arity [:: (srcs, tgt) & ms] prf)))). }
            move: arity_equal__A.
            rewrite size_map size_zip (eqP arity_equal__srcs) minnn.
            move => arity_equal__A.
            rewrite arity_equal__A andTb.
            apply /andP.
            split.
            ** apply /(all_nthP (Omega, Omega)).
               move: (all_nthP (Omega, Omega) srcs__ge).
               rewrite size_zip size_map size_zip (eqP arity_equal__srcs) minnn (eqP arity_equal__A) minnn.
               rewrite size_zip (eqP arity_equal__srcs) (eqP arity_equal__A) minnn.
               move => srcs_n__ge n n__lt.
               move: (srcs_n__ge n n__lt).
               rewrite nth_zip;
                 last by rewrite size_map size_zip (eqP arity_equal__srcs) minnn (eqP arity_equal__A).
               rewrite (nth_map (Omega, Omega) Omega);
                 last by rewrite size_zip (eqP arity_equal__srcs) minnn.
               rewrite nth_zip; last by exact (eqP arity_equal__srcs).
               rewrite nth_zip; last by (rewrite (eqP arity_equal__A); exact (eqP arity_equal__srcs)).
               rewrite {2 6}/fst {1 2}/snd.
               rewrite {1 5}/fst /snd.
               move => /subtypeMachineP n__le.
               apply /subtypeMachineP.
               apply: BCD__Trans; last by exact n__le.
               apply: BCD__Trans; last by apply: cap_dcap.
               apply: BCD__Glb => //.
               apply: BCD__Trans; first by apply: (mergeMultiArrows_srcs_le _ _ arity_equal_srcsms).
                 by apply: BCD__Trans; first by apply: (bcd_cat_bigcap_f _ _ (fun x => nth Omega x.1 n) [:: (srcs, tgt)]).
            ** apply /subtypeMachineP.
               apply: BCD__Trans; first by exact (subtypeMachineP _ _ _ tgt__le).
               apply: BCD__Trans; last by apply: (partition_cover_both covered).
               apply: BCD__Trans; last by apply: bcd_bigcap_cat.
               apply: BCD__Glb => //.
               apply: BCD__Trans; first by apply: BCD__Lub1.
               apply: BCD__Trans;
                 first by (move: instructions_covered__i => /andP [] /andP [] /subtypeMachineP res *; exact res).
               apply: bcd_subset_f.
                 by move: (partitionCover_subset covered toCover) => /allP.
      - move => toCover currentResult prf instructions_covered.
        apply: prf => //.
        rewrite /complete [mergeComponentsOf _ ]/= [subseqs _]/= [filterMergeMultiArrows _]/= all_seq1.
        move => _ _ _ /andP [] notEmpty _ _ /(notDone_incomplete _ _ notEmpty) /implyP disprf _.
        apply: (introT implyP).
          by move => /disprf.
      - move => [] [] srcs tgt covered splits toCover currentResult prf.
        apply: prf.
        + move => partition__eq _ arity_equal__i instructions_covered__i not_omega_instructions__i prime__i notDone.
          rewrite /complete /=.
          rewrite filterMergeMultiArrows_cat all_cat andbT.
          move => /andP [] prf1 prf2.
          rewrite filterMergeMultiArrows_cat map_cat all_cat.
          rewrite filterMergeMultiArrows_cat all_cat.
          rewrite filterMergeMultiArrows_cat all_cat.
          rewrite prf2 andbT.
          rewrite prf1 andbT.
          apply: (introT andP).
          split.
          * apply: (introT allP).
            move => m.
            rewrite filterMergeMultiArrows_map_cons2.
            move => /filterMergedArrows_in_cons.
            move => /orP [].
            ** move => /= /eqP -> /=.
               rewrite implybE.
               apply: (introT orP); left.
               apply: (introT negP).
               move: prf1 prf2 arity_equal__i instructions_covered__i partition__eq not_omega_instructions__i notDone prime__i => _ _ _.
               case: toCover => // path [].
               *** rewrite /instruction_covered /= andbT.
                   case tgt__le: (checkSubtypes tgt path) => //.
                   move => /andP [] /andP [] _ /implyP /(fun prf => prf isT) -> _ /= [] /eqP /nilP //.
                   rewrite andbT.
                   move => _ _ _ currentResult_disprf.
                   rewrite /toCover_prime /= andbT.
                   move => /isPrimeComponentP path_prime /subtypeMachineP devil.
                   move: (primeComponentPrime  _ _ _ _ devil path_prime) => [] /subtypeMachineP.
                   **** by rewrite tgt__le.
                   **** by move => /(negP currentResult_disprf).
               *** move => p toCover /andP [] /andP [] _ /andP [] disprf _ _ partition__eq not_omega.
                   rewrite map_cons.
                   move => /andP [] currentResult_disprf _.
                   move => /andP [] /isPrimeComponentP path_prime _.
                   move => /subtypeMachineP /(fun prf => BCD__Trans _ prf (bcd_cat_bigcap _ [:: path] [:: p & toCover])).
                   move => /(fun prf => BCD__Trans _ prf BCD__Lub1) devil.
                   move: (primeComponentPrime  _ _ _ _ devil path_prime) => [] /subtypeMachineP.
                   **** move => prf.
                        move: disprf partition__eq => /implyP /(fun disprf => disprf prf).
                        rewrite [partitionCover _ _]/= [snd (_, _)]/=.
                        case: (partitionCover covered toCover).
                          by case: (p \in covered) => ? ? -> /= /eqP /nilP. 
                   **** by move => /(negP currentResult_disprf).
            ** move => /hasP [] ms [] inprf /andP [] inprf__merged m__eq.
               move: prf2 => /allP /(fun prf => prf (mergeMultiArrows ms)) /(fun prf => prf inprf__merged).
               move: prf1 => _ prf.
               apply: (introT implyP).
               move: m__eq => /eqP ->.
               move => /subtypeMachineP /(BCD__Trans _ (mergeMultiArrows_tgt_ge _)).
               move: instructions_covered__i => /covered_head_tgt [] prf1 prf2.
               have: (forall A, A \in toCover -> [bcd ((mergeMultiArrow currentResult srcs tgt).2) <= A] -> A \in covered).
               { move => A inprf__A.
                 move: (allP prime__i A inprf__A) => /isPrimeComponentP prime__A /= ge__A.
                 move: (primeComponentPrime  _ _ _ _ ge__A prime__A) => [].
                 - by move => /(prf1 A inprf__A).
                 - by move: (allP notDone A inprf__A) => /negP disprf /subtypeMachineP /disprf. }
               move: prf1 => _ prf1.
               move: prf2 => /(BCD__Trans _ (@BCD__Lub1 _ tgt currentResult.2)) prf2.
               move => /(partitionCover_prime (mergeMultiArrow currentResult srcs tgt) ms covered toCover prime__i prf1 prf2) [] _.
               move => /(BCD__Trans _ (mergeMultiArrows_tgt_le _)).
               rewrite (partitionCover_drop1 _ _ partition__eq).
               move => ms_tgt__le.
               have: (~~nilp ms).
               { apply: (introT negP).
                 move => /nilP ms__eq.
                 move: ms_tgt__le not_omega_instructions__i.
                 rewrite ms__eq /not_omega_instruction /=.
                 clear ...
                 case: toCover => // A toCover.
                 move => /(fun prf => BCD__Trans _ prf (bcd_cat_bigcap _ [:: A] toCover)).
                   by move => /(fun prf => BCD__Trans _ prf (BCD__Lub1)) /subtypeMachineP /= ->. }
               move => ms__nonEmpty.
               move: prf ms_tgt__le => /implyP prf /subtypeMachineP /prf.
               apply: sub_has.
               move => y /andP [] /eqP y__size /andP [] srcs_prf ->.
               rewrite andbT.
               have fold_merge: (mergeMultiArrows [:: currentResult, (srcs, tgt) & ms] =
                                 mergeMultiArrows [:: mergeMultiArrow currentResult srcs tgt & ms]) => //.
               have arity_equal__currentms: (all (fun x => all (fun y => seq.size x.1 == seq.size y.1)
                                                          [:: currentResult, (srcs, tgt) & ms])
                                               [:: currentResult, (srcs, tgt) & ms]).
               { apply: (fun subprf => all_nested_subseq _ _ _ subprf arity_equal__i).
                 rewrite /= eq_refl eq_refl.
                   by apply: subseqs_subseq. }
               have arity_equal__ms: (all (fun x => all (fun y => seq.size x.1 == seq.size y.1)
                                                   [:: (srcs, tgt) & ms])
                                        [:: (srcs, tgt) & ms]).
               { by apply: (all_nested_tl _ currentResult). }
               have arity_equal__mergeCurrentms: (all (fun m1 => all (fun m2 => seq.size m1.1 == seq.size m2.1)
                                                                (mergeMultiArrow currentResult srcs tgt :: ms))
                                                    (mergeMultiArrow currentResult srcs tgt :: ms)).
               { apply: (introT allP).
                 move => x.
                 move: arity_equal__i => /andP [] /andP [] _ /andP [] /eqP arity_equal__currentResult _ _.
                 rewrite in_cons => /orP [].
                 - move => /eqP ->.                   
                   rewrite (all_cat _ [:: _] _) all_seq1 eq_refl /= size_map size_zip arity_equal__currentResult minnn.
                   apply: sub_all; last by (move: arity_equal__ms => /andP [] _ res; exact res).
                     by move => x2 /andP [] /eqP ->.
                 - move: arity_equal__ms => /andP [] _ /allP arity_equal__ms /arity_equal__ms.
                   do 2 rewrite (all_cat _ [:: _] _) all_seq1.
                   move => /andP [] /eqP -> ->.
                     by rewrite /= size_map size_zip arity_equal__currentResult minnn eq_refl. }
               have y__size_srcs: (seq.size y.1 == seq.size ((mergeMultiArrows [:: (mergeMultiArrow currentResult srcs tgt) & ms]).1)).
               { rewrite y__size.
                 move: (mergeMultiArrows_arity _ arity_equal__mergeCurrentms).
                 move => /andP [] /eqP <- _.
                 rewrite /mergeMultiArrow {4}/fst.
                 rewrite size_map size_map size_zip size_zip.
                 apply /eqP.
                 apply: (f_equal (fun x => minn x (seq.size currentResult.1))).
                 move: (mergeMultiArrows_arity _ arity_equal__ms) => /andP [] /eqP -> _.
                 apply: Logic.eq_sym.
                   by apply: mergeMultiArrows_cons_arity. }
               have y__size_mergedsrcs:
                 (seq.size y.1 ==
                  seq.size
                    (map (fun srcs => srcs.1 \dcap srcs.2)
                         (zip (mergeMultiArrows [:: mergeMultiArrow currentResult (srcs, tgt).1 (srcs, tgt).2 & ms]).1
                              currentResult.1))).
               { move: y__size.
                 rewrite (eqP y__size_srcs) => ->.
                 rewrite size_map size_zip size_map size_zip.
                 apply /eqP.
                 apply: (f_equal (fun x => minn x _)).
                 apply: Logic.eq_sym.
                   by apply: mergeMultiArrows_cons_arity. }
               rewrite y__size_mergedsrcs andTb.
               apply: (introT (all_nthP (Omega, Omega))).
               move => n n_lt.
               rewrite nth_zip; last by move: y__size_mergedsrcs => /eqP ->.
               move: srcs_prf n_lt => /(all_nthP (Omega, Omega)).
               rewrite size_zip size_zip -y__size.
               move: y__size_mergedsrcs => /eqP y__size_mergedsrcs.
               rewrite y__size_mergedsrcs.
               rewrite minnn.
               move => nth__le n_lt.
               move: (nth__le n n_lt) => /subtypeMachineP /(fun prf x => BCD__Trans _ x prf).
               rewrite nth_zip; last by rewrite y__size.
               move => res.           
               apply /subtypeMachineP.
               apply: res.
               rewrite (nth_map (Omega, Omega) Omega); last by (move: n_lt; rewrite size_map).
               rewrite nth_zip; last first.
               { rewrite -fold_merge.
                   by move: (mergeMultiArrows_arity _ arity_equal__currentms) => /andP [] /eqP ->. }
               rewrite {2}/fst {2}/snd {6}/fst.
               have currentResult_size: (seq.size (mergeMultiArrows ms).1 = seq.size currentResult.1).
               { rewrite -(mergeMultiArrows_cons_arity (srcs, tgt) ms
                                                       ms__nonEmpty
                                                       arity_equal__ms).
                 rewrite -(mergeMultiArrows_cons_arity currentResult [:: (srcs, tgt) & ms]
                                                       isT
                                                       arity_equal__currentms).
                   by move: (mergeMultiArrows_arity _ arity_equal__currentms) => /andP [] /eqP ->. }
               have n_lt2: (n < seq.size (zip (mergeMultiArrows ms).1 currentResult.1)).
               { rewrite size_zip.
                 rewrite -(mergeMultiArrows_cons_arity (mergeMultiArrow currentResult srcs tgt) ms
                                                       ms__nonEmpty arity_equal__mergeCurrentms).
                   by rewrite -size_zip -(size_map (fun srcs => srcs.1 \dcap srcs.2)). }
               rewrite (nth_map (Omega, Omega) Omega) => //.
               rewrite {1}/fst.
               rewrite nth_zip => //.
               rewrite {4}/fst {2}/snd.
               apply: BCD__Trans; last by apply: cap_dcap.
               apply: BCD__Trans; first by apply: dcap_cap.
               apply: BCD__Glb => //.
               apply: BCD__Trans; first by apply: BCD__Lub1.
               rewrite -fold_merge.
               apply: BCD__Trans; first by apply: mergeMultiArrows_srcs_le.
               apply: BCD__Trans; first by apply: (bcd_cat_bigcap_f _ _ (fun m => nth Omega m.1 n) [:: _; _]).
               apply: BCD__Trans; first by apply: BCD__Lub2.
               apply: mergeMultiArrows_srcs_ge.
               apply: all_nested_tl.
                 by exact arity_equal__ms.
          * move: prf1 prf2 => _ prf.
            apply: (introT allP).
            move => m /filterMergedArrows_in_cons.
            move => /orP [].
            ** move => /= /eqP -> /=.
               rewrite implybE.
               apply: (introT orP); left.
               apply: (introT negP).
               move: prf notDone arity_equal__i prime__i instructions_covered__i partition__eq not_omega_instructions__i => _ _ _ _.
               case: toCover => //= path [] /=.
               *** rewrite /instruction_covered /= andbT.
                     by case: (checkSubtypes tgt path) => // /andP [] /andP [] _ /implyP /(fun prf => prf isT) -> _ /= [] /eqP /nilP.
               *** move => p toCover /andP [] /andP [] _ /andP [] disprf _ _ partition__eq not_omega.
                   move => /subtypeMachineP /(fun prf => BCD__Trans _ prf (BCD__Lub1)) /subtypeMachineP prf.
                   move: disprf partition__eq => /implyP /(fun disprf => disprf prf) ->.
                   case: (partitionCover covered toCover).
                     by case: (p \in covered) => ? ? /= /eqP /nilP.
            ** move => /hasP [] ms [] inprf /andP [] inprf__merged m__eq.
               move: prf => /allP /(fun prf => prf (mergeMultiArrows ms)) /(fun prf => prf inprf__merged).
               move => prf.
               apply: (introT implyP).
               move: m__eq => /eqP ->.
               move => /subtypeMachineP /(BCD__Trans _ (mergeMultiArrows_tgt_ge _)).
               move: instructions_covered__i => /covered_head_tgt [] prf1 prf2.
               move => /(partitionCover_prime (srcs, tgt) ms covered toCover prime__i prf1 prf2) [] _.
               move => /(BCD__Trans _ (mergeMultiArrows_tgt_le _)) /subtypeMachineP.
               rewrite (partitionCover_drop1 _ _ partition__eq).
               move => ms_tgt__le.
               have: (~~nilp ms).
               { apply: (introT negP).
                 move => /nilP ms__eq.
                 move: ms_tgt__le not_omega_instructions__i.
                 rewrite ms__eq /not_omega_instruction /=.
                 clear ...
                 case: toCover => // A toCover.
                 move => /subtypeMachineP /(fun prf => BCD__Trans _ prf (bcd_cat_bigcap _ [:: A] toCover)).
                   by move => /(fun prf => BCD__Trans _ prf (BCD__Lub1)) /subtypeMachineP /= ->. }
               move => ms__nonEmpty.
               move: prf ms_tgt__le => /implyP prf /prf.
               apply: sub_has.
               move => y /andP [] /eqP y__size /andP [] srcs_prf ->.
               rewrite andbT.
               have arity_equal__ms: (all (fun x => all (fun y => seq.size x.1 == seq.size y.1) [:: (srcs, tgt) & ms])
                                        [:: (srcs, tgt) & ms]).
               { apply: (introT allP).
                 move => x x__in.
                 have: (x \in map fst [:: (srcs, tgt, covered) & splits]).
                 { move: x__in.
                   rewrite in_cons.
                   move => /orP [].
                   - move => /eqP -> /=.
                       by rewrite in_cons eq_refl.
                   - move: (subseqs_subseq _ _ inprf).
                     move => /mem_subseq subprf /subprf.
                     rewrite map_cons in_cons => ->.
                       by rewrite orbT. }
                 move: x__in => _.
                 move: x.
                 apply: allP.
                 apply: sub_all; last by exact (proj2 (andP arity_equal__i)).
                 move => x /= /andP [] _ /andP [] -> /allP subprf /=.
                 apply: (introT allP).
                 move => z z__in.
                 apply: subprf.
                 apply: mem_subseq; last by exact z__in.
                   by apply: subseqs_subseq. }
               have arity_equal__currentms: (all (fun x => all (fun y => seq.size x.1 == seq.size y.1)
                                                          [:: currentResult, (srcs, tgt) & ms])
                                               [:: currentResult, (srcs, tgt) & ms]).
               { apply: (fun subprf => all_nested_subseq _ _ _ subprf arity_equal__i).
                 rewrite /= eq_refl eq_refl.
                   by apply: subseqs_subseq. }
               have arity_equal__mergeCurrentms: (all (fun m1 => all (fun m2 => seq.size m1.1 == seq.size m2.1)
                                                                (mergeMultiArrow currentResult srcs tgt :: ms))
                                                    (mergeMultiArrow currentResult srcs tgt :: ms)).
               { apply: (introT allP).
                 move => x.
                 move: arity_equal__i => /andP [] /andP [] _ /andP [] /eqP arity_equal__currentResult _ _.
                 rewrite in_cons => /orP [].
                 - move => /eqP ->.                   
                   rewrite (all_cat _ [:: _] _) all_seq1 eq_refl /= size_map size_zip arity_equal__currentResult minnn.
                   apply: sub_all; last by (move: arity_equal__ms => /andP [] _ res; exact res).
                     by move => x2 /andP [] /eqP ->.
                 - move: arity_equal__ms => /andP [] _ /allP arity_equal__ms /arity_equal__ms.
                   do 2 rewrite (all_cat _ [:: _] _) all_seq1.
                   move => /andP [] /eqP -> ->.
                     by rewrite /= size_map size_zip arity_equal__currentResult minnn eq_refl. }
               have arity_equal_currentResult: (seq.size currentResult.1 == seq.size (mergeMultiArrows ms).1).
               { rewrite -(mergeMultiArrows_cons_arity (srcs, tgt)) => //.
                 rewrite -(mergeMultiArrows_cons_arity currentResult) => //.
                   by move: (mergeMultiArrows_arity _ arity_equal__currentms) => /andP [] ->. }
               have y__size_srcs: (seq.size y.1 ==
                                   seq.size (map (fun srcs => srcs.1 \dcap srcs.2)
                                                 (zip (mergeMultiArrows [:: (srcs, tgt) & ms]).1
                                                      currentResult.1))).
               { rewrite y__size eq_sym size_map size_zip size_map size_zip.                 
                   by rewrite (mergeMultiArrows_cons_arity (srcs, tgt)). }
               rewrite (eqP y__size_srcs) eq_refl andTb.
               apply: (introT (all_nthP (Omega, Omega))).
               move => n n_lt.
               rewrite nth_zip; last by move: y__size_srcs => /eqP ->.
               move: srcs_prf n_lt => /(all_nthP (Omega, Omega)).
               rewrite size_zip size_zip -y__size.
               move: y__size_srcs => /eqP ->.
               rewrite minnn.
               move => nth__le n_lt.
               move: (nth__le n n_lt) => /subtypeMachineP /(fun prf x => BCD__Trans _ x prf).
               rewrite nth_zip; last by rewrite y__size.
               move => res.           
               apply /subtypeMachineP.
               apply: res.
               rewrite (@nth_map _ (Omega, Omega) _ Omega (fun (srcs: IT * IT) => srcs.1 \dcap srcs.2));
                 last by (move: n_lt; rewrite size_map).
               apply: BCD__Trans; first by apply: dcap_cap.
               rewrite nth_zip; last first.
               { rewrite mergeMultiArrows_cons_arity => //.
                   by rewrite (eqP arity_equal_currentResult). }
               rewrite (@nth_map _ (Omega, Omega) _ Omega); last first.
               { move: n_lt.
                   by rewrite size_map size_zip size_zip mergeMultiArrows_cons_arity. }
               rewrite nth_zip; last by rewrite (eqP arity_equal_currentResult).
               apply: BCD__Trans; last by apply: cap_dcap.
               apply BCD__Glb.
               *** apply: BCD__Trans; first by apply: BCD__Lub1.
                   apply: BCD__Trans; first by apply: mergeMultiArrows_srcs_le.
                   apply: BCD__Trans;
                     last by apply: (mergeMultiArrows_srcs_ge _ _ (all_nested_tl _ _ _ arity_equal__ms)).
                   apply: bcd_subset_f.
                     by move: (@mem_behead _ [:: (srcs, tgt) & ms]) .
               *** by apply: BCD__Lub2.
        + move => partition__eq1 partition__eq2 s__suffix arity_equal__i instructions_covered__i not_omega_instructions__i prime__i notDone__i.
          rewrite /complete /=.
          rewrite filterMergeMultiArrows_cat all_cat andbT.
          move => /andP [] prf1 prf2.
          rewrite filterMergeMultiArrows_cat map_cat all_cat.
          rewrite filterMergeMultiArrows_cat all_cat.
          rewrite filterMergeMultiArrows_cat all_cat.
          rewrite prf2 andbT.
          rewrite prf1 andbT.
          apply: (introT andP).
          split.
          * apply: (introT allP).
            move => m /filterMergedArrows_in_cons.
            move => /orP [].
            ** move => /= /eqP -> /=.
               apply: (introT implyP).
               move => tgt__le.               
               move: notDone__i => /(notDone_incomplete _ _ (proj1 (andP (not_omega_instructions__i)))).
                 by rewrite tgt__le.
            ** move => /hasP [] ms [] inprf /andP [] inprf__merged m__eq.
               apply: (introT implyP).
               move: m__eq => /eqP ->.
               move => le__prf.
               apply: (introT hasP).
               exists (mergeMultiArrow currentResult srcs tgt).
               *** move: s__suffix => /suffixP [] s__prefix /eqP ->.
                     by rewrite mem_cat mem_head orbT.
               *** have arity_equal__currentms: (all (fun x => all (fun y => seq.size x.1 == seq.size y.1) [:: currentResult & ms])
                                                   [:: currentResult & ms]).
                   { move: inprf => /subseqs_map_cons.
                     rewrite -(@mem_map _ _ (cons currentResult)); last by move => ? ? [].
                     move => /subseqs_map_cons inprf.
                     apply: all_nested_subseq; first apply: (subseqs_subseq _ _ inprf).
                     rewrite -(map_cons (fun x => x.1) (srcs, tgt, covered) splits).
                       by exact arity_equal__i. }
                   have arity_equal__ms: (all (fun x => all (fun y => seq.size x.1 == seq.size y.1) ms) ms).
                   { apply: all_nested_tl; by exact arity_equal__currentms. }
                   have arity_equal_currentResult: (seq.size currentResult.1 ==
                                                    seq.size (mergeMultiArrows [:: currentResult & ms]).1).
                   { by move: (mergeMultiArrows_arity _ arity_equal__currentms) => /andP [] ->. }
                   have arity_equal__mergeCurrentResult:
                     (seq.size currentResult.1 == seq.size (mergeMultiArrow currentResult srcs tgt).1).
                   { rewrite /= size_map size_zip.
                     move: arity_equal__i => /andP [] /andP [] _ /andP [] /eqP ->.
                       by rewrite minnn. }
                   have arity_equal_mergemerge:
                     (seq.size (mergeMultiArrow currentResult srcs tgt).1 ==
                      seq.size (map (fun srcs => srcs.1 \dcap srcs.2)
                                    (zip (mergeMultiArrows [:: currentResult & ms]).1
                                         currentResult.1))).
                   { rewrite -(eqP arity_equal__mergeCurrentResult).
                       by rewrite size_map size_zip -(eqP arity_equal_currentResult) minnn. }
                   rewrite arity_equal_mergemerge andTb.
                   apply: (introT andP).
                   split.
                   **** apply /(all_nthP (Omega, Omega)).
                        move => n n_lt.
                        rewrite nth_zip; last by move: arity_equal_mergemerge => /eqP ->.
                        rewrite explicit_pair_snd explicit_pair_fst.
                        apply /subtypeMachineP.
                        move: (mergeMultiArrow_srcs_le currentResult (mergeMultiArrows [:: currentResult & ms])).
                        move: (mergeMultiArrow_srcs_ge currentResult (srcs, tgt)).
                        move: prf1 prf2 => _ _.
                        move => /(all_nthP (Omega, (Omega, Omega))) /(fun prf => prf n) prf2.
                        move => /(all_nthP (Omega, (Omega, Omega))) /(fun prf => prf n) prf1.
                        have merge_zip_eq: (seq.size (mergeMultiArrow currentResult srcs tgt).1 =
                                            seq.size (zip currentResult.1 srcs)).
                        { rewrite size_zip.
                          move: arity_equal__i => /andP [] /andP [] _ /andP [] /eqP <- _ _ .
                            by rewrite minnn -(eqP arity_equal__mergeCurrentResult). }
                        have mixmerge_zip_eq: (seq.size
                                                 (mergeMultiArrow currentResult (mergeMultiArrows [:: currentResult & ms]).1
                                                                  (mergeMultiArrows [:: currentResult & ms]).2).1 =
                                               seq.size (zip currentResult.1 (mergeMultiArrows [:: currentResult & ms]).1)).
                        { rewrite mergeMultiArrow_srcs_map_zip size_zip -(eqP arity_equal_mergemerge).
                            by rewrite -(eqP arity_equal_currentResult) minnn (eqP arity_equal__mergeCurrentResult). }
                        have n_lt1: (n < seq.size
                                           (zip (mergeMultiArrow currentResult
                                                                 (mergeMultiArrows [:: currentResult & ms]).1
                                                                 (mergeMultiArrows [:: currentResult & ms]).2).1
                                                (zip currentResult.1 (mergeMultiArrows [:: currentResult & ms]).1))).
                        { rewrite size_zip mixmerge_zip_eq minnn size_zip.
                          move: n_lt.                          
                          rewrite size_zip -(eqP arity_equal_mergemerge) minnn.
                            by rewrite -(eqP arity_equal_currentResult) minnn -(eqP arity_equal__mergeCurrentResult). }
                        have n_lt2: (n < seq.size
                                           (zip (mergeMultiArrow currentResult (srcs, tgt).1 (srcs, tgt).2).1
                                                (zip currentResult.1 (srcs, tgt).1))).
                        { move: n_lt.
                            by rewrite size_zip -(eqP arity_equal_mergemerge) minnn size_zip -merge_zip_eq minnn. }
                        move: prf1 => /(fun prf1 => prf1 n_lt1) /subtypeMachineP.
                        rewrite nth_zip => //.
                        rewrite explicit_pair_snd explicit_pair_fst.
                        move => prf1.
                        move: prf2 => /(fun prf2 => prf2 n_lt2) /subtypeMachineP.
                        rewrite explicit_pair_snd  explicit_pair_fst.
                        rewrite nth_zip => //.
                        rewrite explicit_pair_snd explicit_pair_fst.
                        move => prf2.
                        apply: BCD__Trans; first by exact prf1.
                        apply: BCD__Trans; last by exact prf2.
                        rewrite nth_zip; last by rewrite (eqP arity_equal_currentResult).
                        rewrite explicit_pair_snd explicit_pair_fst.
                        rewrite nth_zip; last by move: arity_equal__i => /andP [] /andP [] _ /andP [] /eqP <- _ _ .
                        rewrite explicit_pair_snd explicit_pair_fst.
                        apply: BCD__Glb => //.
                        apply: BCD__Trans; first by apply: BCD__Lub2.
                        apply: BCD__Trans; first by apply: mergeMultiArrows_srcs_le.
                        apply: BCD__Trans; first by apply: (bcd_cat_bigcap_f _ _ _ [:: _]).
                        apply: BCD__Trans; first by apply: BCD__Lub2.
                        have: (ms = [:: (srcs, tgt) & behead ms]).
                        { move: inprf.
                          clear...
                          elim: (subseqs (map fst splits)) => // x xs IH.
                          rewrite map_cons in_cons.
                          move => /orP [].
                          - by move => /eqP ->.
                          - by apply: IH. }
                        move => ->.
                          by apply: BCD__Trans; first by apply: (bcd_cat_bigcap_f _ _ _ [:: _]).
                   **** apply /subtypeMachineP.
                        apply: BCD__Trans; first by apply: (mergeMultiArrow_tgt_le _ (srcs, tgt)).
                        apply: BCD__Glb => //.
                        apply: BCD__Trans; first by apply: BCD__Lub2.
                        apply: BCD__Trans; last by apply: (bcd_subset_f id _ _ (partitionCover_complete covered toCover)).
                        rewrite (eqP partition__eq2) cats0.
                        apply: BCD__Trans; last by apply: (bcd_subset_f _ _ _ (allP (partitionCover_subset covered toCover))).
                          by move: instructions_covered__i => /andP [] /andP [] /subtypeMachineP. 
          * apply: (introT allP).
            move => m /filterMergedArrows_in_cons.
            move => /orP [].
            ** move => /= /eqP -> /=.
               apply: (introT implyP).
               move => tgt__le.
               apply: (introT hasP).
               exists (mergeMultiArrow currentResult srcs tgt).
               *** move: s__suffix => /suffixP [] s__prefix /eqP ->.
                     by rewrite mem_cat mem_head orbT.
               *** rewrite mergeMultiArrow_srcs_map_zip eq_refl andTb.
                   apply: (introT andP).
                   split.
                   **** apply /(all_nthP (Omega, Omega)).
                        move => n.
                        rewrite size_zip minnn.
                        move => n_lt.
                        rewrite nth_zip => //.
                          by apply /subtypeMachineP.
                   **** apply /subtypeMachineP.
                        apply: BCD__Glb.
                        ***** by apply: BCD__Trans; first by apply: (mergeMultiArrow_tgt_le _ (srcs, tgt)).
                        ***** apply: BCD__Trans; first by apply: (mergeMultiArrow_tgt_le _ (srcs, tgt)).
                              apply: BCD__Trans; first by apply: BCD__Lub2.
                                by apply /subtypeMachineP.
            ** move => /hasP [] ms [] inprf /andP [] inprf__merged m__eq.
               move: prf1 prf2 => _ /allP /(fun prf => prf (mergeMultiArrows ms)) /(fun prf => prf inprf__merged).
               move => prf.
               apply: (introT implyP).
               move: m__eq => /eqP ->.
               move => le__prf.
               apply: (introT hasP).
               exists (mergeMultiArrow currentResult srcs tgt).
               *** move: s__suffix => /suffixP [] s__prefix /eqP ->.
                     by rewrite mem_cat mem_head orbT.
               *** have arity_equal__ms: (all (fun x => all (fun y => seq.size x.1 == seq.size y.1) [:: (srcs, tgt) & ms])
                                            [:: (srcs, tgt) & ms]).
                   { apply: (introT allP).
                     move => x x__in.
                     have: (x \in map fst [:: (srcs, tgt, covered) & splits]).
                     { move: x__in.
                       rewrite in_cons.
                       move => /orP [].
                       - move => /eqP -> /=.
                           by rewrite in_cons eq_refl.
                       - move: (subseqs_subseq _ _ inprf).
                         move => /mem_subseq subprf /subprf.
                         rewrite map_cons in_cons => ->.
                           by rewrite orbT. }
                     move: x__in => _.
                     move: x.
                     apply: allP.
                     apply: sub_all; last by exact (proj2 (andP arity_equal__i)).
                     move => x /= /andP [] _ /andP [] -> /allP subprf /=.
                     apply: (introT allP).
                     move => z z__in.
                     apply: subprf.
                     apply: mem_subseq; last by exact z__in.
                       by apply: subseqs_subseq. } 
                   have arity_equal__currentms: (all (fun x => all (fun y => seq.size x.1 == seq.size y.1)
                                                              [:: currentResult, (srcs, tgt) & ms])
                                                   [:: currentResult, (srcs, tgt) & ms]).
                   { apply: (fun subprf => all_nested_subseq _ _ _ subprf arity_equal__i).
                     rewrite /= eq_refl eq_refl.
                       by apply: subseqs_subseq. }
                   have arity_equal__mergeCurrentms: (all (fun m1 => all (fun m2 => seq.size m1.1 == seq.size m2.1)
                                                                    (mergeMultiArrow currentResult srcs tgt :: ms))
                                                        (mergeMultiArrow currentResult srcs tgt :: ms)).
                   { apply: (introT allP).
                     move => x.
                     move: arity_equal__i => /andP [] /andP [] _ /andP [] /eqP arity_equal__currentResult _ _.
                     rewrite in_cons => /orP [].
                     - move => /eqP ->.                   
                       rewrite (all_cat _ [:: _] _) all_seq1 eq_refl /= size_map size_zip arity_equal__currentResult minnn.
                       apply: sub_all; last by (move: arity_equal__ms => /andP [] _ res; exact res).
                         by move => x2 /andP [] /eqP ->.
                     - move: arity_equal__ms => /andP [] _ /allP arity_equal__ms /arity_equal__ms.
                       do 2 rewrite (all_cat _ [:: _] _) all_seq1.
                       move => /andP [] /eqP -> ->.
                         by rewrite /= size_map size_zip arity_equal__currentResult minnn eq_refl. }
                   have arity_equal_currentResult: (seq.size currentResult.1 ==
                                                    seq.size (mergeMultiArrows [:: (srcs, tgt) & ms]).1).
                   { rewrite -(mergeMultiArrows_cons_arity currentResult) => //.
                       by move: (mergeMultiArrows_arity _ arity_equal__currentms) => /andP [] ->. }
                   have y__size_srcs: (seq.size (mergeMultiArrow currentResult srcs tgt).1 ==
                                       seq.size (map (fun srcs => srcs.1 \dcap srcs.2)
                                                     (zip (mergeMultiArrows [:: (srcs, tgt) & ms]).1
                                                          currentResult.1))).
                   { rewrite eq_sym size_map size_zip size_map size_zip.
                     rewrite (eqP arity_equal_currentResult) minnn.
                     move: (mergeMultiArrows_arity _ arity_equal__ms).
                     move: (fun prf => mergeMultiArrows_cons_arity (srcs, tgt) ms prf arity_equal__ms).                     
                     clear ...
                     case: ms.
                     - by rewrite minnn.
                     - move => m ms /(fun prf => prf isT) -> /andP [] /= /eqP ->.
                         by rewrite minnn. }
                   rewrite y__size_srcs andTb.
                   apply: (introT andP).
                   split.
                   **** apply /(all_nthP (Omega, Omega)).
                        move => n n_lt.
                        rewrite nth_zip; last by rewrite -(eqP y__size_srcs).
                        rewrite [X in checkSubtypes X _]/fst [X in checkSubtypes _ X]/snd.
                        rewrite -(mergeMultiArrow_srcs_map_zip _ _ (mergeMultiArrows [:: (srcs, tgt) & ms]).2).
                        apply /subtypeMachineP.
                        move: (mergeMultiArrow_srcs_le currentResult (mergeMultiArrows [:: (srcs, tgt) & ms])).
                        move => /(all_nthP (Omega, (Omega, Omega))) /(fun prf => prf n) prf1.
                        have: (n < seq.size
                                     (zip (mergeMultiArrow currentResult (mergeMultiArrows [:: (srcs, tgt) & ms]).1
                                                           (mergeMultiArrows [:: (srcs, tgt) & ms]).2).1
                                          (zip currentResult.1 (mergeMultiArrows [:: (srcs, tgt) & ms]).1))).
                        { move: n_lt.
                          rewrite size_zip size_zip size_map size_zip (eqP arity_equal_currentResult) minnn.
                          rewrite size_zip (eqP arity_equal_currentResult) minnn.
                            by rewrite (eqP y__size_srcs) size_map size_zip (eqP arity_equal_currentResult) minnn minnn. }
                        move => n_lt2.
                        move: prf1 => /(fun prf1 => prf1 n_lt2).
                        rewrite nth_zip; last first.
                        { by rewrite size_map size_zip size_zip minnC. }
                        move => /subtypeMachineP prf1.
                        apply: BCD__Trans; first by exact prf1.
                        move: (mergeMultiArrow_srcs_ge currentResult (srcs, tgt)).
                        move => /(all_nthP (Omega, (Omega, Omega))) /(fun prf => prf n) prf2.
                        have: (n < seq.size (zip (mergeMultiArrow currentResult (srcs, tgt).1 (srcs, tgt).2).1
                                                 (zip currentResult.1 (srcs, tgt).1))).
                        { move: n_lt.
                          rewrite size_zip size_map size_zip size_map size_zip size_zip size_zip.
                          rewrite [(srcs, tgt).1]/fst [(srcs, tgt).2]/snd.
                          rewrite (eqP arity_equal_currentResult) minnn (eqP y__size_srcs).
                          rewrite size_map size_zip (eqP arity_equal_currentResult) minnn.
                            by rewrite [minn (seq.size srcs) _]minnC. }
                        move => n_lt3.
                        move: prf2 => /(fun prf2 => prf2 n_lt3).
                        rewrite nth_zip; last first.
                        { by rewrite size_map size_zip size_zip minnC. }
                        move => /subtypeMachineP prf2.
                        apply: BCD__Trans; last by exact prf2.
                        apply: BCD__Glb.
                        ***** repeat rewrite explicit_pair_snd.
                              rewrite nth_zip; last by rewrite (eqP arity_equal_currentResult).
                              rewrite explicit_pair_fst explicit_pair_snd.
                              rewrite nth_zip => //.
                              rewrite (eqP arity_equal_currentResult).
                                by move: (mergeMultiArrows_arity _ arity_equal__ms) => /andP [] /eqP.
                        ***** repeat rewrite explicit_pair_snd.
                              rewrite nth_zip; last by rewrite (eqP arity_equal_currentResult).
                              rewrite explicit_pair_fst explicit_pair_snd.
                              rewrite nth_zip; last first.
                              { rewrite (eqP arity_equal_currentResult).
                                  by move: (mergeMultiArrows_arity _ arity_equal__ms) => /andP [] /eqP. }
                              rewrite explicit_pair_snd.
                              apply: BCD__Trans; first by apply: BCD__Lub2.
                              apply: BCD__Trans; first by apply: mergeMultiArrows_srcs_le => //.
                                by apply: BCD__Trans; first by apply: (bcd_cat_bigcap_f _ _ _ [:: _]).
                   **** apply /subtypeMachineP.
                        apply: BCD__Trans; first by apply: (mergeMultiArrow_tgt_le _ (srcs, tgt)).
                        apply: BCD__Glb => //.
                        apply: BCD__Trans; last by apply: (bcd_subset_f id _ _ (partitionCover_complete covered toCover)).
                        rewrite (eqP partition__eq2) cats0.
                        apply: BCD__Trans; first by apply: BCD__Lub2.
                        apply: (fun cov1 cov2 leprf => proj1 (partitionCover_prime (srcs, tgt) ms covered toCover
                                                                                prime__i cov1 cov2 leprf)) => //.
                        ***** move => A inprf__A.
                              move: (allP instructions_covered__i) => /(fun prf => prf ((srcs, tgt), covered) (mem_head _ _)).
                              move => /andP [] _ /allP /(fun prf => prf A inprf__A) /implyP res /subtypeMachineP.
                                by exact res.
                        ***** move: (allP instructions_covered__i) => /(fun prf => prf ((srcs, tgt), covered) (mem_head _ _)).
                                by move => /andP [] /subtypeMachineP.
                        ***** apply: BCD__Trans; first by apply: mergeMultiArrows_tgt_ge.
                                by move: le__prf => /subtypeMachineP.
        + move => partition__eq1 partition__eq2 merge__eq.
          move => s__suffix arity_equal__i instructions_covered__i not_omega_instructions__i prime__i notDone__i.
          rewrite /complete /=.
          rewrite filterMergeMultiArrows_cat all_cat andbT.
          rewrite filterMergeMultiArrows_cat all_cat.
          move => /andP [] prf1 prf2.
          rewrite filterMergeMultiArrows_cat map_cat all_cat.
          rewrite filterMergeMultiArrows_cat all_cat.
          match goal with
          |[|- (_ ((?x && _) && _))] => have prf: x
          end.
          * apply: (introT allP).
            move => m inprf__m.
            move: prf1.
            rewrite filterMergeMultiArrows_map_cons (map_comp (cons currentResult) (cons (srcs, tgt))).
            move => /allP /(fun prf => prf m inprf__m) /implyP prf1.
            apply /implyP.
            move => /subtypeMachineP le_prf.
            have: (checkSubtypes m.2 (\bigcap_(A_i <- (partitionCover covered toCover).2) A_i)).
            { apply /subtypeMachineP.
                by apply: BCD__Trans; last by apply: (bcd_subset_f _ _ _ (mem_subseq (partitionCover_subseq2 covered toCover))). }
            move => /prf1 /hasP [] y inprf__y /andP [] y__size /andP [] srcs__le tgt__le.
            have arity_equal__mergeCurrentResult:
              (seq.size currentResult.1 == seq.size (mergeMultiArrow currentResult srcs tgt).1).
            { rewrite /= size_map size_zip.
              move: arity_equal__i => /andP [] /andP [] _ /andP [] /eqP -> _ _.
                by rewrite minnn. }
            have y__size_srcs: (seq.size y.1 == seq.size [seq src.1 \dcap src.2 | src <- zip m.1 currentResult.1]).
            { rewrite size_map size_zip (eqP arity_equal__mergeCurrentResult).
              move: y__size.
                by rewrite size_map size_zip. }
            apply /hasP.
            exists y => //.
            rewrite y__size_srcs andTb.
            apply /andP.
            split.
            ** apply /(all_nthP (Omega, Omega)).
               move => n n_lt.
               apply /subtypeMachineP.
               rewrite nth_zip; last by rewrite (eqP y__size_srcs).
               rewrite explicit_pair_fst explicit_pair_snd.
               move: srcs__le => /(all_nthP (Omega, Omega)) /(fun prf => prf n).
               have n_lt1:
                 (n < seq.size (zip (map (fun srcs => srcs.1 \dcap srcs.2)
                                         (zip m.1 (map (fun srcs => srcs.1 \dcap srcs.2) (zip srcs currentResult.1)))) y.1)).
               { rewrite size_zip (eqP y__size) minnn.
                 rewrite -(eqP y__size) (eqP y__size_srcs).
                 move: n_lt.
                   by rewrite size_zip (eqP y__size_srcs) minnn. }
               move => /(fun prf => prf n_lt1) /subtypeMachineP.
               rewrite nth_zip; last by rewrite (eqP y__size).
               rewrite explicit_pair_snd explicit_pair_fst.
               move: prf1 => _ prf1.
               apply: BCD__Trans; last by exact prf1.
                 by rewrite (eqP merge__eq).
            ** apply /subtypeMachineP.
               apply: BCD__Trans; first by (apply /subtypeMachineP; exact tgt__le).
               apply: BCD__Glb;
                 first by apply: BCD__Trans; first by apply: BCD__Lub1.
               apply: BCD__Trans; last by apply: (bcd_subset_f _ _ _ (partitionCover_complete covered toCover)).
               apply: BCD__Trans; last by apply: bcd_bigcap_cat.
               apply: BCD__Glb => //.
               do 2 (apply: BCD__Trans; first by apply: BCD__Lub1).
               apply: BCD__Trans;
                 last by apply: (bcd_subset_f _ _ _ (allP (partitionCover_subset covered toCover))).
                 by move: instructions_covered__i => /andP [] /andP [] /subtypeMachineP.
          * rewrite prf andTb.
            apply /andP.
            split; last (apply /andP; split).
            **  apply: (introT allP).
                move => m /filterMergedArrows_in_cons.
                move => /orP [].
                *** move => /eqP ->.
                    move: not_omega_instructions__i => /andP [] notEmpty _.
                    rewrite /= in notEmpty.
                    move: notDone__i => /notDone_incomplete disprf.
                    apply /implyP.
                      by move: (disprf notEmpty) => /negP.
                *** move => /hasP [] ms [] inprf /andP [] inprf__merged m__eq.
                    have inprf__srcsm: ((mergeMultiArrows [:: currentResult, (srcs, tgt) & ms])
                                        \in filterMergeMultiArrows (map (cons currentResult)
                                                                        (map (cons (srcs, tgt))
                                                                             (subseqs (map fst splits))))).
                    { rewrite filterMergeMultiArrows_map_cons2 /mergeMultiArrow (eqP merge__eq).
                      move: inprf.
                      elim: (subseqs (map fst splits)) => // ms1 mss IH.
                      rewrite in_cons map_cons (filterMergeMultiArrows_cat [:: _]) mem_cat.
                      move => /orP [].
                      - move => /eqP ->.
                          by rewrite mem_seq1 /= /mergeMultiArrow (eqP merge__eq) eq_refl.
                      - move => /IH res.
                          by rewrite res orbT. }
                    apply /implyP.
                    move => le_prf.
                    have: (checkSubtypes (mergeMultiArrows [:: currentResult, (srcs, tgt) & ms]).2
                                         (\bigcap_(A_i <- toCover) A_i)).
                    { apply /subtypeMachineP.
                      move: le_prf => /subtypeMachineP le_prf.
                      apply: BCD__Trans; last by exact le_prf.
                      rewrite (eqP m__eq).
                      apply: BCD__Trans; first by apply: mergeMultiArrows_tgt_le.
                      apply: BCD__Trans; last by apply: mergeMultiArrows_tgt_ge.
                      apply: bcd_subset_f.
                      move => x.
                      do 3 rewrite in_cons.
                      move => /orP [].
                      - by move => /eqP ->; rewrite eq_refl.
                      - by move => ->; rewrite orbT orbT. }
                    move: prf => /allP /(fun prf => prf (mergeMultiArrows [:: currentResult, (srcs, tgt) & ms])).
                    move => /(fun prf => prf inprf__srcsm) /implyP prf.
                    move => /prf /hasP [] y inprf__res /andP [] y__size_srcs /andP [] srcs_le_res tgt_le_res.
                    apply /hasP.
                    exists y => //.
                    have arity_equal__mergeCurrentResult:
                      (seq.size currentResult.1 == seq.size (mergeMultiArrow currentResult srcs tgt).1).
                    { rewrite /= size_map size_zip.
                      move: arity_equal__i => /andP [] /andP [] _ /andP [] /eqP -> _ _.
                        by rewrite minnn. }
                    have arity_equal_currentsrcsms:
                      (all (fun m1 => all (fun m2 => seq.size m1.1 == seq.size m2.1) [:: currentResult, (srcs, tgt) & ms])
                           [:: currentResult, (srcs, tgt) & ms]).
                    { apply: all_nested_subseq; last by exact arity_equal__i.
                      rewrite /mergeComponentsOf map_cons.
                      apply: (@cat_subseq _ [:: currentResult; (srcs, tgt)] ms
                                          [:: currentResult; (srcs, tgt, covered).1] (map fst splits)) => //.
                        by apply: subseqs_subseq. }
                    have fold_merge: (mergeMultiArrows [:: currentResult, (srcs, tgt) & ms] =
                                      mergeMultiArrows [:: (mergeMultiArrow currentResult srcs tgt) & ms]) => //.
                    have arity_equal_mergesrcscurrent:
                      (seq.size (currentResult.1) == seq.size (mergeMultiArrows [:: mergeMultiArrow currentResult srcs tgt & ms]).1).
                    { move: (mergeMultiArrows_arity _ arity_equal_currentsrcsms).
                      rewrite fold_merge.
                        by move => /andP []. }
                    have arity_equal_currentms:
                      (all (fun m1 => all (fun m2 => seq.size m1.1 == seq.size m2.1) [:: currentResult & ms])
                           [:: currentResult & ms]).
                    { apply: all_nested_subseq; last by exact arity_equal_currentsrcsms.
                      apply: (@cat_subseq _ [:: _] ms [:: _; _] ms) => //.
                        by apply (prefix_subseq [:: _]). }
                    have y__size: (seq.size y.1 == seq.size [seq src.1 \dcap src.2 | src <- zip m.1 currentResult.1]).
                    { rewrite (eqP m__eq).
                      rewrite size_map size_zip.
                      move: (mergeMultiArrows_arity _ arity_equal_currentms).
                      move => /andP [] /eqP <- _. 
                      move: y__size_srcs.
                        by rewrite size_map size_zip -(eqP arity_equal_mergesrcscurrent). }
                    rewrite y__size andTb.
                    rewrite tgt_le_res andbT.
                    apply /(all_nthP (Omega, Omega)).
                    move => n n_lt.
                    apply /subtypeMachineP.
                    rewrite nth_zip; last by rewrite (eqP y__size).
                    rewrite explicit_pair_fst explicit_pair_snd.
                    move: srcs_le_res => /(all_nthP (Omega, Omega)) /(fun prf => prf n).
                    have n_lt1: (n < seq.size (zip (map (fun srcs => srcs.1 \dcap srcs.2)
                                                        (zip (mergeMultiArrows [:: currentResult, (srcs, tgt) & ms]).1
                                                             currentResult.1)) y.1)).
                    { rewrite size_zip -(eqP y__size_srcs) (eqP y__size).
                      move: n_lt.
                        by rewrite size_zip (eqP y__size). }
                    move => /(fun prf => prf n_lt1) /subtypeMachineP.
                    rewrite nth_zip; last by rewrite (eqP y__size_srcs).
                    rewrite explicit_pair_snd explicit_pair_fst.
                    move: prf1 => _ prf1.
                    apply: BCD__Trans; last by exact prf1.
                    rewrite (eqP m__eq).
                    rewrite (nth_map (Omega, Omega)); last first.
                    { rewrite size_zip.
                      move: (mergeMultiArrows_arity _ arity_equal_currentms) => /andP [] /eqP <- _.
                      move: n_lt.
                      rewrite size_zip (eqP y__size) size_map size_zip.
                      rewrite (eqP m__eq).
                      move: (mergeMultiArrows_arity _ arity_equal_currentms) => /andP [] /eqP <- _.
                        by rewrite minnn. }
                    apply: BCD__Trans; first by apply: dcap_cap.
                    rewrite nth_zip; last first.
                    { by move: (mergeMultiArrows_arity _ arity_equal_currentms) => /andP [] /eqP <- _. }
                    rewrite (nth_map (Omega, Omega)); last first.
                    { rewrite size_zip fold_merge (eqP arity_equal_mergesrcscurrent).
                      move: n_lt1.
                        by rewrite size_zip (eqP y__size_srcs) size_map size_zip (eqP arity_equal_mergesrcscurrent) minnn. }
                    rewrite nth_zip; last by rewrite (eqP arity_equal_mergesrcscurrent).
                    rewrite explicit_pair_snd explicit_pair_fst.
                    apply: BCD__Trans; last by apply: cap_dcap.
                    rewrite explicit_pair_snd explicit_pair_fst.
                    apply: BCD__Glb => //.
                    apply: BCD__Trans; first by apply: BCD__Lub1.
                    apply: BCD__Trans; first by apply: (mergeMultiArrows_srcs_le _ _ arity_equal_currentms).
                    have: (all
                             (fun m1 => all (fun m2 => seq.size m1.1 == seq.size m2.1) [:: mergeMultiArrow currentResult srcs tgt & ms])
                             [:: mergeMultiArrow currentResult srcs tgt & ms]).
                    { apply /allP.
                      move => x.
                      rewrite in_cons.
                      move => /orP [].
                      - move => /eqP ->.
                        apply /allP.
                        move => z.
                        rewrite in_cons.
                        move => /orP [].
                        + by move => /eqP ->.
                        + move => inprf__z.
                          rewrite -(eqP arity_equal__mergeCurrentResult).
                          move: arity_equal_currentms => /allP /(fun prf => prf z).
                          rewrite in_cons inprf__z orbT.
                            by move => /(fun prf => prf isT) /andP [] /eqP ->.
                      - move => inprf__x.
                        apply /allP.
                        move => z.
                        rewrite in_cons.
                        move => /orP [].
                        + move => /eqP ->.
                          rewrite -(eqP arity_equal__mergeCurrentResult).
                          move: arity_equal_currentms => /allP /(fun prf => prf x).
                          rewrite in_cons inprf__x orbT.
                            by move => /(fun prf => prf isT) /andP [] /eqP ->.
                        + move => inprf__z.
                          move: arity_equal_currentms => /allP res.
                          move: (res x) (res z).
                          rewrite in_cons inprf__x orbT in_cons inprf__z orbT.
                            by do 2 move => /(fun prf => prf isT) /andP [] /eqP -> _. }
                    move: prf2 => _ /(mergeMultiArrows_srcs_ge _ n) prf2.
                    rewrite fold_merge.
                    apply: BCD__Trans; last by exact prf2.
                    move: merge__eq.
                    rewrite /mergeMultiArrow.
                    move => /eqP ->.
                    apply: BCD__Trans; first by apply: (bcd_cat_bigcap_f _ _ _ [::_] _).
                    apply: BCD__Trans; last by apply: (bcd_bigcap_cat_f _ _ _ [::_] _).
                      by apply: BCD__Glb.
            ** apply: (introT allP).
               move => m /filterMergedArrows_in_cons.
               move => /orP [].
               *** move => /eqP ->.
                   apply /implyP.
                   move => /complete_partitionCover.
                   move: instructions_covered__i => /andP [] /andP [] _ all_covered _.
                   move => /(fun prf => prf _ all_covered) disprf.
                   move: partition__eq2.
                     by rewrite disprf.
               *** move => /hasP [] ms [] inprf /andP [] inprf__merged m__eq.
                   have inprf__srcsm: ((mergeMultiArrows [:: currentResult, (srcs, tgt) & ms])
                                       \in filterMergeMultiArrows (map (cons currentResult)
                                                                       (map (cons (srcs, tgt))
                                                                            (subseqs (map fst splits))))).
                    { rewrite filterMergeMultiArrows_map_cons2 /mergeMultiArrow (eqP merge__eq).
                      move: inprf.
                      elim: (subseqs (map fst splits)) => // ms1 mss IH.
                      rewrite in_cons map_cons (filterMergeMultiArrows_cat [:: _]) mem_cat.
                      move => /orP [].
                      - move => /eqP ->.
                          by rewrite mem_seq1 /= /mergeMultiArrow (eqP merge__eq) eq_refl.
                      - move => /IH res.
                          by rewrite res orbT. }
                    apply /implyP.
                    move => le_prf.
                    have: (checkSubtypes (mergeMultiArrows [:: currentResult, (srcs, tgt) & ms]).2
                                         (\bigcap_(A_i <- toCover) A_i)).
                    { apply /subtypeMachineP.
                      move: le_prf => /subtypeMachineP le_prf.
                      apply: BCD__Trans; last by exact le_prf.
                      rewrite (eqP m__eq).
                      apply: BCD__Trans; first by apply: mergeMultiArrows_tgt_le.
                      apply: BCD__Trans; last by apply: mergeMultiArrows_tgt_ge.
                      apply: bcd_subset_f.
                      move => x.
                      do 3 rewrite in_cons.
                      move => /orP [].
                      - by move => /eqP ->; rewrite eq_refl orbT.
                      - by move => ->; rewrite orbT orbT. }
                    move: prf => /allP /(fun prf => prf (mergeMultiArrows [:: currentResult, (srcs, tgt) & ms])).
                    move => /(fun prf => prf inprf__srcsm) /implyP prf.
                    move => /prf /hasP [] y inprf__res /andP [] y__size_srcs /andP [] srcs_le_res tgt_le_res.
                    apply /hasP.
                    exists y => //.
                    have arity_equal__mergeCurrentResult:
                      (seq.size currentResult.1 == seq.size (mergeMultiArrow currentResult srcs tgt).1).
                    { rewrite /= size_map size_zip.
                      move: arity_equal__i => /andP [] /andP [] _ /andP [] /eqP -> _ _.
                        by rewrite minnn. }
                    have arity_equal_currentsrcsms:
                      (all (fun m1 => all (fun m2 => seq.size m1.1 == seq.size m2.1) [:: currentResult, (srcs, tgt) & ms])
                           [:: currentResult, (srcs, tgt) & ms]).
                    { apply: all_nested_subseq; last by exact arity_equal__i.
                      rewrite /mergeComponentsOf map_cons.
                      apply: (@cat_subseq _ [:: currentResult; (srcs, tgt)] ms
                                          [:: currentResult; (srcs, tgt, covered).1] (map fst splits)) => //.
                        by apply: subseqs_subseq. }
                    have fold_merge: (mergeMultiArrows [:: currentResult, (srcs, tgt) & ms] =
                                      mergeMultiArrows [:: (mergeMultiArrow currentResult srcs tgt) & ms]) => //.
                    have arity_equal_mergesrcscurrent:
                      (seq.size (currentResult.1) == seq.size (mergeMultiArrows [:: mergeMultiArrow currentResult srcs tgt & ms]).1).
                    { move: (mergeMultiArrows_arity _ arity_equal_currentsrcsms).
                      rewrite fold_merge.
                        by move => /andP []. }
                    have arity_equal_currentms:
                      (all (fun m1 => all (fun m2 => seq.size m1.1 == seq.size m2.1) [:: currentResult & ms])
                           [:: currentResult & ms]).
                    { apply: all_nested_subseq; last by exact arity_equal_currentsrcsms.
                      apply: (@cat_subseq _ [:: _] ms [:: _; _] ms) => //.
                        by apply (prefix_subseq [:: _]). }
                    have arity_equal_srcsms: (seq.size currentResult.1 == seq.size (mergeMultiArrows [:: (srcs, tgt) & ms]).1).
                    { move: (all_nested_tl _ _ _ arity_equal_currentsrcsms) => /mergeMultiArrows_arity.
                      move => /andP [] /eqP <- _.
                        by move: arity_equal__i => /andP [] /andP [] _ /andP [] ->. }
                    have y__size: (seq.size y.1 == seq.size [seq src.1 \dcap src.2 | src <- zip m.1 currentResult.1]).
                    { rewrite (eqP m__eq).
                      rewrite size_map size_zip.
                      move: (mergeMultiArrows_arity _ arity_equal_currentms).
                      move => /andP [] /eqP <- _.
                      rewrite -(eqP arity_equal_srcsms) minnn (eqP y__size_srcs) (eqP arity_equal_mergesrcscurrent).
                        by rewrite fold_merge size_map size_zip -(eqP arity_equal_mergesrcscurrent) minnn. }
                    rewrite y__size andTb.
                    rewrite tgt_le_res andbT.
                    apply /(all_nthP (Omega, Omega)).
                    move => n n_lt.
                    apply /subtypeMachineP.
                    rewrite nth_zip; last by rewrite (eqP y__size).
                    rewrite explicit_pair_fst explicit_pair_snd.
                    move: srcs_le_res => /(all_nthP (Omega, Omega)) /(fun prf => prf n).
                    have n_lt1: (n < seq.size (zip (map (fun srcs => srcs.1 \dcap srcs.2)
                                                        (zip (mergeMultiArrows [:: currentResult, (srcs, tgt) & ms]).1
                                                             currentResult.1)) y.1)).
                    { rewrite size_zip -(eqP y__size_srcs) (eqP y__size).
                      move: n_lt.
                        by rewrite size_zip (eqP y__size). }
                    move => /(fun prf => prf n_lt1) /subtypeMachineP.
                    rewrite nth_zip; last by rewrite (eqP y__size_srcs).
                    rewrite explicit_pair_snd explicit_pair_fst.
                    move: prf1 => _ prf1.
                    apply: BCD__Trans; last by exact prf1.
                    rewrite (eqP m__eq).
                    rewrite (nth_map (Omega, Omega)); last first.
                    { rewrite size_zip.
                      move: (mergeMultiArrows_arity _ arity_equal_currentms) => /andP [] /eqP <- _.
                      move: n_lt.
                      rewrite size_zip (eqP y__size) size_map size_zip.
                      rewrite (eqP m__eq).
                      move: (mergeMultiArrows_arity _ arity_equal_currentms) => /andP [] /eqP <- _.
                        by rewrite minnn. }
                    apply: BCD__Trans; first by apply: dcap_cap.
                    rewrite nth_zip; last by rewrite (eqP arity_equal_srcsms).
                    rewrite (nth_map (Omega, Omega)); last first.
                    { rewrite size_zip fold_merge (eqP arity_equal_mergesrcscurrent).
                      move: n_lt1.
                        by rewrite size_zip (eqP y__size_srcs) size_map size_zip (eqP arity_equal_mergesrcscurrent) minnn. }
                    rewrite nth_zip; last by rewrite (eqP arity_equal_mergesrcscurrent).
                    rewrite explicit_pair_snd explicit_pair_fst.
                    apply: BCD__Trans; last by apply: cap_dcap.
                    rewrite explicit_pair_snd explicit_pair_fst.
                    apply: BCD__Glb => //.
                    have: (all
                             (fun m1 => all (fun m2 => seq.size m1.1 == seq.size m2.1) [:: mergeMultiArrow currentResult srcs tgt & ms])
                             [:: mergeMultiArrow currentResult srcs tgt & ms]).
                    { apply /allP.
                      move => x.
                      rewrite in_cons.
                      move => /orP [].
                      - move => /eqP ->.
                        apply /allP.
                        move => z.
                        rewrite in_cons.
                        move => /orP [].
                        + by move => /eqP ->.
                        + move => inprf__z.
                          rewrite -(eqP arity_equal__mergeCurrentResult).
                          move: arity_equal_currentms => /allP /(fun prf => prf z).
                          rewrite in_cons inprf__z orbT.
                            by move => /(fun prf => prf isT) /andP [] /eqP ->.
                      - move => inprf__x.
                        apply /allP.
                        move => z.
                        rewrite in_cons.
                        move => /orP [].
                        + move => /eqP ->.
                          rewrite -(eqP arity_equal__mergeCurrentResult).
                          move: arity_equal_currentms => /allP /(fun prf => prf x).
                          rewrite in_cons inprf__x orbT.
                            by move => /(fun prf => prf isT) /andP [] /eqP ->.
                        + move => inprf__z.
                          move: arity_equal_currentms => /allP res.
                          move: (res x) (res z).
                          rewrite in_cons inprf__x orbT in_cons inprf__z orbT.
                            by do 2 move => /(fun prf => prf isT) /andP [] /eqP -> _. }
                    move: prf2 => _ /(mergeMultiArrows_srcs_ge _ n) prf2.
                    rewrite fold_merge.
                    apply: BCD__Trans; last by exact prf2.
                    move: merge__eq.
                    rewrite /mergeMultiArrow.
                    move => /eqP ->.
                    apply: BCD__Trans; last by apply: (bcd_bigcap_cat_f _ _ _ [::_] _).
                    apply: BCD__Glb => //.
                    apply: BCD__Trans; first by apply: BCD__Lub1.
                    apply: BCD__Trans; first by apply: (mergeMultiArrows_srcs_le _ _ (all_nested_tl _ _ _ arity_equal_currentsrcsms)).
                    apply: bcd_subset_f.
                    move => ?.
                    rewrite in_cons.
                    move => ->.
                      by rewrite orbT.
            ** apply /allP.
               move => m inprf__m.
               apply /implyP.
               move => le_prf.
               move: prf2 => /allP /(fun prf => prf m inprf__m) /implyP prf2.
               have: (checkSubtypes m.2 (\bigcap_(A_i <- (partitionCover covered toCover).2) A_i)).
               { apply /subtypeMachineP.
                 move: le_prf => /subtypeMachineP le_prf.
                 apply: BCD__Trans; first by apply: le_prf.
                 apply: bcd_subset_f.
                 apply: mem_subseq.
                   by apply: partitionCover_subseq2. }
               move => /prf2.
               rewrite (eqP merge__eq).
               move => /hasP [] y inprf__res /andP [] y__size_srcs /andP [] srcs_le_res tgt_le_res.
               apply /hasP.
               exists y => //.
               rewrite y__size_srcs srcs_le_res andTb andTb.
               apply /subtypeMachineP.
               move: tgt_le_res => /subtypeMachineP tgt_le_res.
               apply: BCD__Trans; first by exact tgt_le_res.
               apply: BCD__Glb.
               *** by apply: BCD__Trans; first by apply: BCD__Lub1.
               *** apply: BCD__Trans; last by apply: (partition_cover_both covered).
                   apply: BCD__Trans; last by apply: bcd_bigcap_cat.
                   apply: BCD__Glb => //.
                   apply: BCD__Trans; first by apply: BCD__Lub1.
                   apply: BCD__Trans; first by apply: BCD__Lub1.
                   move: (covered_head_tgt _ _ _ _ _ instructions_covered__i) => [] _ tgt_le2.
                   apply: BCD__Trans; first by exact tgt_le2.
                   apply: bcd_subset_f.
                   move => x.
                     by move: (allP (partitionCover_subset covered toCover)) => /(fun prf => prf x).
        + move => partition__eq1 partition__eq2 merge__ineq.
          move => s__suffix arity_equal__i instructions_covered__i not_omega_instructions__i prime__i notDone__i.
          rewrite /complete /=.
          rewrite filterMergeMultiArrows_cat all_cat andbT.
          rewrite filterMergeMultiArrows_cat all_cat.
          move => /andP [] /andP [] prf1 prf2 /andP [] prf3 prf4.
          rewrite filterMergeMultiArrows_cat map_cat all_cat.
          rewrite filterMergeMultiArrows_cat all_cat.
          rewrite filterMergeMultiArrows_cat all_cat.
          rewrite prf3 prf4 andbT andbT.
          apply: (introT andP).
          split.
          * apply: (introT allP).
            move => m inprf__m.
            move: prf1.
            rewrite -(filterMergeMultiArrows_map_cons2 currentResult (srcs, tgt)).
            move => /allP /(fun prf => prf m inprf__m) /implyP prf1.
            move: inprf__m => /filterMergedArrows_in_cons.
            move => /orP [].
            ** move => /eqP ->.
               apply: (introT implyP).
               move: not_omega_instructions__i => /andP [] notEmpty _.
               rewrite /= in notEmpty.
               move: notDone__i => /notDone_incomplete disprf.
                 by move: (disprf notEmpty) => /negP.
            ** move => /hasP [] ms [] inprf /andP [] inprf__merged m__eq.
               move: prf1.
               rewrite (eqP m__eq).
               move => prf1.
               apply: (introT implyP).
               move => le__prf.
               have: (checkSubtypes (mergeMultiArrows (currentResult :: ms)).2
                                    (\bigcap_(A_i <- (partitionCover covered toCover).2) A_i)).
               { apply /subtypeMachineP.
                 apply: BCD__Trans; last by apply (bcd_subset_f _ _ _ (mem_subseq (partitionCover_subseq2 covered toCover))).
                   by apply /subtypeMachineP. }
               move => /prf1 /hasP [] y inprf__res /andP [] y__size /andP [] srcs_le_res tgt_le_res.
               apply /hasP.
               exists y => //.
               have arity_equal__mergeCurrentResult:
                 (seq.size currentResult.1 == seq.size (mergeMultiArrow currentResult srcs tgt).1).
               { rewrite /= size_map size_zip.
                 move: arity_equal__i => /andP [] /andP [] _ /andP [] /eqP -> _ _.
                   by rewrite minnn. }
               have y__size_srcs:
                 (seq.size y.1 ==
                  seq.size (map (fun srcs => srcs.1 \dcap srcs.2)
                                (zip (mergeMultiArrows [:: currentResult & ms]).1
                                     currentResult.1))).
               { rewrite (eqP y__size).
                   by rewrite size_map size_map size_zip size_zip (eqP arity_equal__mergeCurrentResult). }
               rewrite y__size_srcs andTb.
               apply: (introT andP).
               split.
               *** apply /(all_nthP (Omega, Omega)).
                   move => n n_lt.
                   rewrite nth_zip; last by rewrite (eqP y__size_srcs).
                   rewrite explicit_pair_snd explicit_pair_fst.
                   move: srcs_le_res => /(all_nthP (Omega, Omega)) /(fun prf => prf n).
                   rewrite size_zip -(eqP y__size) {1}(eqP y__size_srcs) -size_zip.
                   move => /(fun prf => prf n_lt) /subtypeMachineP.
                   rewrite nth_zip; last by rewrite (eqP y__size).
                   rewrite explicit_pair_snd explicit_pair_fst.
                   move => prf.
                   apply /subtypeMachineP.
                   apply: BCD__Trans; last by exact prf.
                   move: prf1 prf2 prf3 prf4 => _ _ _ _.
                   rewrite -(mergeMultiArrow_srcs_map_zip _ _ (mergeMultiArrows [:: currentResult & ms]).2).
                   rewrite -(mergeMultiArrow_srcs_map_zip _ _ tgt).
                   rewrite -(mergeMultiArrow_srcs_map_zip _ _ (mergeMultiArrows [:: currentResult & ms]).2).
                   move: (mergeMultiArrow_srcs_le currentResult (mergeMultiArrows [:: currentResult & ms])).
                   move => /(all_nthP (Omega, (Omega, Omega))) /(fun prf => prf n).
                   rewrite explicit_pair_fst.
                   have n_lt1: (n <
                                (seq.size (zip (map (fun srcs => srcs.1 \dcap srcs.2)
                                                    (zip (mergeMultiArrows (currentResult :: ms)).1
                                                         currentResult.1))
                                               (zip currentResult.1 (mergeMultiArrows [:: currentResult & ms]).1)))).
                   { move: n_lt.
                     repeat rewrite size_zip.
                       by rewrite size_map size_zip (eqP y__size_srcs) size_map size_zip minnC. }
                   move => /(fun prf => prf n_lt1) /subtypeMachineP.
                   have merge_zip_eq:
                     (seq.size (map (fun srcs => srcs.1 \dcap srcs.2)
                                                    (zip (mergeMultiArrows (currentResult :: ms)).1
                                                         currentResult.1)) =
                      seq.size (zip currentResult.1 (mergeMultiArrows [:: currentResult & ms]).1)).
                   { by rewrite size_map size_zip size_zip minnC. }
                   rewrite nth_zip; last by exact merge_zip_eq.
                   rewrite explicit_pair_fst explicit_pair_snd.
                   move => prf1.
                   apply: BCD__Trans; first by exact prf1.
                   have arity_equal_currentms:
                       all (fun m1 => all (fun m2 => seq.size m1.1 == seq.size m2.1) [:: currentResult & ms])
                           [:: currentResult & ms].
                   { move: inprf => /subseqs_map_cons.
                     rewrite -(@mem_map _ _ (cons currentResult)); last by move => ? ? [].
                     move => /subseqs_map_cons inprf.
                     apply: all_nested_subseq; first apply: (subseqs_subseq _ _ inprf).
                     rewrite -(map_cons (fun x => x.1) (srcs, tgt, covered) splits).
                       by exact arity_equal__i. }
                   have ms_not_nil: ~~(nilp ms).
                   { move: inprf.
                     clear...
                     elim: (subseqs (map fst splits)) => //= ms1 mss IH.
                     rewrite in_cons.
                     move => /orP [].
                     - by move => /eqP ->.
                     - by apply: IH. }
                   have arity_equal_currentResult:
                     (seq.size currentResult.1 == seq.size (mergeMultiArrows [:: currentResult & ms]).1).
                   { by move: arity_equal_currentms => /mergeMultiArrows_arity /andP []. }
                   rewrite nth_zip; last by rewrite (eqP arity_equal_currentResult).
                   rewrite explicit_pair_fst explicit_pair_snd.
                   apply: BCD__Trans; first by apply: BCD__Lub2.
                   move: (mergeMultiArrow_srcs_ge (mergeMultiArrow currentResult srcs tgt)
                                                  (mergeMultiArrows [:: currentResult & ms])).
                   move => /(all_nthP (Omega, (Omega, Omega))) /(fun prf => prf n).
                   rewrite explicit_pair_fst.
                   have n_lt2: (n <
                                (seq.size (zip (map (fun srcs => srcs.1 \dcap srcs.2)
                                                    (zip (mergeMultiArrows (currentResult :: ms)).1
                                                         (mergeMultiArrow currentResult srcs tgt).1))
                                               (zip (mergeMultiArrow currentResult srcs tgt).1
                                                    (mergeMultiArrows [:: currentResult & ms]).1)))).
                   { move: n_lt.
                     repeat rewrite size_zip.
                     rewrite size_map size_zip (eqP y__size) minnC (eqP arity_equal__mergeCurrentResult).
                       by rewrite [minn (seq.size (mergeMultiArrows _).1) _]minnC . }
                   move => /(fun prf => prf n_lt2) /subtypeMachineP.
                   rewrite nth_zip; last first.
                   { by rewrite size_map size_zip size_zip minnC. }
                   rewrite explicit_pair_snd explicit_pair_fst.
                   move => prf2.
                   apply: BCD__Trans; last by exact prf2.
                   rewrite nth_zip; last first.
                   { by rewrite -(eqP arity_equal__mergeCurrentResult) -(eqP arity_equal_currentResult). }
                   rewrite explicit_pair_snd explicit_pair_fst.
                   apply: BCD__Glb => //.
                   move: arity_equal_currentms.
                   have: (ms = [:: (srcs, tgt) & behead ms]).
                   { move: inprf.
                     clear...
                     elim: (subseqs (map fst splits)) => // x xs IH.
                     rewrite map_cons in_cons.
                     move => /orP [].
                     - by move => /eqP ->.
                     - by apply: IH. }                   
                   move => ->.
                   move => arity_equal_currentms.
                   apply: BCD__Trans; first by apply: mergeMultiArrows_srcs_le.
                   apply: BCD__Trans;
                     last apply: (mergeMultiArrows_srcs_ge [:: currentResult; (srcs, tgt)]);
                     last first.
                   { apply: all_nested_subseq; last by exact arity_equal_currentms.
                     rewrite -[[:: _; _]]cats0.
                     apply: (@cat_subseq _ _ _ [:: _; _] _) => //.
                       by apply sub0seq. }
                     by apply: BCD__Trans; first by apply: (bcd_cat_bigcap_f _ _ _ [:: _; _]).
               *** apply /subtypeMachineP.
                   apply: BCD__Trans; first by (apply /subtypeMachineP; exact tgt_le_res).
                   apply: BCD__Glb;
                     first by apply: BCD__Trans; first by apply: BCD__Lub1.
                   apply: BCD__Trans; last by apply: (bcd_subset_f _ _ _ (partitionCover_complete covered toCover)).
                   apply: BCD__Trans; last by apply: bcd_bigcap_cat.
                   apply: BCD__Glb => //.
                   do 2 (apply: BCD__Trans; first by apply: BCD__Lub1).
                   apply: BCD__Trans;
                     last by apply: (bcd_subset_f _ _ _ (allP (partitionCover_subset covered toCover))).
                     by move: instructions_covered__i => /andP [] /andP [] /subtypeMachineP.
          * apply: (introT allP).
            move => m inprf__m.
            move: inprf__m => /filterMergedArrows_in_cons.
            move => /orP [].
            ** move => /eqP ->.
               apply: (introT implyP).
               move: instructions_covered__i => /andP [] /andP [] _.
               move => /(complete_partitionCover _ _ _) disprf _ /disprf.
                 by move: partition__eq2 => /eqP partition__eq2 /partition__eq2.
            ** move => /hasP [] ms [] inprf /andP [] inprf__merged m__eq.
               apply: (introT implyP).
               move => le__prf.
               have: (mergeMultiArrows [:: (mergeMultiArrow currentResult srcs tgt) & ms] \in
                         (filterMergeMultiArrows
                            (map (cons (mergeMultiArrow currentResult srcs tgt)) (subseqs (map fst splits))))).
               { apply: mem_subseq; 
                   first apply: (filterMergeMultiArrows_subseq
                                   [:: [:: mergeMultiArrow currentResult srcs tgt & ms ]]).
                 - move: inprf.
                   clear...
                   elim: (subseqs (map fst splits)) => // ms1 mss IH.
                   rewrite in_cons.
                   move => /orP [].
                   + move => /eqP ->.
                     rewrite map_cons.
                       by apply: prefix_subseq.
                   + move => /IH res.
                     rewrite map_cons.
                     rewrite -[[:: _ & _]]cat0s -[[:: _ & map _ _]]cat1s.                     
                       by apply: cat_subseq.
                 - by rewrite in_cons eq_refl. }
               move: prf1 => /allP prf1 /prf1 /implyP.
               have mergeTgt_le:
                 (checkSubtypes (mergeMultiArrows [:: mergeMultiArrow currentResult srcs tgt & ms]).2
                                (\bigcap_(A_i <- (partitionCover covered toCover).2) A_i)).
               { apply /subtypeMachineP.
                 apply: BCD__Trans; first by apply: mergeMultiArrows_tgt_le.
                 apply: BCD__Trans; first by apply: (bcd_cat_bigcap_f _ _ snd [:: _] _).
                 apply: BCD__Trans;
                   last by apply: (bcd_subset_f id _ _
                                                (mem_subseq (partitionCover_subseq2 covered toCover))).
                 apply: BCD__Trans; last by (apply /subtypeMachineP; apply: le__prf).
                 rewrite (eqP m__eq).
                 apply: BCD__Trans; last by apply: mergeMultiArrows_tgt_ge.
                 apply: BCD__Trans; last by apply: (bcd_bigcap_cat_f _ _ _ [:: _]).
                 apply: BCD__Glb => //.
                 apply: BCD__Trans; first by apply: BCD__Lub1.
                   by apply: BCD__Trans; first by apply: (mergeMultiArrow_tgt_le _ (srcs, tgt)). }
               move => /(fun prf => prf mergeTgt_le) /hasP [] y inprf__y /andP [] y__size /andP [] srcs__le tgt__le.
               apply /hasP.
               exists y => //.
               have arity_equal__mergeCurrentResult:
                 (seq.size currentResult.1 == seq.size (mergeMultiArrow currentResult srcs tgt).1).
               { rewrite /= size_map size_zip.
                 move: arity_equal__i => /andP [] /andP [] _ /andP [] /eqP -> _ _.
                   by rewrite minnn. }
               have arity_equal_currentsrcsms:
                       all (fun m1 => all (fun m2 => seq.size m1.1 == seq.size m2.1) [:: currentResult, (srcs, tgt) & ms])
                           [:: currentResult, (srcs, tgt) & ms].
               { move: inprf.
                 rewrite -(@mem_map _ _ (cons (srcs, tgt))); last by move => ? ? [].
                 move => /subseqs_map_cons.
                 rewrite -(@mem_map _ _ (cons currentResult)); last by move => ? ? [].
                 move => /subseqs_map_cons inprf.
                 apply: all_nested_subseq; first apply: (subseqs_subseq _ _ inprf).
                   by exact arity_equal__i. }
               have arity_equal_mergeRest:
                 (seq.size currentResult.1 == seq.size (mergeMultiArrows ((srcs, tgt) :: ms)).1).
               { rewrite (eqP arity_equal__mergeCurrentResult).
                 move: (mergeMultiArrows_arity _ (all_nested_tl _ _ _ arity_equal_currentsrcsms)).
                 move => /andP [] /eqP <- _.
                 rewrite /= size_map size_zip.
                 move: arity_equal__i => /andP [] /andP [] _ /andP [] /eqP -> _ _.
                   by rewrite minnn. }
               have fold_merge:
                 (mergeMultiArrows [:: currentResult, (srcs, tgt) & ms] =
                  mergeMultiArrows [:: mergeMultiArrow currentResult srcs tgt & ms]) => //.
               have arity_equal_merge:
                   (seq.size currentResult.1 ==
                    seq.size (mergeMultiArrows [:: mergeMultiArrow currentResult srcs tgt & ms]).1).
               { rewrite -fold_merge.
                 move: arity_equal_currentsrcsms.
                   by move => /mergeMultiArrows_arity /andP []. }
               rewrite (eqP m__eq).
               have y__size_srcs:
                 (seq.size y.1 ==
                  seq.size (map (fun srcs => srcs.1 \dcap srcs.2)
                                (zip (mergeMultiArrows [:: (srcs, tgt) & ms]).1
                                     currentResult.1))).
               { rewrite (eqP y__size).
                 rewrite -(mergeMultiArrow_srcs_map_zip currentResult
                                                        (mergeMultiArrows [:: (srcs, tgt) & ms]).1
                                                        (mergeMultiArrows [:: (srcs, tgt) & ms]).2).
                 rewrite -(mergeMultiArrow_srcs_map_zip currentResult srcs tgt).
                 rewrite size_map size_map size_zip size_zip.
                 repeat rewrite -(eqP arity_equal__mergeCurrentResult).
                 rewrite -(eqP arity_equal_mergeRest).
                   by rewrite (eqP arity_equal_merge). }
               rewrite y__size_srcs andTb.
               apply: (introT andP).
               split.
               *** apply /(all_nthP (Omega, Omega)).
                   move => n n_lt.
                   rewrite nth_zip; last by rewrite (eqP y__size_srcs).
                   rewrite explicit_pair_snd explicit_pair_fst.
                   move: srcs__le => /(all_nthP (Omega, Omega)) /(fun prf => prf n).
                   rewrite size_zip -(eqP y__size) {1}(eqP y__size_srcs) -size_zip.
                   move => /(fun prf => prf n_lt) /subtypeMachineP.
                   rewrite nth_zip; last by rewrite (eqP y__size).
                   rewrite explicit_pair_snd explicit_pair_fst.
                   move => prf.
                   apply /subtypeMachineP.
                   apply: BCD__Trans; last by exact prf.
                   move: prf1 prf2 prf3 prf4 => _ _ _ _.
                   rewrite -(mergeMultiArrow_srcs_map_zip _ _ (mergeMultiArrows [:: (srcs, tgt) & ms]).2).
                   rewrite -(mergeMultiArrow_srcs_map_zip _ _ tgt).
                   rewrite -(mergeMultiArrow_srcs_map_zip _ _ (mergeMultiArrows
                                                                 [:: (mergeMultiArrow currentResult srcs tgt)
                                                                  & ms]).2).
                   move: (mergeMultiArrow_srcs_le currentResult (mergeMultiArrows [:: (srcs, tgt) & ms])).
                   move => /(all_nthP (Omega, (Omega, Omega))) /(fun prf => prf n).
                   rewrite explicit_pair_fst.
                   have n_lt1: (n <
                                (seq.size (zip (map (fun srcs => srcs.1 \dcap srcs.2)
                                                    (zip (mergeMultiArrows ((srcs, tgt) :: ms)).1
                                                         currentResult.1))
                                               (zip currentResult.1 (mergeMultiArrows [:: (srcs, tgt) & ms]).1)))).
                   { move: n_lt.
                     repeat rewrite size_zip.
                     rewrite -(eqP arity_equal_mergeRest) minnn.
                     rewrite size_map (eqP y__size).
                     rewrite size_map size_zip size_zip size_map size_zip.
                     rewrite -(eqP arity_equal_merge).
                     move: arity_equal__i => /andP [] /andP [] _ /andP [] /eqP <- _ _.
                       by rewrite minnn minnn. }
                   move => /(fun prf => prf n_lt1) /subtypeMachineP.
                   rewrite nth_zip; last first.
                   { by rewrite size_map size_zip size_zip minnC. }
                   rewrite explicit_pair_fst explicit_pair_snd.
                   move => prf1.
                   apply: BCD__Trans; first by exact prf1.
                   rewrite nth_zip; last by rewrite (eqP arity_equal_mergeRest).
                   rewrite explicit_pair_fst explicit_pair_snd.
                   move: (mergeMultiArrow_srcs_ge (mergeMultiArrow currentResult srcs tgt)
                                                  (mergeMultiArrows [:: mergeMultiArrow currentResult srcs tgt
                                                                     & ms])).
                   move => /(all_nthP (Omega, (Omega, Omega))) /(fun prf => prf n).
                   rewrite explicit_pair_fst.
                   have n_lt2: (n <
                                (seq.size (zip (map (fun srcs => srcs.1 \dcap srcs.2)
                                                    (zip (mergeMultiArrows
                                                            [:: mergeMultiArrow currentResult srcs tgt
                                                             & ms]).1
                                                         (mergeMultiArrow currentResult srcs tgt).1))
                                               (zip (mergeMultiArrow currentResult srcs tgt).1
                                                    (mergeMultiArrows
                                                       [:: mergeMultiArrow currentResult srcs tgt
                                                        & ms]).1)))).
                   { move: n_lt.
                     repeat rewrite size_zip.
                     rewrite size_map size_zip (eqP y__size) minnC (eqP arity_equal__mergeCurrentResult).
                     rewrite -(eqP arity_equal_mergeRest) -(eqP arity_equal_merge).
                       by rewrite [minn (seq.size currentResult.1) _]minnC. }
                   move => /(fun prf => prf n_lt2) /subtypeMachineP.
                   rewrite nth_zip; last first.
                   { by rewrite size_map size_zip size_zip minnC. }
                   rewrite explicit_pair_snd explicit_pair_fst.
                   move => prf2.
                   apply: BCD__Trans; last by exact prf2.
                   rewrite nth_zip; last first.
                   { by rewrite -(eqP arity_equal__mergeCurrentResult) -(eqP arity_equal_merge). }
                   rewrite explicit_pair_snd explicit_pair_fst.
                   apply: BCD__Glb.
                   **** move: (mergeMultiArrow_srcs_ge currentResult (srcs, tgt)).
                        move => /(all_nthP (Omega, (Omega, Omega))) /(fun prf => prf n).
                        have n_lt3:
                          (n < seq.size (zip (mergeMultiArrow currentResult (srcs, tgt).1 (srcs, tgt).2).1
                                             (zip currentResult.1 (srcs, tgt).1))).
                        { move: n_lt.
                          rewrite size_zip size_map size_zip.
                          rewrite -(eqP arity_equal_mergeRest) (eqP y__size).
                          rewrite size_map size_zip -(eqP arity_equal_merge) minnn /=.
                          repeat rewrite size_map.
                          repeat rewrite size_zip.
                          rewrite size_map size_zip.
                          move: arity_equal__i => /andP [] /andP [] _ /andP [] /eqP -> _ _.
                            by repeat rewrite minnn. }
                        move => /(fun prf => prf n_lt3) /subtypeMachineP.
                        rewrite explicit_pair_snd explicit_pair_fst.
                        rewrite nth_zip; last first.
                        { by rewrite /= size_map size_zip size_zip minnC. }
                        rewrite explicit_pair_snd explicit_pair_fst.
                        rewrite nth_zip; last first.
                        { by move: arity_equal__i => /andP [] /andP [] _ /andP [] /eqP -> _ _. }
                        rewrite explicit_pair_snd explicit_pair_fst.
                        move => prf3.
                        apply: BCD__Trans; last by exact prf3.
                        apply: BCD__Glb => //.
                        apply: BCD__Trans; first by apply: BCD__Lub2.
                        apply: BCD__Trans;
                          first by apply (mergeMultiArrows_srcs_le _ _ (all_nested_tl _ _ _
                                                                                      arity_equal_currentsrcsms)).
                          by apply: BCD__Trans; first by apply: (bcd_cat_bigcap_f _ _ _ [:: _] _).
                   **** rewrite /cat -fold_merge.
                        apply: BCD__Trans; last by apply: (mergeMultiArrows_srcs_ge _ _ arity_equal_currentsrcsms).
                        apply: BCD__Trans; last by apply: (bcd_bigcap_cat_f _ _ _ [:: _] _).
                        apply: BCD__Glb => //.
                        apply: BCD__Trans; first by apply: BCD__Lub2.
                        apply: mergeMultiArrows_srcs_le.
                        apply: all_nested_tl.
                          by exact arity_equal_currentsrcsms.
               *** apply /subtypeMachineP.
                   apply: BCD__Trans; first by (apply /subtypeMachineP; exact tgt__le).
                   apply: BCD__Glb;
                     first by apply: BCD__Trans; first by apply: BCD__Lub1.
                   apply: BCD__Trans; last by apply: (bcd_subset_f _ _ _ (partitionCover_complete covered toCover)).
                   apply: BCD__Trans; last by apply: bcd_bigcap_cat.
                   apply: BCD__Glb => //.
                   do 2 (apply: BCD__Trans; first by apply: BCD__Lub1).
                   apply: BCD__Trans;
                     last by apply: (bcd_subset_f _ _ _ (allP (partitionCover_subset covered toCover))).
                     by move: instructions_covered__i => /andP [] /andP [] /subtypeMachineP.
      - move => toCover prf.
        by apply: prf.
      - move => [] [] srcs tgt covered splits toCover prf.
        apply: prf => //.
        + move => impossible _ arity_equal__i instructions_covered__i not_omega_instructions__i prime__i _ _.
          rewrite /complete /=.
          apply /allP.
          move => m inprf__m.
          move: (impossible_notSubtype [:: (srcs, tgt, covered) & splits]
                                       toCover m instructions_covered__i prime__i
                                       impossible inprf__m).
          move => disprf.
            by rewrite implybE disprf.
        + by rewrite andbT.
      - move => toCover currentResult prf.
        apply: prf => //.
        + move => impossible _ arity_equal__i instructions_covered__i not_omega_instructions__i prime__i notDone__i _.
          rewrite /complete /= andbT.
          apply /implyP.     
          move: notDone__i => /(notDone_incomplete _ _ (proj1 (andP (not_omega_instructions__i)))) /=.
            by move => /negbTE ->.
        + by rewrite andbT.
      - move => [] [] srcs tgt covered splits toCover currentResult prf.
        apply: prf => //.
        + move => impossible _ arity_equal__i instructions_covered__i not_omega_instructions__i prime__i notDone__i _.
          rewrite /complete /=.
          rewrite filterMergeMultiArrows_cat.
          rewrite all_cat.
          apply /andP; split.
          * apply /allP.
            move => m /filterMergedArrows_in_cons /orP [].
            ** move /eqP ->.
               move: notDone__i.
               rewrite all_predC.
               move: impossible.
               clear...
               case: toCover => //.
               move => p toCover.
               move => _ disprf.
               apply /implyP.
               move => /subtypeMachineP.
               move => /(fun prf => BCD__Trans _ prf (bcd_cat_bigcap _ [:: _] toCover)).
               move => /(fun prf => BCD__Trans _ prf BCD__Lub1) /subtypeMachineP devil.
               move: disprf => /negP /=.
               rewrite devil /=.
                 by move => /negP.
            ** move => /hasP [] ms inprf__ms /andP [] inprf__mergedms /eqP ->.
               move: impossible.
               rewrite /stillPossible -has_predC.
               move => /hasP [] p inprf__p.
               rewrite [predC _ _]/=.
               move => p_not_covered.
               have impossible_p: ~~(stillPossible [:: (srcs, tgt, covered) & splits] [:: p]).
               { by rewrite /= andbT. }
               have p_covered: (all (fun mps =>
                                       (checkSubtypes mps.1.2 (\bigcap_(A_i <- mps.2) A_i))
                                         && (all (fun A : IT => checkSubtypes mps.1.2 A ==> (A \in mps.2))
                                                 [:: p])) [:: (srcs, tgt, covered) & splits]).
               { apply /allP.
                 move => x inprf__x.
                 move: instructions_covered__i => /allP /(fun prf => prf x inprf__x) /andP [] -> /allP /(fun prf => prf p inprf__p).
                   by rewrite all_seq1. }
               have p_prime: all (fun A => isPrimeComponent A) [:: p].
               { by move: prime__i => /allP /(fun prf => prf p inprf__p) /= ->. }
               move: (impossible_notSubtype [:: (srcs, tgt, covered) & splits]
                                            [:: p] (mergeMultiArrows ms)
                                            p_covered p_prime impossible_p
                                            inprf__mergedms) => disprf.
               suff: ~~(checkSubtypes (mergeMultiArrows [:: currentResult & ms]).2
                                      (\bigcap_(A_i <- toCover) A_i)) by rewrite implybE => ->.
               apply /negP.
               move => /subtypeMachineP /(fun prf => BCD__Trans _ (mergeMultiArrows_tgt_ge _) prf).
               have p_subset: {subset [:: p] <= toCover}.
               { move => p'.
                 rewrite mem_seq1.
                   by move => /eqP ->. }
               move => /(fun prf => BCD__Trans _ prf (bcd_subset_f _ _ _ p_subset)).
               move: p_prime.
               rewrite all_seq1.
               move => /isPrimeComponentP p_prime.
               move => /(fun prf => BCD__Trans _ (bcd_bigcap_cat_f _ _ _ [:: _] _) prf).
               move => /(fun prf => primeComponentPrime _ _ _ _ prf p_prime).
               case.
               *** move => /subtypeMachineP devil.
                   move: notDone__i => /allP /(fun prf => prf p inprf__p).
                     by rewrite devil.
               *** move => /(fun prf => BCD__Trans _ (mergeMultiArrows_tgt_le _) prf) /subtypeMachineP devil.
                   move: disprf.
                     by rewrite devil.
          * apply /allP.
            move => m inprf__m.
            move: (impossible_notSubtype [:: (srcs, tgt, covered) & splits]
                                         toCover m instructions_covered__i prime__i
                                         impossible inprf__m).
            move => disprf.
              by rewrite implybE disprf.
        + by rewrite andbT.
    Qed.

    Lemma steps_complete:
      forall s1 p1 s2,
        (s1, p1) ~~>[*] (s2, [::]) ->
        all arity_equal p1 ->
        all not_omega_instruction p1 ->
        all instruction_covered p1 ->
        all toCover_prime p1 ->
        all currentResultNotDone p1 ->
        all (complete s2) p1.
    Proof.
      move => s1 p1 s2 /nStepSemantics_complete [] n.
      move: s1 p1 s2.
      elim: n.
      - move => s1 p1 s2 /nStepSemantics_inv /(fun res => res (fun _ sp1 sp2 => sp1.2 = sp2.2)).
          by move => /(fun res => res Logic.eq_refl) /= ->.
      - move => n IH s1 p1 s2 /nStepSemantics_inv /(fun prf => prf (fun n sp1 sp2 =>
                                                                  (all arity_equal sp1.2 ->
                                                                   all not_omega_instruction sp1.2 ->
                                                                   all instruction_covered sp1.2 ->
                                                                   all toCover_prime sp1.2 ->
                                                                   all currentResultNotDone sp1.2 ->
                                                                   all (complete sp2.1) sp1.2))%type) prf.
        apply: prf.
        move => [] s3 p3 step steps all_arity_equal all_not_omega_instruction.
        move => all_instruction_covered all_toCoverPrime all_notDone.
        move: (IH s3 p3 s2 steps
                  (arity_equal_step (s1, p1) (s3, p3) step all_arity_equal)
                  (not_omega_instruction_step _ _ _ _ step  all_not_omega_instruction)
                  (instructions_covered_step (s1, p1) (s3, p3) step all_instruction_covered)
                  (toCover_prime_step _ _ _ _ step all_toCoverPrime)
                  (currentResultNotDone_step (s1, p1) (s3, p3) step all_instruction_covered all_toCoverPrime all_notDone)
              ).
        apply: complete_reverse => //; first by exact step.
        apply: (steps_stateMonotonic (s3, p3) (s2, [::])).
        apply: nStepSemantics_sound.
          by exact steps.
    Qed.

     Definition tgt_sound s p :=
      all (fun x => has (fun i => checkSubtypes x.2 (\bigcap_(A_i <-
                                                            match i with
                                                            | ContinueCover _ toCover currentResult
                                                            | CheckContinueCover _ toCover currentResult =>
                                                              [:: currentResult.2 & toCover]
                                                            | Cover _ toCover
                                                            | CheckCover _ toCover => toCover
                                                            end) A_i)) p) s.

    Lemma step_tgt_sound:
      forall sp1 sp2,
        all instruction_covered sp1.2 ->
        sp1 ~~> sp2 ->
        tgt_sound (take (seq.size sp2.1 - seq.size sp1.1) sp2.1) sp1.2.
    Proof.
      move => [] s1 p1 [] s2 p2 covered_prf.
      move => /CoverMachine_inv  /(fun x => x (fun sp1 sp2 => tgt_sound (take (seq.size sp2.1 - seq.size sp1.1) sp2.1) sp1.2)).
      move: covered_prf.
      case: p1 => //.
      case.
      - case.
        + move => toCover p1 covered_prf prf.
          apply: prf.
            by rewrite /= subnn take0.
        + move => [] [] srcs tgt covered splits toCover p1 covered_prf prf.
          apply: prf.
          * by rewrite /= subnn take0.
          * rewrite /= -addn1 addKn take0.
            move => prf1 prf2.
            rewrite /tgt_sound all_seq1.
            apply /hasP.
            exists (Cover [:: (srcs, tgt, covered) & splits] toCover).
            ** by apply: mem_head.
            ** move: covered_prf => /andP [] /andP [] /andP [] /= /subtypeMachineP res _ _ _.
               rewrite -(partitionCover_drop2 _ _ prf2).
               apply /subtypeMachineP.
               apply: BCD__Trans; first by exact res.
               apply: bcd_subset_f.
                 by move: (partitionCover_subset covered toCover) => /allP.
          * by rewrite /= subnn take0.
      - case.
        + move => toCover currentResult p1 covered_prf prf.
          apply: prf.
            by rewrite /= subnn take0.
        + move => [] [] srcs tgt covered splits toCover currentResult p1 covered_prf prf.
          apply: prf.
          * by rewrite /= subnn take0.
          * rewrite /= -addn1 addKn take0.
            move => prf1 prf2.
            rewrite /tgt_sound all_seq1.
            apply /hasP.
            exists (ContinueCover [:: (srcs, tgt, covered) & splits] toCover currentResult).
            ** by apply: mem_head.
            ** move: covered_prf => /andP [] /andP [] /andP [] /= /subtypeMachineP res _ _ _.
               rewrite -(partitionCover_drop2 _ _ prf2).
               apply /subtypeMachineP.
               apply: (BCD__Trans (currentResult.2 \cap (\bigcap_(A_i <- covered) A_i))).
               *** apply: BCD__Glb => //.
                     by apply: BCD__Trans; last by exact res.
               *** move: (partitionCover_subset covered toCover) => /allP.
                   move: prf1.
                   case: ((partitionCover covered toCover).1) => //.
                   move => ? ? _ subset_prf.
                   apply: BCD__Glb => //.
                   apply: BCD__Trans; first by apply: BCD__Lub2.
                     by apply: bcd_subset_f.
          * by rewrite /= subnn take0.
          * by rewrite /= subnn take0.
      - move => splits toCover p1 covered_prf prf.
        apply: prf.
        + by rewrite /= subnn take0.
        + by rewrite /= subnn take0.
      - move => splits toCover currentResult p1 covered_prf prf.
        apply: prf.
        + by rewrite /= subnn take0.
        + by rewrite /= subnn take0.
    Qed.


    Lemma step_tgt_sound_reverse:
      forall i p s1 s2 s,
        all instruction_covered [:: i] ->
        tgt_sound s p ->
        (s1, [:: i]) ~~> (s2, p) ->
        tgt_sound s [:: i].
    Proof.
      move => i p s1 s2 s covered_prf tgt_sound_p prf.
      move: prf covered_prf tgt_sound_p.
      move => /CoverMachine_inv /(fun prf => prf (fun sp1 sp2 =>
                                                (all instruction_covered sp1.2 -> 
                                                  tgt_sound s sp2.2 ->
                                                  tgt_sound s sp1.2)%type)).
      case: i.
      - case.
        + move => toCover prf.
          apply: prf.
          rewrite /= /tgt_sound.
            by case: s.
        + move => [] [] srcs tgt covered splits toCover prf.
          apply: prf => //.
          move => prf1 prf2 covered_prf.
          move => /allP prf.
          apply /allP.
          move => m inprf.
          move: (prf m inprf) => /hasP [] m2.
          rewrite in_cons.
          move => /orP.
          case.
          * move => /eqP -> /subtypeMachineP le_prf.
            rewrite has_seq1.
            apply /subtypeMachineP.
            apply: BCD__Trans; first by exact le_prf.
            apply: BCD__Trans; last by apply: (bcd_subset_f _ _ _
                                                          (partitionCover_complete
                                                             covered toCover)).
            apply: BCD__Trans; last by apply: bcd_bigcap_cat.
            apply: BCD__Glb.
            ** apply: BCD__Trans; first by apply: (bcd_cat_bigcap _ [:: _] _).
               apply: BCD__Trans; first by apply: BCD__Lub1.
               apply: BCD__Trans; last first.
               *** apply: bcd_subset_f.
                   move: (partitionCover_subset covered toCover) => /allP res.
                     by exact res.
               *** by move: covered_prf => /andP [] /andP [] /andP [] /subtypeMachineP.
            ** by apply: BCD__Trans; first by apply: (bcd_cat_bigcap _ [:: _] _).
          * rewrite mem_seq1 has_seq1.
              by move => /eqP ->.
      - case.
        + move => toCover currentResult prf.
          apply: prf.
          rewrite /= /tgt_sound.
            by case: s.
        + move => [] [] srcs tgt splits covered toCover currentResult prf.
          apply: prf => //.
          * move => prf1 prf2 prf3 covered_prf.
            move => /allP prf.
            apply /allP.
            move => m inprf.
            move: (prf m inprf) => /hasP [] m2.
            rewrite mem_seq1 => /eqP -> /subtypeMachineP le_prf.
            rewrite has_seq1.
            apply /subtypeMachineP.
            apply: BCD__Trans; first by exact le_prf.
            apply: BCD__Trans; last by apply: (bcd_bigcap_cat _ [:: _] _).
            apply: BCD__Glb.
            ** apply: BCD__Trans; first by apply: (bcd_cat_bigcap _ [:: _] _).
               apply: BCD__Trans; first by apply: BCD__Lub1.
                 by apply: BCD__Lub2.
            ** apply: BCD__Trans; last by apply: (bcd_subset_f _ _ _
                                                             (partitionCover_complete splits toCover)).
               apply: BCD__Trans; last by apply: bcd_bigcap_cat.
               apply: BCD__Trans; first by apply: (bcd_cat_bigcap _ [:: _] _).
               apply: BCD__Glb => //.
               apply: BCD__Trans; first by apply: BCD__Lub1.
               apply: BCD__Trans; first by apply: BCD__Lub1.
               apply: BCD__Trans; last first.
               *** apply: bcd_subset_f.
                   move: (partitionCover_subset splits toCover) => /allP res.
                     by exact res.
               *** by move: covered_prf => /andP [] /andP [] /andP [] /subtypeMachineP.
          * move => prf1 prf2 _ covered_prf.
             move => /allP prf.
            apply /allP.
            move => m inprf.
            move: (prf m inprf) => /hasP [] m2.
            rewrite in_cons.
            move => /orP.
            case.
            ** move => /eqP -> /subtypeMachineP le_prf.
               rewrite has_seq1.
               apply /subtypeMachineP.
               apply: BCD__Trans; first by exact le_prf.
               apply: BCD__Trans; last by apply: (bcd_bigcap_cat _ [:: _] _).
               apply: BCD__Glb.
               *** apply: BCD__Trans; first by apply: (bcd_cat_bigcap _ [:: _] _).
                   apply: BCD__Trans; first by apply: BCD__Lub1.
                     by apply: BCD__Lub2.
               *** apply: BCD__Trans; last by apply: (bcd_subset_f _ _ _
                                                                 (partitionCover_complete splits toCover)).
                   apply: BCD__Trans; last by apply: bcd_bigcap_cat.
                   apply: BCD__Trans; first by apply: (bcd_cat_bigcap _ [:: _] _).
                   apply: BCD__Glb => //.
                   apply: BCD__Trans; first by apply: BCD__Lub1.
                   apply: BCD__Trans; first by apply: BCD__Lub1.
                   apply: BCD__Trans; last first.
                   **** apply: bcd_subset_f.
                        move: (partitionCover_subset splits toCover) => /allP res.
                          by exact res.
                   **** by move: covered_prf => /andP [] /andP [] /andP [] /subtypeMachineP.
            ** by rewrite has_seq1 mem_seq1 => /eqP ->.
      - move => splits toCover prf.
        apply: prf => //.
          by case: s.
      - move => splits toCover currentResult prf.
        apply: prf => //.
          by case: s.
    Qed.

    Lemma all_filter {A: eqType}: forall (xs: seq A) (f p: A -> bool),
        all p xs = (all p (filter f xs)) && (all p (filter (fun x => negb (f x)) xs)).
    Proof.
      move => xs f p.
      elim: xs => // x xs IH /=.
      case: (f x).
      - by rewrite IH /= andbA.
      - by rewrite IH /= [X in _ = X](andbA) -[X in _ = X && _](andbC) andbA.
    Qed.

    Lemma steps_tgt_sound:
       forall sp1 sp2,
        all instruction_covered sp1.2 ->
        sp1 ~~>[*] sp2 ->
        tgt_sound (take (seq.size sp2.1 - seq.size sp1.1) sp2.1) sp1.2.
    Proof.
      move => sp1 sp2 covered_prf prf.
      move: covered_prf.
      elim: sp1 sp2 /prf.
      - move => sp1.
          by rewrite subnn take0.
      - move => [] s1 p1 [] s2 p2 [] s3 p3 prf.
        rewrite -/((s2, p2) ~~>[*] (s3, p3)).
        move => prfs IH covered_prf.
        move: (step_tgt_sound (s1, p1) (s2, p2) covered_prf prf) => res_prefix.
        move: (IH (instructions_covered_step (s1, p1) (s2, p2) prf covered_prf)) => res_suffix.
        move: (step_programStack s1 p1 s2 p2 prf) => /suffixP [] p2_prefix /eqP p2__eq.
        move: (steps_stateMonotonic (s2, p2) (s3, p3) prfs) => /suffixP [] s3_prefix /eqP s3__eq.
        move: res_prefix res_suffix.
        rewrite p2__eq s3__eq size_cat /= addnK take_cat ltnn subnn take0 cats0 take_cat.
        rewrite -addnBA; last first.
        { move: (step_stateMonotonic s1 p1 s2 p2 prf).
          clear ...
          move: s1.
          elim: s2.
          - by case.
          - move => m2 s2 IH.
            case => // m1 s1 /= /orP.
            case.
            + by move => /eqP [] _ ->.
            + move => /IH /= res.
                by apply: ltn_trans; first by exact res. }
        rewrite -ltn_subRL subnn ltn0 addKn.
        rewrite /tgt_sound all_cat.
        move => ->.
        rewrite andbT.
        set (f xs :=
               fun (x: seq (@IT Constructor) * (@IT Constructor)) =>
                 has
                   (fun i : Instruction =>
                      checkSubtypes x.2
                                    (\bigcap_(A_i <- match i with
                                                    | Cover _ toCover | CheckCover _ toCover => toCover
                                                    | ContinueCover _ toCover currentResult
                                                    | CheckContinueCover _ toCover currentResult =>
                                                      [:: currentResult.2 & toCover]
                                                    end) A_i)) xs).
        do 2 rewrite (all_filter s3_prefix (f p2_prefix)).
        move => /andP [] _ res_rest.
        move: (filter_all (f p2_prefix) s3_prefix) => res_hd.
        apply /andP.
        split; last first.
        + apply /allP => m inprf.
          move: res_rest => /allP /(fun prf => prf m inprf).
          rewrite has_cat.
          move => /orP [].
          * move: inprf.
            rewrite mem_filter /f.
              by move => /andP [] /negbTE ->.
          * move => /hasP [] i inprf__i le_prf.
            apply /hasP.
            exists i; last by exact le_prf.
              by apply: mem_behead.
        + have: (exists i, p1 = [:: i & behead p1] /\ (s1, [:: i]) ~~> (s2, p2_prefix)).
          { move: prf p2__eq.
            move => /CoverMachine_inv /(fun prf => prf (fun sp1 sp2 =>
                                                      (sp2.2 = p2_prefix ++ behead sp1.2 ->
                                                       exists i, sp1.2 = [:: i & behead sp1.2] /\
                                                            (sp1.1, [:: i]) ~~> (sp2.1, p2_prefix)))%type).
            clear ...
            case: p1 => //.
            case.
            - case.
              + move => toCover p1 prf.
                apply: prf.
                move => eq_prf.
                have: (seq.size p2_prefix = 0).
                { move: eq_prf => /(f_equal seq.size).
                  rewrite /= size_cat -[X in X = _](add0n (seq.size p1)).
                    by move => /addIn. }
                move: eq_prf.
                move => _ /size0nil ->.
                eexists; split; first by reflexivity.
                  by constructor.
              + move => [] [] srcs tgt splits covered toCover p1 prf.
                apply: prf.
                * move => /= prf1 eq_prf.
                  have: (seq.size p2_prefix = 1).
                  { move: eq_prf => /(f_equal seq.size).
                    rewrite /= size_cat -addn1 addnC.
                      by move => /addIn. }
                  move: eq_prf.
                  case: p2_prefix => // i [] //=.
                  move => [] <- _.
                  eexists; split; first by reflexivity.
                    by constructor.
                * move => /= prf1 prf2 eq_prf.
                  have: (seq.size p2_prefix = 1).
                  { move: eq_prf => /(f_equal seq.size).
                    rewrite /= size_cat -addn1 addnC.
                      by move => /addIn. }
                  move: eq_prf.
                  case: p2_prefix => // i [] //=.
                  move => [] <- _.
                  eexists; split; first by reflexivity.
                    by constructor.
                *  move => /= prf1 prf2 eq_prf.
                   have: (seq.size p2_prefix = 2).
                   { move: eq_prf => /(f_equal seq.size).
                     rewrite /= size_cat -addn2 addnC.
                       by move => /addIn. }
                   move: eq_prf.
                   case: p2_prefix => // i1 [] i2 [] //=.
                   move => [] <- <- _.
                   eexists; split; first by reflexivity.
                     by constructor.
            - case.
              + move => toCover currentResult p1 prf.
                apply: prf.
                move => eq_prf.
                have: (seq.size p2_prefix = 0).
                { move: eq_prf => /(f_equal seq.size).
                  rewrite /= size_cat -[X in X = _](add0n (seq.size p1)).
                    by move => /addIn. }
                move: eq_prf.
                move => _ /size0nil ->.
                eexists; split; first by reflexivity.
                  by constructor.
              + move => [] [] srcs tgt splits covered toCover currentResult p1 prf.
                apply: prf.
                * move => /= prf1 eq_prf.
                  have: (seq.size p2_prefix = 1).
                  { move: eq_prf => /(f_equal seq.size).
                    rewrite /= size_cat -addn1 addnC.
                      by move => /addIn. }
                  move: eq_prf.
                  case: p2_prefix => // i [] //=.
                  move => [] <- _.
                  eexists; split; first by reflexivity.
                    by constructor.
                * move => /= prf1 prf2 eq_prf.
                  have: (seq.size p2_prefix = 1).
                  { move: eq_prf => /(f_equal seq.size).
                    rewrite /= size_cat -addn1 addnC.
                      by move => /addIn. }
                  move: eq_prf.
                  case: p2_prefix => // i [] //=.
                  move => [] <- _.
                  eexists; split; first by reflexivity.
                    by constructor.
                * move => /= prf1 prf2 prf3 eq_prf.
                  have: (seq.size p2_prefix = 1).
                  { move: eq_prf => /(f_equal seq.size).
                    rewrite /= size_cat -addn1 addnC.
                      by move => /addIn. }
                  move: eq_prf.
                  case: p2_prefix => // i [] //=.
                  move => [] <- _.
                  eexists; split; first by reflexivity.
                    by constructor.
                * move => /= prf1 prf2 prf3 eq_prf.
                  have: (seq.size p2_prefix = 2).
                  { move: eq_prf => /(f_equal seq.size).
                    rewrite /= size_cat -addn2 addnC.
                      by move => /addIn. }
                  move: eq_prf.
                  case: p2_prefix => // i1 [] i2 [] //=.
                  move => [] <- <- _.
                  eexists; split; first by reflexivity.
                    by constructor.
            - move => splits toCover p1 prf.
              apply: prf.
              + move => prf1 eq_prf.
                have: (seq.size p2_prefix = 0).
                { move: eq_prf => /(f_equal seq.size).
                  rewrite /= size_cat -[X in X = _](add0n (seq.size p1)).
                    by move => /addIn. }
                move: eq_prf.
                move => _ /size0nil ->.
                eexists; split; first by reflexivity.
                  by constructor.
              + move => /= prf1 eq_prf.
                have: (seq.size p2_prefix = 1).
                { move: eq_prf => /(f_equal seq.size).
                  rewrite /= size_cat -addn1 addnC.
                    by move => /addIn. }
                move: eq_prf.
                case: p2_prefix => // i [] //=.
                move => [] <- _.
                eexists; split; first by reflexivity.
                  by constructor.
            - move => splits toCover currentResult p1 prf.
              apply: prf.
              + move => prf1 eq_prf.
                have: (seq.size p2_prefix = 0).
                { move: eq_prf => /(f_equal seq.size).
                  rewrite /= size_cat -[X in X = _](add0n (seq.size p1)).
                    by move => /addIn. }
                move: eq_prf.
                move => _ /size0nil ->.
                eexists; split; first by reflexivity.
                  by constructor.
              + move => /= prf1 eq_prf.
                have: (seq.size p2_prefix = 1).
                { move: eq_prf => /(f_equal seq.size).
                  rewrite /= size_cat -addn1 addnC.
                    by move => /addIn. }
                move: eq_prf.
                case: p2_prefix => // i [] //=.
                move => [] <- _.
                eexists; split; first by reflexivity.
                  by constructor. }
          case => i [] p1__eq hd_prf.
          have i_covered: (all instruction_covered [:: i]).
          { move: covered_prf.
              by rewrite p1__eq /= => /andP [] ->. }
          move: (step_tgt_sound_reverse i p2_prefix s1 s2 (filter (f p2_prefix) s3_prefix)
                                        i_covered res_hd hd_prf).
          rewrite /tgt_sound p1__eq.
          move => /allP result.
          apply /allP.
          move => m inprf.
          apply /hasP.
          move: (result m inprf).
          rewrite has_seq1.
          move => le_prf.
            by eexists; first by apply: mem_head.
    Qed.

  End StepInvariants.

  Section SplitProperties.
    Arguments splitRec [Constructor].
    Arguments safeSplit [Constructor].

    Fixpoint arity_increasing n (Delta: seq (seq (@MultiArrow Constructor))): bool :=
      match Delta with
      | [::] => true
      | [:: Delta1 & Delta2] =>
        all (fun m => n == seq.size m.1) Delta1 &&
            arity_increasing n.+1 Delta2
      end.

    Lemma arity_increasing_cat: forall n Delta1 Delta2,
        arity_increasing n (Delta1 ++ Delta2) =
        (arity_increasing n Delta1 && arity_increasing (n + seq.size Delta1) Delta2).
    Proof.
      move => n Delta1.
      move: n.
      elim: Delta1.
      - move => n.
          by rewrite /= addn0.
      - move => ms Delta1 IH n Delta2.
        rewrite /=.
        move: (IH n.+1 Delta2).
        rewrite -(addn1 (seq.size Delta1)) (addnC (seq.size Delta1)) addnA (addn1 n).
        move => ->.
          by rewrite andbA.
    Qed.

    Lemma splitRec_arity:
      forall (A: @IT Constructor) srcs Delta,
        arity_increasing (seq.size srcs).+1 (Delta) ->
        arity_increasing (seq.size srcs).+1 (splitRec A srcs Delta).
    Proof.
      elim => //=.
      - move => A1 IH1 A2 IH2 srcs Delta.
        case: Delta.
        + move => _ /=.
          rewrite eq_refl.
            by apply: IH2.
        + move => Delta1 Delta2 /=.
          case: Delta2.
          * rewrite /= andbT eq_refl.
            move => arity_equal.
            rewrite arity_equal /=.
              by apply: IH2.
          * move => Delta21 Delta22 /andP [] arity_equal1 arity_equal2 /=.
            rewrite eq_refl arity_equal1 /=.
              by apply: IH2.
      - move => A1 IH1 A2 IH2 srcs Delta1 Delta2.
        case: (isOmega A1); first by apply: IH2.
        case: (isOmega A2); first by apply: IH1.
        apply: IH1.
          by apply: IH2.
    Qed.

    Lemma splitTy_arity: forall A, arity_increasing 0 (splitTy A).
    Proof.
      move => A.
      rewrite /splitTy.
      case: (isOmega A) => //=.
        by apply: splitRec_arity.
    Qed.

    Lemma arity_increasing_arity_equal:
      forall n Delta, arity_increasing n Delta ->
                 all (fun ms => all (fun m1 => all (fun m2 => seq.size m1.1 == seq.size m2.1) ms) ms) Delta.
    Proof.
      move => n Delta.
      move: n.
      elim: Delta => // ms mss IH n /andP [] prf prfs.
      rewrite (all_cat _ [::_]).
      apply /andP.
      split.
      - rewrite all_seq1.
        apply: sub_all; last by exact prf.
          by move => m1 /eqP <-.
      - apply: IH; by exact prfs.
    Qed.

    Definition mkArrow (m: @MultiArrow Constructor): @IT Constructor :=
      foldl (fun ty arg => arg -> ty) m.2 m.1.

    Lemma mkArrow_tgt_le:
      forall srcs A B, [bcd A <= B] -> [bcd (mkArrow (srcs, A)) <= (mkArrow (srcs, B))].
    Proof.
      elim => // A1 srcs IH A B prf.
      rewrite /mkArrow /=.
      apply: IH.
        by apply: BCD__Sub.
    Qed.

    Lemma splitRec_monotonic:
      forall A srcs Delta n,
        [bcd (\bigcap_(m_i <- nth [::] (splitRec A srcs Delta) n) (mkArrow m_i)) <=
         (\bigcap_(m_i <- nth [::] Delta n) (mkArrow m_i)) ].
    Proof.
      elim => //.
      - move => A1 _ A2 IH srcs Delta n /=.
        case: Delta.
        + by rewrite nth_nil /=.
        + move => ms1 [] /=.
          * case: n.
            ** do 2 rewrite [nth _ _ 0]/=.
               apply: BCD__Trans; first by apply: (bcd_cat_bigcap_f _ _ mkArrow [:: _] ms1).
                 by apply: BCD__Lub2.
            ** move => n.
                 by rewrite /= nth_nil /=.
          * move => ms2 Delta.
            case: n.
            ** do 2 rewrite [nth _ _ 0]/=.
               apply: BCD__Trans; first by apply: (bcd_cat_bigcap_f _ _ mkArrow [:: _] _).
                 by apply: BCD__Lub2.
            ** move => n.
               do 2 rewrite [nth _ _ n.+1]/=.
                 by apply: IH.
      - move => A1 IH1 A2 IH2 /=.
        case: (isOmega A1); first by apply: IH2.
        case: (isOmega A2); first by apply: IH1.
        move => srcs Delta n.
        apply: BCD__Trans; first by apply: IH1.
          by apply: IH2.
    Qed.

    Lemma splitRec_context_size_eq:
      forall (A: @IT Constructor) srcs Delta1 Delta2,
        seq.size Delta1 == seq.size Delta2 ->
        seq.size (splitRec A srcs Delta1) == seq.size (splitRec A srcs Delta2).
    Proof.
      elim => //.
      - move => A1 _ A2 IH srcs Delta1 Delta2 /=.
        case: Delta1.
        + by case: Delta2.
        + case: Delta2 => // ms2 Delta2 ms1 Delta1.
          case: Delta1.
          * by case: Delta2.
          * case: Delta2 => // ms22 Delta2 ms12 Delta1 /= size_eq.
              by apply: IH.
      - move => A1 IH1 A2 IH2 srcs Delta1 Delta2 size_eq /=.
        case: (isOmega A1); first by apply: IH2.
        case: (isOmega A2); first by apply: IH1.
        apply: IH1.
          by apply: IH2.
    Qed.

    Lemma splitRec_context_monotonic:
      forall A srcs Delta1 Delta2 n,
        seq.size Delta1 == seq.size Delta2 ->
        [bcd (\bigcap_(m_i <- nth [::] Delta1 n) (mkArrow m_i)) <= (\bigcap_(m_i <- nth [::] Delta2 n) (mkArrow m_i))] ->
        [bcd (\bigcap_(m_i <- nth [::] (splitRec A srcs Delta1) n) (mkArrow m_i)) <=
         (\bigcap_(m_i <- nth [::] (splitRec A srcs Delta2) n) (mkArrow m_i)) ].
    Proof.
      elim => //.
      - move => A1 _ A2 IH srcs Delta1 Delta2 n.
        do 2 rewrite [splitRec _ _ _]/=.
        case: Delta1.
        + by case: Delta2.
        + case: Delta2 => // ms2 Delta2 ms1 Delta1.
          rewrite [safeSplit _]/=.
          case: Delta1.
          * case: Delta2 => //= _.
            case: n => //.
            do 4 rewrite nth0 [head _ _]/=.
            move => prf.
            apply: BCD__Trans; last by apply: (bcd_bigcap_cat_f _ _ mkArrow [:: _] ms2).
            apply: BCD__Trans; first by apply: (bcd_cat_bigcap_f _ _ mkArrow [:: _] ms1).
            apply: BCD__Glb => //.
              by apply: BCD__Trans; first by apply: BCD__Lub2.
          * case: Delta2 => //= ms22 Delta2 ms12 Delta1.
            case: n.
            ** do 4 rewrite nth0 [head _ _]/=.
               move => _ prf.
               apply: BCD__Trans; last by apply: (bcd_bigcap_cat_f _ _ mkArrow [:: _] ms2).
               apply: BCD__Trans; first by apply: (bcd_cat_bigcap_f _ _ mkArrow [:: _] ms1).
               apply: BCD__Glb => //.
                 by apply: BCD__Trans; first by apply: BCD__Lub2.
            ** move => n.
               do 4 rewrite [nth _ _ n.+1]/=.
               move => size_eq prf.
                 by apply: IH.
      - move => A1 IH1 A2 IH2 srcs Delta1 Delta2 n.
        do 2 rewrite [splitRec (A1 \cap A2) _ _]/=.
        case: (isOmega A1); first by apply: IH2.
        case: (isOmega A2); first by apply: IH1.
        move => size_eq prf.
        apply: IH1.
        + by apply: splitRec_context_size_eq.
        + by apply: IH2.
    Qed.

    Lemma splitRec_split_context:
      forall B A srcs Delta n,
        [bcd B <= (\bigcap_(m_i <- nth [::] (splitRec A srcs (nseq (seq.size Delta) [::])) n) (mkArrow m_i))] ->
        [bcd B <= (\bigcap_(m_i <- nth [::] Delta n) (mkArrow m_i)) ] ->
        [bcd B <= (\bigcap_(m_i <- nth [::] (splitRec A srcs Delta) n) mkArrow m_i)].
    Proof.
      move => B.
      elim => //.
      - move => A1 _ A2 IH srcs.
        case => // ms Delta.
        case.
        + rewrite [nth _ [:: ms & Delta] 0]nth0 [head _ _]/=.
          do 2 rewrite [splitRec _ _ _]/=.
          case: Delta.
          * do 2 rewrite nth0 [head _ _]/=.
            move => prf1 prf2.
            apply: BCD__Trans; last by apply: (bcd_bigcap_cat_f _ _ mkArrow [:: _] ms).
              by apply: BCD__Glb.
          * move => ms1 Delta.
            do 2 rewrite nth0 [head _ _]/=.
            move => prf1 prf2.
            apply: BCD__Trans; last by apply: (bcd_bigcap_cat_f _ _ mkArrow [:: _] ms).
              by apply: BCD__Glb.
        + move => n.
          do 2 rewrite [splitRec _ _ _]/=.
          case: Delta => // ms1 Delta.
          do 3 rewrite [nth _ _ (n.+1)]/=.
          move => prf1 prf2.
            by apply: IH.
      - move => A1 IH1 A2 IH2 srcs Delta n.
        do 2 rewrite [splitRec (A1 \cap A2) _ _]/=.
        case: (isOmega A1); first by apply: IH2.
        case: (isOmega A2); first by apply: IH1.
        move => prf1 prf2.
        apply: IH1.
        + apply: BCD__Trans; first by exact prf1.
          apply: splitRec_context_monotonic.
          * rewrite size_nseq.
            apply: splitRec_context_size_eq.
              by rewrite size_nseq.
          * rewrite nth_nseq.
              by case: (n < seq.size (splitRec A2 srcs Delta)) => //=.
        + apply: IH2 => //.
            by apply: BCD__Trans; last by apply: (splitRec_monotonic A1).
    Qed.

    Lemma splitRec_sound:
      forall A srcs n Delta,
        [bcd (mkArrow (srcs, A)) <= \bigcap_(m_i <- nth [::] Delta n) (mkArrow m_i)] ->
        [bcd (mkArrow (srcs, A)) <= \bigcap_(m_i <- nth [::] (splitRec A srcs Delta) n) (mkArrow m_i)].
    Proof.
      elim => //.
      - move => A1 IH1 A2 IH2 srcs n Delta.
        rewrite /=.
        case: Delta.
        + rewrite /=.
          case: n => //= n.
          move => _.
          apply: BCD__Trans; last apply: IH2.
          * done.
          * by rewrite nth_nil /=.
        + rewrite /=.
          move => ms [].
          * case: n.
            ** do 2 rewrite [nth _ _ 0]/=.
               move => prf.
               apply: BCD__Trans; last by apply: (bcd_bigcap_cat_f _ _ mkArrow [::_] ms).
                 by apply: BCD__Glb.
            ** move => n.
               do 2 rewrite [nth _ _ n.+1]/=.
               move => prf.
               apply: BCD__Trans; last apply: IH2.
               *** done.
               *** move: prf => _.
                     by case: n => /=.
          * move => m1 mss.
            case: n.
            ** do 2 rewrite [nth _ _ 0]/=.
               move => prf.
               apply: BCD__Trans; last by apply: (bcd_bigcap_cat_f _ _ mkArrow [:: _] ms).
                 by apply: BCD__Glb.
            ** move => n.
               do 2 rewrite [nth _ _ n.+1]/=.
               move => prf.
               apply: BCD__Trans; last apply: IH2.
               *** done.
               *** by exact prf.
      - move => A1 IH1 A2 IH2 /=.
        case isOmega__A1: (isOmega A1).
        + move => srcs n Delta.
          have le_prf: [bcd (mkArrow (srcs, A2)) <= (mkArrow (srcs, A1 \cap A2))].
          { apply: mkArrow_tgt_le.
            apply: BCD__Glb => //.
              by apply: bcd__omega; rewrite isOmega__A1. }
          move => /(fun prf => BCD__Trans _ le_prf prf) /IH2.
            by move => /(fun prf => BCD__Trans _ (mkArrow_tgt_le _ _ _ (@BCD__Lub2 _ A1 A2)) prf).
        + case isOmega__A2: (isOmega A2).
          * move => srcs n Delta.
            have le_prf: [bcd (mkArrow (srcs, A1)) <= (mkArrow (srcs, A1 \cap A2))].
            { apply: mkArrow_tgt_le.
              apply: BCD__Glb => //.
                by apply: bcd__omega; rewrite isOmega__A2. }
            move => /(fun prf => BCD__Trans _ le_prf prf) /IH1.
              by move => /(fun prf => BCD__Trans _ (mkArrow_tgt_le _ _ _ (@BCD__Lub1 _ A1 A2)) prf).
          * move => srcs n Delta prf.
            apply: splitRec_split_context.
            ** apply: BCD__Trans; first by apply: (mkArrow_tgt_le srcs (A1 \cap A2) A1 BCD__Lub1).
               apply: IH1.
               rewrite nth_nseq.
                 by case: (n < seq.size (splitRec A2 srcs Delta)) => //=.
            ** apply: splitRec_split_context => //.
               apply: BCD__Trans; first by apply: (mkArrow_tgt_le srcs (A1 \cap A2) A2 BCD__Lub2).
               apply: IH2.
               rewrite nth_nseq.
                 by case: (n < seq.size Delta) => //=.
    Qed.

    Lemma splitTy_sound:
      forall A n, [bcd A <= \bigcap_(m_i <- nth [::] (splitTy A) n) (mkArrow m_i)].
    Proof.
      move => A n.
      rewrite /splitTy.
      case: (isOmega A).
      - by rewrite nth_nil /=.
      - case: n => // n.
        rewrite [nth _ _ _]/=.
        apply: BCD__Trans; last apply: splitRec_sound.
        + done.
        + by case: n => //=.
    Qed.

    Lemma mkArrow_arity: forall src srcs (B: @IT Constructor),
        (arity (mkArrow (rcons srcs src, B))) = [ eqType of (@IT Constructor * @IT Constructor)%type ].
    Proof.
      move => src.
      elim => //.
      move => src2 srcs IH B.
        by apply: IH.
    Qed.

    Fixpoint merge (mss1 mss2: seq (seq (@MultiArrow Constructor))): seq (seq (@MultiArrow Constructor)) :=
      match mss1, mss2 with
      | [:: ms1 & mss1], [:: ms2 & mss2] => [:: (ms1 ++ ms2) & merge mss1 mss2]
      | [::], mss2 => mss2
      | mss1, [::] => mss1
      end.

    Fixpoint splitTy_slow (A: @IT Constructor): seq (seq (@MultiArrow Constructor)) :=
      if (isOmega A) then [::]
      else match A with
           | A1 -> A2 =>
             [:: [:: ([::], A1 -> A2)] & map (fun ms => map (fun m => (rcons m.1 A1, m.2)) ms) (splitTy_slow A2) ]
           | A1 \cap A2 => [:: [:: ([::], A1 \cap A2)] & behead (merge (splitTy_slow A1) (splitTy_slow A2))]
           | A => [:: [:: ([::], A)]]
           end.

    Lemma merge_assoc:
      forall Delta1 Delta2 Delta3,
        merge (merge Delta1 Delta2) Delta3 =
        merge Delta1 (merge Delta2 Delta3).
    Proof.
      elim.
      - by elim.
      - move => Delta11 Delta1 IH.
        case => // Delta21 Delta2.
        case => //= Delta31 Delta3.
          by rewrite IH catA.
    Qed.

    Lemma merges0:
      forall Delta, merge Delta [::] = Delta.
    Proof. by case. Qed.

    Lemma merge0s:
      forall Delta, merge [::] Delta = Delta.
    Proof. by case. Qed.

    Lemma splitRec_merge:
      forall A srcs Delta,
        splitRec A srcs Delta =
        merge (splitRec A srcs [::]) Delta.
    Proof.
      elim => //.
      - move => A1 _ A2 IH2 srcs Delta.
        rewrite /=.
        case: Delta => // Delta1 Delta2 /=.
        case: Delta2.
        + apply: f_equal.
          rewrite IH2.
            by case: (splitRec A2 [:: A1 & srcs]).
        + move => Delta2 Delta.
          apply: f_equal.
            by rewrite IH2.
      - move => A1 IH1 A2 IH2 srcs Delta /=.
        case: (isOmega A1); first by apply: IH2.
        case: (isOmega A2); first by apply: IH1.
        rewrite (IH1 srcs (splitRec A2 srcs [::])).
          by rewrite IH1 IH2 merge_assoc.
    Qed.

    Lemma map_merge:
      forall Delta1 Delta2 (f: seq (@MultiArrow Constructor) -> seq (@MultiArrow Constructor)),
        (forall ms1 ms2, f (ms1 ++ ms2) = f ms1 ++ f ms2) ->
        map f (merge Delta1 Delta2) = merge (map f Delta1) (map f Delta2).
    Proof.
      elim => // Delta11 Delta1 IH.
      case => // Delta21 Delta2 f f_dist.
      rewrite /= f_dist.
      apply: f_equal.
        by apply: IH.
    Qed.

    Lemma splitRec_rcat:
      forall (A: @IT Constructor) srcs1 srcs2,
        splitRec A (srcs1 ++ srcs2) [::] =
        map (fun ms => map (fun m => (m.1 ++ srcs2, m.2)) ms) (splitRec A srcs1 [::]).
    Proof.
      elim => //=.
      - move => A1 _ A2 IH srcs1 srcs2.
        apply: f_equal.
          by rewrite (IH [:: A1 & srcs1]).
      - move => A1 IH1 A2 IH2 srcs1 srcs2.
        case: (isOmega A1); first by apply: IH2.
        case: (isOmega A2); first by apply: IH1.
        rewrite splitRec_merge (splitRec_merge _ _ (splitRec _ _ _)).
        rewrite map_merge; last by apply: map_cat.
          by rewrite IH1 IH2.
    Qed.


    Lemma splitTy_slow_splitTy: forall A, splitTy A = splitTy_slow A.
    Proof.
      elim => //=.
      - move => A1 IH1 A2 IH2.
        rewrite -IH2 /splitTy /= [isOmega _]/=.
        case: (isOmega A2) => //=.
        apply: f_equal.
        apply: f_equal.
        rewrite (splitRec_rcat A2 [::] [:: A1]).
        apply: eq_map.
        move => ms.
        apply: eq_map.
        move => m.
          by rewrite cats1.
      - move => A1 IH1 A2 IH2.
        rewrite /splitTy /=.
        case omega__Both: (isOmega A1 && isOmega A2) => //.
        rewrite splitRec_merge.
        rewrite -IH1 -IH2.
        rewrite /splitTy /=.
        case isOmega__A1: (isOmega A1) => /=.
        + have notOmega__A2: (isOmega A2 = false).
          { move: omega__Both.
            rewrite isOmega__A1.
              by case: (isOmega A2). }
            by rewrite notOmega__A2 merges0.
        + case isOmegaA2: (isOmega A2) => //.
            by rewrite merges0 /= splitRec_merge.
    Qed.

    Lemma omega_mkArrow_tgt: forall srcs A, isOmega (mkArrow (srcs, A)) = isOmega A.
    Proof.
      rewrite /mkArrow /=.
      elim => //.
      move => src srcs IH A /=.
        by apply: IH.
    Qed.

    Lemma mkArrow_arrow: forall A src srcs,
        mkArrow ([:: src & srcs], A) = (last src srcs -> mkArrow (belast src srcs, A)).
    Proof.
      move => A src srcs.
      move: A src.
      elim: srcs => // src2 srcs IH A src1 /=.
        by apply: IH.
    Qed.

    Lemma mkArrow_rcons: forall A src srcs,
        mkArrow (rcons srcs src, A) = (src -> mkArrow (srcs, A)).
    Proof.
      move => A src srcs.
      move: A src.
      elim: srcs => // src1 srcs IH A src.
        by apply: IH.
    Qed.

    Lemma mkArrow_prime:
      forall srcs A, isPrimeComponent A -> isPrimeComponent (mkArrow (srcs, A)).
    Proof.
      elim => // src srcs IH A prime__A.
        by apply: IH.
    Qed.

    Lemma splitTy_slow_omega:
      forall A, isOmega A -> splitTy_slow A = [::].
    Proof.
        by case => //= ? ? ->.
    Qed.

    Lemma nth_merge:
      forall n mss1 mss2,
        (nth [::] (merge mss1 mss2) n) =
        (nth [::] mss1 n ++ nth [::] mss2 n).
    Proof.
      elim.
      - case.
        + move => mss2.
            by rewrite nth_nil merge0s.
        + move => ms1 mss1.
          case => //.
            by rewrite nth_nil cats0 merges0.
      - move => n IH.
        case.
        + move => mss2.
            by rewrite nth_nil merge0s.
        + move => ms1 mss1.
          case.
          * by rewrite nth_nil cats0 merges0.
          * move => ms2 mss2.
              by apply: IH.
    Qed.

    Lemma splitTy_slow_inter_subseq1:
      forall A1 A2 n,
        subseq
          (nth [::] (splitTy_slow A1) n.+1)
          (nth [::] (splitTy_slow (A1 \cap A2)) n.+1).
    Proof.
      move => A1 A2 n.
      rewrite /= /splitTy_slow.
      case isOmega__A1: (isOmega A1); case isOmega__A2: (isOmega A2).
      - by rewrite -/splitTy_slow splitTy_slow_omega.
      - rewrite -/splitTy_slow splitTy_slow_omega //=.
          by apply: sub0seq.
      - rewrite /= -/splitTy_slow (splitTy_slow_omega A2) //= merges0.
        case: (splitTy_slow A1) => //.
          by apply: sub0seq.
      - rewrite /= -/splitTy_slow nth_behead nth_merge.
          by apply: prefix_subseq.
    Qed.

    Lemma splitTy_slow_inter_subseq2:
      forall A1 A2 n,
        subseq
          (nth [::] (splitTy_slow A2) n.+1)
          (nth [::] (splitTy_slow (A1 \cap A2)) n.+1).
    Proof.
      move => A1 A2 n.
      rewrite /= /splitTy_slow.
      case isOmega__A2: (isOmega A2); case isOmega__A1: (isOmega A1).
      - by rewrite -/splitTy_slow splitTy_slow_omega.
      - rewrite -/splitTy_slow splitTy_slow_omega //=.
          by apply: sub0seq.
      - rewrite /= -/splitTy_slow (splitTy_slow_omega A1) //=.
        case: (splitTy_slow A2) => //.
          by apply: sub0seq.
      - rewrite /= -/splitTy_slow nth_behead nth_merge.
          by apply: suffix_subseq.
    Qed.

    Lemma splitTy_complete_ctor:
      forall c A srcs B,
        [bcd (Ctor c A) <= (mkArrow (srcs, B))] ->
        [bcd
           ((mergeMultiArrows
               (filter (fun m =>
                          (seq.size m.1 == seq.size srcs) &&
                          all (fun AB => checkSubtypes AB.1 AB.2) (zip srcs m.1))
                       (nth [::] (splitTy (Ctor c A)) (seq.size srcs)))).2) <=  B].
    Proof.
      move => c A srcs B.
      elim /last_ind: srcs => // srcs src _.
      rewrite size_rcons /= nth_nil /= mkArrow_rcons.
      move => /subty_complete /SubtypeMachine_inv.
      move => /(fun prf => prf (fun x res =>
                              match x, res return Prop with
                              | [subty _ of B], (Return true) => isOmega B
                              | _, _ => True
                              end)).
      rewrite /=.
      case isOmega__B: (isOmega (mkArrow (srcs, B))).
      - move => _.
        move: isOmega__B.
        rewrite omega_mkArrow_tgt.
          by move => /(bcd__omega _ Omega).
      - move => prf.
        suff: false => //.
        apply: prf.
        case.
        + case => //.
          move => _ /(fun prf => @Omega__subty _ Omega _ prf isT) disprf.
            by rewrite -isOmega__B disprf.
        + move => A1 Delta r'.
          rewrite /cast /= isOmega__B.
            by move => /SubtypeMachine_inv.
    Qed.

    Lemma splitTy_complete_prod:
      forall A1 A2 srcs B,
        [bcd (A1 \times A2) <= (mkArrow (srcs, B))] ->
        [bcd
           ((mergeMultiArrows
               (filter (fun m =>
                          (seq.size m.1 == seq.size srcs) &&
                          all (fun AB => checkSubtypes AB.1 AB.2) (zip srcs m.1))
                       (nth [::] (splitTy (A1 \times A2)) (seq.size srcs)))).2) <=  B].
    Proof.
      move => A1 A2 srcs B.
      elim /last_ind: srcs => // srcs src _.
      rewrite size_rcons /= nth_nil /= mkArrow_rcons.
      move => /subty_complete /SubtypeMachine_inv.
      move => /(fun prf => prf (fun x res =>
                              match x, res return Prop with
                              | [subty _ of B], (Return true) => isOmega B
                              | _, _ => True
                              end)).
      rewrite /=.
      case isOmega__B: (isOmega (mkArrow (srcs, B))).
      - move => _.
        move: isOmega__B.
        rewrite omega_mkArrow_tgt.
          by move => /(bcd__omega _ Omega).
      - move => prf.
        suff: false => //.
        apply: prf.
        case.
        + case => //.
          move => _ /(fun prf => @Omega__subty _ Omega _ prf isT) disprf.
            by rewrite -isOmega__B disprf.
        + move => ? Delta r'.
          rewrite /cast /= isOmega__B.
            by move => /SubtypeMachine_inv.
    Qed.

    Lemma splitTy_complete_omega:
      forall srcs B,
        [bcd Omega <= (mkArrow (srcs, B))] ->
        [bcd
           ((mergeMultiArrows
               (filter (fun m =>
                          (seq.size m.1 == seq.size srcs)
                            && all (fun AB => checkSubtypes AB.1 AB.2) (zip srcs m.1))
                       (nth [::] (splitTy Omega) (seq.size srcs)))).2) <=  B].
    Proof.
      move => srcs B.
      rewrite /splitTy /= nth_nil /=.
      move => /subty_complete /(fun prf => @Omega__subty _ Omega _ prf isT).
      rewrite omega_mkArrow_tgt.
        by move => /(bcd__omega _ Omega).
    Qed.

    Lemma mkArrow_dist:
      forall srcs A1 A2, [bcd (mkArrow (srcs, A1 \cap A2)) <= (mkArrow (srcs, A1)) \cap (mkArrow (srcs, A2))].
    Proof.
      elim /last_ind => // srcs src IH A1 A2.
      do 3 rewrite mkArrow_rcons.
      apply: BCD__Glb.
      - apply: BCD__Sub => //.
          by apply: mkArrow_tgt_le.
      - apply: BCD__Sub => //.
          by apply: mkArrow_tgt_le.
    Qed.

    Lemma subseq_filtered {T: eqType}:
      forall f (xs ys: seq T), subseq xs ys -> subseq (filter f xs) (filter f ys).
    Proof.
      move => f xs ys.
      move: xs.
      elim: ys.
      - by case.
      - move => y ys IH.
        case.
        + by move => ?; apply sub0seq.
        + move => x xs /=.
          case xy__eq: (x == y).
          * move: xy__eq => /eqP ->.
            case: (f y).
            ** move => /IH.
                 by rewrite /= eq_refl.
            ** by apply: IH.
          * move => /IH prf.
            case: (f y).
            ** apply: subseq_trans; first by exact prf.
                 by apply: subseq_cons.
            ** exact prf.
    Qed.

    Lemma splitTy_complete_alternative:
      forall A srcs B,
        [bcd A <= (mkArrow (srcs, B))] ->
        [bcd
           ((mergeMultiArrows
               (filter (fun m =>
                          (seq.size m.1 == seq.size srcs) &&
                          all (fun AB => checkSubtypes AB.1 AB.2) (zip srcs m.1))
                       (nth [::] (splitTy A) (seq.size srcs)))).2) <= B].
    Proof.
      elim.
      - by apply: splitTy_complete_omega.
      - by move => *; apply: splitTy_complete_ctor.
      - move => A1 _ A2 IH srcs B.
        elim /last_ind: srcs.
        + rewrite /= /splitTy /=.
          case isOmega__A2: (isOmega A2) => //.
          move => /subty_complete /(fun prf => @Omega__subty _ (A1 -> A2) _ prf isOmega__A2) isOmega__srcsB.
            by apply: bcd__omega.
        + move => srcs src _.
          rewrite mkArrow_rcons splitTy_slow_splitTy size_rcons /=.
          case isOmega__A2: (isOmega A2).
          * move => /subty_complete /(fun prf => @Omega__subty _ (A1 -> A2) _ prf isOmega__A2).
            rewrite /= omega_mkArrow_tgt.
              by apply: bcd__omega.
          * move => /subty_complete /SubtypeMachine_inv.
            move => /(fun prf => prf (fun i r =>
                                    match i, r with
                                    | [subty (A1 -> A2) of (B1 -> B2)], Return true =>
                                      isOmega (B1 -> B2) \/ ([bcd B1 <= A1] /\ [bcd A2 <= B2])
                                    | _, _ => True
                                    end)).
            move => prf.
            suff: (isOmega (src -> mkArrow (srcs, B)) \/ [ bcd src <= A1] /\ [ bcd (A2) <= mkArrow (srcs, B)]).
            { case;
                first by rewrite /= omega_mkArrow_tgt; apply: bcd__omega.
              move => [] prf__A1 /(fun prf => IH _ _ prf).
              rewrite -splitTy_slow_splitTy.
              case in_bounds: (seq.size srcs < seq.size (splitTy A2)).
              - rewrite (nth_map [::] _ _ in_bounds).
                rewrite filter_map.
                rewrite /preim /=.
                have: ((fun m: MultiArrow =>
                          (seq.size (rcons m.1 A1) == seq.size (rcons srcs src))
                            && (all (fun AB => checkSubtypes AB.1 AB.2)
                                    (zip (rcons srcs src) (rcons m.1 A1)))) =1
                        (fun m: MultiArrow =>
                           (seq.size m.1 == seq.size srcs)
                             && (all (fun AB => checkSubtypes AB.1 AB.2)
                                     (zip srcs m.1)))).
                { move => m.
                  rewrite size_rcons size_rcons eqSS -cats1 -cats1 /=.
                  case size_eq: (seq.size m.1 == seq.size srcs) => //.
                  rewrite andTb andTb.
                  rewrite zip_cat; last by rewrite (eqP size_eq).
                  rewrite all_cat /=.
                  move: prf__A1 => /subtypeMachineP ->.
                    by rewrite andbT andbT. }
                move => /eq_filter <- prf__IH.
                apply: BCD__Trans; first by apply: mergeMultiArrows_tgt_le.
                apply: BCD__Trans; last by exact prf__IH.
                apply: BCD__Trans; last by apply: mergeMultiArrows_tgt_ge.
                rewrite -map_comp.
                rewrite (@eq_map _ _ ([eta snd] \o (fun m : seq IT * IT => (rcons m.1 A1, m.2))) snd) => //.
                  by rewrite size_rcons.
              - rewrite nth_default; last by rewrite leqNgt in_bounds.
                  by rewrite nth_default; last by rewrite size_map leqNgt in_bounds. }
            apply: prf.
            rewrite /=.
            case isOmega__srcsB: (isOmega (mkArrow (srcs, B)));
              first by move => *; left.
            move => Delta r'.
            case: r' => //=.
            move: isOmega__srcsB.
            rewrite /cast /= omega_mkArrow_tgt.
            move => isOmega__B.
            rewrite isOmega__B.
            move => /SubtypeMachine_inv.
            move => /(fun prf => prf (fun x res =>
                                    match x, res with
                                    | [ tgt_for_srcs_gte src in [:: (A1, A2)]], [ check_tgt Delta] =>
                                      ((Types.Semantics [ subty \bigcap_(A__i <- Delta) A__i of mkArrow (srcs, B)]
                                                       (Return true)) ->
                                       [ bcd (src) <= A1] /\ [ bcd (A2) <= mkArrow (srcs, B)])%type
                                    | _, _ => True
                                    end)) prf.
            move => x; right; move: x.
            apply: prf.
            move => Delta' r src_prf.
            move => /SubtypeMachine_inv.
            case: Delta' => // _.
            move: src_prf.
            case: r.
            ** move => /subty__sound /= prf1 /subty__sound /= prf2.
                 by split.
            ** move => _ /(fun prf => @Omega__subty _ Omega _ prf isT) disprf.
               move: isOmega__B.
                 by rewrite -(omega_mkArrow_tgt srcs) disprf.
      - by move => *; apply: splitTy_complete_prod.
      - move => A1 IH1 A2 IH2 srcs B.
        elim /last_ind: srcs.
        { rewrite /= /splitTy.          
          case isOmega__A1A2: (isOmega (A1 \cap A2)) => //=.
          move => /subty_complete /(fun prf => @Omega__subty _ _ _ prf) /= /(fun prf => prf isOmega__A1A2).
            by apply: bcd__omega. }
        move => srcs src _.
        move => /(fun prf => @BCD__Trans _ (A1 \cap A2) (mkArrow (rcons srcs src, B)) _
                                   prf (mkArrow_tgt_le (rcons srcs src) _ _ (primeFactors_geq B))) prf.
        apply: BCD__Trans; last by apply: (primeFactors_leq B).
        move: prf.
        move: (primeFactors_prime B).
        elim: (primeFactors B); first by rewrite /=.
        move => // B1 Bs IH /andP [] /(mkArrow_prime (rcons srcs src)) prime__B1 prime__Bs prf.
        apply: BCD__Trans; last by apply: (bcd_bigcap_cat _ [:: B1] Bs).
        have: ([bcd (A1 \cap A2) <= mkArrow (rcons srcs src, B1)] /\
               [bcd (A1 \cap A2) <= mkArrow (rcons srcs src, \bigcap_(B_i <- Bs) B_i)]).
        { split.
          - apply: BCD__Trans; first by exact prf.
            apply: mkArrow_tgt_le.
              by apply: BCD__Trans; first by apply: (bcd_cat_bigcap _ [:: B1] Bs).
          - apply: BCD__Trans; first by exact prf.
            apply: mkArrow_tgt_le.
              by apply: BCD__Trans; first by apply: (bcd_cat_bigcap _ [:: B1] Bs). }
        move => [] prf__B1 prf__Bs.
        apply: BCD__Glb.
        + move: (primeComponentPrime _ _ _ _ prf__B1 (isPrimeComponentP prime__B1)).
          case.
          * rewrite splitTy_slow_splitTy.
            move => prf__A1.
            apply: BCD__Trans; first by apply: mergeMultiArrows_tgt_le.
            move: (splitTy_slow_inter_subseq1 A1 A2 (seq.size srcs)) => subseq_prf.
            apply: BCD__Trans.
            ** apply: bcd_subset_f.
               apply: mem_subseq.
               apply: subseq_filtered.
               rewrite size_rcons.
                 by exact subseq_prf.
            ** move: prf__A1.
               move => /IH1.
               rewrite splitTy_slow_splitTy size_rcons.
                 by move => /(BCD__Trans _ (mergeMultiArrows_tgt_ge _)).
          * rewrite splitTy_slow_splitTy.
            move => prf__A2.
            apply: BCD__Trans; first by apply: mergeMultiArrows_tgt_le.
            move: (splitTy_slow_inter_subseq2 A1 A2 (seq.size srcs)) => subseq_prf.
            apply: BCD__Trans.
            ** apply: bcd_subset_f.
               apply: mem_subseq.
               apply: subseq_filtered.
               rewrite size_rcons.
                 by exact subseq_prf.
            ** move: prf__A2.
               move => /IH2.
               rewrite splitTy_slow_splitTy size_rcons.
                 by move => /(BCD__Trans _ (mergeMultiArrows_tgt_ge _)).
        + by apply: IH.
    Qed.


    Lemma splitTy_complete:
      forall (A B: @IT Constructor) (srcs: seq (@IT Constructor)),
        [bcd A <= (mkArrow (srcs, B))] ->
        ~~(isOmega (mkArrow (srcs, B))) ->
        has (fun m =>
               [&& (seq.size m.1 == seq.size srcs),
                all (fun AB => checkSubtypes AB.1 AB.2) (zip srcs m.1) &
                checkSubtypes m.2 B])
            (filterMergeMultiArrows (subseqs (nth [::] (splitTy A) (seq.size srcs)))).
    Proof.
      move => A B srcs prf.
      move: (splitTy_complete_alternative A srcs B prf) => res.
      move => notOmega__B.
      have: (subseq
               (filterMergeMultiArrows
                  [:: filter (fun m =>
                                (seq.size m.1 == seq.size srcs)
                                  && all (fun AB => checkSubtypes AB.1 AB.2) (zip srcs m.1))
                      (nth [::] (splitTy A) (seq.size srcs))])
               (filterMergeMultiArrows (subseqs (nth [::] (splitTy A) (seq.size srcs))))).
      { apply: filterMergeMultiArrows_subseq.
        rewrite sub1seq.
        apply: subseq_subseqs.
          by apply: filter_subseq. }
      move: res.
      move: (filter_all (fun m => (seq.size m.1 == seq.size srcs)
                                 && all (fun AB => checkSubtypes AB.1 AB.2) (zip srcs m.1))
                        (nth [::] (splitTy A) (seq.size srcs))).
      case: (filter (fun m => (seq.size m.1 == seq.size srcs)
                             && all (fun AB => checkSubtypes AB.1 AB.2) (zip srcs m.1))
                    (nth [::] (splitTy A) (seq.size srcs))).
      - move => _ /subty_complete /(fun prf => @Omega__subty _ Omega _ prf isT) disprf.
        move: notOmega__B.
          by rewrite omega_mkArrow_tgt disprf.
      - move => m ms prf__srcs prf__tgt.
        rewrite /filterMergeMultiArrows -/filterMergeMultiArrows.
        rewrite sub1seq.
        move => inprf.
        apply /hasP.
        exists (mergeMultiArrows [:: m & ms]) => //.
        move: prf__tgt => /subtypeMachineP ->.
        rewrite andbT.
        have size_eq: (all (fun m1 => all (fun m2 => seq.size m1.1 == seq.size m2.1) [:: m & ms])
                           [:: m & ms]).
        { apply /allP.
          move => m1 inprf__m1.
          apply /allP.
          move => m2 inprf__m2.
          move: prf__srcs => /allP prf__srcs.
          move: (prf__srcs m1 inprf__m1) => /andP [] /eqP ->.
            by move: (prf__srcs m2 inprf__m2) => /andP [] /eqP ->. }
        apply /andP; split.
        + move: size_eq => /(mergeMultiArrows_arity [:: m & ms]) /andP [] /eqP <- _.
            by move: prf__srcs => /andP [] /andP [].
        + apply /(all_nthP (Omega, Omega)).
          move => n n_lt.
          move: (mergeMultiArrows_srcs_ge _ n size_eq) => prf_merged.
          rewrite nth_zip_cond n_lt [fst _]/=.
          apply /subtypeMachineP.
          apply: BCD__Trans; last by apply: prf_merged.
          apply /subtypeMachineP.
          move: prf__srcs.
          clear...
          elim: [:: m & ms]; move: m ms => _ _.
          * move => _.
              by apply /subtypeMachineP => /=.
          * move => m ms IH.
            move => /andP [] prf__m /IH prf__ms.
            apply /subtypeMachineP.
            apply: BCD__Trans; last by apply: (bcd_bigcap_cat_f _ _ _ [:: m] ms).
            apply: BCD__Glb; last by apply /subtypeMachineP.
            move: prf__m => /andP [] size_eq /(all_nthP (Omega, Omega)).
            rewrite size_zip -(eqP size_eq) minnn.
            case n_lt: (n < seq.size m.1).
            ** move => /(fun prf => prf n n_lt).
               rewrite nth_zip; last by rewrite -(eqP size_eq).
                 by move => /subtypeMachineP.
            ** rewrite /= (@nth_default _ Omega m.1) => //.
               rewrite leqNgt.
                 by apply: negbT.
    Qed.
  End SplitProperties.

  Lemma splitTy_instructionsCovered:
    forall A B,
      let Bs := primeFactors B in
      let mss := splitTy A in
      all instruction_covered (map (fun ms => Cover (map (fun m => (m, filter (checkSubtypes m.2) Bs)) ms) Bs) mss).
  Proof.
    move => A B.
    rewrite /instruction_covered.
    apply /allP.
    move => i.
    move => /mapP [] ms ms_in -> /=.
    apply /allP.
    move => [] m__i toCover.
    move => /mapP [] m__i2 mi2_in [] -> -> /=.
    apply /andP.
    split.
    - apply /subtypeMachineP.
      clear...
      elim: (primeFactors B) => //= B1 Bs IH.
      case le_prf: (checkSubtypes m__i2.2 B1).
      + apply: BCD__Trans; last by apply: (bcd_bigcap_cat _ [:: B1] _).
        apply: BCD__Glb; first by apply /subtypeMachineP.
          by exact IH.
      + by exact IH.
    - apply /allP.
      move => B_i inprf.
      apply /implyP.
      move => prf.
        by rewrite mem_filter inprf prf.
  Qed.

  Lemma coverMachine_splitTy_complete:
    forall (A: @IT Constructor) srcs B s,
      [bcd A <= mkArrow (srcs, B)] ->
      ~~(isOmega B) ->
      let Bs := primeFactors B in
      let mss := splitTy A in
      ([::], map (fun ms => Cover (map (fun m => (m, filter (checkSubtypes m.2) Bs)) ms) Bs) mss) ~~>[*] (s, [::]) ->
       has (fun m =>
               [&& (seq.size m.1 == seq.size srcs),
                all (fun AB => checkSubtypes AB.1 AB.2) (zip srcs m.1) &
                checkSubtypes m.2 B]) s.
  Proof.
    move => A srcs B s le__AB.
    rewrite -(omega_mkArrow_tgt srcs).
    move => notOmega__B.
    move: (splitTy_complete A B srcs le__AB notOmega__B).
    move => /hasP [] m inprf__m /andP [] srcs_size__m /andP [] srcs_ge__m tgt_le__m.
    move => Bs mss steps.
    have: (all (complete s) (map (fun ms => Cover (map (fun m => (m, filter (checkSubtypes m.2) Bs)) ms) Bs) mss)).
    { apply: (steps_complete [::] _ s steps).
      - rewrite /mss.
        move: (splitTy_arity A).
        move => /arity_increasing_arity_equal.
        clear ...
        elim: (splitTy A) => // m ms IH /andP [] prf__m prf__ms.
        apply /andP; split.
        + rewrite /arity_equal /= -map_comp.
          rewrite (@eq_map _ _ (fst \o (fun m => (m, [seq x <- Bs | checkSubtypes m.2 x]))) id) => //.
          rewrite map_id.
            by exact prf__m.
        + by apply: IH.
      - rewrite /not_omega_instruction.
        rewrite /mss.
        apply /allP.
        move => i.
        move => /mapP [] ms ms_in -> /=.
        rewrite /Bs /primeFactors.
        move: (primeFactors__notOmega _ B [::] id isT) ->.
        move: (primeFactors_leq B).
        rewrite /primeFactors.
        case: (primeFactors_rec _ B id [::]) => //=.
        move => /subty_complete /(fun prf => Omega__subty _ Omega _ prf isT) disprf.
        move: notOmega__B.
          by rewrite omega_mkArrow_tgt disprf.
      - by apply: splitTy_instructionsCovered.
      - rewrite /toCover_prime.
        rewrite /mss.
        apply /allP.
        move => i.
        move => /mapP [] ms ms_in -> /=.
          by apply: primeFactors_prime.
      - rewrite /currentResultNotDone.
        rewrite /mss.
        apply /allP.
        move => i.
          by move => /mapP [] ms ms_in -> /=. }
    move => /allP prf__complete.
    have: (complete s (Cover (map (fun m => (m, filter (checkSubtypes m.2) Bs))
                                  (nth [::] (splitTy A) (seq.size srcs))) Bs)).
    { apply: prf__complete.
      rewrite mem_map.
      - rewrite /mss.
        apply: mem_nth.
        move: inprf__m.
        case src_size_lt: (seq.size srcs < seq.size (splitTy A)) => //.
        rewrite nth_default => //.
          by rewrite leqNgt src_size_lt.
      - move => x y [].
        apply: inj_map.
          by move => ? ? []. }
    rewrite /complete /mergeComponentsOf -map_comp.
    rewrite (@eq_map _ _ (fst \o (fun m => (m, [seq x <- Bs | checkSubtypes m.2 x]))) id) => //.
    rewrite map_id map_id.
    move => /allP /(fun prf => prf m inprf__m) /implyP.
    have: (forall A, checkSubtypes A (intersect (toCoverOf (Cover (map (fun m => (m, filter (checkSubtypes m.2) Bs))
                                                               (nth [::] (splitTy A) (seq.size srcs))) Bs))) =
                checkSubtypes A B).
    { rewrite /= /Bs.
      move => C.
      case le__CB: (checkSubtypes C B).
      - apply /subtypeMachineP.
        rewrite -(map_id (primeFactors B)).
        apply: BCD__Trans; last by apply (primeFactors_geq B).
          by apply /subtypeMachineP.
      - apply /negbTE.
        case le__CFactors: (checkSubtypes C (intersect (primeFactors B))) => //.
        move: le__CB => /subtypeMachineP le__CB.
        move: le__CFactors.
        rewrite -(map_id (primeFactors B)).
          by move => /subtypeMachineP /(fun prf => BCD__Trans _ prf (primeFactors_leq B)) /le__CB. }
    move => tgt_le_eq.
    rewrite (tgt_le_eq m.2).
    move => /(fun prf => prf tgt_le__m) /hasP [] res inprf__res /andP [] srcs_size__res.
    rewrite (tgt_le_eq res.2).
    move => /andP [] srcs_ge__res tgt_le__res.
    apply /hasP.
    exists res => //.
    rewrite tgt_le__res (eqP srcs_size__res) srcs_size__m andTb andbT.
    apply /(all_nthP (Omega, Omega)).
    move => n n_lt.
    rewrite nth_zip; last by rewrite (eqP srcs_size__res) (eqP srcs_size__m).
    apply /subtypeMachineP.
    move: srcs_ge__res => /(all_nthP (Omega, Omega)) /(fun prf => prf n).
    move: srcs_ge__m => /(all_nthP (Omega, Omega)) /(fun prf => prf n).
    move: n_lt.
    do 3 rewrite size_zip.
    rewrite (eqP srcs_size__res) (eqP srcs_size__m) minnn.
    move => n_lt /(fun prf => prf n_lt) /subtypeMachineP prf1 /(fun prf => prf n_lt) /subtypeMachineP prf2.
    move: prf1 prf2.
    rewrite nth_zip; last by rewrite (eqP srcs_size__m).
    rewrite nth_zip; last by rewrite (eqP srcs_size__res) (eqP srcs_size__m).
    move => prf1 prf2.
    apply: BCD__Trans; first by exact prf1.
      by exact prf2.
  Qed.

  Lemma mkArrow_srcs_ge:
    forall srcs1 srcs2 A,
      seq.size srcs1 = seq.size srcs2 ->
      all (fun srcs => checkSubtypes srcs.1 srcs.2) (zip srcs1 srcs2) ->
      [bcd (mkArrow (srcs2, A)) <= (mkArrow (srcs1, A))].
  Proof.
    elim /last_ind.
    - by case.
    - move => srcs1 src1 IH srcs2 A size_prf.
      have: (exists srcs22 src2, srcs2 = rcons srcs22 src2).
      { move: size_prf.
        rewrite size_rcons.
        case: srcs2 => // x xs.
        move => _.
          by exists (belast x xs), (last x xs); by apply: lastI. }
      move => [] srcs22 [] src2 srcs2__eq.
      move: size_prf.
      rewrite srcs2__eq.
      do 2 rewrite mkArrow_rcons size_rcons.
      move => [] size_prf.
      rewrite (zip_rcons _ _ size_prf) -cats1 all_cat all_seq1.
      move => /andP [] prf src_prf.
      apply: BCD__Sub.
      + by apply /subtypeMachineP.
      + by apply: IH.
  Qed.

  Lemma mergeMultiArrow_le:
    forall m1 m2,
      seq.size m1.1 = seq.size m2.1 ->
      [bcd (mkArrow m1 \cap mkArrow m2) <= mkArrow (mergeMultiArrow m1 m2.1 m2.2)].
  Proof.
    move => [] srcs1 tgt1 [] srcs2 tgt2.
    rewrite /mergeMultiArrow /=.
    move: tgt1 srcs2 tgt2.
    elim /last_ind: srcs1.
    - move => tgt1 [] //= tgt2 _.
        by apply: BCD__Glb.
    - move => srcs1 src1 IH tgt1 srcs2 tgt2 size_prf.
      have: (exists srcs22 src2, srcs2 = rcons srcs22 src2).
      { move: size_prf.
        rewrite size_rcons.
        case: srcs2 => // x xs.
        move => _.
          by exists (belast x xs), (last x xs); by apply: lastI. }
      move => [] srcs22 [] src2 srcs2__eq.
      move: size_prf.
      rewrite srcs2__eq.
      do 2 rewrite mkArrow_rcons size_rcons.
      move => [] size_prf.
      rewrite (zip_rcons _ _ (Logic.eq_sym size_prf)) -cats1 map_cat /= cats1 mkArrow_rcons.
      apply: BCD__Trans; first by apply: bcd__Arr.
      apply: BCD__Sub.
      + apply: BCD__Trans; first by apply: dcap_cap.
          by apply: BCD__Glb.
      + by apply: IH.
  Qed.

  Lemma bcd_multiArrow_Dist:
    forall ms,
      all (fun m1 : @MultiArrow Constructor =>
             all (fun m2 : @MultiArrow Constructor => seq.size m1.1 == seq.size m2.1) ms) ms ->
      [bcd (\bigcap_(m_i <- ms) (mkArrow m_i)) <= mkArrow (mergeMultiArrows ms)].
  Proof.
    rewrite /mergeMultiArrows.
    case => //.
    move => m ms size_prf.
    apply: BCD__Trans; first by apply: (bcd_cat_bigcap_f _ _ mkArrow [:: m] ms).
    have m__eq: (m = mergeMultiArrows [:: m]) by reflexivity.
    move: size_prf.
    rewrite [X in foldl _ X _]m__eq [X in [:: X & _]]m__eq.
    have: [bcd (\bigcap_(m_i <- [:: m]) mkArrow m_i) <= mkArrow (mergeMultiArrows [:: m])] by done.
    have: (~~nilp [:: m]) by done.
    move: [:: m].
    move: m m__eq => _ _.
    elim: ms.
    - rewrite /=.
      move => ms1 _ prf _.
        by apply: BCD__Trans; first by apply: BCD__Lub1.
    - move => m2 ms2 IH ms1 nonEmpty__ms1 prf size_prf.
      rewrite [foldl _ _ _]/=.
      have: (mergeMultiArrow (mergeMultiArrows ms1) m2.1 m2.2 =
             mergeMultiArrows (rcons ms1 m2)).
      { rewrite /mergeMultiArrows.
        have: (exists m1 ms11, ms1 = [:: m1 & ms11]).
        { move: nonEmpty__ms1.
          clear...
          case: ms1 => // m1 ms11 _.
            by (exists m1, ms11). }
        move => [] m1 [] ms11 -> /=.
          by rewrite -cats1 foldl_cat. }
      move => merge_eq.
      rewrite merge_eq.
      apply: (BCD__Trans ((\bigcap_(m_i <- (rcons ms1 m2)) mkArrow m_i) \cap \bigcap_(m_i <- ms2) mkArrow m_i)).
      + apply: BCD__Glb.
        * rewrite -cats1.
          apply: BCD__Trans; last by apply: bcd_bigcap_cat_f.
          apply: BCD__Glb => //.
          apply: BCD__Trans; first by apply: BCD__Lub2.
            by apply: BCD__Trans; first by apply: (bcd_cat_bigcap_f _ _ mkArrow [:: m2] ms2).
        * apply: BCD__Trans; first by apply: BCD__Lub2.
            by apply: BCD__Trans; first by apply: (bcd_cat_bigcap_f _ _ mkArrow [:: m2] ms2).
      + apply: IH.
        * move: nonEmpty__ms1.
          clear...
            by case ms1.
        * rewrite -merge_eq.
          rewrite -cats1.
          apply: BCD__Trans; first by apply: bcd_cat_bigcap_f.
          apply: (BCD__Trans (mkArrow (mergeMultiArrows ms1) \cap mkArrow m2)).
          ** apply: BCD__Glb => //.
               by apply: BCD__Trans; first by apply: BCD__Lub1.
          ** apply: mergeMultiArrow_le.
             move: size_prf.
             rewrite (all_cat _ [:: _]) all_seq1 (all_cat _ [:: _]).
             move => /andP [] /andP [] _ size_prf _.
             move: size_prf.
             rewrite (all_cat _ [:: _]) all_seq1.
               by move => /andP [] /eqP.
        * rewrite (all_cat _ [:: _]).
          apply /andP.
          move: size_prf.
          rewrite (all_cat _ [:: _; _]).
          move => /andP [] _ /allP size_prf.
          have size_prf__ms2: (all
                               (fun m : MultiArrow =>
                                  seq.size (mergeMultiArrows (rcons ms1 m2)).1 ==
                                  seq.size m.1) ms2).
          { apply /allP.
             move => m inprf.
             move: size_prf => /(fun prf => prf m inprf) size_prf.
             rewrite -cats1 /mergeMultiArrows.
             have: (exists m1 ms11, ms1 = [:: m1 & ms11]).
             { move: nonEmpty__ms1.
               clear ...
               case: ms1 => // m1 ms11 _.
                 by (exists m1, ms11). }
             move =>  [] m1 [] ms11 ms1__eq.
             rewrite ms1__eq /= foldl_cat /= -/(mergeMultiArrows [:: m1 & ms11]) size_map size_zip.
             move: size_prf.
             rewrite ms1__eq (all_cat _ [:: _]) all_seq1.
             move => /andP [] /eqP <-.
             rewrite (all_cat _ [:: _]) all_seq1.
             move => /andP [] /eqP <- _.
               by rewrite minnn. }
          split.
          ** by rewrite all_seq1 (all_cat _ [:: _]) /= eq_refl /=.
          ** apply /allP.
             move => m inprf.
             rewrite (all_cat _ [:: _]) all_seq1.
             move: size_prf__ms2 => /allP /(fun prf => prf m inprf) /eqP ->.
             rewrite eq_refl andTb.
             move: size_prf => /(fun prf => prf m inprf).
             rewrite (all_cat _ [:: _; _]).
               by move => /andP [].
  Qed.

  Lemma coverMachine_splitTy_sound:
    forall (A: @IT Constructor) B s,
      ~~(isOmega B) ->
      let Bs := primeFactors B in
      let mss := splitTy A in
      ([::], map (fun ms => Cover (map (fun m => (m, filter (checkSubtypes m.2) Bs)) ms) Bs) mss) ~~>[*] (s, [::]) ->
      all (fun m => checkSubtypes A (mkArrow m)) s.
  Proof.
    move => A B s notOmega__B Bs mss.
    move: (splitTy_sound A) => split_sound.
    move => /(semantics_mergeComponents _ _).
    rewrite /= subn0 (take_oversize (leqnn _)).
    elim: s => // m s IH.
    rewrite /sound (all_cat _ [:: m] s) -/(sound s _) all_seq1.
    move => /andP [] m_sound s_sound.
    apply /andP.
    split.
    - apply /subtypeMachineP.
      move: m_sound.
      rewrite -map_comp /=.
      have: (((fun i => filterMergeMultiArrows (subseqs (mergeComponentsOf i)))
                \o (fun ms => Cover (map (fun m => (m, filter (checkSubtypes m.2) Bs)) ms) Bs))
             =1 (fun ms => filterMergeMultiArrows (subseqs ms))).
      { move => ms.
        rewrite /= -map_comp.
          by rewrite map_id. }
      move => /eq_map /(fun prf => prf mss) ->.
      move => /flatten_mapP [] ms inprf__ms inprf__m.
      move: (inprf__ms) => /(nth_index [::]) ms_pos.
      apply: BCD__Trans; first by exact (split_sound (index ms mss)).
      rewrite ms_pos.
      have: (exists2 ms2, subseq ms2 ms & m = mergeMultiArrows ms2).
      { move: inprf__m (subseqs_subseq ms).
        clear ...
        elim: (subseqs ms) => // ms21 mss22 IH.
        rewrite /=.
        case: ms21.
        - move => inprf__m subseq_prf.
          apply: IH => //.
          move => ms2 inprf.
          apply: subseq_prf.
            by apply: mem_behead.
        - move => m21 ms21.
          rewrite -/(mergeMultiArrows [:: m21 & ms21]) in_cons.
          move => /orP [].
          + move => /eqP m__eq /(fun prf => prf [:: m21 & ms21] (mem_head _ _)) subseq_prf.
              by (exists [:: m21 & ms21]).
          + move => inprf__m subseq_prf.
            apply: IH => //.
            move => ms2 inprf.
            apply: subseq_prf.
              by apply: mem_behead. }
      move => [] ms2 subseq_prf m_eq.
      apply: BCD__Trans; first by apply: (bcd_subset_f mkArrow ms ms2 (mem_subseq subseq_prf)).
      rewrite m_eq.
      have: (all (fun (m1: @MultiArrow Constructor) =>
                    all (fun (m2: @MultiArrow Constructor) => seq.size m1.1 == seq.size m2.1) ms2) ms2).
      { move: (arity_increasing_arity_equal 0 mss (splitTy_arity A)) => /allP /(fun prf => prf ms inprf__ms) prf.
          by apply: (all_nested_subseq _ ms). }
        by apply: bcd_multiArrow_Dist.
    - by apply: IH.
  Qed.

  Lemma coverMachine_splitTy_tgt_sound:
    forall (A: @IT Constructor) B s,
      let Bs := primeFactors B in
      let mss := splitTy A in
      ([::], map (fun ms => Cover (map (fun m => (m, filter (checkSubtypes m.2) Bs)) ms) Bs) mss) ~~>[*] (s, [::]) ->
      all (fun m => checkSubtypes m.2 B) s.
  Proof.
    move => A B s Bs mss.
    move: (primeFactors_leq B) => le__Bs.
    move => /(steps_tgt_sound ([::], map (fun ms => Cover (map (fun m => (m, filter (checkSubtypes m.2) Bs)) ms) Bs) mss)
                           (s, [::])
                           (splitTy_instructionsCovered A B)).
    rewrite /= subn0 take_oversize => //.
    move => /allP tgt_sound_prf.
    apply /allP.
    move => m inprf.
    apply /subtypeMachineP.
    apply: BCD__Trans; last by exact le__Bs.
    move: (tgt_sound_prf m inprf) => /hasP [] i [].
    move => /mapP [] ms inprf__ms i__eq.
    rewrite i__eq.
      by move => /subtypeMachineP.
  Qed.

  Section PostReductionPhase.
    Fixpoint reduceMultiArrows (ms: seq (@MultiArrow Constructor)) : seq (@MultiArrow Constructor) :=
      if ms is [:: m1 & ms2]
      then
        let ms__red := reduceMultiArrows ms2 in
        if has (fun m2 => [&& (seq.size m2.1 == seq.size m1.1)
                           & all (fun AB => checkSubtypes AB.1 AB.2) (zip m1.1 m2.1)]) ms__red
           then ms__red
           else [:: m1 & filter (fun m2 => negb [&& (seq.size m2.1 == seq.size m1.1)
                                              & all (fun AB => checkSubtypes AB.1 AB.2) (zip m2.1 m1.1)])
                                ms__red ]
      else [::].

    Lemma reduction_subseq: forall ms, subseq (reduceMultiArrows ms) ms.
    Proof.
      elim => // m1 ms2 IH.
      rewrite [reduceMultiArrows _]/=.
      case: (has (fun m2 => [&& (seq.size m2.1 == seq.size m1.1)
                          & all (fun AB => checkSubtypes AB.1 AB.2) (zip m1.1 m2.1)]) (reduceMultiArrows ms2)).
      - apply: subseq_trans; first by exact IH.
          by apply: subseq_cons.
      - apply: (@cat_subseq _ [:: m1] _ [:: m1] _) => //.
          by apply: subseq_trans; first by apply filter_subseq.
    Qed.

    Lemma soundnessPreserving:
      forall A ms,
        all (fun m => checkSubtypes A (mkArrow m)) ms ->
        all (fun m => checkSubtypes A (mkArrow m)) (reduceMultiArrows ms).
    Proof.
      move => ? ? /allP prf.
      apply /allP.
      move => m inprf.
      apply: prf.
      apply: mem_subseq; last by exact inprf.
        by apply: reduction_subseq.
    Qed.

    Lemma tgt_soundnessPreserving:
      forall B ms,
        all (fun m => checkSubtypes m.2 B) ms ->
        all (fun m => checkSubtypes m.2 B) (reduceMultiArrows ms).
    Proof.
      move => ? ? /allP prf.
      apply /allP.
      move => m inprf.
      apply: prf.
      apply: mem_subseq; last by exact inprf.
        by apply: reduction_subseq.
    Qed.

    Lemma completenessPreserving:
      forall srcs B ms,
        all (fun m => checkSubtypes m.2 B) ms ->
        has (fun m =>
               [&& (seq.size m.1 == seq.size srcs),
                all (fun AB => checkSubtypes AB.1 AB.2) (zip srcs m.1) &
                checkSubtypes m.2 B]) ms ->
        has (fun m =>
               [&& (seq.size m.1 == seq.size srcs),
                all (fun AB => checkSubtypes AB.1 AB.2) (zip srcs m.1) &
                checkSubtypes m.2 B]) (reduceMultiArrows ms).
    Proof.
      move => srcs B.
      elim => // m ms IH tgt_sound_prf.
      move => /hasP [] m2.
      rewrite in_cons => /orP [].
      - move => /eqP -> prf.
        rewrite [reduceMultiArrows _]/=.
        case rest_prf: (has (fun m2 => [&& (seq.size m2.1 == seq.size m.1)
                                     & all (fun AB => checkSubtypes AB.1 AB.2) (zip m.1 m2.1)])
                            (reduceMultiArrows ms)).
        + move: rest_prf => /hasP [] m3 inprf /andP [] /eqP srcs_size srcs_prf.
          apply /hasP.
          exists m3 => //.
          have size__eq: (seq.size m3.1 == seq.size srcs).
          { rewrite srcs_size.
              by move: prf => /andP []. }
          rewrite size__eq andTb.
          apply /andP.
          split.
          * apply /(all_nthP (Omega, Omega)).
            move => n n__lt.
            apply /subtypeMachineP.
            rewrite nth_zip /=; last by rewrite (eqP size__eq).
            apply: (BCD__Trans (nth Omega m.1 n)).
            ** apply /subtypeMachineP.
               move: prf => /andP [] /eqP msize__eq /andP [].
               move => /(all_nthP (Omega, Omega)).
               rewrite size_zip -srcs_size -size_zip.
               move => /(fun prf => prf n n__lt).
                 by rewrite nth_zip /=.
            ** apply /subtypeMachineP.
               move: srcs_prf => /(all_nthP (Omega, Omega)).
               rewrite size_zip (eqP (proj1 (andP prf))) -size_zip.
               move => /(fun prf => prf n n__lt).
                 by rewrite nth_zip /=.
          * move: tgt_sound_prf => /allP /(fun prf => prf m3) res.
            apply: res.
            rewrite in_cons.
            apply /orP; right.
            apply: mem_subseq; last by exact inprf.
              by apply: reduction_subseq.
        + by rewrite /= prf.
      - move => inprf prf.
        have: (has (fun m2 => [&& (seq.size m2.1 == seq.size srcs),
                            all (fun AB => checkSubtypes AB.1 AB.2) (zip srcs m2.1)
                            & checkSubtypes m2.2 B])
                   (reduceMultiArrows ms)).
        { apply: IH.
          - by move: tgt_sound_prf => /andP [].
          - apply /hasP.
              by (exists m2). }
        rewrite [reduceMultiArrows [:: m & ms]]/=.
        case rest_prf: (has (fun m2 => [&& (seq.size m2.1 == seq.size m.1)
                                     & all (fun AB => checkSubtypes AB.1 AB.2) (zip m.1 m2.1)])
                            (reduceMultiArrows ms)) => //.
        case m_prf: [&& (seq.size m2.1 == seq.size m.1)
                     & all (fun AB => checkSubtypes AB.1 AB.2) (zip m2.1 m.1)].
        + move => _ /=.
          apply /orP; left.
          move: prf => /andP [] /eqP srcs_size /andP [] srcs_prf tgt_prf.
          move: m_prf => /andP [] /eqP msize__eq m_srcs_ge.
          have size__eq: (seq.size m.1 = seq.size srcs).
          { by rewrite -srcs_size msize__eq. }
          rewrite size__eq eq_refl andTb.
          apply /andP.
          split.
          * apply /(all_nthP (Omega, Omega)).
            move => n n__lt.
            apply /subtypeMachineP.
            rewrite nth_zip /=; last by rewrite size__eq.
            apply: (BCD__Trans (nth Omega m2.1 n)).
            ** apply /subtypeMachineP.
               move: srcs_prf => /(all_nthP (Omega, Omega)).
               rewrite size_zip msize__eq -size_zip.
               move => /(fun prf => prf n n__lt).
                 by rewrite nth_zip /=.
            ** apply /subtypeMachineP.
               move: m_srcs_ge => /(all_nthP (Omega, Omega)).
               rewrite size_zip srcs_size -size_zip.
               move => /(fun prf => prf n n__lt).
                 by rewrite nth_zip /=.
          * by move: tgt_sound_prf => /andP [].
        + case hd_prf: [&& seq.size m.1 == seq.size srcs,
                        all (fun AB : IT * IT => checkSubtypes AB.1 AB.2)
                            (zip srcs m.1)
                        & checkSubtypes m.2 B]; first by rewrite /= hd_prf.
          move => /hasP [] m3 inprf__m3 m3_prf.
          apply /hasP.
          exists m3 => //.
          apply: mem_behead => /=.
          rewrite mem_filter inprf__m3 andbT negb_and.
          move: m_prf => /negbT.
          rewrite negb_and.
          move => /orP [].
          * move: prf => /andP [] /eqP -> _.
              by move: m3_prf => /andP [] /eqP -> _ ->.
          * case size__eq: (seq.size m3.1 == seq.size m.1) => //=.
            move: size__eq => /eqP size__eq _.
            rewrite -has_predC.
            move: hd_prf.
            have srcs_size: (seq.size m.1 == seq.size srcs).
            { move: m3_prf => /andP [] /eqP <- _.
                by rewrite size__eq. }
            rewrite srcs_size.
            move: tgt_sound_prf => /andP [] -> _.
            rewrite andbT andTb.
            move => /negbT.
            rewrite -has_predC.
            move => /(has_nthP (Omega, Omega)) [] n n_lt disprf.
            apply /(has_nthP (Omega, Omega)).
            exists n.
            ** move: n_lt.
               do 2 rewrite size_zip.
                 by rewrite size__eq (eqP srcs_size).
            ** rewrite /= -implybF.
               apply /implyP.
               rewrite nth_zip => //=.
               move => /subtypeMachineP le_prf.
               move: disprf.
               rewrite /= -implybF.
               move => /implyP disprf.
               apply: disprf.
               apply /subtypeMachineP.
               rewrite nth_zip; last by rewrite (eqP srcs_size).
               apply: BCD__Trans; last by exact le_prf.
               apply /subtypeMachineP.
               move: m3_prf => /andP [] /eqP m3_size__eq /andP [] /(all_nthP (Omega, Omega)).
               rewrite size_zip size__eq -size_zip.
               move => /(fun prf => prf n n_lt).
                 by rewrite nth_zip.
    Qed.
               
  End PostReductionPhase.
End CoverMachineProperties.
 
Arguments coverMachine [Constructor].
Arguments reduceMultiArrows [Constructor].
Arguments mkArrow [Constructor].
