Require Import PeanoNat.
Require Import Coq.Arith.Wf_nat.
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


(*


  Definition changedCover
             (covered: seq (@IT Constructor))
             (toCover: seq (@IT Constructor)): option (seq (@IT Constructor)) :=
    let (coveredFresh, uncovered) := paritionCover covered toCover in
    if coveredFresh is [::] then None else Some uncovered.

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
*)


(** A machine a machine covering paths with multi arrows **)
Section CoverMachine.
  Variable Constructor: ctor.

  Fixpoint paritionCover
             (covered: seq (@IT Constructor))
             (toCover: seq (@IT Constructor)): seq (@IT Constructor) * seq (@IT Constructor) :=
    match toCover with
    | [::] => ([::], [::])
    | [:: A & Delta ] =>
      let (coveredFresh, uncovered) := paritionCover covered Delta in
      if A \in covered
      then ([:: A & coveredFresh], uncovered)
      else (coveredFresh, [:: A & uncovered])
    end.

  (** Small step semantics of the cover machine **)
  Inductive StepSemantics :
    @State Constructor * seq (@Instruction Constructor) -> (@State Constructor) * seq (@Instruction Constructor) -> Prop :=
  | step__done: forall s toCover p,
      (s, [:: Cover [::] toCover & p]) ~~> (s, p)
  | step__doneContinue: forall s toCover currentResult p,
      (s, [:: ContinueCover [::] toCover currentResult & p]) ~~> (s, p)
  | step__skip: forall s src tgt covered splits toCover p,
      ((paritionCover covered toCover).1 == [::]) ->
      (s, [:: Cover [:: (src, tgt, covered) & splits] toCover & p]) ~~> (s, [:: Cover splits toCover & p])
  | step__skipContinue: forall s src tgt covered splits toCover currentResult p,
      ((paritionCover covered toCover).1 == [::]) ->
      (s, [:: ContinueCover [:: (src, tgt, covered) & splits] toCover currentResult & p])
        ~~> (s, [:: ContinueCover splits toCover currentResult & p])
  where "p1 ~~> p2" := (StepSemantics p1 p2).
End CoverMachine.

Arguments StepSemantics [Constructor].
Arguments step__done [Constructor s toCover p].
Arguments step__doneContinue [Constructor s toCover currentResult p].
Arguments step__Arr [Constructor A B1 B2 Delta r].
Arguments step__chooseTgt [Constructor B A Delta Delta' r].
Arguments step__doneTgt [Constructor B].
Arguments step__Prod [Constructor A B1 B2 r1 r2].
Arguments step__Inter [Constructor A B1 B2 r1 r2].
Hint Constructors Semantics.
Notation "p1 ~~> p2" := (Semantics p1 p2).

Arguments slow_cast [Constructor].
Arguments cast [Constructor].