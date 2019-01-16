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

  Definition Semantics := clos_refl_trans_1n _ StepSemantics.
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
    end.

  Lemma stepSize:
    forall sp1 sp2,
      sp1 ~~> sp2 ->
      (\sum_(i <- sp2.2) (3 ^ (seq.size (splitsOf i)))) < \sum_(i <- sp1.2) (3 ^ (seq.size (splitsOf i))).
  Proof.
    move => sp1 sp2 /CoverMachine_inv.
    move => /(fun res => res (fun sp1 sp2 => (\sum_(i <- sp2.2) (3 ^ (seq.size (splitsOf i))))
                                      < \sum_(i <- sp1.2) (3 ^ (seq.size (splitsOf i))))).
    case: sp1 => s1 p1.
    case: sp2 => s2 p2.
    case: p1 => // i p1.
    case: i.
    - case.
      + move => toCover res.
        apply: res.
        rewrite unlock /=.
          by rewrite -[X in X < _]add0n ltn_add2r.
      + move => [] [] srcs tgt covered splits toCover res.
        apply: res.
        * by rewrite unlock /= ltn_add2r ltn_exp2l.
        * by rewrite unlock /= ltn_add2r ltn_exp2l.
        * by rewrite unlock /= addnA ltn_add2r expnS addnn -mul2n ltn_pmul2r //= expn_gt0.
    - case.
      + move => toCover currentResult res.
        apply: res.
        by rewrite unlock /= -[X in X < _]add0n ltn_add2r.
      + move => [] [] srcs tgt covered splits toCover currentResult res.
        apply: res.
        * by rewrite unlock /= ltn_add2r ltn_exp2l.
        * by rewrite unlock /= ltn_add2r ltn_exp2l.
        * by rewrite unlock /= ltn_add2r ltn_exp2l.
        * by rewrite unlock /= addnA ltn_add2r expnS addnn -mul2n ltn_pmul2r //= expn_gt0.
  Qed.

  Lemma maxSteps:
    forall n sp1 sp2, sp1 ~~>[n] sp2 -> n <= \sum_(i <- sp1.2) (3 ^ (seq.size (splitsOf i))).
  Proof.
    move => n sp1 sp2 prf.
    elim: n sp1 sp2 / prf.
    - case => s p /=.
        by case p.
    - move => n sp1 sp2 sp3 prf1 prf2 IH.
      apply: leq_ltn_trans; first by exact IH.
        by apply: stepSize.
  Qed.

  Definition step s1 p1: (p1 = [::]) + { sp2 | (s1, p1) ~~> sp2 } :=
    match p1 as p1 return (p1 = [::]) + { sp2 | (s1, p1) ~~> sp2 } with
    | [::] => inl (Logic.eq_refl _)
    | [:: Cover [::] toCover  & p1 ] => inr (exist _ (s1, p1) step__done)
    | [:: ContinueCover [::] toCover currentResult  & p1 ] => inr (exist _ (s1, p1) step__doneContinue)
    | [:: Cover [:: (srcs, tgt, covered) & splits ] toCover  & p1 ] =>
      inr (let pc := partitionCover covered toCover in
           match boolP (pc.1 == [::]) with
           | AltTrue noFresh =>
             exist _ (s1, [:: Cover splits toCover & p1]) (step__skip noFresh)
           | AltFalse fresh =>
             match boolP (pc.2 == [::]) with
             | AltTrue noLeft =>
               exist _ ([:: (srcs, tgt) & s1],
                        [:: Cover splits toCover & p1]) (step__addDone fresh noLeft)
             | AltFalse someLeft =>
               exist _ (s1, [:: ContinueCover splits pc.2 (srcs, tgt), Cover splits toCover & p1])
                     (step__continue fresh someLeft)
             end
           end)
    | [:: ContinueCover [:: (srcs, tgt, covered) & splits ] toCover currentResult  & p1 ] =>
      inr (let pc := partitionCover covered toCover in
           match boolP (pc.1 == [::]) with
           | AltTrue noFresh =>
             exist _ (s1, [:: ContinueCover splits toCover currentResult & p1]) (step__skipContinue noFresh)
           | AltFalse fresh =>
             match boolP (pc.2 == [::]) with
             | AltTrue noLeft =>
               exist _ ([:: mergeMultiArrow currentResult srcs tgt & s1],
                        [:: ContinueCover splits toCover currentResult & p1]) (step__mergeDone fresh noLeft)
             | AltFalse someLeft =>
               let ma := (mergeMultiArrow currentResult srcs tgt) in
               match boolP (ma.1 == currentResult.1) with
               | AltTrue redundant =>
                 exist _ (s1, [:: ContinueCover splits pc.2 ma & p1])
                       (step__continueMergeAlways fresh someLeft redundant)
               | AltFalse notRedundant =>
                 exist _ (s1, [:: ContinueCover splits pc.2 ma, ContinueCover splits toCover currentResult & p1])
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
    move: (\sum_(i <- sp1.2) 3 ^ seq.size (splitsOf i)) => k.
    move: sp1.
    apply: (fun start step => nat_rect
                             (fun k =>
                                (forall sp1,
                                    (forall n sp2, (sp1 ~~>[ n] sp2 -> n <= k)%type) ->
                                    exists (n : nat) (s2 : State), sp1 ~~>[ n] (s2, [::]))%type)
                             start step k).
    - move => [] s1 p1 limit.
      exists 0, s1.
      case: (step s1 p1).
      + by move => ->.
      + by move => [] sp2 /(fun prf => MoreSteps 0 _ _ _ prf (Done _)) /limit.
    - move: k => _ k IH [] s1 p1 limit.
      case: (step s1 p1).
      + move => ->.
          by exists 0, s1.
      + move => [] sp2 prf.
        suff: (exists n s2, sp2 ~~>[n] (s2, [::])).
        { move => [] n [] s2 prfs.
          exists n.+1, s2.
            by apply: MoreSteps; first by exact prf. }
        apply: IH.
          by move => n sp3 /(MoreSteps _ _ _ _ prf) /limit.
  Qed.

  Lemma step_last: forall s p, p = [::] -> (s, p) ~~>[*] (s, [::]).
  Proof.
    move => s p <-.
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

  Lemma step_next: forall s1 p1 s2 p2 s3, (s1, p1) ~~> (s2, p2) -> (s2, p2) ~~>[*] (s3, [::]) -> (s1, p1) ~~>[*] (s3, [::]).
  Proof.
    move => s1 p1 s2 p2 s3 prf prfs.
      by apply: rt1n_trans; first by exact prf.
  Qed.

  Fixpoint coverMachine_rec s1 p1 (dom: Domain (s1, p1)) {struct dom}: { s | (s1, p1) ~~>[*] (s, [::])} :=
    match step s1 p1 return { s | (s1, p1) ~~>[*] (s, [::])} with
    | inl prf => exist _ s1 (step_last _ _ prf)
    | inr (exist (s2, p2) prf) =>
      let (s, prfs) := coverMachine_rec s2 p2 (Domain_continue _ _ dom prf) in
      exist _ s (step_next _ _ _ _ _ prf prfs)
    end.

  Definition coverMachine sp : { s | sp ~~>[*] (s, [::])} :=
    match sp with | (s, p) => coverMachine_rec s p (Domain_total (s, p)) end.

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

    Lemma mergeMultiArrows_src_size:
      forall ms, seq.size (mergeMultiArrows ms).1 = \big[minn/0%N]_(m_i <- ms) (seq.size m_i.1).
    Proof.
      rewrite /mergeMultiArrows.
      case.
      - by rewrite unlock.
      - move => m ms.
        move: m.
        elim: ms.
        + rewrite unlock /=.
        rewrite unlock /= => <-.





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
        all (fun i2 => splitsOf i2 == behead (splitsOf i1)) (take (seq.size p2 - seq.size p1) p2).
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
    Qed.



    Lemma step_mergeComponents_in:
      forall s1 i1 p1 s2 p2,
        (s1, [:: i1 & p1]) ~~> (s2, p2) ->
        all (fun i2 => if i2 is ContinueCover _ _ currentResult
                    then currentResult \in filterMergeMultiArrows (subseqs (mergeComponentsOf i1))
                    else true) (take (seq.size p2 - seq.size p1) p2).
    Proof.
      move => s1 i1 p1 s2 p2 /CoverMachine_inv.
      move => /(fun prf => prf (fun sp1 sp2 =>
                              if sp1.2 is [:: i1 & p1]
                              then all (fun i2 =>  if i2 is ContinueCover _ _ currentResult
                                                then currentResult \in filterMergeMultiArrows (subseqs (mergeComponentsOf i1))
                                                else true)
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
                   (prefix = [:: ContinueCover splits1 (partitionCover covered toCover).2 (srcs, tgt) ; Cover splits1 toCover])).
            { move: res.
              move => /(fun res =>
                         res (fun sp1 sp2 =>
                                let prefix := take (seq.size sp2.2 - seq.size (behead sp1.2)) sp2.2 in
                                (prefix = [:: Cover splits1 toCover]) \/
                                (prefix = [:: ContinueCover splits1 (partitionCover covered toCover).2 (srcs, tgt) ;
                                           Cover splits1 toCover]))).
              rewrite size_cat /= addnK take_cat ltnn subnn take0 cats0.
              move => res.
              apply: res.
              - rewrite -add1n addnK take0.
                move => _.
                  by left.
              - rewrite -add1n addnK take0.
                move => _.
                  by left.
              - move => _ _.
                rewrite -add2n addnK take0.
                  by right. }
            move => prf.
            move: inPrefix.
            case: prf => ->.
            ** rewrite mergedMultiArrows_cat mem_cat mem_cat orbF /=.
               move => ->.
                 by rewrite orbT.
            ** rewrite mergedMultiArrows_cat /= cats0 mem_cat mem_cat mergedMultiArrows_cat mem_cat.
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
                   (prefix = [:: ContinueCover splits1 (partitionCover covered toCover).2
                                 (mergeMultiArrow currentResult srcs tgt);
                              ContinueCover splits1 toCover currentResult])).
            { move: res.
              move => /(fun res =>
                         res (fun sp1 sp2 =>
                                let prefix := take (seq.size sp2.2 - seq.size (behead sp1.2)) sp2.2 in
                                (prefix = [:: ContinueCover splits1 toCover currentResult]) \/
                                (prefix = [:: ContinueCover splits1 (partitionCover covered toCover).2
                                              (mergeMultiArrow currentResult srcs tgt)]) \/
                                (prefix = [::  ContinueCover splits1 (partitionCover covered toCover).2
                                               (mergeMultiArrow currentResult srcs tgt);
                                           ContinueCover splits1 toCover currentResult]))).
              rewrite size_cat /= addnK take_cat ltnn subnn take0 cats0.
              move => res.
              apply: res.
              - rewrite -add1n addnK take0.
                move => _.
                  by left.
              - rewrite -add1n addnK take0.
                move => _.
                  by left.
              - move => _ _ _.
                rewrite -add1n addnK take0.
                  by right; left.
              - move => _ _ _.
                rewrite -add2n addnK take0.
                  by right; right. }
            move => prf.
            move: inPrefix.
            case: prf; last case; move => ->.
            ** rewrite mergedMultiArrows_cat mem_cat mem_cat orbF /=.
               rewrite map_cat [X in (_ -> _ -> (_ \in X) || _)%type]mergedMultiArrows_cat mem_cat.
               do 2 rewrite mergedMultiArrows_cat mem_cat.
                 by move => /orP [] ->; repeat rewrite orbT.
            ** rewrite mergedMultiArrows_cat mem_cat mem_cat orbF /=.
               rewrite map_cat [X in (_ -> _ -> (_ \in X) || _)%type]mergedMultiArrows_cat mem_cat.
               do 2 rewrite mergedMultiArrows_cat mem_cat.
               move => /orP []; last by move => ->; repeat rewrite orbT.
                 by rewrite -map_comp mergedMultiArrows_map_cons => ->.
            ** rewrite mergedMultiArrows_cat mem_cat mem_cat orbF /=.
               do 3 rewrite mergedMultiArrows_cat mem_cat.
               rewrite mem_cat map_cat [X in (_ -> _ -> (_ \in X) || _)%type]mergedMultiArrows_cat mem_cat.
               move => /orP [].
               *** move => /orP []; last by move => ->; repeat rewrite orbT.
                     by rewrite -map_comp mergedMultiArrows_map_cons => ->.
               *** by move => /orP [] ->; repeat rewrite orbT.
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
      end.

    Definition complete s p :=
      all (fun x =>
             checkSubtypes x.1.2 (\bigcap_(A_i <- x.2) A_i) ==>
             has (fun y => [&& seq.size y.1 == seq.size x.1.1,
                         all (fun AB => checkSubtypes AB.1 AB.2) (zip x.1.1 y.1) &
                         checkSubtypes y.2 (\bigcap_(A_i <- x.2) A_i)]) s)
          (flatten (map (fun i => map (fun m => (m, toCoverOf i))
                                   (mergedMultiArrows (subseqs (mergeComponentsOf i))))
                        p)).

    Lemma complete_cat:
      forall s p1 p2, complete s (p1 ++ p2) -> complete s p1 && complete s p2.
    Proof.
      move => s p1 p2 /allP prf.
      rewrite /complete.
      apply: (introT andP).
      split.
      - apply: (introT allP).
        move => x inprf.
        apply: prf.
          by rewrite map_cat flatten_cat mem_cat inprf.
      - apply: (introT allP).
        move => x inprf.
        apply: prf.
          by rewrite map_cat flatten_cat mem_cat inprf orbT.
    Qed.

    Lemma cat_complete:
      forall s p1 p2, complete s p1 -> complete s p2 -> complete s (p1 ++ p2).
    Proof.
      move => s p1 p2 /allP prf1 /allP prf2.
      apply: (introT allP).
      move => x.
      rewrite map_cat flatten_cat mem_cat.
      move => /orP [].
      - by apply: prf1.
      - by apply: prf2.
    Qed.

    Definition instruction_covered (i: @Instruction Constructor): bool :=
      all (fun mps => all (fun A => (checkSubtypes mps.1.2 A) ==> (A \in mps.2)) (toCoverOf i)) (splitsOf i).

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
            move: covered2 => /allP /(fun prf => prf x inprf) /allP covered2.
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
            move: covered2 => /allP /(fun prf => prf x inprf) /allP covered2.
            apply: (introT allP) => y inprf2.
            apply: covered2.
            move: (partitionCover_subseq2 covered toCover) => /mem_subseq res.
              by apply: res.
          * move => _ _ _ /= /andP [] covered1 ->.
            move: covered1.
            rewrite /instruction_covered /= => /andP [] /= covered1 covered2.
            rewrite andbT covered2 andbT.
            apply: (introT allP) => x inprf.
            move: covered2 => /allP /(fun prf => prf x inprf) /allP covered2.
            apply: (introT allP) => y inprf2.
            apply: covered2.
            move: (partitionCover_subseq2 covered toCover) => /mem_subseq res.
              by apply: res.
    Qed.

    Definition not_omega_instruction (i: @Instruction Constructor): bool :=
      toCoverOf i != [::].

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
          by rewrite /not_omega_instruction /= => ->.
      - by move => ? ? ? prf; apply: prf => /andP [].
      - move => [] [] srcs tgt covered splits toCover currentResult p1 prf.
        apply: prf => //=.
        + move => _.
            by rewrite /not_omega_instruction /= => -> _ /andP [].
        + move => _.
            by rewrite /not_omega_instruction /= => ->.
    Qed.

    (*Lemma mergeMultiArrows_coContra:
      forall m ms, foldl (fun s m => mergeMultiArrows mergedMultiArrows ms*)

    Definition arity_equal (i: @Instruction Constructor): bool :=
      all (fun x => all (fun y => seq.size x.1 == seq.size y.1) (mergeComponentsOf i)) (mergeComponentsOf i).

    Lemma mergedMultiArrowsA:
      forall (m: @MultiArrow Constructor) m1 ms,
        let m1ms := foldl (fun m__s m => mergeMultiArrow m__s m.1 m.2) m1 ms in
        let mm1ms := foldl (fun m__s m => mergeMultiArrow m__s m.1 m.2) m [:: m1 & ms] in
        [&& seq.size (mergeMultiArrow m m1ms.1 m1ms.2).1 == seq.size mm1ms.1,
         all (fun m1m2 =>
                (checkSubtypes m1m2.1 m1m2.2) && (checkSubtypes m1m2.2 m1m2.1))
             (zip (mergeMultiArrow m m1ms.1 m1ms.2).1 mm1ms.1),
         (checkSubtypes (mergeMultiArrow m m1ms.1 m1ms.2).2 mm1ms.2)
         & (checkSubtypes mm1ms.2 (mergeMultiArrow m m1ms.1 m1ms.2).2)].
    Proof.
      move => m m1 ms.
      move: m m1.
      elim: ms => /=.
      - admit.
      - move => m2 ms IH m m1.
        move: (IH (mergeMultiArrow m m1.1 m1.2) m2).
        move => /andP [] /eqP <-.
        do 2 rewrite size_map size_zip.
        




    Lemma mergedMultiArrowsA:
      forall (P: @MultiArrow Constructor -> Prop),
        (forall  m1 m2 m3,
            P (mergeMultiArrow m1
                               (mergeMultiArrow m2 m3.1 m3.2).1
                               (mergeMultiArrow m2 m3.1 m3.2).2) ->
            P (mergeMultiArrow (mergeMultiArrow m1 m2.1 m2.2) m3.1 m3.2)) ->
        forall m ms, P (if ms is [:: m1 & ms]
                   then
                     mergeMultiArrow m
                                     (foldl (fun m__s m => mergeMultiArrow m__s m.1 m.2) m1 ms).1
                                     (foldl (fun m__s m => mergeMultiArrow m__s m.1 m.2) m1 ms).2
                   else m) ->
                P (foldl (fun m__s m => mergeMultiArrow m__s m.1 m.2) m ms).
    Proof.
      move => P P__assoc m ms prf.
      have: (P (if ms is [:: m1 & ms]
                   then
                     mergeMultiArrow m
                                     (foldr (fun m__s m => mergeMultiArrow m m__s.1 m__s.2) m1 (rev ms)).1
                                     (foldr (fun m__s m => mergeMultiArrow m m__s.1 m__s.2) m1 (rev ms)).2
                else m)).
      { move: prf.
        case: ms => // m1 ms.
          by rewrite -(revK ms) foldl_rev revK. }
      rewrite -(revK ms) foldl_rev.
      move: prf => _.
      move: m.
      move size__eq: (seq.size (rev ms)) => n.
      move: size__eq => /eq_leq.
      move: ms.
      elim: n.
      - admit.
      - move => n IH ms.
        case: (rev ms) => //= m1 msr.
        case: msr => //= m2 msr.
        rewrite -addn1 -[X in (_ <= X -> _)%type]addn1 leq_add2r.
        move => size__leq m prf.
        apply P__assoc.
        rewrite -/(foldr (fun m__s m => mergeMultiArrow m m__s.1 m__s.2)
                         (foldr (fun m__s m => mergeMultiArrow m m__s.1 m__s.2) m msr)
                         [:: (mergeMultiArrow m2 m1.1 m1.2)]).
        rewrite -foldr_cat.
        rewrite -(revK ([:: mergeMultiArrow m2 m1.1 m1.2] ++ msr)).
        apply: IH.
        + admit.
        + rewrite revK.
          move: prf.
          move: ms size__leq => _ _.
          rewrite /= rev_cons rev_cons rev_cons.
          case: (rev msr) => //= m3 ms.
          rewrite rev_rcons rev_rcons.
          have: ([:: m1, m2 & rev ms] = [:: m1; m2] ++ rev ms) by done.
          move => ->.
          rewrite foldr_cat rev_rcons [mergeMultiArrow]lock /= -lock.
          move => prf.
          apply: P__assoc.




          

      
      

      rewrite -(revK ms) foldl_rev.
      

      move msr__eq: (rev ms) => msr.
      move: msr__eq.
      case: msr => // m1 msr.
      elim: msr => //= m2 msr ms__eq prf.
      apply: P__assoc.
      move: prf.

      rewrite -ms__eq.

      


      rewrite /=.
      apply: P__assoc.

      move: ms m.
      apply: last_ind => // ms m1 IH m.
      rewrite rev_rcons /=.
      move: IH.
      case: (rev ms) => //= m2 msr IH prf.
      apply: P__assoc.
      apply: IH.

      



      move: m.
      move n__eq: (seq.size ms) => n.
      move: n__eq => /eq_leq.
      move: ms.
      elim: n.
      - move => ms.
        rewrite leqn0.
          by move => /eqP /size0nil ->.
      - move => n IH [] //= m1 ms.
        rewrite -addn1 -[X in (_ <= X -> _)%type]addn1 leq_add2r.
        move => size__leq m prf.
        apply: IH => //.
        move: prf.
        rewrite -(revK ms) foldl_rev.
        

        case: ms =
        apply IH.
        + by move: size__leq => /ltnW.
        + move: prf size__leq.
          case: ms.
          * by rewrite /foldl => /P__assoc.
          * move => ? ? ? ?.
            apply: P__assoc.




    Lemma complete_reverse:
      forall s s1 p1 s2 p2,
        (s1, p1) ~~> (s2, p2) ->
        suffix s2 s ->
        all arity_equal p1 ->
        all not_omega_instruction p1 ->
        all instruction_covered p1 ->
        complete s p2 ->
        complete s p1.
    Proof.
      move => s s1 p1 s2 p2 step s2_suffix arity_equal_instructions not_omega_instructions instructions_covered complete__p2.
      suff: (complete s (take 1 p1)).
      { move: complete__p2.
        move: (step_programStack _ _ _ _ step).
        move /suffixP => [] p3 /eqP -> /complete_cat /andP [] _ complete__rest complete__head.
        have: (p1 = take 1 p1 ++ behead p1) by case p1 => //= ? ?; rewrite take0.
        move => ->.
          by apply: cat_complete. }
      move: step arity_equal_instructions instructions_covered not_omega_instructions.
      case: p1 => //=.
      move => i1 p1 step.
      move: (step_programStack _ _ _ _ step) => /suffixP [] p3 /eqP p2__eq.
      move: step complete__p2.
      rewrite p2__eq.
      move => step.
      move => /complete_cat => /andP [] complete__p3 _.
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
            by apply: prf; move => *; constructor. }
      rewrite take0.
      move: p2 step => _ _ step /andP [] arity_equal__i _ /andP [] covered__i _ /andP [] not_omega__i _.
      move: p1 => _.
      move: step arity_equal__i covered__i not_omega__i complete__p3.
      move => /CoverMachine_inv
              /(fun res => res (fun sp1 sp2 => (
                                 arity_equal (head i1 sp1.2) ->
                                 instruction_covered (head i1 sp1.2) ->
                                 not_omega_instruction (head i1 sp1.2) ->
                                 complete s sp2.2 -> complete s sp1.2)%type)).
      case: i1; case => /=.
      - move => toCover prf instructions_covered.
          by apply: prf.
      - move => [] [] srcs tgt covered splits toCover prf.
        apply: prf.
        + move => partition__eq arity_equal__i instructions_covered__i not_omega_instructions__i.
          rewrite /complete /= cats0 cats0 mergedMultiArrows_cat map_cat all_cat.
          move => prf.
          rewrite prf andbT.
          move: prf.
          elim: (subseqs (map fst splits)) => // ms mss IH.
          rewrite (mergedMultiArrows_cat [:: ms]) map_cons (mergedMultiArrows_cat [:: [:: (srcs, tgt) & ms]]).
          do 2 rewrite map_cat all_cat.
          move => /andP [] prf__ms /IH ->.
          rewrite andbT /= andbT.
          move: prf__ms.
          rewrite /=.
          case: ms => /=.



      

                  


      rewrite take0.




      move => /suffixP.
      move: step => /CoverMachine_inv
                    /(fun res => res (fun sp1 sp2 => (
                                       all not_omega_instruction sp1.2 ->
                                       all instruction_covered sp1.2 ->
                                       complete s sp2.2 ->
                                       complete s sp1.2)%type)).
      case: p1 => // i p1.
      case: i; case.
      - move => toCover prf instructions_covered.
          by apply: prf.
      - move => [] [] srcs tgt covered splits toCover prf.
        apply: prf.
        + move => partition__eq not_omega_instructions instructions_covered /(complete_cat _ [:: _] p1) /andP [] prf1 prf2.
          apply: (cat_complete _ [:: _] p1) => //.
          move:  prf1.
          rewrite /complete /= cats0 mergedMultiArrows_cat all_cat andbT map_cat all_cat.
          move => prf1.
          rewrite prf1 andbT.
          move: prf1.
          elim: (subseqs (map fst splits)) => // ms mss IH.
          rewrite (mergedMultiArrows_cat [:: ms]) map_cons (mergedMultiArrows_cat [:: [:: (srcs, tgt) & ms]]).
          do 2 rewrite map_cat all_cat.
          move => /andP [] prf__ms /IH ->.
          rewrite andbT /= andbT.
          move: prf__ms.
          rewrite /=.
          case: ms => /=.
          * move: instructions_covered => /andP [].
            rewrite /instruction_covered => /andP [] /= disprf _ _.
            suff: (~~ checkSubtypes tgt (\bigcap_(A_i <- toCover) A_i)) by move => /negbTE ->.
            apply: (introT negP).
            move: IH not_omega_instructions disprf partition__eq => _.
            case: toCover => //= path [] /=.
            ** move => _.
                 by case: (checkSubtypes tgt path) => // /andP [] /implyP /(fun prf => prf isT) -> _ /= [] /eqP /nilP.
            ** move => p toCover _ /andP [] disprf _ partition__eq.
               move => /subtypeMachineP /(fun prf => BCD__Trans _ prf (BCD__Lub1)) /subtypeMachineP prf.
               move: disprf partition__eq => /implyP /(fun disprf => disprf prf) ->.
               case: (partitionCover covered toCover).
                 by case: (p \in covered) => ? ? /= /eqP /nilP.
          * admit.
        + admit.
        +admit.
      - 

              


              move => /subtypeMachineP /bcd_bigcap.




          apply: (introT allP).
          move => x.
          rewrite mem_filter => /andP [] prf__le.

          have: (injective (cons (srcs, tgt))); first by move => ? ? [].
          move => /mem_map <-.
          rewrite -(map_eq [x).


          rewrite /complete /=.

*)
      

    Lemma steps_complete:
      forall s1 p1 s2, (s1, p1) ~~>[*] (s2, [::]) -> complete s2 p1.
    Proof.
      move => s1 p1 s2 /nStepSemantics_complete [] n.
      move: s1 p1 s2.
      elim: n.
      - move => s1 p1 s2 /nStepSemantics_inv /(fun res => res (fun _ sp1 sp2 => sp1.2 = sp2.2)).
          by move => /(fun res => res Logic.eq_refl) /= ->.
      - move => n IH s1 p1 s2 /nStepSemantics_inv /(fun prf => prf (fun n sp1 sp2 => complete sp2.1 sp1.2)) prf.
        apply: prf.
        move => [] s3 p3 step steps.
        move: (IH s3 p3 s2 steps).





   
  End StepInvariants.
End CoverMachineProperties.

Recursive Extraction coverMachine.
 
Arguments coverMachine [Constructor].

