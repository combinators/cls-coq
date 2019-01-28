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
               do 3 rewrite filterMergeMultiArrows_cat mem_cat.
               rewrite mem_cat map_cat [X in (_ -> _ -> (_ \in X) || _)%type]filterMergeMultiArrows_cat mem_cat.
               move => /orP [].
               *** move => /orP []; last by move => ->; repeat rewrite orbT.
                     by rewrite -map_comp filterMergeMultiArrows_map_cons => ->.
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
             checkSubtypes x.1.2 (\bigcap_(A_i <- behead (x.2)) A_i) ==>
             has (fun y => [&& seq.size y.1 == seq.size x.1.1,
                         all (fun AB => checkSubtypes AB.1 AB.2) (zip x.1.1 y.1) &
                         checkSubtypes y.2 (\bigcap_(A_i <- x.2) A_i)]) s)
          (flatten (map (fun i => map (fun m => (m, if i is ContinueCover _ _ currentResult
                                              then [:: currentResult.2 & toCoverOf i]
                                              else [:: Omega & toCoverOf i]))
                                   (filterMergeMultiArrows (subseqs (mergeComponentsOf i))))
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
    Qed.

    Definition arity_equal (i: @Instruction Constructor): bool :=
      all (fun x => all (fun y => seq.size x.1 == seq.size y.1) (mergeComponentsOf i)) (mergeComponentsOf i).


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

    Lemma map_in_pairWithConst {A B: eqType}:
      forall (xs: seq A) (y: B) xy,
        (xy \in map (fun x => (x, y)) xs) ->
        (xy.2 == y) && (xy.1 \in xs).
    Proof.
      elim => // x xs IH y xy.
      rewrite map_cons in_cons in_cons.
      move => /orP [].
      - move => /eqP ->.
          by rewrite /= eq_refl eq_refl.
      - move => /IH /andP [] -> ->.
          by rewrite orbT.
    Qed.

    Lemma pairWithConst_in_map {A B: eqType}:
      forall (xs: seq A) (y: B) x,
        (x \in xs) ->
        (x, y) \in map (fun x => (x, y)) xs.
    Proof.
      elim => // x1 xs IH y x.
      rewrite map_cons in_cons in_cons.
      move => /orP [].
      - move => /eqP ->.
          by rewrite eq_refl.
      - move => /IH ->.
          by rewrite orbT.
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
      if i is ContinueCover _ toCover currentResult
      then all (fun A => ~~(checkSubtypes currentResult.2 A)) toCover
      else true.

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
          do 3 rewrite (all_cat _ [:: Cover _ _]) all_seq1.
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
          rewrite (all_cat _ [:: ContinueCover _ _ _]) all_seq1.
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
          do 4 rewrite (all_cat _ [:: ContinueCover _ _ _]) all_seq1.
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

    Lemma complete_reverse:
      forall s s1 p1 s2 p2,
        (s1, p1) ~~> (s2, p2) ->
        suffix s2 s ->
        all arity_equal p1 ->
        all not_omega_instruction p1 ->
        all instruction_covered p1 ->
        all toCover_prime p1 ->
        all currentResultNotDone p1 ->
        complete s p2 ->
        complete s p1.
    Proof.
      move => s s1 p1 s2 p2 step s2_suffix.
      move => arity_equal_instructions not_omega_instructions instructions_covered.
      move => prime_instructions notDone complete__p2.
      suff: (complete s (take 1 p1)).
      { move: complete__p2.
        move: (step_programStack _ _ _ _ step).
        move /suffixP => [] p3 /eqP -> /complete_cat /andP [] _ complete__rest complete__head.
        have: (p1 = take 1 p1 ++ behead p1) by case p1 => //= ? ?; rewrite take0.
        move => ->.
          by apply: cat_complete. }
      move: step arity_equal_instructions instructions_covered not_omega_instructions prime_instructions notDone.
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
                                 complete s sp2.2 -> complete s sp1.2)%type)).
      case: i1; case => /=.
      - move => toCover prf instructions_covered.
          by apply: prf.
      - move => [] [] srcs tgt covered splits toCover prf.
        apply: prf.
        + move => partition__eq _ arity_equal__i instructions_covered__i not_omega_instructions__i prime__i _.
          rewrite /complete /= cats0 cats0 filterMergeMultiArrows_cat map_cat all_cat.
          move => prf.
          rewrite prf andbT.
          apply: (introT allP).
          move => [] m toCover' /map_in_pairWithConst /andP [] toCover__eq /filterMergedArrows_in_cons.
          rewrite /= in toCover__eq.
          move: toCover__eq => /eqP ->.
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
            move: prf => /allP /(fun prf => prf (mergeMultiArrows ms, [:: Omega & toCover])
                                            (pairWithConst_in_map _ [:: Omega & toCover] (mergeMultiArrows ms) inprf__merged)).
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
            rewrite {1 3}/fst {2}/fst {3}/fst.
            apply: (BCD__Trans (\bigcap_(A_i <- [:: (srcs, tgt) & ms]) (nth Omega A_i.1 n))).
            ** by apply: mergeMultiArrows_srcs_le.
            ** apply: BCD__Trans; first by apply: (bcd_cat_bigcap_f _ _ (fun x => nth Omega x.1 n) [:: (srcs, tgt)]).
               apply: BCD__Trans; first by apply: (BCD__Lub2).
               apply: mergeMultiArrows_srcs_ge.
               apply: sub_all; last by (move: arity_equal__ms => /andP [] _ restprf; exact restprf).
                 by move => ? /andP [].
        + move => partition__eq1 partition__eq2 s__suffix arity_equal__i instructions_covered__i not_omega_instructions__i prime__i _.
          rewrite /complete /= cats0 cats0 filterMergeMultiArrows_cat map_cat all_cat.
          move => prf.
          rewrite prf andbT.
          apply: (introT allP).
          move => [] m toCover' /map_in_pairWithConst /andP [] toCover__eq /filterMergedArrows_in_cons.
          rewrite /= in toCover__eq.
          move: toCover__eq => /eqP ->.
          move => /orP [].
          * move => /= /eqP -> /=.
            apply: (introT implyP).
            move => tgt__le.
            apply: (introT hasP).
            exists (srcs, tgt).
            ** move: s__suffix => /suffixP [] s__prefix /eqP ->.
                 by rewrite mem_cat mem_head orbT.
            ** rewrite eq_refl /=.
               apply (introT andP).               
               split.
               *** apply: (introT allP).
                   move => ? /zip_eq ->.
                     by apply /subtypeMachineP.
               *** apply /subtypeMachineP.
                   apply: BCD__Trans; last by apply: (bcd_bigcap_cat _ [:: Omega] toCover).
                   apply: BCD__Glb => //=.
                     by apply /subtypeMachineP.
          * move => /hasP [] ms [] inprf /andP [] inprf__merged m__eq.
            move: prf => /allP /(fun prf => prf (mergeMultiArrows ms, toCover)
                                            (pairWithConst_in_map _ toCover (mergeMultiArrows ms) inprf__merged)).
            move => prf.
            apply: (introT implyP).
            move: m__eq => /eqP ->.
            move => le__prf.
            apply: (introT hasP).
            exists (srcs, tgt).
            ** move: s__suffix => /suffixP [] s__prefix /eqP ->.
                 by rewrite mem_cat mem_head orbT.
            ** have arity_equal__ms: (all (fun x => all (fun y => seq.size x.1 == seq.size y.1) [:: (srcs, tgt) & ms])
                                     [:: (srcs, tgt) & ms]).
               {  apply: (introT allP).
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
               move => /(BCD__Glb BCD__omega).
               move => /(fun prf => BCD__Trans _ prf (bcd_bigcap_cat _ [:: Omega] _)).
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
          rewrite /complete /= cats0 cats0 filterMergeMultiArrows_cat all_cat.
          move => /andP [] prf1 prf2.
          rewrite map_cat all_cat prf2 andbT.
          move: prf2 prf1 => _.
          rewrite map_cat all_cat.
          move => /andP [] prf _.
          apply: (introT allP).
          move => [] m toCover' /map_in_pairWithConst /andP [] toCover__eq inprf.
          move: (filterMergedArrows_in_cons _ _ _ inprf).
          rewrite /= in toCover__eq.
          move: toCover__eq => /eqP -> /orP [].
          * move => /eqP ->.
            apply: (introT implyP).
            move: instructions_covered__i => /andP [] /andP [] _.
            move => /(complete_partitionCover _ _ _) disprf _ /disprf.
              by move: partition__eq2 => /eqP partition__eq2 /partition__eq2.
          * move => m__shape.
            have: (exists x, splits = [:: x & behead splits]).
            { move: m__shape.
              clear ...
              case: splits => // x ?.
              exists x; done.
            }
            move => [] x splits__cons.
            move: prf inprf.
            rewrite splits__cons.          
            move => /allP /(fun prf => @prf (m, [:: tgt & (partitionCover covered toCover).2])).
            rewrite mem_map; last by move => ? ? [].
            move => prf /prf.
            move: prf => _.
            move => /implyP prf.
            apply: (introT implyP).
            have partition_subset: {subset (partitionCover covered toCover).2 <= toCover}.
            { move: (partitionCover_subseq2 covered toCover).
                by move => /mem_subseq. }
            move => /subtypeMachineP /(fun prf => BCD__Trans _ prf (bcd_subset_f id _ _ partition_subset)).
            have: [bcd ((m, [:: Omega & toCover]).1.2) <= tgt].
            { move: m__shape => /hasP [] ms inprf__ms /andP [] inprf__merge /eqP ->.
              apply: BCD__Trans; first by apply: mergeMultiArrows_tgt_le.
                by apply: BCD__Trans; first by apply: (bcd_cat_bigcap_f _ _ snd [:: (srcs, tgt)]). }
            move => /BCD__Glb mk__le /mk__le.
            move: mk__le => _ /(fun prf => BCD__Trans _ prf BCD__Lub2).
            move => /subtypeMachineP /prf.
            apply: sub_has.
            move => A /andP [] -> /andP [] ->.
            rewrite [X in (_ -> X)%type]/=.
            move => /subtypeMachineP /BCD__Trans res.
            apply /subtypeMachineP.
            apply: res.
            apply: BCD__Trans; last by apply: (bcd_bigcap_cat _ [:: Omega] _).
            apply: BCD__Glb; first by apply: BCD__omega.
            apply: BCD__Trans; last by apply: (partition_cover_both covered).
            apply: BCD__Trans; last by apply: bcd_bigcap_cat.
            apply: BCD__Trans; first by apply: (bcd_cat_bigcap _ [:: tgt]).
            apply: BCD__Glb => //.
            apply: BCD__Trans; first by apply: BCD__Lub1.
            apply: BCD__Trans;
              first by (move: instructions_covered__i => /andP [] /andP [] /subtypeMachineP res *; exact res).
            apply: bcd_subset_f.
              by move: (partitionCover_subset covered toCover) => /allP.
      - move => toCover currentResult prf instructions_covered.
        apply: prf => //.
        rewrite /complete [map _ _]/= [flatten _]/= all_nil.
        move => _ _ _ /andP [] notEmpty _ _ /(notDone_incomplete _ _ notEmpty) /implyP disprf _.
        rewrite [map _ _]/= [flatten _]/= all_seq1.
        apply: (introT implyP).
          by move => /disprf.
      - move => [] [] srcs tgt covered splits toCover currentResult prf.
        apply: prf.
        + move => partition__eq _ arity_equal__i instructions_covered__i not_omega_instructions__i prime__i notDone.
          rewrite /complete /= cats0 cats0.
          rewrite filterMergeMultiArrows_cat map_cat all_cat.
          move => /andP [] prf1 prf2.
          rewrite filterMergeMultiArrows_cat map_cat all_cat.
          rewrite filterMergeMultiArrows_cat map_cat map_cat all_cat.
          rewrite filterMergeMultiArrows_cat map_cat all_cat.
          rewrite prf2 andbT.
          rewrite prf1 andbT.
          apply: (introT andP).
          split.
          * apply: (introT allP).
            move => [] m toCover' /map_in_pairWithConst /andP [] toCover__eq.
            rewrite filterMergeMultiArrows_map_cons2.
            move => /filterMergedArrows_in_cons.
            rewrite /= in toCover__eq.
            move: toCover__eq => /eqP ->.
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
               move: prf2 => /allP /(fun prf => prf (mergeMultiArrows ms, [:: currentResult.2 & toCover])
                                                (pairWithConst_in_map _ [:: currentResult.2 & toCover]
                                                                      (mergeMultiArrows ms) inprf__merged)).
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
                 apply: sub_all; last by (move: arity_equal__i => /andP [] _ arity_equal__i; exact arity_equal__i).
                 move => x /= /andP [] _ /andP [] -> /allP subprf /=.
                 apply: (introT allP).
                 move => z z__in.
                 apply: subprf.
                 apply: mem_subseq; last by exact z__in.
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
               have y__size_srcs: (seq.size y.1 == seq.size ((mergeMultiArrows [:: (mergeMultiArrow currentResult srcs tgt) & ms]).1)).
               { rewrite y__size eq_sym.
                   by rewrite (mergeMultiArrows_cons_arity (mergeMultiArrow currentResult srcs tgt) ms ms__nonEmpty);
                     first by rewrite /= eq_refl.  }
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
            rewrite {1 3}/fst {2}/fst {3}/fst.
            apply: (BCD__Trans (\bigcap_(A_i <- [:: mergeMultiArrow currentResult srcs tgt & ms]) (nth Omega A_i.1 n))).
            *** by apply: mergeMultiArrows_srcs_le.
            *** apply: BCD__Trans; first by apply: (bcd_cat_bigcap_f _ _ (fun x => nth Omega x.1 n)
                                                                   [:: mergeMultiArrow currentResult srcs tgt]).
                apply: BCD__Trans; first by apply: (BCD__Lub2).
                apply: mergeMultiArrows_srcs_ge.
                apply: sub_all; last by (move: arity_equal__ms => /andP [] _ restprf; exact restprf).
                  by move => ? /andP [].
          * apply: (introT allP).
            move => [] m toCover' /map_in_pairWithConst /andP [] toCover__eq /filterMergedArrows_in_cons.
            rewrite /= in toCover__eq.
            move: toCover__eq => /eqP ->.
            move => /orP [].
            ** move => /= /eqP -> /=.
               rewrite implybE.
               apply: (introT orP); left.
               apply: (introT negP).
               move: prf1 prf2 notDone arity_equal__i prime__i instructions_covered__i partition__eq not_omega_instructions__i => _ _ _ _ _.
               case: toCover => // path [].
               *** rewrite /instruction_covered /= andbT.
                   case tgt__le: (checkSubtypes tgt path) => //.
                     by move => /andP [] /andP [] _ /implyP /(fun prf => prf isT) -> _ /= [] /eqP /nilP.
               *** move => p toCover /andP [] /andP [] _ /andP [] disprf _ _ partition__eq not_omega.
                   rewrite map_cons.
                   move => /subtypeMachineP /(fun prf => BCD__Trans _ prf (bcd_cat_bigcap _ [:: path] [:: p & toCover])).
                   move => /(fun prf => BCD__Trans _ prf BCD__Lub1) /subtypeMachineP prf.
                   move: disprf partition__eq => /implyP /(fun disprf => disprf prf).
                   rewrite [partitionCover _ _]/= [snd (_, _)]/=.
                   case: (partitionCover covered toCover).
                     by case: (p \in covered) => ? ? -> /= /eqP /nilP.
            ** move => /hasP [] ms [] inprf /andP [] inprf__merged m__eq.
               move: prf2 => /allP /(fun prf => prf (mergeMultiArrows ms, [:: currentResult.2 & toCover])
                                                (pairWithConst_in_map _ [:: currentResult.2 & toCover]
                                                                      (mergeMultiArrows ms) inprf__merged)).
               move: prf1 => _ prf.
               apply: (introT implyP).
               move: m__eq => /eqP ->.
               move => /subtypeMachineP /(BCD__Trans _ (mergeMultiArrows_tgt_ge _)).
               move: instructions_covered__i => /covered_head_tgt [] prf1 prf2.
               move => /(partitionCover_prime (srcs, tgt) ms covered toCover prime__i prf1 prf2) [] _.
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
                 apply: sub_all; last by (move: arity_equal__i => /andP [] _ arity_equal__i; exact arity_equal__i).
                 move => x /= /andP [] _ /andP [] -> /allP subprf /=.
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
            rewrite {1 3}/fst {2}/fst {3}/fst.
            apply: (BCD__Trans (\bigcap_(A_i <- [:: (srcs, tgt) & ms]) (nth Omega A_i.1 n))).
            *** by apply: mergeMultiArrows_srcs_le.
            *** apply: BCD__Trans; first by apply: (bcd_cat_bigcap_f _ _ (fun x => nth Omega x.1 n) [:: (srcs, tgt)]).
                apply: BCD__Trans; first by apply: (BCD__Lub2).
                apply: mergeMultiArrows_srcs_ge.
                apply: sub_all; last by (move: arity_equal__ms => /andP [] _ restprf; exact restprf).
                  by move => ? /andP [].
        + move => partition__eq1 partition__eq2 s__suffix arity_equal__i instructions_covered__i not_omega_instructions__i prime__i notDone.
          rewrite /complete /= cats0 cats0.
          rewrite filterMergeMultiArrows_cat map_cat all_cat.
          move => /andP [] prf1 prf2.
          rewrite filterMergeMultiArrows_cat map_cat all_cat.
          rewrite filterMergeMultiArrows_cat map_cat map_cat all_cat.
          rewrite filterMergeMultiArrows_cat map_cat all_cat.
          rewrite prf2 andbT.
          rewrite prf1 andbT.
          apply: (introT andP).
          split.
          * admit.
          * apply: (introT allP).
            move => [] m toCover' /map_in_pairWithConst /andP [] toCover__eq /filterMergedArrows_in_cons.
            rewrite /= in toCover__eq.
            move: toCover__eq => /eqP ->.
            move => /orP [].
            ** move => /= /eqP -> /=.
               apply: (introT implyP).
               move => tgt__le.
               apply: (introT hasP).
               exists (mergeMultiArrow currentResult srcs tgt).
               *** move: s__suffix => /suffixP [] s__prefix /eqP ->.
                     by rewrite mem_cat mem_head orbT.
               *** have arity_equal__srcs: (seq.size (mergeMultiArrow currentResult srcs tgt).1 = seq.size srcs).
                   { rewrite /= size_map size_zip.
                     move: arity_equal__i => /andP [] /andP [] _ /andP [] /eqP ->.
                       by rewrite minnn. }
                   rewrite arity_equal__srcs eq_refl andTb.
                   apply (introT andP).
                   split.
                   **** apply: (introT allP).

                        move => x inprf__x /(nth_index (Omega, Omega)).
                        rewrite (nth_zip Omega Omega (index x (zip srcs (mergeMultiArrow currentResult srcs tgt).1))
                                         (Logic.eq_sym arity_equal__srcs)).
                        move => <- /=.

                        move: (mergeMultiArrows_srcs_ge
                        move => ? /zip_eq ->.
                     by apply /subtypeMachineP.
               *** apply /subtypeMachineP.
                   apply: BCD__Trans; last by apply: (bcd_bigcap_cat _ [:: Omega] toCover).
                   apply: BCD__Glb => //=.
                     by apply /subtypeMachineP.
          * move => /hasP [] ms [] inprf /andP [] inprf__merged m__eq.
            move: prf => /allP /(fun prf => prf (mergeMultiArrows ms, toCover)
                                            (pairWithConst_in_map _ toCover (mergeMultiArrows ms) inprf__merged)).
            move => prf.
            apply: (introT implyP).
            move: m__eq => /eqP ->.
            move => le__prf.
            apply: (introT hasP).
            exists (srcs, tgt).
            ** move: s__suffix => /suffixP [] s__prefix /eqP ->.
                 by rewrite mem_cat mem_head orbT.
            ** have arity_equal__ms: (all (fun x => all (fun y => seq.size x.1 == seq.size y.1) [:: (srcs, tgt) & ms])
                                     [:: (srcs, tgt) & ms]).
               {  apply: (introT allP).
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
               move => /(BCD__Glb BCD__omega).
               move => /(fun prf => BCD__Trans _ prf (bcd_bigcap_cat _ [:: Omega] _)).
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

