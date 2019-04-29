Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Logic.Eqdep_dec.
From mathcomp Require Import all_ssreflect.
Require Import PreOrders.
Require Import Types.
Require Import FCL.
Require Import Algebra.

Set Bullet Behavior "Strict Subproofs".
Open Scope alg_scope.

Import EqNotations.

Section LabyrinthSpec.
  Definition Position: Set := nat * nat.

  Variable free: seq (seq bool).
  Variables goal start: Position.

  Inductive Move: Set := Up | Down | Left | Right.

  Definition Path := seq Move.

  Definition step (from: Position) (m: Move): option Position :=
    let tgt :=
        match m with
        | Down => Some (from.1, from.2.+1)
        | Up => if (from.2 > 0) then Some (from.1, from.2.-1) else None
        | Left => if (from.1 > 0) then Some (from.1.-1, from.2) else None
        | Right => Some (from.1.+1, from.2)
        end in
    if tgt is Some (col, row)
    then if (nth false (nth [::] free row) col)
         then Some (col, row)
         else None
    else None.


  Fixpoint run (path: Path) (start: Position): option Position :=
    if path is [:: m & path]
    then obind (run path) (step start m)
    else Some start.

  Definition Solution (from: Position) := { path : Path | run path from = Some goal }.

  Section MoveMathcompInstances.
    Definition Move2o (m: Move): 'I_4 :=
      match m with
      | Up => inord 0
      | Down => inord 1
      | Left => inord 2
      | Right => inord 3
      end.

    Definition o2Move (o: 'I_4): option Move :=
      match val o with
      | 0 => Some Up
      | 1 => Some Down
      | 2 => Some Left
      | 3 => Some Right
      | _ => None
      end.

    Lemma pcan_Move: pcancel Move2o o2Move.
    Proof. by case; rewrite /Move2o /o2Move /= inordK. Qed.
    Definition Move_eqMixin := PcanEqMixin pcan_Move.
    Canonical Move_eqType := EqType Move Move_eqMixin.
    Definition Move_choiceMixin := PcanChoiceMixin pcan_Move.
    Canonical Move_choiceType := ChoiceType Move Move_choiceMixin.
    Definition Move_countMixin := PcanCountMixin pcan_Move.
    Canonical Move_countType := CountType Move Move_countMixin.
    Definition Move_finMixin := PcanFinMixin pcan_Move.
    Canonical Move_finType := FinType Move Move_finMixin.
  End MoveMathcompInstances.

  Definition S: Type := option Position.
  Definition I: Type :=
    seq_sub (flatten (map (fun n => (foldl (fun s x => (s.1.+1, if x then [:: (s.1, n) & s.2] else s.2))
                                        (0, [::]) (nth [::] free n)).2)
                          (iota 0 (seq.size free)))).

  Definition O: finType :=
    sum_finType unit_finType Move_finType.

  Definition sigSpec__Lab (i: I) (o: O): (seq S * S) :=
    match o with
    | inl tt => if ssval i == goal then ([::], Some goal) else ([::], None)
    | inr m =>
      if step (ssval i) m is Some to then ([:: Some to],  Some (ssval i)) else ([::], None)
    end.

  Definition Sigma__Lab : sigFam I := (@sigFamSpec_Type I (diag_preOrderedType [countType of S]) O sigSpec__Lab).

  Definition C__Lab : forall (c: S), Type := fun c => if c is Some fromPos then Solution fromPos else unit.

  Definition LabAction : forall s, F Sigma__Lab C__Lab s -> C__Lab s.
  Proof.
    move => s x.
    case: x.
    move => i o.
    case: o.
    - rewrite /=.
      move => x args.
      rewrite /[sort _ <= _] /= => /eqP <-.
      rewrite /range /=.
      clear args.
      case: ((ssval i) == goal).
      + case: x => /=.      
          by (exists [::] => /=).
      + by case x.
    - move => m args.
      rewrite /[sort _ <= _] /= => /eqP <-.
      rewrite /range /=.
      move: args.
      rewrite /arity /dom /=.
      move i_eq: (step (ssval i) m) => idx.
      move: i_eq.
      case: idx.
      + move => to to_eq /(fun args => args (inord 0)).
        rewrite /= (tnth_nth None) /= inordK // /=.
        move => toprf.
        exists [:: m & sval toprf].
        rewrite /= /run to_eq /=.
        case: toprf => path pathok /=.
          by rewrite -/run pathok.
      + done.
  Defined.

  Definition Alg__Lab: sigAlg Sigma__Lab := sigAlg_Type LabAction.

  Definition testLabSig := Sigma__Lab.

  Definition Gamma__Lab := Gamma _ testLabSig.
  Definition C__Goal := C__FCL _ testLabSig (Some start).

  Definition result_grammar := inhabit _ _ Gamma__Lab (embed _ testLabSig (Some start)).

  Fixpoint result_terms {Combinator: finType} {Constructor: ctor}
           (G: @TreeGrammar Combinator Constructor) (fuel: nat) (A: @IT Constructor): seq (@Term Combinator) :=
    if fuel is n.+1
    then flatten (map (fun rule =>
                         if rule is RuleCombinator B c
                         then if B == A
                              then [:: (Var c)]
                              else [::]
                         else if rule is RuleApply B C D
                              then if B == A
                                   then (allpairs (@App _) (result_terms G n C) (result_terms G n D))
                                   else [::]
                              else [::]) G)
    else [::].

  Lemma result_terms_words: forall n A M, M \in result_terms (result_grammar) n A -> word result_grammar A M.
  Proof.
    elim => // n IH A M.
    rewrite /result_terms.
    move => /flattenP [] res /mapP [] r.
    case: r.
    - by move => ? _ ->.
    - move => B c.
      case B__eq: (B == A).
      + move => inprf__r ->.
        rewrite mem_seq1 => /eqP -> /=.
        apply /hasP.
        eexists; first by exact inprf__r.
          by rewrite /= (eqP B__eq) eq_refl eq_refl.
      + by move => _ ->.
    - move => B C D.
      case B__eq: (B == A).
      + move => inprf__r -> /allpairsP [] [] M1 M2 [] /IH prf1 /IH prf2 ->.
        rewrite /=.
        apply /hasP.
        eexists; first by exact inprf__r.
          by rewrite /= (eqP B__eq) prf1 prf2 eq_refl.
      + by move => _ ->.
  Qed.

  Definition result_terms_carrier: forall (n: nat), seq C__Goal.
  Proof.
    move => n.
    move: (result_terms_words n (embed _ testLabSig (Some start))) => /allP.
    move: (result_terms _ n (embed _ testLabSig (Some start))).
    elim.
    - move => _.
        by exact [::].
    - move => M Ms IH /andP [] prf /IH results.
      have tychecks: (typeCheck Gamma__Lab M (embed _ testLabSig (Some start))).
      { apply /fclP.
        apply: inhabit_sound.
        exact prf. }
        by exact [:: exist _ M tychecks & results].
  Defined.

  Definition result_terms_mapped (n: nat): seq (C__Lab (Some start)) :=
    map (algebra_morphism__FCL _ _ Alg__Lab (Some start)) (result_terms_carrier n).

End LabyrinthSpec.

Section LabExample.
  Let X := false.
  Let O := true.

  (** Small Test
  Definition free :=
    [::[:: O; O; X; O; O ]
     ; [:: O; X; X; X; O ]
     ; [:: O; X; O; X; O ]
     ; [:: O; X; O; O; O ]
     ; [:: O; O; O; O; O ]
    ].

  Definition goal := (3, 3).
  Definition start := (2, 2). 
   **)

  (** Benchmark **)
  Definition free :=
    [::[:: O; X; O; O; O; O; O; X; O; O; O; O; O; X; O; X; O; O; O; X; O; O; O; X; O; O; O; X; O; O ]
     ; [:: O; O; O; O; O; O; O; O; O; X; O; X; X; O; O; X; X; O; O; O; O; O; O; O; O; O; X; X; X; O ]
     ; [:: O; O; O; O; O; O; O; X; O; X; O; O; O; O; X; O; O; O; O; O; X; X; O; O; X; O; O; X; O; X ]
     ; [:: O; O; O; O; O; X; O; O; X; X; O; O; O; O; O; O; O; O; O; O; O; O; O; O; X; O; O; O; O; X ]
     ; [:: O; O; O; O; O; X; O; O; X; X; O; X; O; X; O; O; X; O; O; O; O; O; O; X; O; O; O; O; O; X ]
     ; [:: O; O; X; X; O; O; O; O; X; O; O; O; O; O; X; O; O; O; X; O; O; O; O; O; X; O; O; O; O; O ]
     ; [:: O; O; O; X; O; X; X; O; O; X; O; O; O; X; O; O; O; O; O; O; O; O; O; O; O; O; O; O; O; O ]
     ; [:: O; O; O; X; O; X; X; O; O; X; X; X; O; O; O; O; X; O; O; O; X; O; O; O; O; X; O; O; X; O ]
     ; [:: O; O; O; X; O; O; X; O; O; X; O; X; O; O; X; X; X; O; X; O; O; O; O; O; X; X; O; X; O; O ]
     ; [:: O; X; X; O; O; O; O; O; O; O; O; O; X; O; O; O; X; O; O; O; O; O; O; O; X; X; O; X; O; O ]
     ; [:: O; X; O; X; O; O; X; O; O; O; O; O; O; O; O; X; O; O; O; X; O; X; O; X; O; O; X; X; O; X ]
     ; [:: O; O; O; X; O; O; O; O; O; X; O; O; O; O; O; X; O; O; X; X; O; X; O; O; O; O; O; O; O; O ]
     ; [:: O; X; O; O; X; X; O; X; X; O; O; O; X; O; O; O; O; O; X; O; O; O; O; O; O; O; O; O; O; O ]
     ; [:: O; O; O; X; O; O; X; O; O; O; O; O; O; O; O; O; X; O; O; O; O; O; O; O; O; O; X; O; O; O ]
     ; [:: X; O; O; X; O; O; X; O; O; O; O; O; X; O; O; X; O; O; O; X; O; O; O; X; O; O; O; O; O; O ]
     ; [:: O; X; X; O; O; O; X; X; O; O; X; X; O; O; X; O; O; X; X; O; O; O; O; O; O; O; X; O; O; O ]
     ; [:: O; O; X; X; O; O; O; O; O; O; O; X; O; O; O; O; O; O; O; O; O; O; O; O; O; X; O; O; O; O ]
     ; [:: O; O; O; O; O; O; O; O; O; O; X; X; O; O; O; X; X; X; O; X; O; O; O; O; O; O; O; O; O; O ]
     ; [:: O; O; O; O; O; X; O; O; O; X; O; X; X; O; O; O; O; O; X; O; O; O; O; O; O; O; O; X; X; O ]
     ; [:: X; X; O; O; X; O; X; O; O; X; X; O; X; O; O; O; O; O; O; O; O; O; O; O; O; X; O; O; O; O ]
     ; [:: O; O; O; X; X; X; O; X; O; O; O; O; O; X; O; O; O; O; O; O; O; O; X; O; X; O; O; O; O; X ]
     ; [:: X; O; O; O; O; O; O; O; O; O; O; X; O; O; O; O; O; O; O; O; O; O; O; O; O; X; O; X; X; O ]
     ; [:: O; O; O; O; O; X; O; O; O; O; O; O; O; O; X; O; X; O; O; X; O; O; O; O; O; O; O; O; O; O ]
     ; [:: O; O; O; X; O; O; O; O; X; O; O; X; O; O; O; O; O; X; O; O; X; O; O; O; O; X; O; X; O; O ]
     ; [:: O; O; O; O; O; O; O; X; O; O; O; O; O; O; O; O; O; X; O; O; O; O; O; O; O; X; X; O; O; O ]
     ; [:: O; O; O; X; O; O; X; O; O; O; O; X; O; O; O; O; O; O; X; X; O; O; O; O; X; O; O; O; X; O ]
     ; [:: X; X; O; O; X; O; O; O; O; X; O; O; O; X; O; O; X; X; O; O; O; O; O; O; O; O; X; X; X; O ]
     ; [:: O; O; O; O; O; O; O; X; O; X; O; X; O; X; O; O; X; X; X; O; O; O; O; O; O; O; O; O; O; O ]
     ; [:: O; O; X; O; X; O; O; O; O; O; X; O; O; O; O; O; X; O; O; X; X; O; X; O; X; O; O; X; O; O ]
     ; [:: O; O; O; O; O; X; O; O; X; X; X; O; O; X; X; O; X; X; O; O; O; X; O; O; O; O; O; O; O; O ]
    ].
  Definition start := (0, 0).
  Definition goal := (seq.size free - 1, seq.size free - 1).
  Example upto100 := (result_terms_mapped free goal start 100).
End LabExample.



Extraction Language Haskell.
Recursive Extraction upto100.
  

