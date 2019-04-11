Require Import Coq.Relations.Relation_Operators.
From mathcomp Require Import all_ssreflect.
Require Import PreOrders.
Require Import Algebra.

Set Bullet Behavior "Strict Subproofs".

Delimit Scope alg_scope with ALG.
Open Scope alg_scope.

Import EqNotations.

Section AutomatonSpec.
  Variable State: finType.
  Definition Config : Type := State * (nat * nat).

  Inductive Transition: Type :=
  | Add : State -> bool -> State -> Transition
  | Sub : State -> bool -> State -> Transition
  | Tst : State -> bool -> State -> State -> Transition.

  Variable transitions: seq Transition.

  Definition step (c: Config) (t: Transition): option Config :=
    match t with
    | Add from useSecond to =>
      if from == c.1
      then Some (to, if useSecond
                     then (c.2.1, c.2.2.+1)
                     else (c.2.1.+1, c.2.2))
      else None
    | Sub from useSecond to =>
      if from == c.1
      then if useSecond && (c.2.2 > 0)
           then Some (to, (c.2.1, c.2.2.-1))
           else if ~~useSecond && (c.2.1 > 0)
                then Some (to, (c.2.1.-1, c.2.2))
                else None
      else None
    | Tst from useSecond to_zero to_succ =>
      if from == c.1
      then if useSecond
           then if c.2.2 == 0
                then Some (to_zero, c.2)
                else Some (to_succ, c.2)
           else if c.2.1 == 0
                then Some (to_zero, c.2)
                else Some (to_succ, c.2)
      else None
    end.

  Definition Step : Config -> Config -> Prop :=
    fun c1 c2 => has (fun t => step c1 t == Some c2) transitions.

  Definition Trace : Config -> Config -> Prop :=
    clos_refl_trans _ Step.

  Variables start stop: State.

  Section TransitionMathcompInstances.
    Definition Transition2o (t: Transition): (State * bool * State) + (State * bool * State) + (State * bool * State * State) :=
      match t with
      | Add from useSecond to => inl (inl (from, useSecond, to))
      | Sub from useSecond to => inl (inr (from, useSecond, to))
      | Tst from useSecond to_zero to_succ => inr (from, useSecond, to_zero, to_succ)
      end.

    Definition o2Transition (o: (State * bool * State) + (State * bool * State) + (State * bool * State * State)): Transition :=
      match o with
      | inl (inl (from, useSecond, to)) => Add from useSecond to
      | inl (inr (from, useSecond, to)) => Sub from useSecond to
      | inr (from, useSecond, to_zero, to_succ) => Tst from useSecond to_zero to_succ
      end.

    Lemma can_sumTrans: cancel Transition2o o2Transition.
    Proof. by case. Qed.
    Definition Transition_eqMixin := CanEqMixin can_sumTrans.
    Canonical Transition_eqType := EqType Transition Transition_eqMixin.
    Definition Transition_choiceMixin := CanChoiceMixin can_sumTrans.
    Canonical Transition_choiceType := ChoiceType Transition Transition_choiceMixin.
    Definition Transition_countMixin := CanCountMixin can_sumTrans.
    Canonical Transition_countType := CountType Transition Transition_countMixin.
    Definition Transition_finMixin := CanFinMixin can_sumTrans.
    Canonical Transition_finType := CountType Transition Transition_finMixin.
  End TransitionMathcompInstances.

  Definition isTest (t: Transition): bool :=
    if t is Tst _ _ _ _ then true else false.

  Definition I: Type := nat * nat.
  Definition O: finType :=
    sum_finType unit_finType
                (sum_finType [finType of seq_sub (filter isTest transitions)]
                             (sum_finType [finType of seq_sub (filter isTest transitions)]
                                          [finType of seq_sub (filter (predC isTest) transitions)])).
  Definition S: preOrdered := diag_preOrderedType [countType of Config].

  Definition sigSpec__Aut (i: I) (o: O): (seq Config * Config) :=
    match o with
    | inl tt => ([::], (stop, i))
    | inr (inl t) =>
      match ssval t with
      | Tst from useSecond to_zero to_succ => ([:: (to_zero, if useSecond then (i.1, 0) else (0, i.2))],
                                              (from, if useSecond then (i.1, 0) else (0, i.2)))
      | _ => ([::], (stop, i))
      end
    | inr (inr (inl t)) =>
      match ssval t with
      | Tst from useSecond to_zero to_succ => ([:: (to_succ, if useSecond then (i.1, i.2.+1) else (i.1.+1, i.2)) ],
                                              (from, if useSecond then (i.1, i.2.+1) else (i.1.+1, i.2)))
      | _ => ([::], (stop, i))
      end
    | inr (inr (inr t)) =>
      match ssval t with
      | Add from useSecond to => ([:: (to, if useSecond then (i.1, i.2.+1) else (i.1.+1, i.2))],
                                 (from, i))
      | Sub from useSecond to => ([:: (to, i)],
                                 (from, if useSecond then (i.1, i.2.+1) else (i.1.+1, i.2)))
      | _ => ([::], (stop, i))
      end
    end.



  Definition Sigma__Aut : sigFam I := (@sigFamSpec_Type I S O sigSpec__Aut).

  Definition C__Aut : forall (c: Config), Type := fun c => { i : I | Trace c (stop, i) }.

  Ltac elimFiltered :=
    let devil := fresh "devil" in
    (move => ? ? ? devil;
            suff: false;
            last by (move: devil; rewrite mem_filter))
    || (move => ? ? ? ? devil;
            suff: false;
            last by (move: devil; rewrite mem_filter)).

  Lemma transition_arity1: forall i o, arity Sigma__Aut i (inr o) = 1.
  Proof.
    move => i.
    case.
    - case; case => //; by elimFiltered.
    - case.
      + case; case => //; by elimFiltered.
      + case; case => //; by elimFiltered.
  Qed.

  Lemma sound_Sigma__Aut: forall i o,
      Step (range Sigma__Aut i (inr o)) (tnth (dom Sigma__Aut i (inr o))
                                            (rew <- [fun n => 'I_n] transition_arity1 i o in
                                                (Ordinal (ltn0Sn 0)))).
  Proof.
    move => i o.
    move: (rew <- [fun n => 'I_n] transition_arity1 i o in (Ordinal (ltn0Sn 0))).
    case o.
    - case; case => //; try by elimFiltered.
      move => from useSecond to_zero to_succ prf ord.
      rewrite /dom /range /= /Step.
      apply /hasP.
      eexists.
      + move: ord => _.
        move: prf.
        rewrite mem_filter => [] /andP [] _ res.
          by exact res.
      + rewrite /= eq_refl.
        move: ord.
        rewrite /arity /=.
        case; case => //=.
        rewrite /tnth /=.
        move: prf => _.
          by case: useSecond.
    - case.
      + case; case => //; try by elimFiltered.
        move => from useSecond to_zero to_succ prf ord.
        rewrite /dom /range /= /Step.
        apply /hasP.
        eexists.
        * move: ord => _.
          move: prf.
          rewrite mem_filter => [] /andP [] _ res.
            by exact res.
        * rewrite /= eq_refl.
          move: ord.
          rewrite /arity /=.
          case; case => //=.
          rewrite /tnth /=.
          move: prf => _.
            by case: useSecond.
      + case; case => //; try by elimFiltered.
        * move => from useSecond to prf ord.
          rewrite /dom /range /= /Step.
          apply /hasP.
          eexists.
          ** move: ord => _.
             move: prf.
             rewrite mem_filter => [] /andP [] _ res.
               by exact res.
          ** rewrite /= eq_refl.
             move: ord.
             rewrite /arity /=.
               by case; case => //=.
        * move => from useSecond to prf ord.
          rewrite /dom /range /= /Step.
          apply /hasP.
          eexists.
          ** move: ord => _.
             move: prf.
             rewrite mem_filter => [] /andP [] _ res.
               by exact res.
          ** rewrite /= eq_refl.
             move: ord.
             rewrite /arity /=.
             case; case => //=.
             rewrite /tnth /=.
             move: prf => _.
               by case: useSecond; case i.
  Qed.

  Definition AutAction : forall s, F Sigma__Aut C__Aut s -> C__Aut s :=
    fun s x =>
      match op x as o return range Sigma__Aut (index x) o = s ->
                             (if o is inr o return Prop
                              then Step (range Sigma__Aut (index x) (inr o))
                                        (tnth (dom Sigma__Aut (index x) (inr o))
                                              (rew <- [fun n => 'I_n] transition_arity1 (index x) o in
                                                  (Ordinal (ltn0Sn 0))))
                              else True) ->
                             {ffun forall n : 'I_(arity Sigma__Aut (index x) o), C__Aut (tnth (dom Sigma__Aut (index x) o) n)} ->
                             C__Aut s with
      | inl tt => fun eqprf _ _ => rew eqprf in exist _ (index x) (rt_refl _ _ (stop, (index x)))
      | inr o => fun eqprf step_prf args =>
                  rew eqprf in
                  let: exist i steps := (args (rew <- [fun n => 'I_n] transition_arity1 (index x) o in
                                                     (Ordinal (ltn0Sn 0))))
                  in exist _ i (rt_trans _ _ _ _ (stop, i) (rt_step _ _ _ _ step_prf) steps)
      end (eqP (range_cond x))
          (match op x as o return (if o is inr o return Prop
                                   then Step (range Sigma__Aut (index x) (inr o))
                                             (tnth (dom Sigma__Aut (index x) (inr o))
                                                   (rew <- [fun n => 'I_n] transition_arity1 (index x) o in
                                                       (Ordinal (ltn0Sn 0))))
                                   else True) with
           | inr o => sound_Sigma__Aut (index x) o
           | _ => Logic.I
           end)
          (args x).

  
  Definition AutAlg : sigAlg Sigma__Aut := sigAlg_Type AutAction.
  
End AutomatonSpec.


