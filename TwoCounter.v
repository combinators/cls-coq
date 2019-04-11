Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Logic.Eqdep_dec.
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

  Variables stop: State.

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
                             {ffun forall n : 'I_(arity Sigma__Aut (index x) o),
                                   C__Aut (tnth (dom Sigma__Aut (index x) o) n)} ->
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

  Variable start: Config.

  Lemma sound: C__Aut start -> { i : nat * nat | Trace start (stop, i) }.
  Proof. done. Qed.

  Lemma complete:
    forall i, Trace start (stop, i) -> exists (trace: C__Aut start), AlgGen Sigma__Aut AutAlg start trace.
  Proof.
    move => i /(@clos_rt_rt1n _ _ _ _) trace.
    have: exists j, (stop, j) = (stop, i) by (exists i => //).
    elim: trace; clear start i.
    - move => [] start i [] j <-.
      exists (action AutAlg (stop, j) (@mkF I Sigma__Aut C__Aut (stop, j) j (inl tt)
                                      [ffun n => False_rect _ (notF (@ltn_ord 0 n))]
                                      (preorder_reflexive _))).
      constructor => /=.
      rewrite /Sigma__Aut /arity /=.
        by case.
    - move => c1 c2 c3 /hasP [] t.
      case: t.
      + move => from useSecond to inprf step_prf prfs IH /IH [] [] i__stop steps steps__gen.
        have @x: F Sigma__Aut C__Aut c1.
        { apply: (fun inprf =>
                    (@mkF I Sigma__Aut C__Aut c1 (c1.2)
                          (inr (inr (inr (@SeqSub _ _ (Add from useSecond to) inprf)))))).
          - by rewrite mem_filter inprf.
          - move => inprf__o.
            apply finfun.
            rewrite /Sigma__Aut /arity /dom /=.
            case; case => //= ?.
            rewrite /tnth /=.
            exists i__stop.
            rewrite /Trace.
            suff: (((to, if useSecond then (c1.2.1, c1.2.2.+1) else (c1.2.1.+1, c1.2.2))) = c2)
              by (move => ->; exact steps).
            move: step_prf.
            rewrite /=.
              by case: (from == c1.1) => // /eqP [] <-.
          - move => ?.
            rewrite /range /=.
            move: step_prf.
            rewrite /=.
            case from__eq: (from == c1.1) => //.
            rewrite (eqP from__eq).
            move => _.
            clear...
            case: c1 => * /=.
              by apply preorder_reflexive. }
        exists (action AutAlg c1 x).
        constructor.
        move => n.
        rewrite /x /= ffunE /dom /tnth /=.
        case: n; case => //= _.
        move: x => _.
        move: step_prf.
        rewrite /step.
        case: (from == c1.1) => //= step_prf.
        rewrite /ssr_suff /eq_ind_r /eq_ind.
        move: (elimTF eqP step_prf).
        move: (eqP step_prf) => [] -> eq_prf.
        have: (eq_prf = erefl _).
        { apply: UIP_dec.
          move => x y.
          case xy__eq: (x == y).
          - left; by exact (eqP xy__eq).
          - right.
            apply /eqP.
              by rewrite xy__eq. }
        move => ->.
          by rewrite /=.
      + move => from useSecond to inprf step_prf prfs IH /IH [] [] i__stop steps steps__gen.
        have @x: F Sigma__Aut C__Aut c1.
        { apply: (fun inprf =>
                    (@mkF I Sigma__Aut C__Aut c1 (if useSecond then (c1.2.1, c1.2.2.-1) else (c1.2.1.-1, c1.2.2))
                          (inr (inr (inr (@SeqSub _ _ (Sub from useSecond to) inprf)))))).
          - by rewrite mem_filter inprf.
          - move => inprf__o.
            apply finfun.
            rewrite /Sigma__Aut /arity /dom /=.
            case; case => //= ?.
            rewrite /tnth /=.
            move: inprf__o inprf => _ _.
            exists i__stop.
            rewrite /Trace.
            suff: (((to, if useSecond then (c1.2.1, c1.2.2.-1) else (c1.2.1.-1, c1.2.2))) = c2)
              by (move => ->; exact steps).
            move: step_prf => /eqP.
            rewrite /step /=.
            case: (from == c1.1) => //.
            case: useSecond.
            + by case: (0 < c1.2.2) => //= [] [] ->.
            + by case: (0 < c1.2.1) => //= [] [] ->.
          - move => ?.
            rewrite /range /=.
            move: step_prf.
            rewrite /=.
            case from__eq: (from == c1.1) => //.
            case: (useSecond) => //.
            + move: from__eq => /eqP.
              case c122__lt: (0 < c1.2.2) => //=.
              move: c122__lt.
              case: c1 => c11 [] c111 c112 /ltn_predK -> -> /= _.
                by apply preorder_reflexive.
            + move: from__eq => /eqP.
              case c121__lt: (0 < c1.2.1) => //=.
              move: c121__lt.
              case: c1 => c11 [] c111 c112 /ltn_predK -> -> /= _.
                by apply preorder_reflexive. }
        exists (action AutAlg c1 x).
        constructor.
        move => n.
        rewrite /x /= ffunE /dom /tnth /=.
        case: n; case => //= _.
        move: x => _.
        move: step_prf.
        rewrite /step.
        case: (from == c1.1) => //= step_prf.
        rewrite /ssr_suff /eq_ind_r /eq_ind.
        move: (elimTF eqP step_prf).
        move: (eqP step_prf) => [].
        move: step_prf inprf => _ _.
        case: useSecond => /=.
        * case: (0 < c1.2.2) => //.
          move => [] -> eq_prf.
          have: (eq_prf = erefl _).
          { apply: UIP_dec.
            move => x y.
            case xy__eq: (x == y).
            - left; by exact (eqP xy__eq).
            - right.
              apply /eqP.
                by rewrite xy__eq. }
          move => ->.
            by rewrite /=.
        * case: (0 < c1.2.1) => //.
          move => [] -> eq_prf.
          have: (eq_prf = erefl _).
          { apply: UIP_dec.
            move => x y.
            case xy__eq: (x == y).
            - left; by exact (eqP xy__eq).
            - right.
              apply /eqP.
                by rewrite xy__eq. }
          move => ->.
            by rewrite /=.
      + move => from useSecond to_zero to_succ inprf step_prf prfs IH /IH [] [] i__stop steps steps__gen.
        have @x: F Sigma__Aut C__Aut c1.
        { apply: (fun inprf =>
                    (@mkF I Sigma__Aut C__Aut c1
                          (if useSecond
                           then if c1.2.2 == 0
                                then c1.2
                                else (c1.2.1, c1.2.2.-1)
                           else if c1.2.1 == 0
                                then c1.2
                                else (c1.2.1.-1, c1.2.2))
                          (if useSecond
                           then if c1.2.2 == 0
                                then inr (inl (@SeqSub _ _ (Tst from useSecond to_zero to_succ) inprf))
                                else inr (inr (inl (@SeqSub _ _ (Tst from useSecond to_zero to_succ) inprf)))
                           else if c1.2.1 == 0
                                then inr (inl (@SeqSub _ _ (Tst from useSecond to_zero to_succ) inprf))
                                else inr (inr (inl (@SeqSub _ _ (Tst from useSecond to_zero to_succ) inprf)))))).
          - by rewrite mem_filter inprf.
          - move: inprf step_prf => _.
            rewrite /step.
            case: useSecond.
            + case c122__eq: (c1.2.2 == 0).
              * case from__eq: (from == c1.1) => // /eqP [] c2__eq.
                rewrite /Sigma__Aut /arity /dom /=.
                move => _.
                apply: finfun.
                case; case => //= ?.
                exists i__stop.
                rewrite /tnth /= -(eqP c122__eq).
                clear IH prfs steps__gen.
                move: c2__eq steps.
                  by case: c2 => ? [] ? ? [] -> ->.
              * case from__eq: (from == c1.1) => // /eqP [] c2__eq.
                rewrite /Sigma__Aut /arity /dom /=.
                move => _.
                apply: finfun.
                case; case => //= ?.
                exists i__stop.
                rewrite /tnth /=.
                move: c122__eq => /neq0_lt0n /ltn_predK ->.
                clear IH prfs steps__gen.
                move: c2__eq steps.
                  by case: c2 => ? [] ? ? [] -> ->.
            + case c121__eq: (c1.2.1 == 0).
              * case from__eq: (from == c1.1) => // /eqP [] c2__eq.
                rewrite /Sigma__Aut /arity /dom /=.
                move => _.
                apply: finfun.
                case; case => //= ?.
                exists i__stop.
                rewrite /tnth /= -(eqP c121__eq).
                clear IH prfs steps__gen.
                move: c2__eq steps.
                  by case: c2 => ? [] ? ? [] -> ->.
              * case from__eq: (from == c1.1) => // /eqP [] c2__eq.
                rewrite /Sigma__Aut /arity /dom /=.
                move => _.
                apply: finfun.
                case; case => //= ?.
                exists i__stop.
                rewrite /tnth /=.
                move: c121__eq => /neq0_lt0n /ltn_predK ->.
                clear IH prfs steps__gen.
                move: c2__eq steps.
                  by case: c2 => ? [] ? ? [] -> ->.
          - move => inprf__o.
            rewrite /range /=.
            move: step_prf.
            rewrite /=.
            case from__eq: (from == c1.1) => //.
            move: inprf__o.
            case: (useSecond).
            + case c122__eq: (c1.2.2 == 0).
              * rewrite /=.
                move => _ _.
                rewrite -(eqP c122__eq) (eqP from__eq).
                clear...
                case: c1 => ? [] ? ? /=.
                  by apply: preorder_reflexive.
              * rewrite /=.
                move => _ _.
                move: c122__eq => /neq0_lt0n /ltn_predK ->.
                rewrite (eqP from__eq).
                clear...
                case: c1 => ? [] ? ? /=.
                  by apply: preorder_reflexive.
            + case c121__eq: (c1.2.1 == 0).
              * rewrite /=.
                move => _ _.
                rewrite -(eqP c121__eq) (eqP from__eq).
                clear...
                case: c1 => ? [] ? ? /=.
                  by apply: preorder_reflexive.
              * rewrite /=.
                move => _ _.
                move: c121__eq => /neq0_lt0n /ltn_predK ->.
                rewrite (eqP from__eq).
                clear...
                case: c1 => ? [] ? ? /=.
                  by apply: preorder_reflexive. }
        exists (action AutAlg c1 x).
        constructor.
        rewrite /x /=.
        move: step_prf inprf x.
        case: useSecond.
        * rewrite /eq_ind_r /= /eq_ind /=.
          case: (from == c1.1) => //=.
          case: c1 => c11 [] c121 [].
          ** rewrite /=.
             move => step_prf inprf _.
             rewrite /arity /=.
             case; case => //= ?.
             rewrite ffunE /=.
             have: (eqP (erefl (0 == 0)) = erefl _).
             { apply: UIP_dec.
               move => n m.
               case nm__eq: (n == m).
               + by left; rewrite (eqP nm__eq).
               + right.
                 move => /eqP.
                   by rewrite nm__eq. }
             move => -> /=.
             rewrite /dom /= /tnth /=.
             move: (elimTF eqP step_prf).
             move: step_prf => /eqP [].
             move: steps steps__gen.
             clear prfs IH.
             case: c2 => c21 [] c221 c222 steps steps_gen [] -> -> -> eq_prf.
             have: (eq_prf = erefl _).
             { apply: UIP_dec.
               move => x y.
               case xy__eq: (x == y).
               - left; by rewrite (eqP xy__eq).
               - right.
                 move => /eqP.
                   by rewrite xy__eq. }
               by move => -> /=.
          ** rewrite /=.
             move => c122 step_prf inprf _.
             rewrite /arity /=.
             case; case => //= ?.
             rewrite ffunE /=.
             have: (Logic.eq_sym
                      (ltn_predK (m:=0) (n:=c122.+1)
                                 (neq0_lt0n (n:=c122.+1)
                                            (erefl (c122.+1 == 0)))) = erefl _).
             { apply: UIP_dec.
               move => n m.
               case nm__eq: (n == m).
               + by left; rewrite (eqP nm__eq).
               + right.
                 move => /eqP.
                   by rewrite nm__eq. }
             move => -> /=.
             rewrite /dom /= /tnth /=.
             move: (elimTF eqP step_prf).
             move: step_prf => /eqP [].
             move: steps steps__gen.
             clear prfs IH.
             case: c2 => c21 [] c221 c222 steps steps_gen [] -> -> -> eq_prf.
             have: (eq_prf = erefl _).
             { apply: UIP_dec.
               move => x y.
               case xy__eq: (x == y).
               - left; by rewrite (eqP xy__eq).
               - right.
                 move => /eqP.
                   by rewrite xy__eq. }
               by move => -> /=.
        * rewrite /eq_ind_r /= /eq_ind /=.
          case: (from == c1.1) => //=.
          case: c1 => c11 [] [].
          ** rewrite /=.
             move => c122 step_prf inprf _.
             rewrite /arity /=.
             case; case => //= ?.
             rewrite ffunE /=.
             have: (eqP (erefl (0 == 0)) = erefl _).
             { apply: UIP_dec.
               move => n m.
               case nm__eq: (n == m).
               + by left; rewrite (eqP nm__eq).
               + right.
                 move => /eqP.
                   by rewrite nm__eq. }
             move => -> /=.
             rewrite /dom /= /tnth /=.
             move: (elimTF eqP step_prf).
             move: step_prf => /eqP [].
             move: steps steps__gen.
             clear prfs IH.
             case: c2 => c21 [] c221 c222 steps steps_gen [] -> -> -> eq_prf.
             have: (eq_prf = erefl _).
             { apply: UIP_dec.
               move => x y.
               case xy__eq: (x == y).
               - left; by rewrite (eqP xy__eq).
               - right.
                 move => /eqP.
                   by rewrite xy__eq. }
               by move => -> /=.
          ** rewrite /=.
             move => c121 c122 step_prf inprf _.
             rewrite /arity /=.
             case; case => //= ?.
             rewrite ffunE /=.
             have: (Logic.eq_sym
                      (ltn_predK (m:=0) (n:=c121.+1)
                                 (neq0_lt0n (n:=c121.+1)
                                            (erefl (c121.+1 == 0)))) = erefl _).
             { apply: UIP_dec.
               move => n m.
               case nm__eq: (n == m).
               + by left; rewrite (eqP nm__eq).
               + right.
                 move => /eqP.
                   by rewrite nm__eq. }
             move => -> /=.
             rewrite /dom /= /tnth /=.
             move: (elimTF eqP step_prf).
             move: step_prf => /eqP [].
             move: steps steps__gen.
             clear prfs IH.
             case: c2 => c21 [] c221 c222 steps steps_gen [] -> -> -> eq_prf.
             have: (eq_prf = erefl _).
             { apply: UIP_dec.
               move => x y.
               case xy__eq: (x == y).
               - left; by rewrite (eqP xy__eq).
               - right.
                 move => /eqP.
                   by rewrite xy__eq. }
               by move => -> /=.
  Qed.
  
End AutomatonSpec.
