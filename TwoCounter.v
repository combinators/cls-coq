Require Import Lists.List.
Require Import Arith.PeanoNat.
Require Import Arith.Wf_nat.
Require Import Coq.Logic.Eqdep_dec.
Require Import VectorQuantification.
Require Import SigmaAlgebra.
Require Import SortEmbeddings.
Require Import VarianceLabeledTree.
Require Import Cantor.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Vectors.Fin.
Require Import Coq.Vectors.Vector.
Import ListNotations.

Definition State : Set := nat.

Inductive Command: Set :=
| Add : State -> Command
| Sub : State -> Command
| Tst : State -> State -> Command.

Record Transition : Set :=
  MkTransition { startState : State;
                 command : Command;
                 useSecondCounter : bool }.

Record TwoCounterAutomaton: Set :=
  { start : State;
    final :  State;
    transitions : list Transition }.

Record Config: Set :=
  MkConfig { state : State;
             firstCounter : nat;
             secondCounter : nat }.

Inductive MayExecuteCommand: Config -> Command -> bool -> Prop :=
| MayExecuteAdd : forall C p useSecondCounter, MayExecuteCommand C (Add p) useSecondCounter
| MayExecuteSubFirst : forall q m n p, MayExecuteCommand (MkConfig q (S m) n) (Sub p) false
| MayExecuteSubSecond : forall q m n p, MayExecuteCommand (MkConfig q m (S n)) (Sub p) true
| MayExecuteTst : forall C p r useSecondCounter, MayExecuteCommand C (Tst p r) useSecondCounter.

Definition DoStep (C: Config)
           (command: Command)
           (useSecondCounter: bool)
           (allowed: MayExecuteCommand C command useSecondCounter): Config :=
  match command with
  | Add p =>
    if useSecondCounter
    then MkConfig p (firstCounter C) (1 + secondCounter C)
    else MkConfig p (1 + firstCounter C) (secondCounter C)
  | Sub p => 
    if useSecondCounter
    then MkConfig p (firstCounter C) (secondCounter C - 1)
    else MkConfig p (firstCounter C - 1) (secondCounter C)
  | Tst p r =>
    if useSecondCounter
    then match (secondCounter C) with
         | 0 => MkConfig p (firstCounter C) (secondCounter C)
         | _ => MkConfig r (firstCounter C) (secondCounter C)
         end
    else match (firstCounter C) with
         | 0 => MkConfig p (firstCounter C) (secondCounter C)
         | _ => MkConfig r (firstCounter C) (secondCounter C)
         end
  end.

Inductive CanStep (automaton: TwoCounterAutomaton): Config -> Config -> Prop :=
| Here : forall C, CanStep automaton C C
| Step : forall (C: Config) (command: Command) (useSecondCounter: bool) (C'': Config)
           (allowed: MayExecuteCommand C command useSecondCounter),
    List.In (MkTransition (state C) command useSecondCounter) (transitions automaton) ->
    CanStep automaton (DoStep C command useSecondCounter allowed) C'' ->
    CanStep automaton C C''.


Module Type TwoCounterSpec.
  Parameter automaton: TwoCounterAutomaton.
End TwoCounterSpec.

Module Type TwoCounterTreeSpec(Import Automaton: TwoCounterSpec) <: TreeSpec.
  Inductive LabelTy: Set := Zero | Succ | Conf.
  Definition Label := LabelTy.
  Inductive VarTy : Set := valpha | vbeta.
  Definition Var := VarTy.
  Definition LOrder: Label -> Label -> Prop := @eq Label.
  Instance Info : LabelInfo Label :=
    { labelArity := fun label =>
                      match label with
                      | Zero => 0
                      | Succ => 1
                      | Config => 3
                      end;
      successorVariance := fun l pos => VarianceLabeledTree.In }.

  Instance LOrder_pre: PreOrder LOrder :=
    {| PreOrder_Reflexive := eq_Reflexive; PreOrder_Transitive := eq_Transitive |}.

  Inductive OperationTy: Set :=
  | CFin : OperationTy
  | CAdd : forall (useSecondCounter: bool) (q p : State),
      List.In (MkTransition q (Add p) useSecondCounter) (transitions automaton) ->
      OperationTy
  | CSub : forall (useSecondCounter: bool) (q p : State),
      List.In (MkTransition q (Sub p) useSecondCounter) (transitions automaton) ->
      OperationTy
  | CTstZ : forall (useSecondCounter: bool) (q p r : State),
      List.In (MkTransition q (Tst p r) useSecondCounter) (transitions automaton) ->
      OperationTy
  | CTstNZ : forall (useSecondCounter: bool) (q p r : State),
      List.In (MkTransition q (Tst p r) useSecondCounter) (transitions automaton) ->
      OperationTy.
  Definition Operation := OperationTy.

  Import VectorNotations.
  Inductive WfNat: VLTree Label EmptySet -> Prop :=
  | WfNat_Zero : WfNat (Node _ _ Zero [])
  | WfNat_Succ : forall n, WfNat n -> WfNat (Node _ _ Succ [n]).
                         
  Definition WellFormed: (Var -> VLTree Label EmptySet) -> Prop :=
    fun S => WfNat (S valpha) /\ WfNat (S vbeta).

  Definition ZeroTree {V: Set} : VLTree Label V := Node _ _ Zero [].
  Definition SuccTree {V: Set} (n: VLTree Label V): VLTree Label V := Node _ _ Succ [n].
  Fixpoint natAsTree {V: Set} (n: nat): VLTree Label V :=
    match n with
    | 0 => ZeroTree
    | S n => SuccTree (natAsTree n)
    end.
  Fixpoint treeAsNat (tree: VLTree Label EmptySet): nat :=
    match tree with
    | Node _ _ Zero [] => 0
    | Node _ _ Succ [n] => S (treeAsNat n)
    | _ => 0
    end.

  Lemma treeAsNat_natAsTree: forall n, treeAsNat (natAsTree n) = n.
  Proof.
    intro n.
    induction n; simpl; auto.
  Qed.

  Lemma natAsTree_treeAsNat: forall t, WfNat t -> natAsTree (treeAsNat t) = t.
  Proof.
    intros t.
    induction t as [ | l successors IH ] using VLTree_rect';
      intro prf; inversion prf as [ label_eq | n wfn label_eq ].
    - revert successors IH prf.
      rewrite <- label_eq.
      simpl labelArity.
      intro successors.
      apply (fun P r => case0 P r successors).
      intros; reflexivity.
    - revert successors IH prf.
      rewrite <- label_eq.
      simpl labelArity.
      intro successors.
      apply (caseS' successors).
      clear successors.
      intros succ successors.
      apply (fun P r => case0 P r successors).
      intros IH prf.
      simpl.
      unfold SuccTree.
      apply f_equal.
      apply (f_equal (fun x => cons _ x _ (nil _))).
      inversion prf.
      apply (Forall_nth _ _ (ForAll'Forall _ _ IH) Fin.F1).
      assumption.
  Qed.

  Lemma natAsTree_WfNat: forall n, WfNat (natAsTree n).
  Proof.
    intro n.
    induction n; constructor; auto.
  Qed.

  Lemma substitute_nat: forall {V: Set} (S: V -> VLTree Label EmptySet) n, substitute S (natAsTree n) = natAsTree n.
  Proof.
    intros V S n.
    induction n as [ | n IH ].
    - reflexivity.
    - simpl.
      rewrite IH.
      reflexivity.
  Qed. 
  
  Definition configTree {V: Set} (state counter1 counter2: VLTree Label V): VLTree Label V :=
    Node _ _ Conf [state; counter1; counter2].  
  Definition alpha : VLTree Label Var := Hole Label Var valpha.
  Definition beta : VLTree Label Var := Hole Label Var vbeta.
  
  Instance Sigma : Signature (VLTree Label) Var Operation :=
    { arity := fun op =>
                 match op with
                 | CFin => 0
                 | _ => 1
                 end;
      domain := fun op =>
                  match op with
                  | CFin => []
                  | CAdd true q p _ => [configTree (natAsTree p) alpha (SuccTree beta)]
                  | CAdd false q p _ => [configTree (natAsTree p) (SuccTree alpha) beta]
                  | CSub _ q p _ => [configTree (natAsTree p) alpha beta]
                  | CTstZ true q p r _ => [configTree (natAsTree p) alpha ZeroTree]
                  | CTstZ false q p r _ => [configTree (natAsTree p) ZeroTree beta]
                  | CTstNZ true q p r _ => [configTree (natAsTree r) alpha (SuccTree beta)]
                  | CTstNZ false q p r _ => [configTree (natAsTree r) (SuccTree alpha) beta]
                  end;
      range := fun op =>
                 match op with
                 | CFin => configTree (natAsTree (final automaton)) alpha beta
                 | CAdd _ q p _ => configTree (natAsTree q) alpha beta
                 | CSub true q p _ => configTree (natAsTree q) alpha (SuccTree beta)
                 | CSub false q p _ => configTree (natAsTree q) (SuccTree alpha) beta
                 | CTstZ true q p r _ => configTree (natAsTree q) alpha ZeroTree
                 | CTstZ false q p r _ => configTree (natAsTree q) ZeroTree beta
                 | CTstNZ true q p r _ => configTree (natAsTree q) alpha (SuccTree beta)
                 | CTstNZ false q p r _ => configTree (natAsTree q) (SuccTree alpha) beta
                 end
    }.

  Lemma Var_eq_dec: forall (x y: Var), { x = y } + { x <> y }.
  Proof.
    intros x y;
      destruct x;
      destruct y;
      solve [ left; reflexivity | right; intro devil; inversion devil ].
  Defined.
  Lemma Label_eq_dec: forall (x y: Label), { x = y } + { x <> y }.
  Proof.
    intros x y;
      destruct x;
      destruct y;
      solve [ left; reflexivity | right; intro devil; inversion devil ].
  Defined.
  Definition LOrder_dec := Label_eq_dec.
  Instance Vars_finite : Finite Var :=
    {| cardinality := 2;
       toFin := fun x => match x with | valpha => F1 | vbeta => Fin.FS F1 end;
       fromFin := fun x => match x return Var with | F1 => valpha | _ => vbeta end;
       fromToFin_id := fun x => match x with | valpha => eq_refl | vbeta  => eq_refl end |}.
  Instance Labels_countable : Countable Label :=
    { toNat := fun l => match l with
                     | Zero => 0
                     | Succ => 1
                     | Config => 2
                     end;
      fromNat := fun n => match n with
                       | 0 => Zero
                       | 1 => Succ
                       | _ => Conf
                       end;
      fromTo_id := fun l => match l with | Zero => eq_refl | Succ => eq_refl | Conf => eq_refl end }.

  Definition GroundLabel: { l : Label | labelArity l = 0 } := exist _ Zero (@eq_refl _ 0). 
End TwoCounterTreeSpec.

Module Type MkTwoCounterSigSpec(Automaton: TwoCounterSpec).
  Declare Module TreeSpec: TwoCounterTreeSpec(Automaton).
  Declare Module TreeSigSpec: TreeSignatureSpec(TreeSpec).
  Declare Module SigSpec: TreeSortCLSignature(TreeSpec)(TreeSigSpec).
End MkTwoCounterSigSpec.  

Module Type TwoCounterAlgebra
       (Automaton: TwoCounterSpec)
       (MkSpec: MkTwoCounterSigSpec(Automaton))
       (Import Alg: Algebraic(MkSpec.SigSpec)).
  Import MkSpec.SigSpec.
  Import MkSpec.TreeSpec.
  Import Automaton.

  Definition mkConfigTree {V: Set} (C: Config): VLTree Label V :=
    configTree (natAsTree (state C)) (natAsTree (firstCounter C)) (natAsTree (secondCounter C)).
  
  Definition TwoCounterCarrier :=
    fun (s: Sort EmptySet) => { fromTo : Config * Config
                           | s = mkConfigTree (fst fromTo) /\
                             CanStep automaton (fst fromTo) (snd fromTo) /\
                             state (snd fromTo) = final automaton }.

  Lemma subsort_eq: forall s1 s2, subsorts s1 s2 -> s1 = s2.
  Proof.
    intros s1.
    induction s1 as [| l1 successors1 IH] using VLTree_rect'; intros s2 prf.
    - contradiction.
    - inversion prf as [ ? l2 arityEq varianceEq ? successors2 labelEq childrenLe ].
      clear varianceEq.
      match goal with
      |[s2_eq : _ = s2 |- _ ] => clear s2_eq
      end.
      revert arityEq successors2 childrenLe.      
      rewrite <- labelEq.
      intro arityEq.
      unfold eq_rect_r.
      intro successors2.
      rewrite <- (eq_rect_eq_dec (Nat.eq_dec) (fun y => t (VLTree Label False) y) successors2 (eq_sym arityEq)).
      intro childrenLe.
      apply f_equal.
      match goal with        
      | [ successors1_eq: existT _ _ _ = existT _ _ successors1 |- _ ] =>
        rewrite (vect_exist_eq _ _ (existT_fg_eq (t (VLTree Label False)) _ _ _ _ successors1_eq)) in childrenLe;
          clear successors1_eq
      end.
      assert (variance_eq: map (successorVariance l1) (positions (labelArity l1)) =
                           const (VarianceLabeledTree.In) (labelArity l1)).
      { apply (nth_const _ VarianceLabeledTree.In).
        intro pos.
        rewrite (nth_map _ _ pos pos eq_refl).
        reflexivity. }
      rewrite variance_eq in childrenLe.
      assert (forall pos, subsorts (nth successors1 pos) (nth successors2 pos)).
      { revert childrenLe.
        clear...
        revert successors1 successors2.
        induction (labelArity l1) as [ | n IH ]. 
        - intros successors1 successors2 childrenLe pos.
          inversion pos.
        - intro successors1.
          apply (caseS' successors1).
          clear successors1.
          intros succ1 successors1.
          intro successors2.
          apply (caseS' successors2).
          clear successors2.
          intros succ2 successors2.
          intros childrenLe pos.
          apply (Fin.caseS' pos).
          + simpl.
            inversion childrenLe.
            assumption.
          + simpl.
            apply IH.
            inversion childrenLe.
            repeat match goal with
                   |[ eq: existT _ _ _ = existT _ _ _ |- _ ] => rewrite <- (vect_exist_eq _ _ eq)
                   end.
            assumption. }
      generalize (Forall_nth _ _ (ForAll'Forall _ _ IH)).
      intro IH'; clear IH.
      apply eq_nth_iff.
      intros pos1 pos2 pos_eq.
      apply IH'.
      rewrite pos_eq.
      auto.
  Qed.  

  Ltac equate_config C S WFS :=
    simpl;
    unfold C;
    unfold mkConfigTree;
    simpl;
    unfold configTree;
    try rewrite (natAsTree_treeAsNat _ (proj1 WFS));
    try rewrite (natAsTree_treeAsNat _ (proj2 WFS));
    rewrite (substitute_nat S _);
    reflexivity.

  Lemma configTree_eq:
    forall (S: Var -> Sort EmptySet) p q c1 t1 c2 t2,
      substitute S (configTree (natAsTree p) t1 t2) =
      mkConfigTree {| state := q; firstCounter := c1; secondCounter := c2 |} ->
      (p = q) /\ (substitute S t1 = natAsTree c1) /\ (substitute S t2 = natAsTree c2).
  Proof.
    intros S p q c1 t1 c2 t2 eq.
    unfold mkConfigTree in eq.
    unfold configTree in eq.
    simpl in eq.
    inversion eq.
    repeat split.
    match goal with
    |[ pq_eq: substitute S (natAsTree p) = _ |-_] =>
     rewrite (substitute_nat S p) in pq_eq;
       generalize (f_equal treeAsNat pq_eq);
       do 2 rewrite treeAsNat_natAsTree;
       trivial
    end.
  Qed.
    
  
  Definition TwoCounterAlgebra: SigmaAlgebra TwoCounterCarrier.
  Proof.
    intros s f.
    destruct f as [ op S WFS dom subsort ].
    revert dom subsort.
    destruct op as [
                  | useSecond q p isTrans
                  | useSecond q p isTrans
                  | useSecond q p r isTrans
                  | useSecond q p r isTrans ];
      intros dom subsort;
      rewrite <- (subsort_eq _ _ subsort);
      try solve
          [ set (C := MkConfig (final automaton)
                               (treeAsNat (S valpha))
                               (treeAsNat (S vbeta)));
            exists (C, C); repeat split;
            [ equate_config C S WFS| apply Here ]
          | destruct useSecond;
            match goal with
            |[|- TwoCounterCarrier (applySubst S (range (CAdd _ _ _ _)))] =>
             set (C := MkConfig q
                                (treeAsNat (substitute S alpha))
                                (treeAsNat (substitute S beta)))
            |[|- TwoCounterCarrier (applySubst S (range (CSub true _ _ _)))] =>
             set (C := MkConfig q
                                (treeAsNat (S valpha))
                                (treeAsNat (SuccTree (S vbeta))))
            |[|- TwoCounterCarrier (applySubst S (range (CSub false _ _ _)))] =>
             set (C := MkConfig q
                                (treeAsNat (SuccTree (S valpha)))
                                (treeAsNat (S vbeta)))
            |[|- TwoCounterCarrier (applySubst S (range (CTstZ false _ _ _ _)))] =>
             set (C := MkConfig q
                                (treeAsNat ZeroTree)
                                (treeAsNat (S vbeta)))
            |[|- TwoCounterCarrier (applySubst S (range (CTstZ true _ _ _ _)))] =>
             set (C := MkConfig q
                                (treeAsNat (S valpha))
                                (treeAsNat ZeroTree))
            |[|- TwoCounterCarrier (applySubst S (range (CTstNZ false _ _ _ _)))] =>
             set (C := MkConfig q
                                (treeAsNat (SuccTree (S valpha)))
                                (treeAsNat (S vbeta)))
            |[|- TwoCounterCarrier (applySubst S (range (CTstNZ true _ _ _ _)))] =>
             set (C := MkConfig q
                                (treeAsNat (S valpha))
                                (treeAsNat (SuccTree (S vbeta))))
            end;
            exists (C, snd (proj1_sig (fst dom)));
            repeat split;
            try solve
                [ equate_config C S WFS
                | simpl;
                  match goal with
                  |[ isTrans: List.In {| startState := _; command := ?cmd; useSecondCounter := ?snd |} _ |- _] =>
                   assert (allowed: MayExecuteCommand C cmd snd); [ constructor; auto | ]
                  end;
                  eapply (Step _ C _ _ _ allowed isTrans);
                  set (result := proj1 (proj2 (proj2_sig (fst dom))));
                  match goal with
                  |[result : CanStep _ ?C_given _ |- CanStep _ ?C_tgt _] =>
                   assert (C'_eq: C_tgt = C_given); [ | rewrite C'_eq; exact result ]
                  end;
                  destruct dom as [ [ [[q' first' second'] C_fin] [ C'_eq [ canStep isFin ] ] ] ok ];
                  destruct (configTree_eq _ _ _ _ _ _ _ C'_eq) as [ q'_eq [ first'_eq second'_eq ] ];
                  simpl;
                  rewrite q'_eq;
                  rewrite <- (treeAsNat_natAsTree first');
                  rewrite <- (treeAsNat_natAsTree second');
                  rewrite <- first'_eq;
                  rewrite <- second'_eq;
                  try rewrite Nat.sub_0_r;
                  reflexivity
                | destruct dom as [ [? [ ? [ ? isFin ] ]] ok ]; assumption
                ]
          ].
  Defined.

  Lemma SuccTree_pred_eq:
    forall C s snd,
      MayExecuteCommand C (Sub s) snd ->
      @SuccTree EmptySet (natAsTree (pred (if snd then secondCounter C else firstCounter C))) =
      natAsTree (if snd then secondCounter C else firstCounter C).
  Proof.
    intros C nextState snd.
    destruct C as [ currentState firstCounter secondCounter ].
    destruct snd;
      [ destruct secondCounter | destruct firstCounter ];
      intro prf;
      inversion prf;
      reflexivity.
  Qed.

  Lemma AllGenerated:
    forall C C' (stepPrf: CanStep automaton C C')
      (isFinal: state C' = final automaton),
      exists c,
        AlgebraicallyGenerated
          TwoCounterCarrier TwoCounterAlgebra
          (mkConfigTree C) c.
  Proof.
    intros C C' stepPrf.
    induction stepPrf as [ | C cmd useSecondCounter C'' allowed isTrans canStep IH ]; intro finPrf.
    - set (S := fun v =>
                  match v return Sort EmptySet with
                  | valpha => natAsTree (firstCounter C)
                  | vbeta => natAsTree (secondCounter C)
                  end).
      set (WF_S := conj (natAsTree_WfNat (firstCounter C))
                        (natAsTree_WfNat (secondCounter C))).
      assert (subPrf: subsorts (applySubst S (range CFin)) (mkConfigTree C)).
      { simpl.
        unfold mkConfigTree.
        unfold configTree.
        rewrite (substitute_nat).
        rewrite finPrf.
        reflexivity. }
      exists (TwoCounterAlgebra _ {| op := CFin; subst := S; wf_subst := WF_S; args := tt; subsort := subPrf |}).
      apply FromF.
      apply GeneratedArgs_nil.
    - destruct (IH finPrf) as [ arg argPrf ].
      set (op :=
             match cmd with
             | Add p => fun isTrans => CAdd useSecondCounter (state C) p isTrans
             | Sub p => fun isTrans => CSub useSecondCounter (state C) p isTrans
             | Tst p r =>
               match useSecondCounter with
               | true =>
                 match secondCounter C with
                 | 0 => fun isTrans => CTstZ true (state C) p r isTrans
                 | _ => fun isTrans => CTstNZ true (state C) p r isTrans
                 end
               | false =>
                 match firstCounter C with
                 | 0 => fun isTrans => CTstZ false (state C) p r isTrans
                 | _ => fun isTrans => CTstNZ false (state C) p r isTrans
                 end
               end
             end isTrans).      
      set (S := fun v =>
                  match cmd, useSecondCounter with
                  | Add _, _ =>
                    match v return Sort EmptySet with
                    | valpha => natAsTree (firstCounter C)
                    | vbeta => natAsTree (secondCounter C)
                    end
                  | _, true =>
                    match v return Sort EmptySet with
                    | valpha => natAsTree (firstCounter C)
                    | vbeta => natAsTree (pred (secondCounter C))
                    end
                  | _, false =>
                    match v return Sort EmptySet with
                    | valpha => natAsTree (pred (firstCounter C))
                    | vbeta => natAsTree (secondCounter C)
                    end
                  end).
      assert (WF_S: WellFormed S).      
      { split; destruct cmd; destruct useSecondCounter; apply natAsTree_WfNat. }
      assert (subPrf: subsorts (substitute S (range op)) (mkConfigTree C)).
      { unfold op.
        unfold S.
        destruct cmd; destruct useSecondCounter;
          simpl;
          unfold mkConfigTree;
          unfold configTree;
          try rewrite (substitute_nat);
          try rewrite <- (SuccTree_pred_eq _ _ _ allowed);
          try solve
              [ reflexivity
              | destruct (secondCounter C); simpl; rewrite substitute_nat; reflexivity
              | destruct (firstCounter C); simpl; rewrite substitute_nat; reflexivity
              ]. }
      assert (genArgs: { args: F_args TwoCounterCarrier S (domain op)
                       | GeneratedArgs TwoCounterCarrier TwoCounterAlgebra _ _ _ args }).
      { revert arg argPrf.
        unfold mkConfigTree.
        unfold F_args.
        unfold configTree.
        unfold op.
        destruct cmd;
          simpl;
          (destruct useSecondCounter; [ destruct (secondCounter C) | destruct (firstCounter C) ]);
          simpl;
          match goal with
          |[|- context f [ substitute S (natAsTree ?x)  ]] =>
           rewrite <- (substitute_nat S x)
          end;
          try rewrite (Nat.sub_0_r _);
          intros arg argPrf;
          exists (arg, tt);
          (apply GeneratedArgs_cons; [ exact argPrf | apply GeneratedArgs_nil ]). }
      exists (TwoCounterAlgebra _
                           {| op := op; subst := S; wf_subst := WF_S;
                              args := (proj1_sig genArgs); subsort := subPrf |}).
      apply FromF.
      exact (proj2_sig genArgs).
  Qed.
End TwoCounterAlgebra.
