Require Import Lists.List.
Require Import Arith.PeanoNat.
Require Import Arith.Wf_nat.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Vectors.Fin.
Require Import Coq.Vectors.Vector.

Require Import VectorQuantification.
Require Import SigmaAlgebra.
Require Import SortEmbeddings.
Require Import VarianceLabeledTree.
Require Import Cantor.
Require Import FunctionSpace.

Import ListNotations.
Import EqNotations.

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

  Lemma Label_eq_dec: forall (x y: Label), { x = y } + { x <> y }.
  Proof.
    intros x y;
      destruct x;
      destruct y;
      solve [ left; reflexivity | right; intro devil; inversion devil ].
  Defined.

  Import VectorNotations.
  Inductive WfNat: VLTree Label EmptySet -> Prop :=
  | WfNat_Zero : WfNat (Node _ _ Zero [])
  | WfNat_Succ : forall n, WfNat n -> WfNat (Node _ _ Succ [n]).
                         
  Definition WellFormed: Type :=
    { mn : _ | WfNat (fst mn) /\ WfNat (snd mn) }.

  Definition WF_take (S: WellFormed) (x: Var): (VLTree Label EmptySet) :=
    match x with | valpha => fst (proj1_sig S) | vbeta => snd (proj1_sig S) end.

  Lemma WfNat_ext: forall m n (p1: WfNat m) (p2: WfNat n) (mn_eq: n = m), p1 = (rew [WfNat] mn_eq in p2).
  Proof.
    intros m n p1.
    revert n.
    apply (fun caseZ caseS =>
             WfNat_ind (fun m => forall p1 n p2 (mn_eq: n = m), p1 = rew [WfNat] mn_eq in p2)
                       caseZ caseS m p1); clear p1.
    - match goal with
      |[|- forall (p1 : WfNat ?m''), _] =>
       remember m'' as m' eqn:m_eq
      end.
      intro p1.
      destruct p1.
      + intros n p2.
        destruct p2.
        * clear m_eq.
          intro mn_eq.
          rewrite (UIP_dec (Tree_eq_dec _ _ Label_eq_dec (fun x => False_rect _ x)) mn_eq eq_refl).
          reflexivity.
        * intro mn_eq.
          inversion mn_eq.
      + inversion m_eq.
    - intros child wf_child IH.
      match goal with
      |[|- forall (p1 : WfNat ?m''), _] =>
       remember m'' as m' eqn:m_eq
      end.
      intro p1.
      destruct p1 as [ | child' child'_wf ].
      + inversion m_eq.
      + intros n p2.
        destruct p2.
        * intro mn_eq; inversion mn_eq.
        * intro mn_eq.
          assert (n_eq: n = child').
          { revert mn_eq.
            clear ...
            intro mn_eq.
            inversion mn_eq.
            reflexivity. }
          revert IH child'_wf mn_eq.
          rewrite <- n_eq.
          intros IH child'_wf mn_eq.
          rewrite (UIP_dec (Tree_eq_dec _ _ Label_eq_dec (fun x => False_rect _ x)) mn_eq eq_refl).
          simpl.
          apply f_equal.
          assert (n_eq': n = child).
          { revert n_eq m_eq.
            clear ...
            intros n_eq m_eq.
            rewrite <- n_eq in m_eq.
            inversion m_eq.
            reflexivity. }
          generalize (IH (rew n_eq' in child'_wf) n p2 n_eq').
          intro result.
          rewrite <- n_eq' in result.
          exact result.
  Qed.
  
  Lemma WF_take_extensional: forall S S', (forall x, WF_take S x = WF_take S' x) -> S = S'.
  Proof.
    intros S S' prf.
    destruct S as [ [ m n ] [ WF_m WF_n ] ];
      destruct S' as [ [ m' n' ] [ WF_m' WF_n' ] ].
    generalize (prf valpha); generalize (prf vbeta).
    clear prf.
    simpl.
    intros p1 p2.
    revert WF_m WF_n.
    rewrite p1.
    rewrite p2.
    intros WF_m WF_n.
    rewrite (WfNat_ext _ _ WF_m WF_m' eq_refl).
    rewrite (WfNat_ext _ _ WF_n WF_n' eq_refl).
    reflexivity.
  Qed.
  
  Instance WellFormedSpace: FunctionSpace WellFormed Var (VLTree Label EmptySet) :=
    {| take := WF_take;
       extensional := WF_take_extensional |}.

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
 
  Definition LOrder_dec := Label_eq_dec.
  Instance Vars_finite : Finite Var :=
    {| cardinality := 2;
       toFin := fun x => match x with | valpha => F1 | vbeta => Fin.FS F1 end;
       fromFin := fun x => match x return Var with | F1 => valpha | _ => vbeta end;
       fromToFin_id x := match x with | valpha => eq_refl | vbeta  => eq_refl end;
       toFromFin_id x := Fin.caseS' x (fun y => _ (_ y) = y) (eq_refl)
                                    (fun x' => Fin.caseS' x' (fun y => _ (_ (Fin.FS y)) = Fin.FS y) (eq_refl)
                                                       (fun x'' => False_rect _ (Fin.case0 (fun x => False) x'')))
    |}.
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

  Ltac equate_config C WFS :=
    simpl;
    unfold C;
    unfold mkConfigTree;
    simpl;
    unfold configTree;
    try rewrite (natAsTree_treeAsNat _ (proj1 (proj2_sig WFS)));
    try rewrite (natAsTree_treeAsNat _ (proj2 (proj2_sig WFS)));
    rewrite (substitute_nat (WF_take WFS) _);
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
    destruct f as [ op S dom subsort ].
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
                               (treeAsNat (take S valpha))
                               (treeAsNat (take S vbeta)));
            exists (C, C); repeat split;
            [ equate_config C S | apply Here ]
          | destruct useSecond;
            match goal with
            |[|- TwoCounterCarrier (applySubst (take S) (range (CAdd _ _ _ _)))] =>
             set (C := MkConfig q
                                (treeAsNat (substitute (take S) alpha))
                                (treeAsNat (substitute (take S) beta)))
            |[|- TwoCounterCarrier (applySubst (take S) (range (CSub true _ _ _)))] =>
             set (C := MkConfig q
                                (treeAsNat (take S valpha))
                                (treeAsNat (SuccTree (take S vbeta))))
            |[|- TwoCounterCarrier (applySubst (take S) (range (CSub false _ _ _)))] =>
             set (C := MkConfig q
                                (treeAsNat (SuccTree (take S valpha)))
                                (treeAsNat (take S vbeta)))
            |[|- TwoCounterCarrier (applySubst (take S) (range (CTstZ false _ _ _ _)))] =>
             set (C := MkConfig q
                                (treeAsNat ZeroTree)
                                (treeAsNat (take S vbeta)))
            |[|- TwoCounterCarrier (applySubst (take S) (range (CTstZ true _ _ _ _)))] =>
             set (C := MkConfig q
                                (treeAsNat ((take S) valpha))
                                (treeAsNat ZeroTree))
            |[|- TwoCounterCarrier (applySubst (take S) (range (CTstNZ false _ _ _ _)))] =>
             set (C := MkConfig q
                                (treeAsNat (SuccTree (take S valpha)))
                                (treeAsNat (take S vbeta)))
            |[|- TwoCounterCarrier (applySubst (take S) (range (CTstNZ true _ _ _ _)))] =>
             set (C := MkConfig q
                                (treeAsNat (take S valpha))
                                (treeAsNat (SuccTree (take S vbeta))))
            end;
            exists (C, snd (proj1_sig (fst dom)));
            repeat split;
            try solve
                [ equate_config C S
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
    - set (WF_S :=
             exist (fun mn => WfNat (fst mn) /\ WfNat (snd mn))
                   (natAsTree (firstCounter C), natAsTree (secondCounter C))
                   (conj (natAsTree_WfNat (firstCounter C))
                         (natAsTree_WfNat (secondCounter C)))).
      assert (subPrf: subsorts (applySubst (take WF_S) (range CFin)) (mkConfigTree C)).
      { simpl.
        unfold mkConfigTree.
        unfold configTree.
        rewrite (substitute_nat).
        rewrite finPrf.
        reflexivity. }
      exists (TwoCounterAlgebra _ {| op := CFin; subst := WF_S; args := tt; subsort := subPrf |}).
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
      set (S := match cmd, useSecondCounter return (nat * nat) with
                | Add _, _ =>
                  (firstCounter C, secondCounter C)
                | _, true =>
                  (firstCounter C, pred (secondCounter C))
                | _, false =>
                  (pred (firstCounter C), secondCounter C)
                end).
      set (WF_S := exist (fun mn => WfNat (fst mn) /\ WfNat (snd mn))
                         (natAsTree (fst S), natAsTree (snd S))
                         (match cmd, useSecondCounter with
                          | _, _ => conj (natAsTree_WfNat (fst S)) (natAsTree_WfNat (snd S))
                          end)).                        
      assert (subPrf: subsorts (substitute (take WF_S) (range op)) (mkConfigTree C)).
      { unfold op.
        unfold WF_S.
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
      assert (genArgs: { args: F_args TwoCounterCarrier (take WF_S) (domain op)
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
          |[|- context f [ substitute (WF_take WF_S) (natAsTree ?x)  ]] =>
           rewrite <- (substitute_nat (WF_take WF_S) x)
          end;
          try rewrite (Nat.sub_0_r _);
          intros arg argPrf;
          exists (arg, tt);
          (apply GeneratedArgs_cons; [ exact argPrf | apply GeneratedArgs_nil ]). }
      exists (TwoCounterAlgebra _
                           {| op := op; subst := WF_S;
                              args := (proj1_sig genArgs); subsort := subPrf |}).
      apply FromF.
      exact (proj2_sig genArgs).
  Qed.
End TwoCounterAlgebra.
