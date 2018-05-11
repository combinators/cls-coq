Require Import Coq.Lists.List.
Import ListNotations.

Definition id : Set := nat.

Inductive aexp: Set :=
| ANum : nat -> aexp
| AId: id -> aexp
| APlus : aexp -> aexp -> aexp.

Inductive bexp: Set :=
| BTrue : bexp
| BFalse : bexp
| BLe : aexp -> aexp -> bexp
| BNand : bexp -> bexp -> bexp.

Inductive com : Set :=
| CSkip : com
| CAss : id -> aexp -> com
| CSeq : com -> com -> com
| CWhile : bexp -> com -> com.

Definition state : Set := id -> nat.

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).

Notation "'¬' x" := (BNand x x) (at level 75, right associativity).
Notation "x '&&' y" := (BNand (BNand x y) (BNand x y)).
Notation "x '||' y" := (BNand (BNand x x) (BNand y y)).
Notation "x '==>' y" := (BNand x (BNand y y)) (at level 95, right associativity, y at level 96).

Fixpoint aeval (st: state) (a: aexp) : nat :=
  match a with
  | ANum x => x
  | AId x => st x
  | APlus x y => aeval st x + aeval st y
  end.

Fixpoint beval (st: state) (b: bexp): bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BLe x y => Nat.leb (aeval st x) (aeval st y)
  | BNand x y => negb (andb (beval st x) (beval st y))
  end.

Definition update (st: state) (x: id) (val: nat): state :=
  fun y => if Nat.eqb x y then val else st y.

Reserved Notation "c1 '/' st '⇓' st'"
                  (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
| E_Skip : forall st, SKIP / st ⇓ st
| E_Ass : forall st a1 n x, aeval st a1 = n -> (x ::= a1) / st ⇓ (update st x n)
| E_Seq : forall c1 c2 st st' st'',
    c1 / st ⇓ st' -> c2 / st' ⇓ st'' -> (c1 ;; c2) / st ⇓ st''
| E_WhileEnd : forall b st c, beval st b = false -> (WHILE b DO c END) / st ⇓ st
| E_WhileLoop : forall st st' st'' b c,
    beval st b = true ->
    c / st ⇓ st' ->
    (WHILE b DO c END) / st' ⇓ st'' ->
    (WHILE b DO c END) / st ⇓ st''
where "c1 '/' st '⇓' st'" := (ceval c1 st st').

Fixpoint subst_aexp (inexp: aexp) (x: id) (byexp: aexp): aexp :=
  match inexp with
  | ANum x => ANum x
  | AId y => if Nat.eqb x y then byexp else AId y
  | APlus l r => APlus (subst_aexp l x byexp) (subst_aexp r x byexp)
  end.

Fixpoint subst_bexp (inexp: bexp) (x: id) (byexp: aexp): bexp :=
  match inexp with
  | BLe l r => BLe (subst_aexp l x byexp) (subst_aexp r x byexp)
  | BNand l r => BNand (subst_bexp l x byexp) (subst_bexp r x byexp)
  | e => e
  end.

Definition Assertion (P: bexp) := forall (st: state), beval st P = true.

Inductive hoare_proof : bexp -> com -> bexp -> Type :=
| H_Skip : forall P, hoare_proof P CSkip P
| H_Asgn : forall Q V a, hoare_proof (subst_bexp Q V a) (V ::= a) Q
| H_Seq : forall P c Q d R, hoare_proof P c Q -> hoare_proof Q d R -> hoare_proof P (c;;d) R
| H_While : forall P b c, hoare_proof (P && b) c P -> hoare_proof P (WHILE b DO c END) (P && ¬b)
| H_Consequence: forall P Q P' Q' c, hoare_proof P c Q -> Assertion (P' ==> P) -> Assertion (Q ==> Q') -> hoare_proof P' c Q'.


Definition hoare_triple (P:bexp) (c:com) (Q:bexp) : Prop :=
  forall st st', c / st ⇓ st' -> beval st P = true -> beval st' Q = true.
Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q) (at level 90, c at next level).

Lemma subst_aexp_eq: forall inexp V byexp st,
    aeval st (subst_aexp inexp V byexp) = aeval (update st V (aeval st byexp)) inexp.
Proof.
  intros inexp V.
  induction inexp as [ | | l IHl r IHr ] ; intros byexp st.
  - reflexivity.
  - unfold update.
    simpl.
    destruct (Nat.eqb V i); reflexivity.
  - simpl.
    rewrite IHl.
    rewrite IHr.
    reflexivity.
Qed.

Lemma subst_bexp_eq: forall inexp V byexp st,
    beval st (subst_bexp inexp V byexp) = beval (update st V (aeval st byexp)) inexp.
Proof.
  intros inexp V.
  induction inexp as [ | | | l IHl r IHr ]; intros byexp st.
  - reflexivity.
  - reflexivity.
  - simpl.
    rewrite subst_aexp_eq.
    rewrite subst_aexp_eq.
    reflexivity.
  - simpl.
    rewrite IHl.
    rewrite IHr.
    reflexivity.
Qed.

Lemma beval_assertion: forall Q Q' st, Assertion (Q ==> Q') -> beval st Q = true -> beval st Q' = true.
Proof.
  intros Q Q' st prf Qst.
  generalize (prf st).
  simpl.
  rewrite Qst.
  simpl.
  destruct (beval st Q'); intro; assumption.
Qed.

Lemma while_loop_cond_false: forall st st' b c, (WHILE b DO c END) / st ⇓ st' -> beval st' b = false.
Proof.
  intros st st' b c.
  remember (WHILE b DO c END) as c' eqn:c'_eq.
  intro prf.
  revert b c c'_eq.  
  induction prf as [ | | | | st st' st'' b c bholds eval_prf IH1 prf IH2 ];
    intros b' c'' c'_eq; try solve [ inversion c'_eq ].
  - inversion c'_eq as [ [ b_eq c''_eq ] ].
    rewrite <- b_eq.
    assumption.
  - rewrite c'_eq in IH2.
    inversion c'_eq as [ [ b_eq c_eq ] ].
    apply (IH2 _ _ eq_refl).
Qed.

Lemma while_loop_invariant: forall P b c, {{P && b}} c {{P}} -> {{P}} WHILE b DO c END {{P}}.
Proof.
  intros P b c triple st st' eval_prf Pholds.
  remember (WHILE b DO c END) as c' eqn:c'_eq.
  revert b c triple c'_eq.
  induction eval_prf as [ | | | | st st' st'' b c bholds eval_prf IH1 prf IH2 ];
    intros b' c'' triple c'_eq;
    try solve [ inversion c'_eq ].
  - assumption.
  - inversion c'_eq as [ [ b_eq c_eq ] ].
    rewrite <- c_eq in triple.
    rewrite <- b_eq in triple.
    assert (Pbholds : beval st (P && b) = true).
    { simpl.
      rewrite Pholds.
      rewrite bholds.
      reflexivity. }
    apply (IH2 (triple st st' eval_prf Pbholds) b c triple eq_refl).
Qed. 

Lemma hoare_sound: forall P c Q, hoare_proof P c Q -> {{P}} c {{Q}}.
Proof.
  intros P c Q prf.
  induction prf as [ | | | P b c prf IH | P Q P' Q' c prf IH PP' QQ' ];
    intros st1 st2 eval_prf;
    try solve [ inversion eval_prf; intro; eauto ].
  - rewrite subst_bexp_eq.
    inversion eval_prf as [ | ? ? ? ? aeval_eq | | | ].
    rewrite <- aeval_eq.
    intro; assumption.    
  - intro Pholds.
    simpl.
    rewrite (while_loop_cond_false _ _ _ _ eval_prf).
    simpl.
    rewrite (while_loop_invariant P b c IH st1 st2 eval_prf Pholds).
    reflexivity.
  - intro P'holds.
    assert (Pholds: beval st1 P = true).
    { generalize (PP' st1).
      simpl.
      rewrite P'holds.
      simpl.
      case (beval st1 P); intro; assumption. }
    set (Qholds := IH st1 st2 eval_prf Pholds).
    generalize (QQ' st2).    
    simpl.
    rewrite Qholds.
    case (beval st2 Q'); intro; assumption.
Qed.

Lemma strengthen_precondition: forall P P' c Q, Assertion (P' ==> P) -> {{P}} c {{Q}} -> {{P'}} c {{Q}}.
Proof.
  intros P P' c Q prf triple st st' evalprf P'holds.
  assert (Pholds : beval st P = true).
  { generalize (prf st).
    simpl.
    rewrite P'holds.
    simpl.
    case (beval st P); intro; assumption. }
  apply (triple st st' evalprf Pholds).
Qed.

Lemma weaken_postcondition: forall P c Q Q', Assertion (Q ==> Q') -> {{P}} c {{Q}} -> {{P}} c {{Q'}}.
Proof.
  intros P c Q Q' prf triple st st' evalprf Pholds.
  generalize (prf st').
  simpl.
  rewrite (triple st st' evalprf Pholds).
  case (beval st' Q'); intro; assumption.
Qed.

Lemma hoare_complete: forall P c Q, {{P}} c {{Q}} -> hoare_proof P c Q.
Proof.
  intros P c Q.
  revert P Q.
  induction c as [ | V a | c1 IH1 c2 IH2 | cond body IH ];
    intros P Q triple.
  - apply (H_Consequence P P P Q).
    + apply H_Skip.
    + intro st.
      simpl.
      case (beval st P); reflexivity.
    + intro st.
      generalize (triple st st (E_Skip _)).
      simpl.
      case (beval st P).
      * intro prf; rewrite (prf eq_refl); reflexivity.
      * intros; reflexivity.
  - apply (H_Consequence (subst_bexp Q V a) Q P Q).
    + apply H_Asgn.
    + generalize (
      intro st.
      simpl.
      
      
      unfold Assertion.
      intro state.
      apply (triple state (update state V (aeval state a))).
      