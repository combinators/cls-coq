Require Import Coq.Vectors.Vector.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Eqdep_dec.

Module Type TermSignature.
  Parameter CombinatorSymbol: Set.
End TermSignature.
  
Module Type Terms(Import TermSig: TermSignature).
  Import EqNotations.
  
  Inductive Term : Set :=
  | Symbol: forall (c : CombinatorSymbol), Term
  | App: forall (M N: Term), Term.

  Fixpoint rootOf (M: Term): CombinatorSymbol :=
    match M with
    | Symbol c => c
    | App M' N => rootOf M'
    end.

  Fixpoint argumentCount (M: Term): nat :=
    match M with
    | Symbol c => 0
    | App M' N => 1 + (argumentCount M')
    end.

  Fixpoint argumentsOf (M: Term): t Term (argumentCount M) :=
    match M as M' return t Term (argumentCount M') with
    | Symbol c => nil _
    | App M' N => shiftin N (argumentsOf M')
    end.

  Fixpoint applyAll {n : nat} (M: Term) (Ns : t Term n) { struct Ns }: Term :=
    match Ns with
    | nil _ => M
    | cons _ N _ Ns => applyAll (App M N) Ns
    end.

  Lemma applyAll_shiftin {n : nat}:
    forall M N (Ns: t Term n),
      applyAll M (shiftin N Ns) = App (applyAll M Ns) N.
  Proof.
    intros M N Ns.
    revert M N.
    induction Ns as [ | ? ? ? IH ].
    - intros; reflexivity.
    - intros M N.
      simpl.
      rewrite IH.
      reflexivity.
  Qed.
  
  Lemma applyAllSpec : forall M, applyAll (Symbol (rootOf M)) (argumentsOf M) = M.
  Proof.
    intro M.
    induction M as [ | ? IH ].
    - reflexivity.
    - simpl.
      rewrite (applyAll_shiftin).
      rewrite IH.
      reflexivity.
  Qed.

  Lemma applyAllRoot: forall M n (Ms: t Term n), rootOf (applyAll M Ms) = rootOf M.
  Proof.
    intros M n Ms.
    revert M.
    induction Ms as [ | ? ? ? IH ].
    - intro; reflexivity.
    - intro M.
      simpl.
      rewrite IH.
      reflexivity.
  Qed.

  Lemma applyAllArgumentCount: forall M n (Ms: t Term n),
      argumentCount (applyAll M Ms) = (argumentCount M + n)%nat.
  Proof.
    intros M n Ms.
    revert M.
    induction Ms as [ | ? ? ? IH ].
    - intro; rewrite (Nat.add_0_r); reflexivity.
    - intro M.
      simpl.
      rewrite IH.
      rewrite (Nat.add_succ_r).
      reflexivity.
  Qed.
  
  Lemma applyAllArguments: forall M n (Ms: t Term n),
      argumentsOf (applyAll M Ms) =
      (rew <- (applyAllArgumentCount M n Ms) in append (argumentsOf M) Ms).
  Proof.    
    intros M n Ms.
    revert M.
    induction Ms as [ | M' m' Ms IH ].
    - intro M.
      simpl.
      generalize (argumentsOf M).
      generalize (applyAllArgumentCount M 0 (nil _)).
      simpl.
      generalize (argumentCount M).
      intro n.
      intros eq xs.
      revert eq.
      induction xs as [ | x n xs IH ].
      + simpl.
        intro eq.
        unfold eq_rect_r.
        rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ (eq_sym eq)).
        reflexivity.
      + simpl.
        intro eq.
        rewrite (IH (eq_sym (Nat.add_0_r n))) at 1.
        revert eq.
        rewrite <- (Nat.add_0_r n).
        intro eq.
        unfold eq_rect_r.
        rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ (eq_sym eq)).
        simpl.
        reflexivity.      
    - intro M.
      simpl.
      rewrite (IH (App M M')).
      generalize (applyAllArgumentCount (App M M') m' Ms).
      generalize (applyAllArgumentCount M (S m') (cons _ M' _ Ms)).
      simpl.
      intro eq.
      rewrite eq.
      unfold eq_rect_r.
      simpl.
      clear eq.
      intro eq.
      generalize (argumentsOf M).
      revert eq.
      generalize (argumentCount M).
      intros n'.
      assert (append_shift:
                forall A n (xs: t A n) m (ys: t A m) x,
                  append (shiftin x xs) ys =
                  rew (Nat.add_succ_r n m) in append xs (cons _ x _ ys)).
      { intros A n'' xs.
        induction xs as [ | ? n''' ? IH' ].
        - simpl.
          intro m.
          generalize (Nat.add_succ_r 0 m).
          simpl.
          intros eq ys x.
          rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ eq).
          reflexivity.
        - simpl.
          intros m ys x.
          rewrite (IH' _ ys x).
          generalize (Nat.add_succ_r (S n''') m).
          simpl.
          rewrite <- (Nat.add_succ_r (n''') m).
          intro eq.
          rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ eq).
          reflexivity. }
      intros eq xs.
      rewrite (append_shift _ _ xs _ Ms).
      revert eq.
      rewrite <- (Nat.add_succ_r n' m').
      intro eq.
      rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ (eq_sym eq)).
      reflexivity.
  Qed.
End Terms.
  