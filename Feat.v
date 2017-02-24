Require Import Coq.Lists.Streams.
Require Import Coq.Vectors.Fin.
Require Import Coq.Vectors.Vector.
Require Import VectorQuantification.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Logic.Eqdep_dec.

Import EqNotations.


Module Finite.

  Section SingleType.
    Variable A : Type.

    Structure Finite :=
      { cardinality : nat;
        index : { n : _ | n < cardinality } -> A }.

    Definition empty: Finite :=
      {| cardinality := 0;
         index :=
           fun idx =>
             False_rect _ (Nat.nle_succ_diag_l _ (Nat.le_trans _ _ _
                                                               (proj2_sig idx)
                                                               (le_0_n (proj1_sig idx)))) |}.

    Definition singleton x: Finite :=
      {| cardinality := 0;
         index := fun idx => x |}.
    
    Lemma idx_right: forall i m n, i < m + n -> i >= m -> (i - m) < n.
    Proof.
      intro i.
      induction i as [ | i IH ].
      - intros m n i_lt i_ge.
        revert i_lt.
        inversion i_ge.
        simpl.
        intro; assumption.
      - intros m n i_le i_gt.
        destruct m.
        + assumption.
        + simpl.
          apply IH.
          * simpl in i_le.
            rewrite <- Nat.succ_lt_mono in i_le.
            assumption.
          * unfold ge.
            rewrite Nat.succ_le_mono.
            assumption.
    Qed.
    
    Definition append xs ys :=
      {| cardinality := cardinality xs + cardinality ys;
         index :=
           fun idx =>
             match lt_dec (proj1_sig idx) (cardinality xs) with
             | left prf => index xs (exist _ (proj1_sig idx) prf)
             | right prf => index ys (exist _ ((proj1_sig idx) - cardinality xs)
                                           (idx_right (proj1_sig idx) _ _ (proj2_sig idx) (not_lt _ _ prf)))
             end
      |}.
  End SingleType.

  Lemma etaEquivalence : forall (A B : Type) (f : A -> B), (fun x : A => f x) = f.
  Proof. reflexivity. Qed.
  
  Definition product {A B: Type} (b: B) (xs: Finite A) (ys: Finite B): Finite (A * B) :=
    {| cardinality := (cardinality _ xs * cardinality _ ys)%nat;
       index :=
         match cardinality _ xs as cxs return {n : _ | n < cxs * cardinality _ ys } ->
                                              ({n : _ | n < cxs } -> A) ->
                                              
                                              (A * B) with
         | 0 =>
           fun idx _ =>
             False_rect _ (Nat.nle_succ_diag_l _ (Nat.le_trans _ _ _
                                                               (proj2_sig idx)
                                                               (le_0_n (proj1_sig idx))))
         | S n =>
           fun idx index_xs =>
             let old_pos := (proj1_sig idx) in
             (index_xs (exist (fun n' => n' < S n)
                              (Nat.div old_pos (S n))
                              (rew (@eq_refl _ (S n)) in
                                  Nat.mod_upper_bound (old_pos) (S n)
                                                      (fun eq =>
                                                         eq_rect (S n)
                                                                 (fun x => match x with
                                                                        | 0 => False
                                                                        | _ => True
                                                                        end) I 0 eq))),
              b
              (*index _ ys (exist _ (Nat.modulo (proj1_sig idx) (cardinality _ xs)) _)*))
         end (index _ xs) |}.
                 
  
  

End Finite.

Module Enumeration.
  
  
  
  CoInductive Enumeration: Type :=
  | Cons : t A n -> Enumeration (S n) -> Enumeration n

  
  Fixpoint finite_prod (B: Type) {m n: nat} (xs : t A m) (ys: t B n): t (A * B) (m * n) :=
    match xs with
    | nil _ => rew (Nat.mul_0_l n) in nil _
    | cons _ x m' xs =>
      rew <- (Nat.mul_succ_l m' n) in
          rew (Nat.add_comm _ _) in
          append (map (fun y => (x, y)) ys) (finite_prod _ xs ys)
    end.

  Lemma FincaseS':
    forall n (i: Fin.t (S n)) P,
      (P (@F1 n)) -> (forall (i': Fin.t n), P (FS i')) -> P i.
    exact (
        fun n i P f1 fs =>
          match i  as i' in (Fin.t (S n)) return forall P, (P (@F1 n)) -> (forall (i': Fin.t n), P (FS i')) -> P i'  with
          | F1 => fun P f1 _ => f1
          | FS n => fun P _ fs => fs n
          end P f1 fs).
  Qed.

  Lemma rewrite_vect_eqtrans:
    forall B m n o (xs: t B m) (eq1: m = n) (eq2: n = o),
      rew eq2 in rew eq1 in xs = rew (eq_trans eq1 eq2) in xs.
  Proof.
    intros B m n o.
    destruct m; destruct n;
      intros ys eq1;
      inversion eq1 as [ eq1' ].
    - rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ eq1).
      rewrite <- (UIP_dec (Nat.eq_dec) eq_refl eq1).
      destruct o;
        intro eq2;
        inversion eq2.
      rewrite <- (UIP_dec (Nat.eq_dec) eq_refl eq2).
      reflexivity.
    - revert eq1.
      rewrite <- eq1'.
      intro eq1.
      rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ eq1).
      rewrite <- (UIP_dec (Nat.eq_dec) eq_refl eq1).
      intro eq2.
      destruct o;
        inversion eq2 as [eq2'].
      revert eq2.
      rewrite <- eq2'.
      intro eq2.
      rewrite <- (UIP_dec (Nat.eq_dec) eq_refl eq2).
      reflexivity.
  Qed.

  Lemma nth_append_l:
    forall A n m (xs: t A n) (ys: t A m) (i : Fin.t n),
      nth (append xs ys) (L _ i) = nth xs i.
  Proof.
    intros A' n m xs.
    induction xs.
    - intros ys i; inversion i.
    - intros ys i.
      apply (FincaseS' _ i).
      + reflexivity.
      + simpl; auto.
  Qed.

  Lemma nth_append_r:
    forall A n m (xs: t A n) (ys: t A m) (i : Fin.t m),
      nth (append xs ys) (R _ i) = nth ys i.
  Proof.
    intros A' n m xs.
    induction xs.
    - intros ys i. reflexivity.
    - intros ys i.
      simpl.
      auto.
  Qed.
  
  Lemma finite_prod_sanity:
    forall B m n (xs: t A m) (ys: t B n),
      forall i j, (nth xs i, nth ys j) = nth (finite_prod B xs ys) (depair i j).
  Proof.
    intros B m n xs ys i.
    induction i as [ m' | m' i ].
    - intro j.
      destruct j as [ n' | n' j ] .
      + apply (caseS' xs); clear xs; intros x xs.
        apply (caseS' ys); clear ys; intros y ys.
        intros.
        simpl.
        unfold eq_rect_r.
        rewrite (rewrite_vect_eqtrans _ _ ).
        match goal with
        | [ |- _ = nth (rew ?eq in _) F1 ] => generalize eq
        end.
        intro eq.
        rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ eq).
        reflexivity.
      + apply (caseS' xs); clear xs; intros x xs.
        apply (caseS' ys); clear ys; intros y ys.
        intros.
        simpl.
        unfold eq_rect_r.
        rewrite (rewrite_vect_eqtrans _ _ ).
        match goal with
        | [ |- _ = nth (rew ?eq in _) _ ] => generalize eq
        end.
        intro eq.
        rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ eq).
        simpl.
        match goal with
        | [ |- _ = nth (append ?xs ?ys) _ ] =>
          rewrite (nth_append_l _ _ _ xs ys j)
        end.
        rewrite (nth_map _ _ _ _ eq_refl).
        reflexivity.
    - intro j.
      apply (caseS' xs); clear xs; intros x xs.
      simpl.
      unfold eq_rect_r.
      rewrite (rewrite_vect_eqtrans _ _ ).
      match goal with
      | [ |- _ = nth (rew ?eq in _) _ ] => generalize eq
      end.
      intro eq.
      rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ eq).
      simpl.
      rewrite nth_append_r.
      auto.
  Qed.

  CoFixpoint empty {n : nat}: Enumeration n := Skip _ empty.
  CoFixpoint singleton x: Enumeration 1 := Cons _ (cons _ x _ (nil _)) empty.
  Fixpoint index n
  