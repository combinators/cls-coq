Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.NArith.NArith.
Require Import Coq.NArith.Nnat.
Require Import Coq.NArith.Ndigits.
Require Import Coq.Vectors.Vector.
Require Import VectorQuantification.
Require Import Coq.Logic.Eqdep_dec.

Import EqNotations.

Class Countable (A: Set) : Set :=
  { toNat : A -> nat;
    fromNat : nat -> A;
    fromTo_id : forall x, fromNat (toNat x) = x }.

Class Finite (A : Set) : Set :=
  { cardinality : nat;
    toFin : A -> Fin.t cardinality;
    fromFin : Fin.t cardinality -> A;
    fromToFin_id : forall x, fromFin (toFin x) = x }.

Class NonEmptyFinite (A: Set): Set :=
  { IsFinite :> Finite A;
    cardinality_nonempty: cardinality = 0 -> False }.

Definition toNatFromToFin {A: Set} {card: nat} (toFin: A -> Fin.t card): A -> nat :=
  fun x => proj1_sig (Fin.to_nat (toFin x)).

Definition fromNatFromFromFin {A: Set} {card: nat} (fromFin: Fin.t card -> A) (not_empty: card = 0 -> False): nat -> A:=
  fun n =>
    match lt_dec n card with
    | left ltprf => fromFin (Fin.of_nat_lt ltprf)
    | _ =>
      match card as card' return (card' = 0 -> False) -> (Fin.t card' -> A) -> A with
      | S n => fun ne fromFin => fromFin Fin.F1
      | 0 => fun ne _ => False_rect _ (ne eq_refl)
      end not_empty fromFin
    end.

Lemma fromTo_of_FromFin:
  forall {A: Set} {card: nat} (toFin: A -> Fin.t card) (fromFin: Fin.t card -> A)
    (not_empty: card = 0 -> False)
    (fromToFin_id : forall x, fromFin (toFin x) = x) x,
    fromNatFromFromFin fromFin not_empty (toNatFromToFin toFin x) = x.
Proof.
  intros A card toFin fromFin not_empty fromToFin_id x.
  unfold toNatFromToFin.
  unfold fromNatFromFromFin.
  generalize (proj2_sig (Fin.to_nat (toFin x))).
  intro lt_prf.
  destruct (lt_dec (proj1_sig (Fin.to_nat (toFin x))) card) as [ prf | disprf ].
  - rewrite (Fin.of_nat_ext prf (proj2_sig (Fin.to_nat (toFin x)))).
    rewrite Fin.of_nat_to_nat_inv.
    auto.
  - contradiction.
Qed.

Instance CountableFromFinite A `{NonEmptyFinite A}: Countable A :=
  {| toNat := toNatFromToFin toFin;
     fromNat := fromNatFromFromFin fromFin cardinality_nonempty;
     fromTo_id := fromTo_of_FromFin toFin fromFin cardinality_nonempty fromToFin_id
  |}.

Lemma add_succ_succ: forall n, S (S (n + n)) = S n + S n.
Proof.
  intro n.
  simpl.
  rewrite Nat.add_succ_r.
  reflexivity.
Qed.
  
Definition merge {A: Type} {n :nat} (xs: t A n) (ys: t A n): t A (n + n) :=
  (fix merge_rec n : t A n -> t A n -> t A (n + n) :=
     match n as n' return t A n' -> t A n' -> t A (n' + n') with
     | 0 => fun (xs: t A 0) (ys: t A 0) => nil A
     | S n =>
       fun (xs: t A (S n)) (ys: t A (S n)) =>
         rew (add_succ_succ n) in
           cons A (hd xs) (S (n + n)) (cons A (hd ys) (n + n) (merge_rec n (tl xs) (tl ys)))
     end) n xs ys.

Definition unmerge {A: Type} {n: nat} (xys: t A (n + n)): (t A n) * (t A n) :=
  (fix unmerge_rec n :=
     match n as n' return t A (n' + n') -> (t A n') * (t A n')  with
     | 0 => fun _ => (nil A, nil A)
     | S n => fun xys => (cons A (hd xys) n
                           (fst (unmerge_rec n (tl (rew [t A] (Nat.add_succ_r n n) in tl xys)))),
                      cons A (hd (rew [t A] (Nat.add_succ_r n n) in tl xys)) n
                           (snd (unmerge_rec n (tl (rew [t A] (Nat.add_succ_r n n) in tl xys)))))
     end) n xys.

Lemma merge_inj {A: Type} {n: nat}:
  forall (xs ys: t A n), unmerge (merge xs ys) = (xs, ys).
Proof.
  intro xs.
  induction xs as [ | x n xs IH ].
  - apply case0.
    reflexivity.
  - intro ys.
    apply (caseS' ys); clear ys; intros y ys.
    fold (fst (xs, ys)).
    rewrite <- (f_equal fst (IH ys)) at 2.
    fold (snd (xs, ys)).
    rewrite <- (f_equal snd (IH ys)) at 4.
    unfold fst at 1.
    unfold snd at 1.
    simpl.
    clear IH.
    assert (rew_hd_eq : forall n m xs x (eq: S m = S n), hd (rew [t A] eq in (cons _ x _ xs)) = x).
    { clear ...
      intros n m xs x eq.
      destruct m; destruct n;
        inversion eq as [ eq' ].
      - rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ eq).
        reflexivity.
      - revert eq.
        rewrite <- eq'.
        intro eq.
        rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ eq).
        reflexivity. }
    assert (rew_tl_eq : forall n m xs x (eq: S m = S n),
               tl (rew [t A] eq in (cons _ x _ xs)) = rew [t A] (Nat.succ_inj _ _ eq) in xs).
    { clear ...
      intros n m xs x eq.
      destruct m; destruct n;
        inversion eq as [ eq' ].
      - rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ eq).
        rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ (Nat.succ_inj _ _ eq)).
        reflexivity.
      - revert eq.
        rewrite <- eq'.
        intro eq.
        rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ eq).
        rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ (Nat.succ_inj _ _ eq)).
        reflexivity. }
    rewrite rew_hd_eq.
    rewrite (rew_tl_eq).
    assert (rew_eq_trans:
              rew [t A] Nat.add_succ_r n n in
               rew [t A] Nat.succ_inj (S (n + n)) (n + S n) (add_succ_succ n) in
               (cons A y (n + n) (merge xs ys)) =
               (cons A y (n + n) (merge xs ys))).
    { clear ...
      generalize (Nat.add_succ_r n n).
      intro eq1.
      generalize (Nat.succ_inj (S (n + n)) (n + S n) (add_succ_succ n)).
      intro eq2.
      revert eq1.
      rewrite <- eq2.
      simpl.
      intro eq1.
      rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ eq1).
      reflexivity. }   
    rewrite rew_eq_trans.
    simpl.
    reflexivity.
Qed.

Lemma max_fill_eq:
  forall m n, m + (max m n - m) = max m n.
Proof.
  intros m n.
  rewrite Nat.add_comm.
  apply Nat.sub_add.
  apply Nat.le_max_l.
Qed.

Definition cantor_pair (m n: nat) : nat :=
  let m' := N.of_nat m in
  let n' := N.of_nat n in
  N.to_nat
    (Bv2N ((S (max (N.size_nat m') (N.size_nat n'))) + S (max (N.size_nat m') (N.size_nat n')))
          (merge (shiftin true (N2Bv_gen (max (N.size_nat m') (N.size_nat n')) m'))
                 (shiftin true (N2Bv_gen (max (N.size_nat m') (N.size_nat n')) n')))).

Lemma merge_last {A: Type} {n : nat}:
  forall (xs ys: t A n) x y, last (merge (shiftin x xs) (shiftin y ys)) = y.
Proof.
  induction n as [ | n IH ].
  - intro xs.
    apply (fun r => case0 (fun xs => forall ys x y, last (merge (shiftin x xs) (shiftin y ys)) = y) r xs).
    intro ys.
    apply (fun r => case0 (fun ys => forall x y, last (merge (shiftin x (nil A)) (shiftin y ys)) = y) r ys).
    intros.
    simpl.
    generalize (add_succ_succ 0).
    intro eq.
    simpl in eq.
    rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ eq).
    reflexivity.
  - intros xs ys.
    apply (caseS' xs); clear xs; intros x xs.
    apply (caseS' ys); clear ys; intros y ys.
    intros x' y'.
    generalize (IH xs ys x' y').
    simpl.
    generalize (add_succ_succ (S n)).
    intro eq.
    simpl in eq.
    revert eq.
    rewrite (Nat.add_succ_r n (S n)).
    intro eq.
    rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ eq).
    generalize (add_succ_succ n).
    intro eq'.
    simpl in eq'.
    revert eq'.
    rewrite (Nat.add_succ_r n n).
    intro eq'.
    rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ eq').
    simpl.
    intro; assumption.
Qed.

Lemma cantor_pair_size: forall m n,
    N.size_nat (N.of_nat (cantor_pair m n)) = (S (max (N.size_nat (N.of_nat m))
                                                         (N.size_nat (N.of_nat n)))) +
                                              (S (max (N.size_nat (N.of_nat m))
                                                      (N.size_nat (N.of_nat n)))).
Proof.
  intros m n.
  unfold cantor_pair.
  rewrite N2Nat.id.
  apply Bv2N_Nsize_1.
  unfold Bvector.Bsign.
  rewrite merge_last.
  reflexivity.
Qed.

Lemma sub_1 : forall n, ((S n) - 1) = n.
Proof.
  intro n.
  rewrite Nat.sub_succ.
  rewrite Nat.sub_0_r.
  reflexivity.
Qed.

Definition clear_last {n: nat} (xs: t bool n): t bool (n - 1) :=
  match n as n' return t bool n' -> t bool (n' - 1)  with
  | S n => fun xs => rew <- [t bool] (sub_1 n) in shiftout xs
  | 0 => fun xs => nil _
  end xs.

Lemma clear_last_shiftin {n : nat}:
  forall (xs: t bool n) b, clear_last (shiftin b xs) = rew <- (sub_1 n) in xs.
Proof.
  intros xs b.
  unfold clear_last.
  rewrite <- (shiftout_shiftin _ b).
  reflexivity.
Qed.

Definition cantor_pair_inv (o : nat): (nat * nat) :=
  let (m, n) := unmerge (N2Bv_gen (N.size_nat (N.of_nat o) / 2 + N.size_nat (N.of_nat o) / 2)%nat  (N.of_nat o)) in
  (N.to_nat (Bv2N _ (clear_last m)), N.to_nat (Bv2N _ (clear_last n))).

Lemma max_mn_plus: forall m n, max m n = m + (max m n - m).
Proof.
  intros m n.
  destruct (Nat.max_dec m n) as [ maxm | maxn ].
  - rewrite maxm.
    rewrite Nat.sub_diag.
    rewrite Nat.add_0_r.
    reflexivity.
  - rewrite maxn.
    rewrite Nat.add_comm.
    rewrite Nat.sub_add.
    + reflexivity.
    + apply Nat.max_l_iff.
      rewrite Nat.max_comm.
      assumption.
Qed.

Lemma Bv_append:
  forall (a: N) (k: nat),
    Bv2N _ (append (N2Bv a) (const false k)) = a.
Proof.
  intros a.
  induction a as [ | a ].
  - intro k.
    simpl.
    induction k as [ | k IH ].
    + reflexivity.
    + simpl.
      rewrite IH.
      reflexivity.
  - induction a as [ a IH | a IH | ].
    + intro k.
      simpl.
      rewrite IH.
      reflexivity.
    + intro k.
      simpl.
      rewrite IH.
      reflexivity.
    + intro k.
      simpl.
      assert (const_zero : Bv2N k (const false k) = 0%N). 
      { induction k as [ | k IH ].
        * reflexivity.
        * simpl.
          rewrite IH.
          reflexivity. }
      rewrite const_zero.
      reflexivity.
Qed.        

Lemma cantor_pair_inj: forall m n, (m, n) = cantor_pair_inv (cantor_pair m n).
Proof.
  intros m n.
  unfold cantor_pair_inv.
  rewrite cantor_pair_size.
  set (max_mn := S (Nat.max (N.size_nat (N.of_nat m)) (N.size_nat (N.of_nat n)))). 
  set (maxs := max_mn + max_mn).
  assert (size_eq: maxs / 2 + maxs / 2 = maxs).
  { fold (Nat.double (maxs / 2)).
    rewrite Nat.double_twice.
    assert (even_prf: Nat.modulo maxs 2 = 0).
    { fold (Nat.double max_mn) in maxs.
      set (maxs_eq := Nat.double_twice max_mn).
      unfold maxs.
      rewrite maxs_eq.
      rewrite Nat.mul_comm.
      rewrite Nat.mod_mul.
      - reflexivity.
      - apply (not_eq_sym (O_S 1)). }
    apply eq_sym.
    apply (proj2 (Nat.div_exact maxs 2 (not_eq_sym (O_S 1)))).
    assumption. }
  unfold cantor_pair.
  rewrite N2Nat.id.
  fold maxs.
  assert (bv_id:
            forall n xs (eq: (n / 2) + (n / 2) = n),
              N2Bv_gen ((n / 2) + (n / 2)) (Bv2N n xs) = rew <- eq in xs).
  { clear...
    intros n xs eq.
    rewrite eq.
    apply N2Bv_Bv2N. }
  rewrite (bv_id _ _ size_eq).
  clear bv_id.
  assert (max_mn_eq : maxs / 2 = max_mn).
  { unfold maxs.
    fold (Nat.double max_mn).
    rewrite (Nat.double_twice).
    rewrite (Nat.mul_comm).
    apply Nat.div_mul.
    apply (not_eq_sym (O_S 1)). }
  fold max_mn.
  assert (unmerge_merge_eq:
            forall m n (xs ys : t bool m) (eq: n + n = m + m) (eq' : n = m),
              @unmerge _ n (rew <- eq in @merge _ m xs ys) = (rew <- eq' in xs, rew <- eq' in ys)).
  { clear ...
    intros m n xs ys eq eq'.
    revert eq.
    rewrite eq'.
    intro eq.
    unfold eq_rect_r.
    rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ (eq_sym eq)).
    simpl.
    rewrite merge_inj.
    reflexivity. }
  rewrite (unmerge_merge_eq _ _ _ _ size_eq max_mn_eq).
  rewrite max_mn_eq.
  unfold eq_rect_r.
  simpl eq_rect.
  unfold max_mn.
  rewrite (clear_last_shiftin).
  rewrite (clear_last_shiftin).
  rewrite sub_1.
  unfold eq_rect_r.
  simpl.
  match goal with
  | [|- (m, n) = (?xs, ?ys) ] =>
    assert (m_eq: m = xs);
      [ | assert (n_eq: n = ys) ] 
  end.
  - rewrite (max_mn_plus).
    rewrite N2Bv_N2Bv_gen_above.
    rewrite Bv_append.
    rewrite Nat2N.id.
    reflexivity.
  - rewrite (Nat.max_comm).
    rewrite (max_mn_plus).
    rewrite N2Bv_N2Bv_gen_above.
    rewrite Bv_append.
    rewrite Nat2N.id.
    reflexivity.
  - rewrite m_eq at 1.
    rewrite n_eq at 3.
    reflexivity.
Qed.

Definition cantor_sum (mn: nat + nat) : nat :=
  match mn with
  | inl m => 2 * m
  | inr n => (2 * n) + 1
  end.

Definition cantor_sum_inv (mn: nat): nat + nat :=
  match Nat.modulo mn 2 with
  | 0 => inl (mn / 2)
  | _ => inr (mn / 2)
  end.

Lemma cantor_sum_inj: forall mn, cantor_sum_inv (cantor_sum mn) = mn.
Proof.
  intro mn.
  destruct mn.
  - simpl.
    rewrite Nat.add_0_r.
    unfold cantor_sum_inv.
    fold (Nat.double n).
    rewrite (Nat.double_twice).
    rewrite (Nat.mul_comm).
    rewrite Nat.mod_mul.
    + apply f_equal.
      apply Nat.div_mul.
      apply not_eq_sym.
      apply O_S.
    + apply not_eq_sym.
      apply O_S.
  - simpl.
    rewrite Nat.add_0_r.
    unfold cantor_sum_inv.
    rewrite (Nat.add_comm).
    fold (Nat.double n).
    rewrite (Nat.double_twice).
    rewrite (Nat.mul_comm).
    rewrite (Nat.mod_add).
    + rewrite Nat.div_add.
      * reflexivity.
      * apply not_eq_sym.
        apply O_S.
    + apply not_eq_sym.
      apply O_S.
Qed.

Definition cantor_fin_fun (card: nat) (f: Fin.t card -> nat): nat :=
  (fix cantor_fin_fun_rec n xs : nat :=
     match xs with
     | nil _ => 0
     | cons _ x _ xs => cantor_pair x (cantor_fin_fun_rec _ xs)
     end) _ (map f (positions card)).

Definition cantor_fin_fun_inv (card: nat) (n: nat): Fin.t card -> nat :=
  nth ((fix cantor_fin_fun_inv_rec card n : t nat card :=
          match card with
          | 0 => nil _
          | S card => cons _ (fst (cantor_pair_inv n))
                          _ (cantor_fin_fun_inv_rec card (snd (cantor_pair_inv n)))
          end) card n).

Lemma cantor_fin_fun_ext_inj:
  forall (card: nat) (f: Fin.t card -> nat) x, f x = cantor_fin_fun_inv _ (cantor_fin_fun card f) x.
Proof.
  intros card f x.
  unfold cantor_fin_fun.
  unfold cantor_fin_fun_inv.
  induction x as [ | card x IH ].
  - simpl.
    rewrite <- cantor_pair_inj.
    reflexivity.
  - rewrite (IH (fun x => f (Fin.FS x))).
    simpl.
    rewrite <- map_fg.
    rewrite <- cantor_pair_inj.
    reflexivity.
Qed.

Lemma cantor_fin_fun_idem:
  forall (card: nat) (f: Fin.t card -> nat),
    cantor_fin_fun_inv _ (cantor_fin_fun card f) =
    cantor_fin_fun_inv card (cantor_fin_fun card (cantor_fin_fun_inv _ (cantor_fin_fun card f))).
Proof.
  intros card f.
  unfold cantor_fin_fun_inv at 2.
  unfold cantor_fin_fun at 2.
  rewrite <- (map_extensional _ _ _ (cantor_fin_fun_ext_inj card f)).
  unfold cantor_fin_fun.
  unfold cantor_fin_fun_inv.
  reflexivity.
Qed.