Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.NArith.NArith.
Require Import Coq.NArith.Nnat.
Require Import Coq.NArith.Ndigits.
Require Import Coq.Vectors.Vector.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Arith.Compare_dec.
Require Import VectorQuantification.
Require Import Coq.Logic.Eqdep_dec.

Import EqNotations.

Class Countable (A: Type) : Type :=
  { toNat : A -> nat;
    fromNat : nat -> A;
    fromTo_id : forall x, fromNat (toNat x) = x }.

Class Finite (A : Type) : Type :=
  { cardinality : nat;
    toFin : A -> Fin.t cardinality;
    fromFin : Fin.t cardinality -> A;
    fromToFin_id : forall x, fromFin (toFin x) = x;
    toFromFin_id : forall x, toFin (fromFin x) = x }.

Class NonEmptyFinite (A: Type): Type :=
  { IsFinite :> Finite A;
    cardinality_nonempty: cardinality = 0 -> False }.

Definition toNatFromToFin {A: Type} {card: nat} (toFin: A -> Fin.t card): A -> nat :=
  fun x => proj1_sig (Fin.to_nat (toFin x)).

Definition fromNatFromFromFin {A: Type} {card: nat} (fromFin: Fin.t card -> A) (not_empty: card = 0 -> False): nat -> A:=
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
  forall {A: Type} {card: nat} (toFin: A -> Fin.t card) (fromFin: Fin.t card -> A)
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
    match goal with
    | [ |- (cons _ _ _ (fst (unmerge (tl ?vect))), _) = _ ] =>
      assert (rew_eq_trans: vect = (cons A y (n + n) (merge xs ys)))
    end.
    { clear ...
      generalize (Nat.add_succ_r n n).
      intro eq1.
      generalize (Nat.succ_inj (S (n + n)) (n + S n) (add_succ_succ n)).
      intro eq2.
      rewrite (UIP_dec (Nat.eq_dec) eq2 (eq_sym eq1)).
      clear eq2.
      match goal with
      |[|- rew _ in rew _ in ?M = _ ] =>
       generalize M
      end.
      rewrite <- eq1.
      intro; reflexivity. }
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
    match goal with
    |[|- last ?merged = _ -> _ ] =>
     generalize merged
    end.
    clear ...
    generalize (add_succ_succ (S n)).
    intro eq.
    cbv in eq.
    fold (Nat.add n (S n)) in eq.
    fold (Nat.add n (S (S n))) in eq.
    fold (Nat.add n (S n)).
    fold (Nat.add n (S (S n))).
    revert eq.
    rewrite (Nat.add_succ_r n (S n)).
    intros eq xs last_eq.
    rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ eq).
    simpl.
    exact last_eq.
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

Definition vectToNat {A: Type} (toNat: A -> nat) {n: nat} (xs: t A n): nat :=
  (fix vectToNat_rec (n: nat) (xs: t A n): nat :=
     match xs with
     | nil _ => 0
     | cons _ x n xs => cantor_pair (toNat x) (vectToNat_rec _ xs)
     end) _ xs.

Definition vectFromNat {A: Type} (fromNat: nat -> A) (m: nat) (n: nat): t A m :=
  (fix vectFromNat_rec m n: t A m :=
     match m with
     | 0 => nil _
     | S m => cons _ (fromNat (fst (cantor_pair_inv n))) _
                  (vectFromNat_rec m (snd (cantor_pair_inv n)))
     end) m n.

Lemma vect_inj:
  forall (A: Type) n (xs: t A n) (fromNat: nat -> A) (toNat: A -> nat)
    (IH: Forall (fun x => fromNat (toNat x) = x) xs),
    vectFromNat fromNat n (vectToNat toNat xs) = xs.
Proof.
  intros A n xs fromNat toNat prfs.
  induction prfs as [ | n x xs prf prfs IH ].
  - reflexivity.
  - unfold vectToNat.
    unfold vectFromNat.
    rewrite <- cantor_pair_inj.
    unfold fst.
    unfold snd.
    rewrite prf.
    apply f_equal.
    apply IH.
Defined.

Definition listToNat {A: Type} (toNat: A -> nat) (xs: list A): nat :=
  cantor_pair (length xs) (vectToNat toNat (of_list xs)).

Definition listFromNat {A: Type} (fromNat: nat -> A) (n : nat): list A :=
  to_list (vectFromNat fromNat (fst (cantor_pair_inv n)) (snd (cantor_pair_inv n))).

Lemma listToNat_inj:
  forall (A: Type) (xs: list A) (fromNat: nat -> A) (toNat: A -> nat)
    (IH: List.Forall (fun x => fromNat (toNat x) = x) xs),
    listFromNat fromNat (listToNat toNat xs) = xs.
Proof.
  intros A xs fromNat toNat prfs.
  unfold listFromNat.
  unfold listToNat.
  rewrite <- cantor_pair_inj.
  simpl fst.
  simpl snd.
  rewrite (vect_inj A _ _ fromNat toNat (ListForall_Forall _ prfs)).
  rewrite to_list_of_list_opp.
  reflexivity.
Qed.

Lemma n_add_sub_le_lt: forall n k j, n < k + j -> n >= k -> n - k < j.
Proof.
  intros n k j n_lt n_ge.
  rewrite Nat.add_comm in n_lt.
  destruct (Nat.lt_trichotomy (n - k) j) as [ | [ nk_eq | nk_gt ] ]; [ assumption | | ].
  - rewrite <- nk_eq in n_lt.
    rewrite (Nat.sub_add _ _ n_ge) in n_lt.
    assert False; [ | contradiction ].
    apply (Nat.nle_succ_diag_l n).
    exact n_lt.
  - generalize (proj2 (Nat.lt_add_lt_sub_r _ _ _) nk_gt).
    intro n_gt.
    assert False; [| contradiction].
    apply (@asymmetry nat lt (StrictOrder_Asymmetric Nat.lt_strorder) (j + k) n); assumption.
Qed.      

Definition toFin_union {A B: Type} `{finA: Finite A} `{finB: Finite B} (x: A + B):
  Fin.t ((@cardinality A finA) + (@cardinality B finB)) :=
  match x with
  | inl a => Fin.L _ (toFin a)
  | inr b => Fin.R _ (toFin b)
  end.

Definition fromFin_union {A B: Type} `{finA: Finite A} `{finB: Finite B}
           (x: Fin.t ((@cardinality A finA) + (@cardinality B finB))): A + B :=
  match le_lt_dec (@cardinality A finA) (proj1_sig (Fin.to_nat x)) with
  | right n_lt => inl (fromFin (Fin.of_nat_lt n_lt))
  | left n_gte => inr (fromFin (Fin.of_nat_lt (n_add_sub_le_lt _ _ _ (proj2_sig (Fin.to_nat x)) n_gte)))
  end.

Lemma fromToFin_union_id {A B: Type} `{finA: Finite A} `{finB: Finite B}:
  forall (x: A + B), fromFin_union (toFin_union x) = x.
Proof.
  intro x.
  destruct x as [ a | b ].
  - simpl.
    generalize (Fin.L_sanity (@cardinality B finB) (toFin a)).
    intro l_sane.
    unfold fromFin_union.
    match goal with
    |[|- match ?x with | _ => _ end = _ ] =>
     destruct x as [ n_gte | n_lt ]
    end.
    + assert False; [ | contradiction ].
      rewrite l_sane in n_gte.
      generalize (proj2_sig (Fin.to_nat (toFin a))).
      intro devil.
      apply (@irreflexivity nat lt _ _ (Nat.lt_le_trans _ _ _ devil n_gte)).
    + revert n_lt.
      rewrite l_sane.
      intro n_lt.
      rewrite (Fin.of_nat_ext n_lt (proj2_sig (Fin.to_nat (toFin a)))).
      rewrite (Fin.of_nat_to_nat_inv).
      rewrite (fromToFin_id a).
      reflexivity.
  - simpl.
    generalize (Fin.R_sanity (@cardinality A finA) (toFin b)).
    intro r_sane.
    unfold fromFin_union.
    match goal with
    |[|- match ?x with | _ => _ end = _ ] =>
     destruct x as [ n_gte | n_lt ]
    end.
    + match goal with
      |[|- context [ n_add_sub_le_lt ?a ?b ?c ?d ?e] ] =>
       generalize (n_add_sub_le_lt a b c d e)
      end.
      revert n_gte.
      rewrite r_sane.
      intro n_gte.
      rewrite Nat.add_comm.
      rewrite (Nat.add_sub).
      intro prf.
      rewrite (Fin.of_nat_ext prf (proj2_sig (Fin.to_nat (toFin b)))).
      rewrite (Fin.of_nat_to_nat_inv (toFin b)).
      rewrite (fromToFin_id b).
      reflexivity.
    + assert False; [ | contradiction ].
      rewrite r_sane in n_lt.
      generalize (Nat.le_lt_trans _ _ _ (Nat.le_add_r _ _) n_lt).
      intro devil.
      apply (@irreflexivity nat lt _ _ devil).
Qed.

Lemma toFromFin_union_id  {A B: Type} `{finA: Finite A} `{finB: Finite B}:
  forall (x: Fin.t ((@cardinality A finA) + (@cardinality B finB))), toFin_union (fromFin_union x) = x.
Proof.
  intro x.
  unfold fromFin_union.
  remember (Fin.to_nat x) as xnat eqn:xnat_eq.
  destruct (le_lt_dec (@cardinality A finA) (proj1_sig xnat)).
  - unfold toFin_union.
    rewrite (toFromFin_id).
    apply (Fin.to_nat_inj).
    rewrite (Fin.R_sanity).
    rewrite (Fin.to_nat_of_nat _).
    simpl.
    rewrite Nat.add_comm.
    rewrite (Nat.sub_add); [| assumption ].
    rewrite xnat_eq.
    reflexivity.
  - unfold toFin_union.
    apply (Fin.to_nat_inj).
    rewrite (Fin.L_sanity).
    rewrite (toFromFin_id).
    rewrite (Fin.to_nat_of_nat).
    simpl.
    rewrite xnat_eq.
    reflexivity.
Qed.      

Instance FiniteUnion (A B: Type) `(finA: Finite A) `(finB: Finite B): Finite (A + B) :=
  { cardinality := (@cardinality A finA) + (@cardinality B finB);
    toFin := toFin_union;
    fromFin := fromFin_union;
    fromToFin_id := fromToFin_union_id;
    toFromFin_id := toFromFin_union_id }.

Definition toFin_product {A B: Type} `{finA: Finite A} `{finB: Finite B} (x: A * B):
  Fin.t ((@cardinality A finA) * (@cardinality B finB)) :=
  Fin.depair (toFin (fst x)) (toFin (snd x)).

Definition fromFin_product {A B: Type} `{finA: Finite A} `{finB: Finite B}
           (x: Fin.t ((@cardinality A finA) * (@cardinality B finB))): A * B :=
  (@fromFin A finA (@Fin.of_nat_lt
                      (Nat.div (proj1_sig (Fin.to_nat x)) (@cardinality B finB))
                      (@cardinality A finA)
                      (Nat.div_lt_upper_bound _ (@cardinality B finB) _
                                              (fun eq => Fin.case0 (fun _ => False)
                                                                (rew [Fin.t] Nat.mul_0_r _ in
                                                                    rew [fun x => Fin.t (_ * x)] eq in x))
                                              (rew [fun x => _ < x] Nat.mul_comm _ _ in proj2_sig (Fin.to_nat x)))),
   @fromFin B finB (@Fin.of_nat_lt
                      (Nat.modulo (proj1_sig (Fin.to_nat x)) (@cardinality B finB))
                      (@cardinality B finB)
                      (Nat.mod_upper_bound _ _
                                           (fun eq => Fin.case0 (fun _ => False)
                                                             (rew [Fin.t] Nat.mul_0_r _ in
                                                                 rew [fun x => Fin.t (_ * x)] eq in x))))).

Lemma fromToFin_product_id {A B: Type} `{finA: Finite A} `{finB: Finite B}:
  forall (x: A * B), fromFin_product (toFin_product x) = x.
Proof.
  intro x.
  unfold fromFin_product.
  match goal with
  |[|- (fromFin (Fin.of_nat_lt ?p1), fromFin (Fin.of_nat_lt ?p2)) = _] =>
   generalize p1 p2
  end.
  unfold toFin_product.
  rewrite Fin.depair_sanity.
  rewrite (Nat.mul_comm).
  rewrite (Nat.add_comm).
  rewrite (Nat.mod_add).
  - rewrite (Nat.mod_small _ _ (proj2_sig (Fin.to_nat _))).
    rewrite (Nat.div_add).
    + rewrite (Nat.div_small _ _ (proj2_sig (Fin.to_nat _))).
      simpl.
      do 2 (intro eq;
            rewrite (Fin.of_nat_ext eq (proj2_sig (Fin.to_nat _)));
            clear eq;
            rewrite (Fin.of_nat_to_nat_inv);
            rewrite fromToFin_id
           ).
      destruct x; reflexivity.
    + intro eq.
      apply Fin.case0.
      rewrite <- eq.
      apply (toFin (snd x)).
  - intro eq.
    apply Fin.case0.
    rewrite <- eq.
    apply (toFin (snd x)).
Qed.

Lemma toFromFin_product_id  {A B: Type} `{finA: Finite A} `{finB: Finite B}:
  forall (x: Fin.t ((@cardinality A finA) * (@cardinality B finB))), toFin_product (fromFin_product x) = x.
Proof.
  intro x.
  unfold toFin_product.
  apply (Fin.to_nat_inj).
  rewrite (Fin.depair_sanity).
  unfold fromFin_product.
  simpl.
  repeat (rewrite (toFromFin_id); rewrite (Fin.to_nat_of_nat)).
  simpl.
  rewrite (Nat.mod_eq).
  - rewrite (Nat.add_comm).
    rewrite (Nat.sub_add).
    + reflexivity.
    + apply (Nat.mul_div_le).
      intro eq.
      apply (Fin.case0).
      rewrite eq in x.
      rewrite (Nat.mul_0_r _) in x.
      exact x.
  - intro eq.
    apply (Fin.case0).
    rewrite eq in x.
    rewrite (Nat.mul_0_r _) in x.
    exact x.
Qed.

Instance FiniteProduct (A B: Type) `(finA: Finite A) `(finB: Finite B): Finite (A * B) :=
  { cardinality := (@cardinality A finA) * (@cardinality B finB);
    toFin := toFin_product;
    fromFin := fromFin_product;
    fromToFin_id := fromToFin_product_id;
    toFromFin_id := toFromFin_product_id }.


Lemma fromToFin_bijection_id {A B: Type} `{finA: Finite A}
      (f : A -> B) (g : B -> A) (fg_eq: forall x, f (g x) = x):
  forall x, f (fromFin (toFin (g x))) = x.
Proof.
  intro x.
  rewrite (fromToFin_id (g x)).
  exact (fg_eq x).
Qed.

Lemma toFromFin_bijection_id {A B: Type} `{finA: Finite A}
      (f : A -> B) (g : B -> A) (gf_eq: forall x, g (f x) = x):
  forall x, toFin (g (f (fromFin x))) = x.
Proof.
  intro x.
  rewrite (gf_eq (fromFin x)).
  exact (toFromFin_id x).
Qed. 

Instance FiniteBijection (A B: Type) `(finA: Finite A)
         (f : A -> B) (g : B -> A) (fg_eq: forall x, f (g x) = x) (gf_eq: forall x, g (f x) = x): Finite B :=
  { cardinality := @cardinality A finA;
    toFin x := toFin (g x);
    fromFin x := f (fromFin x);
    fromToFin_id := fromToFin_bijection_id f g fg_eq;
    toFromFin_id := toFromFin_bijection_id f g gf_eq }.

Instance FinFinite (n: nat): Finite (Fin.t n) :=
  { cardinality := n;
    toFin x := x;
    fromFin x := x;
    fromToFin_id x := eq_refl;
    toFromFin_id x := eq_refl }.

Instance UnitFinite: Finite unit :=
  { cardinality := 1;
    toFin x := Fin.F1;
    fromFin x := tt;
    fromToFin_id x := match x with | tt => eq_refl end;
    toFromFin_id x := match x as x' in Fin.t (S n') return n' = 0 -> @Fin.F1 n'  = x' with
                      | Fin.F1 => fun _ => eq_refl
                      | Fin.FS n => fun devil => False_rect _ (Fin.case0 (fun _ => False)  (rew devil in n))
                      end eq_refl }.
