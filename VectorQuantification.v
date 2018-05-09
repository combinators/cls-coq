Require Import Coq.Lists.List.
Require Import Coq.Vectors.Fin.
Require Import Coq.Vectors.Vector.
Require Import Coq.Sorting.Permutation.

Require Import Logic.Eqdep_dec.
Require Import Arith.PeanoNat.
Require Import Arith.Peano_dec.

Import EqNotations.

Definition table_of {n: nat} {A: Type} (f: Fin.t n -> A): t A n :=
  (fix table_of_rec n (f: Fin.t n -> A) {struct n}: t A n :=
     match n as n' return (Fin.t n' -> A) -> t A n' with
     | 0 => fun _ => nil _
     | S n => fun f => cons _ (f (@F1 n)) _ (table_of_rec n (fun x => f (FS x)))
     end f) n f.

Lemma table_of_inv {n : nat} {A: Type}: forall (f: Fin.t n -> A) x, nth (table_of f) x = f x.
Proof.
  induction n as [ | n IH ]; intros f x.
  - inversion x.
  - apply (Fin.caseS' x).
    + reflexivity.
    + intro p.
      simpl.
      rewrite IH.
      reflexivity.
Qed.

Lemma shiftin_shiftout {T : Type} {n : nat}:
  forall (xs: t T (S n)),
    xs = shiftin (last xs) (shiftout xs).
Proof.
  induction n as [ | n IH ]; intro xs.
  - apply (caseS' xs).
    clear xs; intros x xs.
    apply (fun r => case0 (fun xs => cons _ _ _ xs = shiftin (last (cons _ _ _ xs)) (shiftout (cons _ _ _ xs))) r xs).
    reflexivity.
  - apply (caseS' xs).
    clear xs; intros x xs.
    simpl.
    rewrite (IH xs) at 1.
    reflexivity.
Qed.

Lemma shiftout_shiftin {T : Type} {n : nat}:
  forall (xs: t T n) x,
    xs = shiftout (shiftin x xs).
Proof.
  induction n as [ | n IH ]; intro xs.
  - intro.
    apply (fun r => case0 (fun xs => xs = shiftout (shiftin _ xs)) r xs).
    reflexivity.
  - apply (caseS' xs).
    clear xs; intros x xs x'.
    simpl.
    rewrite (IH xs) at 1.
    reflexivity.
Qed.
  
Lemma rewrite_vect {S T: Type} {n n': nat}:
  forall (P : forall n, (t S n) -> T) (n_eq: n = n') (xs: t S n),
    P _ (rew [fun n => t S n] n_eq in xs) = P _ xs.
Proof.
  intros P.
  destruct n; destruct n';
    intro n_eq;
    try solve [ inversion n_eq ].
  - intros; destruct n_eq; reflexivity.
  - inversion n_eq as [ n_eq' ].
    generalize n_eq.
    clear n_eq.
    rewrite n_eq'.
    intros n_eq xs.
    rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ n_eq).
    reflexivity.
Qed.

Lemma Vector_tl_ineq:
  forall {T} (x : T) {n} xs ys, xs <> ys -> cons T x n xs <> cons T x n ys.
Proof.
  intros T x n xs ys ineq.
  intro devil.
  injection devil as devil.
  contradict ineq.
  apply inj_pair2_eq_dec.
  - apply Nat.eq_dec.
  - exact devil.
Qed.

Definition Vector_eq_dec: forall {T} {n} (t_eq_dec: forall (x y: T), {x = y} + {x <> y}) (xs ys: t T n), {xs = ys} + {xs <> ys}.
Proof.
  intros T n t_eq_dec xs.
  induction xs as [ | x n xs IH ]; intros ys.
  - apply (fun P prf => case0 P prf ys).
    left; reflexivity.
  - apply (caseS' ys).
    clear ys; intros y ys.
    destruct (t_eq_dec x y) as [ x_eq | x_ineq ].
    + rewrite x_eq.
      destruct (IH ys) as [ xs_eq | ].
      * rewrite xs_eq.
        left; reflexivity.
      * right; apply Vector_tl_ineq; assumption.
    + right; intro devil; inversion devil.
      contradiction x_ineq.
Defined.

Lemma Vector_append_nil:
  forall {T} {n} (xs: t T n),
    existT (fun n => t T n) n xs = existT (fun n => t T n) (n + 0) (append xs (nil T)).
Proof.
  intros T n xs.
  induction xs as [ | x n' xs IH ] .
  - reflexivity.
  - simpl.
    dependent rewrite <- IH.
    reflexivity.
Qed.

Lemma Vector_append_assoc:
  forall {T: Type} {m n o: nat} (xs: t T m) (ys: t T n) (zs: t T o),
    append (append xs ys) zs = rew (Nat.add_assoc m n o) in append xs (append ys zs).
Proof.
  intros T m n o xs.
  induction xs as [ | ? m ? IH].
  - intros ys zs.
    simpl.
    generalize (Nat.add_assoc 0 n o).
    intro eq.
    simpl in eq.
    rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ eq).
    reflexivity.
  - simpl append.
    intros ys zs.
    rewrite IH.
    generalize (Nat.add_assoc m n o).
    intro eq.
    destruct m.
    + simpl in eq.
      rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ eq).
      generalize (Nat.add_assoc 1 n o).
      intro eq'.
      rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ eq').
      reflexivity.
    + simpl in eq.
      generalize (Nat.add_assoc (S (S m)) n o).
      intro eq'.
      simpl in eq'.
      inversion eq' as [ eq'' ].
      revert eq'.
      revert eq.
      simpl.
      rewrite <- eq''.
      intros eq eq'.
      rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ eq).
      rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ eq').
      reflexivity.
Qed.

Lemma Vector_append_assoc':
  forall {T: Type} {m n o: nat} (xs: t T m) (ys: t T n) (zs: t T o),
    rew <- (Nat.add_assoc m n o) in append (append xs ys) zs = append xs (append ys zs).
Proof.
  intros.
  rewrite Vector_append_assoc.
  rewrite (rew_opp_l).
  reflexivity.
Qed.

Inductive ForAll' {S : Type} (P : S -> Type): forall {n : nat}, t S n -> Type :=
| ForAll'_nil: ForAll' P (nil _)
| ForAll'_cons: forall x {n: nat} xs,
    P x -> ForAll' P xs -> ForAll' P (cons _ x n xs).

Lemma Forall_tautology:
  forall {T} {n} (xs: t T n) (P : T -> Prop), (forall x, P x) -> Forall P xs.
Proof.
  intros T n xs P taut.
  induction xs.
  - apply Forall_nil.
  - apply Forall_cons; auto.
Qed.
 

Lemma Forall_append: forall {n m} {T} P (xs: t T n) (ys: t T m),
    Forall P xs -> Forall P ys -> Forall P (append xs ys).
Proof.
  intros n m T P xs.
  induction xs as [ | ? ? ? IH ]; intro ys.
  - intros prfxs prfys.
    simpl; assumption.
  - intros prfxs prfys.
    inversion prfxs as [ | ? ? ? prfx prfxs' neq [ xeq xseq ] ].
    dependent rewrite xseq in prfxs'.
    clear neq xeq xseq.
    apply Forall_cons.
    + assumption.
    + apply IH; assumption.
Qed.

Lemma append_Forall1: forall {n m} {T} P (xs: t T n) (ys: t T m),
    Forall P (append xs ys) -> Forall P xs.
Proof.
  intros n m T P xs ys.
  induction xs.
  - intro; apply Forall_nil.
  - intro prf.
    inversion prf as [ | ? ? ? prf_hd prf_tl n_eq [ hd_eq tl_eq ]].
    dependent rewrite tl_eq in prf_tl.
    apply Forall_cons.
    + assumption.
    + auto.
Qed.

Lemma append_Forall2: forall {n m} {T} P (xs: t T n) (ys: t T m),
    Forall P (append xs ys) -> Forall P ys.
Proof.
  intros n m T P xs ys.
  induction xs.
  - intro; assumption.
  - intro prf.
    inversion prf as [ | ? ? ? prf_hd prf_tl n_eq [ hd_eq tl_eq ]].
    dependent rewrite tl_eq in prf_tl.
    auto.
Qed.

Lemma Forall_map: forall {T} {n} (xs: t T n) (P: T -> Prop) f,
    Forall P (map f xs) -> Forall (fun x => P (f x)) xs.
Proof.
  intros T n xs P f.
  induction xs as [ | h ? tl IH ]; intro prf.
  - apply Forall_nil.
  - simpl in prf.
    inversion prf as [ | ? ? prfPh prftl prfPtl prfneq [ prfheq prftleq ] ].
    dependent rewrite prftleq in prfPtl.
    apply Forall_cons.
    + assumption.
    + apply IH; assumption.
Qed.

Lemma map_Forall: forall {T1 T2} {n} (xs: t T1 n) (P: T2 -> Prop) (f : T1 -> T2),
    Forall (fun x => P (f x)) xs -> Forall P (map f xs).
Proof.
  intros T1 T2 n xs P f.
  induction xs as [ | h ? tl IH ]; intro prf.
  - apply Forall_nil.
  - simpl in prf.
    inversion prf as [ | ? ? prfPh prftl prfPtl prfneq [ prfheq prftleq ] ].
    dependent rewrite prftleq in prfPtl.
    apply Forall_cons.
    + assumption.
    + apply IH; assumption.
Qed.

Lemma decideForall:
  forall {T : Type} (P: T -> Prop) m
    (args: t T m)
    (IH: ForAll' (fun sigma => P sigma \/ (P sigma -> False)) args),
    Forall P args \/ (Forall P args -> False).
Proof.
  intros T n m args.
  induction args as [ | h m' tl IH ]; intro prfs.
  - left; apply Forall_nil.
  - inversion prfs as [ | ? ? ? prf prfs' mEq [ hEq tlEq ] ].
    dependent rewrite tlEq in prfs'.
    destruct prf as [ prf | disprf ].
    + destruct (IH prfs') as [ prfs'' | disprfs ].
      * left; apply Forall_cons; assumption.
      * right.
        intro devil.
        inversion devil as [ | ? ? ? dh dtl dmEq [ dhEq dtlEq ] ].
        dependent rewrite dtlEq in dtl.
        apply disprfs.
        assumption.
    + right.
      intro devil.
      inversion devil as [ | ? ? ? dh dtl dmEq [ dhEq dtlEq ] ].
      apply disprf.
      assumption.
Qed.

Lemma Forall_last:
  forall {T : Type} (P : T -> Prop) m (args: t T (S m)),
    Forall P args -> P (last args).
Proof.
  intros T P m.
  induction m.
  - intro args.
    apply (caseS' args); clear args; intros arg args.
    apply (fun r => case0 (fun xs => Forall _ (cons _ _ _ xs) -> P (last (cons _ _ _ xs))) r args).
    intro prfs.
    inversion prfs.
    assumption.
  - intro args.
    apply (caseS' args); clear args; intros arg args.
    intro prfs.
    inversion prfs as [ | ? ? ? ? prfs' n_eq [ arg_eq args_eq ] ].
    dependent rewrite args_eq in prfs'.
    simpl.
    auto.
Qed.

Lemma Forall_shiftout:
  forall {T : Type} (P : T -> Prop) m (args: t T (S m)),
    Forall P args -> Forall P (shiftout args).
Proof.
  intros T P m.
  induction m.
  - intro args.
    apply (caseS' args); clear args; intros arg args.
    apply (fun r => case0 (fun xs => Forall P (cons _ _ _ xs) -> Forall P (shiftout (cons _ _ _ xs))) r args).
    intro; apply Forall_nil.
  - intro args.
    apply (caseS' args); clear args; intros arg args.
    intro prfs.
    inversion prfs as [ | ? ? ? prf prfs' n_eq [ hd_eq tl_eq ] ].
    dependent rewrite tl_eq in prfs'.
    apply Forall_cons; [ assumption | auto ].
Qed.
   
Lemma Forall_dec_eq:
  forall {T : Type} m
    (xs ys: t T m)
    (IH: Forall (fun sigma => forall tau, sigma = tau \/ sigma <> tau) xs),
    xs = ys \/ xs <> ys.
Proof.
  intros T m xs.
  induction xs as [ | x n xs IHxs ]; intros ys IH.
  - intros; left; apply case0; reflexivity.
  - apply (caseS' ys); clear ys; intros y ys.
    inversion IH as [ | ? ? ? prf prfs' nEq [ hEq tlEq ] ].
    destruct (prf y) as [ xy_eq | ];
      [ | right; intro devil; inversion devil; contradiction ].
    rewrite xy_eq.
    dependent rewrite tlEq in prfs'.
    destruct (IHxs ys prfs') as [ xs_eq | xs_ineq ];
      [ | right; intro devil ].
    + left; rewrite xs_eq; reflexivity.
    + exact (Vector_tl_ineq _ _ _ xs_ineq devil).
Qed.

Lemma ForAll'Forall: forall {T} {n} (xs: t T n) (P: T -> Prop),
    ForAll' P xs -> Forall P xs.
Proof.
  intros T n xs P.
  induction xs as [ | h ? tl IH ]; intro prf.
  - apply Forall_nil.
  - inversion prf as [ | ? ? prfPh prftl prfPtl prfneq [ prfheq prftleq ] ].
    dependent rewrite prftleq in prfPtl.
    apply Forall_cons.
    + assumption.
    + apply IH; assumption.
Qed.


Lemma ForallEq_map: forall {T} {n} (xs: t T n) f,
    Forall (fun x => f x = x) xs -> map f xs = xs.
Proof.
  intros T n xs f.
  induction xs as [ | h n tl IH ]; intros prf.
  - reflexivity.
  - inversion prf as [ | ? ? ? prfh prftl prfneq [ prfheq prftleq ] ].
    dependent rewrite prftleq in prftl.
    clear prfheq prftleq prfneq.
    simpl.
    rewrite prfh.
    apply f_equal.
    apply IH.
    assumption.
Qed.


Lemma Forall_ap: forall {T} {n} (xs: t T n) (R: T -> Prop) (S: T -> Prop),
    Forall (fun x => R x -> S x) xs -> Forall R xs -> Forall S xs.
Proof.
  intros T n xs R S.
  induction xs as [ | h n tl IH ]; intros prfRS prfR.
  - apply Forall_nil.
  - inversion prfRS as [ | ? ? ? RSh RStl RSneq [ RSheq RStleq ] ].
    dependent rewrite RStleq in RStl.
    clear RSheq RStleq RSneq.
    inversion prfR as [ | ? ? ? Rh Rtl Rneq [ Rheq Rtleq ] ].
    dependent rewrite Rtleq in Rtl.
    clear Rheq Rtleq Rneq.
    apply Forall_cons.
    + apply RSh; assumption.
    + apply IH; assumption.
Qed.

Lemma nth_Forall:
  forall {n} {T} (ts: t T n) (P : T -> Prop),
    (forall (k : Fin.t n), P (nth ts k)) -> Forall P ts.
Proof.
  intros n T ts P.
  induction ts
    as [ | h n tl IH ]; intro prf.
  - apply Forall_nil.
  - apply Forall_cons.
    + exact (prf F1).
    + apply IH.
      intro k.
      exact (prf (FS k)).
Qed.

Lemma Forall_nth:
  forall {n} {T} (ts: t T n) (P : T -> Prop),
    Forall P ts -> (forall (k : Fin.t n), P (nth ts k)).
Proof.
  intros n T ts P.
  induction ts as [ | h n tl IH]; intro prf.
  - intro k; inversion k.
  - intro k.
    inversion prf as [ | n' h' tl' Ph Ptl' n_eq [ h_eq tl_eq ] ].
    dependent rewrite tl_eq in Ptl'.
    apply (Fin.caseS' k).
    + assumption.
    + intro k'.
      simpl.
      apply IH.
      assumption.
Qed.

Lemma nth_Forall2:
  forall {n} {S T : Type} (P : S -> T -> Prop) (xs: t S n) (ys: t T n),
    (forall (k : Fin.t n), P (nth xs k) (nth ys k)) -> Forall2 P xs ys.
Proof.
  intros n S T P.
  induction n as [ | n IHn ];
    intros xs ys.
  - intro prf.
    apply (fun r => case0 (fun xs => Forall2 P xs ys) r xs).
    apply (fun r => case0 (fun ys => Forall2 P (nil _) ys) r ys).
    apply Forall2_nil.
  - apply (caseS' xs (fun xs => forall p, Forall2 P xs ys)).
    clear xs; intros x xs.
    apply (caseS' ys (fun ys => forall p, Forall2 P (cons _ x _ xs) ys)).
    clear ys; intros y ys.
    intro prf.
    apply Forall2_cons.
    + apply (prf F1).
    + apply IHn.
      intro pos.
      apply (prf (FS pos)).
Qed.

Lemma vect_exist_eq {T: Type} {n : nat}:
  forall xs ys, existT (t T)  n xs = existT (t T) n ys -> xs = ys.
Proof.
  intro xs.
  induction xs as [ | x n xs IHxs ].
  - intro ys.
    apply (fun r => case0 (fun ys => _ = existT _ 0 ys -> _ = ys) r ys).
    intros; reflexivity.
  - intro ys.
    apply (caseS' ys).
    clear ys; intros y ys.
    intro xs_eq.
    inversion xs_eq.
    apply f_equal.
    apply IHxs.
    assumption.
Qed.

Lemma Forall2_nth:
  forall {n} {S T : Type} (P : S -> T -> Prop) (xs: t S n) (ys: t T n),
    Forall2 P xs ys -> (forall (k : Fin.t n), P (nth xs k) (nth ys k)).
Proof.
  intros n S T P.
  induction n as [ | n IHn ];
    intros xs ys.
  - intros prf k; inversion k.
  - apply (caseS' xs).
    clear xs; intros x xs.
    apply (caseS' ys).
    clear ys; intros y ys.
    intros prf k.
    inversion prf as [ | ? ? ? xs' ys'  prf_hd prf_tl size_eq [ x_eq xs_eq ] [ y_eq ys_eq ] ].    
    apply (Fin.caseS' k).
    + assumption.
    + rewrite (vect_exist_eq _ _ (eq_sym xs_eq)).
      rewrite (vect_exist_eq _ _ (eq_sym ys_eq)).
      apply IHn.
      assumption.
Qed.

Lemma Forall2_shiftin {S T : Type} {n : nat} (P: S -> T -> Prop):
  forall (xs: t S n) (ys: t T n) x y, P x y -> Forall2 P xs ys -> Forall2 P (shiftin x xs) (shiftin y ys).
Proof.
  intros xs.
  induction xs as [ | x' n xs IH ]; intros ys x y.
  - intros.
    apply (fun r => case0 (fun ys => Forall2 P _ (shiftin y ys)) r ys).
    apply Forall2_cons; [ | apply Forall2_nil ].
    assumption.
  - apply (caseS' ys).
    clear ys.
    intros y' ys prf prfs.
    inversion prfs as [ | ? ? ? ? ? ? prfs' n_eq [ x'_eq xs_eq ] [ y'_eq ys_eq ] ].
    apply Forall2_cons.
    + assumption.
    + rewrite (vect_exist_eq _ _ xs_eq) in prfs'.
      rewrite (vect_exist_eq _ _ ys_eq) in prfs'.
      apply IH; assumption.
Qed.

Lemma Forall2_shiftout {T U : Type} {n : nat} (P: T -> U -> Prop):
  forall (xs: t T (S n)) (ys: t U (S n)),
    Forall2 P xs ys -> Forall2 P (shiftout xs) (shiftout ys).
Proof.
  induction n as [ | n IH ]; intros xs ys.
  - apply (caseS' xs); clear xs; intros x xs.
    apply (caseS' ys); clear ys; intros y ys.
    intro.
    apply (fun r => case0 (fun xs => Forall2 _ (shiftout (cons _ _ _ xs)) _) r xs).
    apply (fun r => case0 (fun xs => Forall2 _ _ (shiftout (cons _ _ _ xs))) r ys).
    apply Forall2_nil.
  - apply (caseS' xs); clear xs; intros x xs.
    apply (caseS' ys); clear ys; intros y ys.
    intro prfs.
    inversion prfs as [ | ? ? ? ? ? prf prfs' n_eq [ hd_eq1 tl_eq1 ] [hd_eq2 tl_eq2] ].
    rewrite (vect_exist_eq _ _ tl_eq1) in prfs'.
    rewrite (vect_exist_eq _ _ tl_eq2) in prfs'.
    apply Forall2_cons; [ assumption | auto ].
Qed.

Lemma Forall2_last {T U : Type} {n : nat} (P: T -> U -> Prop):
  forall (xs: t T (S n)) (ys: t U (S n)),
    Forall2 P xs ys -> P (last xs) (last ys).
Proof.
  induction n; intros xs ys.
  - apply (caseS' xs); clear xs; intros x xs.
    apply (caseS' ys); clear ys; intros y ys.
    intro prf.
    inversion prf.
    apply (fun r => case0 (fun xs => P (last (cons _ _ _ xs)) _) r xs).
    apply (fun r => case0 (fun xs => P _ (last (cons _ _ _ xs))) r ys).
    assumption.
  - apply (caseS' xs); clear xs; intros x xs.
    apply (caseS' ys); clear ys; intros y ys.
    intro prfs.
    inversion prfs as [ | ? ? ? ? ? prf prfs' n_eq [ hd_eq1 tl_eq1 ] [hd_eq2 tl_eq2] ].
    rewrite (vect_exist_eq _ _ tl_eq1) in prfs'.
    rewrite (vect_exist_eq _ _ tl_eq2) in prfs'.
    simpl.
    auto.
Qed.
  
(*Lemma ForAll2'_tail: forall {n: nat} {A B: Type} (P : A -> B -> Type) (xs: t A (S n)) (ys: t B (S n)) (prfs: ForAll2' P xs ys), ForAll2' P (tl xs) (tl ys).
Proof.
  intros n A B P xs ys prfs.
  inversion prfs as [ | ? ? ? ? ? ? ? ? n_eq m_eq xs_eq ys_eq ].
  revert xs_eq.
  revert ys_eq.
  apply (caseS' xs
                (fun xs =>
                   (existT _ (S n) (cons _ y _ ys0) = existT _ (S n) ys) ->
                   (existT _ (S n) (cons _ x _ xs0) = existT _ (S n) xs) ->
                   ForAll2' P (tl xs) (tl ys))).
  intros x' xs'.
  apply (caseS' ys
                (fun ys =>
                   (existT _ (S n) (cons _ y _ ys0) = existT _ (S n) ys) ->
                   (existT _ (S n) (cons _ x _ xs0) = existT _ (S n) (cons _ x' _ xs')) ->
                   ForAll2' P (tl (cons _ x' _ xs')) (tl ys))).
  intros y' ys'.
  intros ys_eq xs_eq.
  injection xs_eq as x_eq xs'_eq.
  injection ys_eq as y_eq ys'_eq.
  simpl.
  set (G := fun n xs' => ForAll2' (n := n) P xs' ys').
  fold (G n xs').
  dependent rewrite <- xs'_eq.
  unfold G.
  set (G' := fun n ys' => ForAll2' (m := n) P xs0 ys').
  fold (G' n ys').
  dependent rewrite <- ys'_eq.
  unfold G'.
  assumption.
Qed.
        

Lemma ForAll2'_shiftin: forall {n : nat} {A B: Type} (P : A -> B -> Type) (xs: t A n) (ys: t B n) (prfs: ForAll2' P xs ys) (x: A) (y: B) (prf: P x y), ForAll2' P (shiftin x xs) (shiftin y ys).
Proof.
  intro n.
  induction n; intros A B P xs ys prfs x y prf.
  - apply (case0 (fun xs => ForAll2' P (shiftin x xs) (shiftin y ys))).
    apply (case0 (fun ys => ForAll2' P (shiftin x (nil _)) (shiftin y ys))).
    apply ForAll2'_cons.
    + assumption.
    + apply ForAll2'_nil.
  - generalize prfs.
    clear prfs.
    apply (caseS' _ (fun xs => ForAll2' P xs ys -> ForAll2' P (shiftin x xs) (shiftin y ys))).
    intros x' xs'.
    apply (caseS' _ (fun ys => ForAll2' P (cons _ x' _ xs') ys -> ForAll2' P (shiftin x (cons _ x' _ xs')) (shiftin y ys))).
    intros y' ys' prfs.
    simpl.
    apply ForAll2'_cons.
    + inversion prfs; assumption.
    + apply IHn.
      * exact (ForAll2'_tail _ _ _ prfs).
      * inversion prfs; assumption.
Qed.      *)                 

Definition dirac {T : Type} {n: nat} (zero: T) (one: T) (pos: Fin.t n): t T n :=
  (fix dirac (m: nat) (p: Fin.t m): t T m :=
     match p in (Fin.t n) return t T n with
     | F1 => cons _ one _ (const zero _)
     | FS p' => cons _ zero _ (dirac _ p')
     end) _ pos.

Lemma dirac_spec_one: forall {T: Type} {n: nat} (zero: T) (one: T) (pos: Fin.t n),
    forall i, pos = i -> nth (dirac zero one pos) i = one.
Proof.
  intros T n.
  induction n as [ | n IHn ] ; intros zero one pos i i_eq.
  - inversion i.
  - remember (S n) as n' eqn:n'_eq.
    destruct pos; rewrite <- i_eq.
    + reflexivity.
    + simpl.
      clear i_eq i.
      revert pos.
      injection n'_eq as n_eq.
      rewrite n_eq.
      intro pos.
      apply IHn.
      reflexivity.
Qed.

Lemma dirac_spec_zero: forall {T: Type} {n: nat} (zero: T) (one: T) (pos: Fin.t n),
    forall i, pos <> i -> nth (dirac zero one pos) i = zero.
Proof.
  intros T n.
  induction n as [ | n IHn ] ; intros zero one pos i i_eq.
  - inversion i.
  - remember (S n) as n' eqn:n'_eq.
    revert i_eq.
    destruct pos.
    + apply (Fin.caseS' i).
      * intro i_eq.
        contradiction i_eq.
        reflexivity.
      * intros i' i_eq.
        simpl.
        apply const_nth.
    + apply (Fin.caseS' i).
      * intro i_eq.
        reflexivity.
      * clear i.
        revert pos.
        injection n'_eq as n_eq.
        rewrite n_eq.          
        intros pos i' i_eq.
        simpl.
        apply IHn.
        unfold not.
        intro i'_eq.
        apply (i_eq (f_equal FS i'_eq)).
Qed.

Fixpoint positions (n : nat): t (Fin.t n) n :=
  match n with
  | O => nil _
  | S n => cons _ F1 _ (map FS (positions n))
  end.

Lemma positions_spec: forall n k, nth (positions n) k = k.
Proof.
  intro n.
  induction n as [ | n IHn ]; intro k.
  - inversion k.
  - remember (S n) as n' eqn:n'_eq.
    destruct k.
    + reflexivity.
    + simpl.
      injection n'_eq as n_eq.
      revert k.
      rewrite n_eq.
      intro k.
      rewrite (nth_map _ _ _ _ (eq_refl k)).
      rewrite (IHn k).
      reflexivity.
Qed.

Definition diag {T : Type} {n : nat} (zero: T) (xs: t T n): t (t T n) n :=
  map2 (dirac zero) xs (positions n).

Lemma diag_spec_outer {T : Type} {n : nat} (xs: t T n) (zero : T):
  forall i, nth (diag zero xs) i = dirac zero (nth xs i) i.
Proof.    
  destruct i;
    apply (caseS' xs);
    clear xs;
    intros x xs.
  + reflexivity.
  + simpl.
    rewrite (nth_map2 (dirac zero) xs (map FS (positions _)) i i i eq_refl eq_refl).
    rewrite (nth_map FS (positions _) i i eq_refl).
    rewrite (positions_spec _ _).
    reflexivity.
Qed.       

Lemma diag_spec_one {T : Type} {n : nat} (xs: t T n) (zero: T):
  forall i j, i = j -> nth (nth (diag zero xs) i) j = nth xs i.
Proof.
  intro i.
  rewrite (diag_spec_outer xs zero i).
  exact (dirac_spec_one _ _ _).
Qed.

Lemma diag_spec_zero {T : Type} {n : nat} (xs: t T n) (zero: T):
  forall i j, i <> j -> nth (nth (diag zero xs) i) j = zero.
Proof.
  intro i.
  rewrite (diag_spec_outer xs zero i).
  exact (dirac_spec_zero _ _ _).
Qed.

Lemma map_id {T : Type} {n: nat} (xs: t T n):
  forall f, (forall x, f x = x) -> map f xs = xs.
Proof.
  intros f f_id.
  induction xs as [ | x n xs IHxs ].
  - reflexivity.
  - simpl.
    rewrite f_id.
    rewrite IHxs.
    reflexivity.
Qed.

Lemma diag_diag {T : Type} {n: nat} (zero: T):
  forall (xs: t T n) k, map (fun xs => nth xs k) (diag zero xs) = dirac zero (nth xs k) k.
Proof.
  intros xs k.
  apply eq_nth_iff.
  intros pos pos2 pos_eq.
  rewrite <- pos_eq.
  clear pos_eq pos2.
  rewrite (nth_map _ _ _ _ eq_refl).
  destruct (Fin.eq_dec pos k) as [ eq | ineq ].
  + rewrite (diag_spec_one xs zero pos k eq).
    rewrite (dirac_spec_one zero (nth xs k) k pos (eq_sym eq)).
    rewrite eq.
    reflexivity.
  + rewrite (diag_spec_zero xs zero pos k ineq).
    rewrite (dirac_spec_zero zero (nth xs k) k pos (not_eq_sym ineq)).
    reflexivity.
Qed.


Lemma replace_id {T: Type} {n: nat}:
  forall (xs: t T n) (pos: Fin.t n) (x: T),
    x = nth xs pos ->
    replace xs pos x = xs.
Proof.
  intro xs.
  induction xs as [ | ? ? ? IHxs ].
  - intro pos; inversion pos.
  - intro pos.
    apply (Fin.caseS' pos).
    + intros x xeq.
      rewrite xeq.
      reflexivity.
    + intros p x xeq.
      simpl.
      apply f_equal.
      apply IHxs.
      assumption.
Qed.

Lemma replace_replaced {T : Type} {n: nat}:
  forall (xs: t T n) (pos k: Fin.t n) (x: T),
    k = pos ->
    nth (replace xs pos x) k = x.
Proof.
  intros xs.
  induction xs as [ | ? ? ? IHxs ]; intros pos k x pos_eq.
  - inversion pos.
  - rewrite pos_eq.
    clear pos_eq.
    clear k.
    apply (Fin.caseS' pos).
    + reflexivity.
    + intro pos'.
      apply (IHxs pos' pos' x eq_refl).
Qed.

Lemma replace_others {T : Type} {n: nat}:
  forall (xs: t T n) (pos k: Fin.t n) (x: T),
    k <> pos ->
    nth (replace xs pos x) k = nth xs k.
Proof.
  intros xs.
  induction xs as [ | ? ? ? IHxs ]; intros pos k x.
  - inversion pos.
  - apply (Fin.caseS' k).
    + apply (Fin.caseS' pos).
      * intro devil.
        contradict (devil eq_refl).
      * intros pos' pos_ineq.
        reflexivity.
    + apply (Fin.caseS' pos).
      * intros pos' pos_ineq.
        reflexivity.
      * intros pos' k' pos_ineq.
        assert (pos'_ineq: pos' <> k').
        { intro devil.
          rewrite devil in pos_ineq.
          contradict (pos_ineq eq_refl). }
        simpl.
        apply (IHxs pos' k' x (not_eq_sym pos'_ineq)).
Qed.

Lemma map_append {S T : Type} {m n: nat}:
  forall (xs: t S m) (ys: t S n) (f : S -> T), map f (append xs ys) = append (map f xs) (map f ys).
Proof.
  intro xs.
  induction xs.
  - intros; reflexivity.
  - intros ys f.
    simpl.
    apply f_equal.
    auto.
Qed.

Lemma map_fg {S T U: Type} {n: nat}:
  forall (xs: t S n) (f : T -> U) (g: S -> T), map (fun x => f (g x)) xs = map f (map g xs).
Proof.
  intros xs f g.
  induction xs.
  - reflexivity.
  - simpl.
    apply f_equal.
    assumption.
Qed.

Lemma map_extensional {S T : Type} {n: nat}:
  forall (xs: t S n) (f: S -> T) (g: S -> T) (fg_eq: forall x, f x = g x),
    map f xs = map g xs.
Proof.
  intros xs f g fg_eq.
  induction xs.
  - reflexivity.
  - simpl.
    rewrite fg_eq.
    apply f_equal.
    assumption.
Qed.

Lemma map_const {S T : Type} {n: nat}:
  forall (xs: t S n) (f: S -> T) (c: T) (f_const: forall x, f x = c),
    map f xs = const c n.
Proof.
  intros xs f c f_const.
  induction xs as [ | ? ? ? IHxs ].
  - reflexivity.
  - simpl.
    rewrite f_const.
    rewrite IHxs.
    reflexivity.
Qed.

Lemma map_rew {S T : Type} {m n: nat}:
  forall (xs: t S m) (f: S -> T) (eq: m = n),
    rew eq in map f xs = map f (rew eq in xs).
Proof.
  intros xs f.
  destruct xs as [ | x m xs ]; intro eq.
  - destruct n; [ | inversion eq ].
    rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ eq).
    rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ eq).
    reflexivity.
  - destruct n; inversion eq as [ eq' ].
    revert eq.
    rewrite <- eq'.
    intro eq.
    rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ eq).
    rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ eq).
    reflexivity.
Qed.   

Lemma map_map2_fg {S T U V: Type} {n: nat}:
  forall (xs: t S n) (ys: t T n) (f: S -> T -> U) (g: U -> V),
    map g (map2 f xs ys) = map2 (fun x y => g (f x y)) xs ys.
Proof.
  intro xs.
  induction xs as [ | x n' xs IH ]; intros ys f g.
  - apply (fun r => case0 (fun ys => map g (map2 f _ ys) = map2 _ _ ys) r ys).
    reflexivity.
  - apply (caseS' ys).
    clear ys; intros y ys.
    simpl.
    apply f_equal.
    apply IH.
Qed.

Lemma map2_map_fg {S T U V W: Type} {n: nat}:
  forall (xs: t S n) (ys: t T n) (f: S -> U) (g: T -> V) (h: U -> V -> W),
    map2 h (map f xs) (map g ys) = map2 (fun x y => h (f x) (g y)) xs ys.
Proof.
  intro xs.
  induction xs as [ | x n xs IH ].
  - intros ys f g h.
    apply (fun r => case0 (fun ys => map2 h _ (map _ ys) = map2 _ _ ys) r ys).
    reflexivity.
  - intro ys; apply (caseS' ys); clear ys; intros y ys.
    intros f g h.
    simpl.
    apply f_equal.
    apply IH.
Qed.

Lemma nth_k {T: Type} {n n': nat}:
  forall (n_eq: n = n') (xs: t T n) (k: Fin.t n'), nth (rew n_eq in xs) k = nth xs (rew <- n_eq in k).
Proof.
  destruct n; destruct n';
    intro n_eq;
    try solve [ inversion n_eq ].
  - intros xs k; inversion k.
  - inversion n_eq as [ n_eq' ].
    generalize n_eq.
    clear n_eq.
    rewrite n_eq'.
    intros n_eq xs k.
    rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ n_eq).
    unfold eq_rect_r.
    rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ (eq_sym n_eq)).
    reflexivity.
Qed.

Lemma nth_rew {T: nat -> Type} {n n': nat}:
  forall (n_eq: n = n') (xs: t (T n) n) (k: Fin.t n), nth (rew [fun n => t (T n) n] n_eq in xs) (rew n_eq in k) = rew n_eq in nth xs k.
Proof.
  destruct n; destruct n';
    intro n_eq;
    try solve [ inversion n_eq ].
  - intros xs k; inversion k.
  - inversion n_eq as [ n_eq' ].
    generalize n_eq.
    clear n_eq.
    rewrite n_eq'.
    intros n_eq xs k.
    rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ n_eq).
    rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ n_eq).
    rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ n_eq).
    reflexivity.
Qed.


Lemma nth_eq {m n: nat} {T: Type}:
  forall (xs: t T m) (mn_eq: m = n) (k: Fin.t m),
    nth (rew mn_eq in xs) (rew mn_eq in k) = nth xs k.
Proof.
  intros xs.
  induction xs.
  - intros ? k; inversion k.
  - intro mn_eq.
    destruct n; [ inversion mn_eq | ].
    inversion mn_eq as [ mn_eq' ].
    generalize mn_eq.
    clear mn_eq.
    rewrite <- mn_eq'.
    intros mn_eq k.
    rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ mn_eq).
    rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ mn_eq).
    reflexivity.
Qed.

Lemma nth_const {n: nat} {T : Type}:
  forall (xs: t T n) x, (forall k, nth xs k = x) -> xs = const x n.
Proof.
  intro xs.
  induction xs as [ | x' ? xs IH ].
  - intros; reflexivity.
  - intros x xs_const.
    set (x'_eq := xs_const F1).
    simpl in x'_eq.
    rewrite x'_eq.
    simpl.
    apply f_equal.
    apply IH.
    intro k'.
    exact (xs_const (FS k')).
Qed.

Lemma discharge_Forall2_head {n: nat} {S T: Type} {P: S -> T -> Prop}:
  forall x y (xs: t S n) (ys: t T n), (P x y -> False) -> Forall2 P (cons _ x _ xs) (cons _ y _ ys) -> False.
Proof.
  intros x y xs ys disprf prf.
  inversion prf.
  contradiction.
Qed.

Lemma discharge_Forall2_tail {n: nat} {S T: Type} {P: S -> T -> Prop}:
  forall x y (xs: t S n) (ys: t T n), (Forall2 P xs ys -> False) -> Forall2 P (cons _ x _ xs) (cons _ y _ ys) -> False.
Proof.
  intros x y xs ys disprf prf.
  inversion prf as [ | ? ? ? ? ? ? tl_prf n_eq [x_eq xs_eq] [y_eq ys_eq]].
  rewrite (vect_exist_eq _ _ xs_eq) in tl_prf.
  rewrite (vect_exist_eq _ _ ys_eq) in tl_prf.
  contradiction.
Qed.

Lemma existT_fg {S T : Type}: forall (f : T -> Type)  (g: S -> T) x (y : f (g x)) P,
    P (projT2 (existT (fun x => f (g x)) x y)) -> P (projT2 (existT f (g x) y)).
Proof.
  intros f g x y P prf.
  simpl.
  assumption.
Qed.

Lemma existT_fg' {S T : Type}: forall (f : T -> Type)  (g: S -> T) x (y : f (g x)) P,
    P (projT2 (existT f (g x) y)) -> P (projT2 (existT (fun x => f (g x)) x y)).
Proof.
  intros f g x y P prf.
  simpl.
  assumption.
Qed.

Lemma existT_fg_eq {S T : Type}: forall (f : T -> Type)  (g: S -> T) x (y y' : f (g x)),
    existT (fun x => f (g x)) x y = existT (fun x => f (g x)) x y' ->
    existT f (g x) y = existT f (g x) y'.
Proof.
  intros f g x y y' prf.
  remember (existT f (g x) y) as lhs eqn:lhs_eq.
  dependent rewrite prf in lhs_eq.
  rewrite lhs_eq.
  reflexivity.
Qed.

Lemma existT_eq {T : Type}: forall (x y : T) (P: T -> Type) (xs : P x) (ys : P y) (xy_eq : x = y),
    rew [P] xy_eq in xs = ys -> existT P x xs = existT P y ys.
Proof.
  intros x y P xs ys xy_eq.
  revert xs.
  rewrite xy_eq.
  intros xs xsys_eq.
  simpl in xsys_eq.
  rewrite xsys_eq.
  reflexivity.
Qed.

Lemma Exists_map {S T : Type} {n: nat}:
  forall (xs: t S n) f (P: T -> Prop), Exists (fun x => P (f x)) xs -> Exists P (map f xs).
Proof.
  intro xs.
  induction xs.
  - intros f P devil; inversion devil.
  - intros f P prf.
    inversion prf as [ | ? ? ? tl_prf n_eq [ hd_eq tl_eq ] ].
    + apply Exists_cons_hd.
      assumption.
    + dependent rewrite tl_eq in tl_prf.
      simpl.
      apply Exists_cons_tl.
      auto.
Qed.

Lemma Exists_append1 {T : Type} {m n : nat}:
  forall (xs: t T m) (ys: t T n) (P: T -> Prop), Exists P xs -> Exists P (append xs ys).
Proof.
  intros xs.
  induction xs.
  - intros ? ? devil; inversion devil.
  - intros ? ? prf.
    inversion prf as [ | ? ? ? tl_prf n_eq [ hd_eq tl_eq ] ].
    + apply Exists_cons_hd; assumption.
    + dependent rewrite tl_eq in tl_prf.
      simpl.
      apply Exists_cons_tl.
      auto.
Qed.

Lemma Exists_append2 {T : Type} {m n : nat}:
  forall (xs: t T m) (ys: t T n) (P: T -> Prop), Exists P ys -> Exists P (append xs ys).
Proof.
  intros xs.
  induction xs.
  - intros; assumption.
  - intros;
    simpl.
    apply Exists_cons_tl.
    auto.
Qed.

Lemma Exists_in {T : Type} {m: nat}:
  forall (xs : t T m) (P: T -> Prop), Exists P xs -> exists x, P x /\ In x xs.
Proof.
  intros xs P ex_prf.
  induction ex_prf as [ ? ? ? here | ? ? ? ? IH ].
  - eexists; split; [ eassumption | left; reflexivity ].
  - destruct IH as [ x' [ Px' in_xs ] ].
    eexists; split; [ eassumption | right; eassumption ].
Qed.  

Lemma nth_Exists {T : Type} {n : nat}:
  forall (xs: t T n) (P : T -> Prop) k, P (nth xs k) -> Exists P xs.
Proof.
  intros xs P.
  induction xs as [ | ? ? ? IH ].
  - intro k; inversion k.
  - intro k.
    apply (Fin.caseS' k).
    + intro; apply Exists_cons_hd; assumption.
    + intros; apply Exists_cons_tl.
      eapply IH; eassumption.
Qed.

Lemma In_nth {T : Type} {n: nat}:
  forall (xs: t T n) x, In x xs -> exists k, nth xs k = x.
Proof.
  intro xs.
  induction xs as [ | x n xs IH ]; intros x' in_prf.
  - inversion in_prf.
  - inversion in_prf as [ ? ? n_eq here | ? ? ? there n_eq [hd_eq tl_eq]].
    + exists F1; reflexivity.
    + dependent rewrite tl_eq in there.
      destruct (IH _ there) as [ k kth_eq ].
      exists (FS k); assumption.
Qed.

Lemma nth_In {T : Type} {n: nat}:
  forall (xs: t T n) k, In (nth xs k) xs.
Proof.
  intro xs.
  induction xs as [ | x n xs IH ]; intro k.
  - inversion k.
  - apply (Fin.caseS' k).
    + left; reflexivity.
    + intro k'; right; apply IH; apply FS; assumption.
Qed.

Lemma In_last {T: Type} {n: nat}:
  forall (xs: t T (S n)) x,
    In x xs <-> In x (shiftout xs) \/ x = last xs.
Proof.
  intros xs x.
  rewrite (shiftin_shiftout xs).
  generalize (last xs).
  generalize (shiftout xs).
  clear xs.
  intro xs.
  induction xs as [ | x' n xs' IH ]; intro lastx.
  - split.
    + intro inprf.
      inversion inprf as [ ? ? n_eq [ hd_eq tl_eq ]| ? ? ? devil n_eq [ hd_eq tl_eq ]  ].
      * dependent rewrite tl_eq.
        right; reflexivity.
      * dependent rewrite tl_eq in devil; inversion devil.
    + intro inprf.
      inversion inprf as [ devil | inprf' ].
      * inversion devil.
      * simpl in *.
        rewrite inprf'.
        left.
  - split.
    + rewrite <- (shiftout_shiftin).
      intro inprf.
      inversion inprf as [ ? ? n_eq [ hd_eq tl_eq] | ? ? ? inprf' n_eq [ hd_eq tl_eq ] ].
      * left; left.
      * dependent rewrite tl_eq in inprf'.
        generalize (proj1 (IH _) inprf').
        intro inprf''.
        rewrite <- (shiftout_shiftin) in inprf''.
        simpl.
        inversion inprf''.
        { left; right; assumption. }
        { right; assumption. }
    + rewrite <- shiftout_shiftin.
      intro inprf.
      inversion inprf as [ inl | inr ].
      * inversion inl as [ ? ? n_eq [ hd_eq tl_eq ] | ? ? ? inprf' n_eq [hd_eq tl_eq ] ].
        { left. }
        { right.
          dependent rewrite tl_eq in inprf'.
          generalize (proj2 (IH lastx)).
          rewrite <- shiftout_shiftin.
          intro; tauto. }
      * right.
        simpl in inr.
        generalize (proj2 (IH lastx)).
        tauto.
Qed.

Lemma ListForall_Forall {A: Type} {P : A -> Prop}: forall xs, List.Forall P xs -> Forall P (of_list xs). 
Proof.      
  intro xs.
  induction xs.
  - intro; apply Forall_nil.
  - intro prf.
    inversion prf.
    apply Forall_cons; auto.
Qed.

Lemma Forall_ListForall {A: Type} {P : A -> Prop} {n: nat}: forall (xs: t A n), Forall P xs -> List.Forall P (to_list xs).
Proof.
  intro xs.
  induction xs.
  - intros; apply List.Forall_nil.
  - intro prfs.
    inversion prfs as [ | n' x xs' prf_x prfs_xs n_eq [ x_eq xs_eq ] ].
    dependent rewrite xs_eq in prfs_xs.
    apply List.Forall_cons; auto.
Qed.

Lemma ListExists_Exists {A: Type} {P : A -> Prop}: forall xs, List.Exists P xs -> Exists P (of_list xs).
Proof.
  intros xs prf.
  induction prf.
  - apply Exists_cons_hd; assumption.
  - apply Exists_cons_tl; assumption.
Qed.

Lemma Exists_ListExists {A: Type} {P : A -> Prop} {n: nat}: forall (xs: t A n), Exists P xs -> List.Exists P (to_list xs).
Proof.
  intros xs prf.
  induction prf.
  - apply List.Exists_cons_hd; assumption.
  - apply List.Exists_cons_tl; assumption.
Qed.

Lemma List_nth_nth {A : Type}:
  forall (xs: list A) n (prf: n < length xs), nth_error xs n  = Some (nth (of_list xs) (Fin.of_nat_lt prf)).
Proof.
  intros xs n.
  revert xs.
  induction n as [ | n IH ];
    intros xs prf;
    (destruct xs; [ inversion prf | ]).
  - reflexivity.
  - apply IH.
Qed. 

Inductive IsSuffix {A: Type} (s: list A): list A -> Prop :=
| IsSuffix_tl: forall x l, IsSuffix s l -> IsSuffix s (List.cons x l)
| IsSuffix_hd: IsSuffix s s.

Lemma in_suffix {A: Type}:
  forall (x : A) xs, List.In x xs -> exists l, IsSuffix (List.cons x l) xs.
Proof.
  intros x xs.
  induction xs as [ | x' xs IH ].
  - intro devil; inversion devil.
  - intro inprf.
    destruct inprf as [ here | there ].
    + exists xs; rewrite here; apply IsSuffix_hd.
    + destruct (IH there) as [ l prf ].
      eexists; apply IsSuffix_tl; eassumption.
Qed.

Lemma suffix_in {A: Type}:
  forall (x: A) s l, IsSuffix (List.cons x s) l -> List.In x l.
Proof.
  intros x s l suffix.
  induction suffix.
  + right; assumption.
  + left; reflexivity.
Qed.

Fixpoint powerset {A: Type} (xs: list A): list (list A) :=
  match xs with
  | List.nil => List.cons List.nil List.nil
  | List.cons x xs =>
    List.app
      (List.map (List.cons x) (powerset xs))
      (powerset xs)
  end.

Lemma powerset_empty_incl: forall {A} (xs: list A), List.In List.nil (powerset xs).
Proof.
  intros A xs.
  induction xs as [ | x xs IH ].
  - left; reflexivity.
  - simpl.
    induction (List.map (List.cons x) (powerset xs)).
    + assumption.
    + right; assumption.
Qed.

Lemma powerset_smaller_set_incl: forall {A} (x: A) xs ys,
    List.In (List.cons x xs) (powerset ys) ->
    List.In xs (powerset ys).
Proof.
  intros A x xs ys.
  induction ys as [ | y ys IH ].
  - intro devil; inversion devil as [ devil' | devil' ]; inversion devil'.
  - unfold powerset.
    fold (powerset ys).
    intro in_app.
    destruct (in_app_or _ _ _ in_app) as [ inleft | inright ].
    + apply in_app_iff.
      right.
      clear in_app IH.
      induction (powerset ys).
      * contradiction.
      * inversion inleft as [ eq | ].
        { left; inversion eq; reflexivity. }
        { right; auto. }
    + apply in_or_app; right; auto.
Qed.

Lemma powerset_split: forall {A} xs (y: A) ys,
    List.In xs (powerset (List.cons y ys)) ->
    List.In xs (List.map (List.cons y) (powerset ys)) \/
    List.In xs (powerset ys).
Proof.
  intros A xs.
  induction xs as [ | x xs IH ].
  - intros; right; apply powerset_empty_incl.
  - intros y ys xxs_in.
    unfold powerset in xxs_in.
    fold (powerset ys) in xxs_in.
    apply in_app_or.
    assumption.
Qed.

Lemma ListIn_map_cons: forall {A} (x: A) xs ys,
    List.In ys (List.map (List.cons x) xs) -> exists ys', ys = List.cons x ys' /\ List.In ys' xs.
Proof.
  intros A x xs.
  induction xs as [ | x' xs IH ].
  - intros ? devil; inversion devil.
  - intros ys in_prf.
    destruct in_prf as [ eq | in_rest ].
    + destruct ys as [ | y ys ].
      * inversion eq.
      * inversion eq.
        eexists; split; [ reflexivity | left; reflexivity ].
    + destruct (IH _ in_rest) as [ ? [ ? ? ]].
      eexists; split; [ eassumption | right; eassumption ].
Qed.

Lemma ListIn_map_cons': forall {A} (x: A) xs ys,
    List.In xs ys -> List.In (List.cons x xs) (List.map (List.cons x) ys).
Proof.
  intros A x xs ys.
  revert xs.
  induction ys.
  - intros ? devil; inversion devil.
  - intros xs in_prf.
    destruct in_prf as [ eq | ].
    + inversion eq.
      left; reflexivity.
    + right; auto.
Qed.



Lemma powerset_spec {A: Type} {A_dec : forall (x y : A), { x = y } + { x <> y }}:
  forall (x : A) xs ys,
    List.In x ys ->
    List.In xs (powerset ys) ->
    exists xs',
      List.In xs' (powerset ys) /\
      Permutation (if In_dec A_dec x xs then xs else List.cons x xs) xs'.
Proof.
  intros x xs ys.
  revert xs.
  induction ys as [ | y ys IH ].
  - intros ? devil; inversion devil.
  - intros xs x_in xs_in.
    destruct (In_dec _ x xs) as [ x_in_xs | x_not_in_xs ].
    + simpl in xs_in.
      destruct (in_app_or _ _ _ xs_in) as [ xs_inl | xs_inr ].
      * destruct (ListIn_map_cons _ _ _ xs_inl) as [ xs' [ xs_eq xs'_in ] ].
        exists (List.cons y xs'); split.
        { apply in_or_app; left; apply ListIn_map_cons'; assumption. }
        { rewrite xs_eq; reflexivity. }
      * exists xs; split.
        { apply in_or_app; right; assumption. }
        { reflexivity. }
    + simpl in x_in.
      destruct x_in as [ x_eq | x_not_eq ].
      * destruct (in_app_or _ _ _ xs_in) as [ xs_inl | xs_inr ].
        { destruct (ListIn_map_cons _ _ _ xs_inl) as [ xs' [ xs_eq xs'_in ] ].
          rewrite x_eq in xs_eq.
          rewrite xs_eq in x_not_in_xs.
          assert False; [ apply x_not_in_xs; left; reflexivity | contradiction ]. }
        { exists (List.cons x xs); split.
          - apply in_or_app.
            left.
            rewrite x_eq.
            apply ListIn_map_cons'.
            assumption.
          - reflexivity. }
      * destruct (in_app_or _ _ _ xs_in) as [ xs_inl | xs_inr ].
        { destruct (ListIn_map_cons _ _ _ xs_inl) as [ xs' [ xs_eq xs'_in ] ].
          destruct (IH _ x_not_eq xs'_in) as [ xs_res [ xs_res_in xs_res_prem ] ].
          exists (List.cons y xs_res); split.
          - apply in_or_app.
            left.
            apply ListIn_map_cons'.
            assumption.
          - rewrite xs_eq.
            destruct (In_dec _ x xs') as [ x_in_xs' | ].
            + rewrite xs_eq in x_not_in_xs.
              assert False; [ apply x_not_in_xs; right; assumption | contradiction ].
            + rewrite (Permutation_middle (List.cons y List.nil) xs' x).
              simpl.
              rewrite xs_res_prem.
              reflexivity. }
        { generalize (IH _ x_not_eq xs_inr).
          destruct (In_dec A_dec x xs).
          - contradiction.
          - intro prf.
            destruct prf as [ ? [ ? ? ] ].
            eexists; split; [ | eassumption ].
            apply in_or_app.
            right; assumption. }
Qed.

Fixpoint deduplicate {A: Type} {A_dec: forall (x y: A), {x = y} + {x <> y}} (xs: list A): list A :=
  match xs with
  | List.cons x xs =>
    if In_dec A_dec x xs
    then @deduplicate _ A_dec xs
    else List.cons x (@deduplicate _ A_dec xs)
  | List.nil => List.nil
  end.

Lemma deduplicate_spec {A: Type} {A_dec: forall (x y: A), {x = y} + {x <> y}}: forall (x: A) xs,
    List.In x xs <-> List.In x (@deduplicate _ A_dec xs).
Proof.
  intros x xs.
  induction xs as [ | x' xs IH ].
  - split; intro devil; inversion devil.
  - split.
    + intro prf.
      inversion prf as [ eq | in_rest ].
      * simpl.
        destruct (In_dec A_dec x' xs) as [ in_xs | not_in_xs ].
        { rewrite eq in in_xs; apply IH; assumption. }
        { left; rewrite eq; reflexivity. }
      * simpl.
        destruct (In_dec A_dec x' xs) as [ in_xs | not_in_xs ].
        { apply IH; assumption. }
        { right; apply IH; assumption. }
    + intro prf.
      simpl in prf.
      destruct (In_dec A_dec x' xs) as [ in_xs | not_in_xs ].
      * right; apply IH; assumption.
      * inversion prf as [ eq | in_rest ].
        { rewrite eq; left; reflexivity. }
        { right; apply IH; assumption. }
Qed.

Lemma powerset_permut_incl {A: Type} {A_dec: forall (x y : A), {x = y} + {x <> y}}:
  forall (xs: list A) ys,
    List.Forall (fun x' => List.In x' ys) xs ->
    exists xs',
      List.In xs' (powerset ys) /\
      Permutation (@deduplicate _ A_dec xs) xs'.
Proof.
  intros xs.
  induction xs as [ | x xs IH ].
  - intros.
    exists List.nil; split.
    + apply powerset_empty_incl.
    + reflexivity.
  - intros ys prf.
    inversion prf as [ | ? ? x_prf xs_prf ].
    simpl.
    generalize (IH _ xs_prf).
    intro IH'.
    destruct IH' as [ xs' [ in_xs' perm_xs' ] ].
    destruct (In_dec A_dec x xs) as [ in_x_xs | not_in_x_xs ].
    + exists xs'; split.
      * assumption.
      * assumption.
    + destruct (@powerset_spec _ A_dec x xs' ys x_prf in_xs') as [ xs'' [ in_xs'' perm_xs'' ] ].
      exists xs''; split.
      * assumption.
      * assert (x_dedup : List.In x (@deduplicate _ A_dec xs) -> False).
        { intro devil.
          apply not_in_x_xs.
          apply (@deduplicate_spec _ A_dec).
          assumption. }
        destruct (In_dec A_dec x xs') as [ in_x_xs' | ].
        { assert False.
          { apply x_dedup.
            eapply Permutation_in.
            - symmetry; eassumption.
            - assumption. }
          contradiction. }
        { rewrite perm_xs'.
          assumption. }
Qed.

Lemma powerset_permute_prop {A: Type} {A_dec: forall (x y : A), {x = y} + { x <> y }}:
  forall (P : list A -> Prop) xs ys,
    P (@deduplicate _ A_dec xs) ->
    (forall xs ys, Permutation (@deduplicate _ A_dec xs) ys -> P (@deduplicate _ A_dec xs) -> P ys) ->
    List.Forall (fun x => List.In x ys) xs ->
    List.Exists P (powerset ys).
Proof.
  intros P xs ys Pxs P_stable xs_in.
  destruct (@powerset_permut_incl _ A_dec xs ys xs_in) as [ xs' [ in_xs' permut_xs' ] ].
  induction (powerset ys).
  - inversion in_xs'.
  - inversion in_xs' as [ eq | in_tl ].
    + apply List.Exists_cons_hd.
      rewrite eq.
      apply (P_stable _ _ permut_xs' Pxs).
    + apply List.Exists_cons_tl.
      auto.
Qed.

Lemma ListIn_In: forall {A: Type} xs (x: A), List.In x xs -> exists k, nth (of_list xs) k = x.
Proof.
  intros A xs x.
  induction xs as [ | x' xs IH ].
  - intro devil; inversion devil.
  - intro prf.
    destruct prf as [ | in_rest ].
    + exists F1; assumption.
    + destruct (IH in_rest) as [ k prf ].
      exists (FS k); assumption.
Qed.

Lemma In_ListIn: forall {A: Type} xs (x: A) k, nth (of_list xs) k = x -> List.In x xs.
Proof.
  intros A xs x.
  induction xs as [ | x' xs IH ].
  - intro devil; inversion devil.
  - intro k.
    apply (Fin.caseS' k).
    + intro; left; assumption.
    + simpl; intros; right; eapply IH; eassumption.
Qed.

Lemma powerset_hd_in: forall {A: Type} (x: A) xs ys,
    List.In (List.cons x xs) (powerset ys) ->
    List.In x ys.
Proof.
  intros A x xs ys.
  revert xs.
  induction ys.
  - intros ? devil; inversion devil as [ devil' | devil']; inversion devil'.
  - intros xxs xxs_in.
    destruct (in_app_or _ _ _ xxs_in) as [ inl | inr ].
    + destruct (ListIn_map_cons _ _ _ inl) as [ ? [ x_eq nil_in ] ].
      inversion x_eq; left; reflexivity.
    + right; eauto.
Qed.

Lemma powerset_spec_in: forall {A: Type} (xs ys: list A),
    List.In xs (powerset ys) -> List.Forall (fun x => List.In x ys) xs.
Proof.
  intros A xs.
  induction xs as [ | x xs IH ].
  - intros; apply List.Forall_nil.
  - intros ys in_xs.
    destruct ys.
    + inversion in_xs as [ devil | devil ].
      * inversion devil.
      * inversion devil.
    + simpl in in_xs.
      destruct (in_app_or _ _ _ in_xs) as [ inl | inr ].
      * destruct (ListIn_map_cons _ _ _ inl) as [ ys' [ xs_eq xs_in' ] ].
        inversion xs_eq as [ [ hd_eq tl_eq ] ].
        apply List.Forall_cons.
        { left; reflexivity. }
        { rewrite tl_eq in IH.
          apply IH.
          apply in_or_app; right.
          assumption. }
      * apply List.Forall_cons.
        { eapply powerset_hd_in; eassumption. }
        { apply Forall_forall.
          intros x' x'_in_xs.
          generalize (IH _ (powerset_smaller_set_incl _ _ _ inr)).
          intro xs_in_ys.
          right.
          revert x'_in_xs xs_in_ys.
          clear ...
          intros x'_in_xs xs_in_ys.
          induction xs.
          - inversion x'_in_xs.
          - destruct x'_in_xs as [ eq | inr ].
            + rewrite eq in *.
              inversion xs_in_ys.
              assumption.
            + inversion xs_in_ys.
              auto. }
Qed.

Lemma fold_left_append {A B: Type} {m n: nat}:
  forall (xs : t A m) (ys: t A n) (s: B) f,
    fold_left f s (append xs ys) = fold_left f (fold_left f s xs) ys.
Proof.
  intro xs.
  induction xs.
  - intros; reflexivity.
  - intros; simpl; auto.
Qed.

Lemma powerset_p: forall {A: Type} (P : A -> Prop) xs,
    List.Forall P xs ->
    List.Forall (List.Forall P) (powerset xs).
Proof.
  intros A P xs prf.
  apply List.Forall_forall.
  intros xs' in_prf.
  apply List.Forall_forall.
  intros x x_in_xs.
  eapply (proj1 (List.Forall_forall _ _)).
  + apply prf.
  + generalize (powerset_spec_in _ _ in_prf).
    intro xs'_prfs. 
    apply (proj1 (List.Forall_forall _ _) xs'_prfs).
    assumption.
Qed.

Lemma powerset_map: forall {A B: Type} (f: A -> B) xs,
    powerset (List.map f xs) = List.map (List.map f) (powerset xs).
Proof.
  intros A B f xs.
  induction xs as [ | x xs IH ].
  - reflexivity.
  - simpl List.map.
    simpl powerset.
    rewrite (List.map_app).
    rewrite IH.
    apply (f_equal (fun xs => xs ++ _)).
    rewrite (List.map_map).
    rewrite (List.map_map).
    simpl.
    reflexivity.
Qed.


Lemma deduplicate_map {A B: Type}
      {A_dec: forall (x y: A), { x = y } + { x <> y }}
      {B_dec: forall (x y: B), { x = y } + { x <> y }}:
  forall xs (f: A -> B),
    (forall x y, f x = f y -> x = y) -> 
    List.map f (@deduplicate _ A_dec xs) = @deduplicate _ B_dec (List.map f xs).
Proof.
  intros xs f f_inj.
  induction xs as [ | x xs IH ].
  - reflexivity.
  - simpl List.map.
    simpl deduplicate.
    destruct (In_dec A_dec x xs) as [ in_x | not_in_x ].
    + rewrite IH.
      destruct (In_dec B_dec (f x) (List.map f xs)) as [ in_fx | not_in_fx ] .
      * reflexivity.
      * assert False; [ | contradiction ].
        apply not_in_fx.
        clear not_in_fx IH.
        induction xs.
        { inversion in_x. }
        { destruct in_x as [ here | there ].
          - rewrite here; left; reflexivity.
          - right; auto. }
    + destruct (In_dec B_dec (f x) (List.map f xs)) as [ in_fx | not_in_fx ] .
      * assert False; [ | contradiction ].
        apply not_in_x.
        clear not_in_x IH.
        induction xs.
        { inversion in_fx. }
        { destruct in_fx as [ here | there ].
          - rewrite (f_inj _ _ here); left; reflexivity.
          - right; auto. }
      * simpl; rewrite IH; reflexivity.
Qed.

Lemma exists_deduplicate {A: Type} {A_dec: forall (x y: A), { x = y } + { x <> y }}:
  forall (P : A -> Prop) xs, Exists P (of_list xs) -> Exists P (of_list (@deduplicate _ A_dec xs)).
Proof.
  intros P xs.
  induction xs as [ | x xs IH ].
  - intro devil; inversion devil.
  - intro ex_prf.
    inversion ex_prf as [ ? ? ? prf_here | ? ? ? prf_there n_eq [ hd_eq tl_eq ] ].
    + generalize (proj1 (@deduplicate_spec _ A_dec x (List.cons x xs)) (or_introl (eq_refl x))).
      intro in_x_dedup.
      induction (deduplicate (List.cons x xs)).
      * inversion in_x_dedup.
      * destruct in_x_dedup as [ eq | in_rest ].
        { rewrite eq.
          apply Exists_cons_hd.
          assumption. }
        { apply Exists_cons_tl; auto. }
    + dependent rewrite tl_eq in prf_there.
      unfold deduplicate.
      destruct (In_dec A_dec x xs).
      * auto.
      * apply Exists_cons_tl; auto.
Qed.

Lemma exists_permute {A: Type} {A_dec: forall (x y: A), { x = y } + { x <> y }}:
  forall (P : A -> Prop) xs ys,
    Permutation xs ys ->
    Exists P (of_list xs) -> Exists P (of_list ys).
Proof.
  intros P xs ys perm_xs_ys ex_x.
  assert (ex_x': exists x, List.In x xs /\ P x).
  { revert ex_x; clear ...
    intro ex_x.
    induction xs as [ | ? ? IH ].
    - inversion ex_x.
    - inversion ex_x as [ | ? ? ? prfs_tl n_eq [ hd_eq tl_eq ]].
      + eexists; split; [ apply (or_introl (eq_refl _)) | eassumption ].
      + dependent rewrite tl_eq in prfs_tl.
        destruct (IH prfs_tl) as [ x' [ in_prf prf ] ].
        exists x'; split; [ right; assumption | assumption ]. }
  destruct ex_x' as [ x' [ in_x' prf_x' ] ].
  generalize (Permutation_in _ perm_xs_ys in_x').
  revert prf_x'.
  clear ...
  induction ys.
  - intros ? devil; inversion devil.
  - intros x'_prf in_x'_ys.
    destruct in_x'_ys as [ here | there ].
    + rewrite here.
      apply Exists_cons_hd; assumption.
    + apply Exists_cons_tl; auto.
Qed.

Lemma ListLen_impl:
  forall {A: Type} (xs: list A) (p1 p2: A -> bool),
    (forall x, p1 x = true -> p2 x = true) ->
    (List.length (List.filter p1 xs) <= List.length (List.filter p2 xs))%nat.
Proof.
  intros A xs p1 p2 p_impl.
  induction xs as [ | x xs IH ].
  - reflexivity.
  - simpl.
    generalize (p_impl x).
    destruct (p1 x).
    + intro prf; rewrite (prf eq_refl).
      simpl.
      rewrite <- Nat.succ_le_mono.
      assumption.
    + intro prf; clear prf.
      destruct (p2 x).
      * simpl.
        rewrite IH.
        apply le_S.
        reflexivity.
      * assumption.
Qed.

Lemma ListLen_ineq:
  forall {A: Type} (xs: list A) (p1 p2: A -> bool) (x: A),
    List.In x xs -> p1 x = true -> p2 x = false ->
    (forall y, p2 y = true -> p1 y = true) ->
    List.length (List.filter p1 xs) > List.length (List.filter p2 xs).
Proof.
  intros A xs p1 p2.
  induction xs as [ | x xs IH ]; intros y in_xxs p1_y not_p2_y p2_impl.
  - inversion in_xxs.
  - destruct in_xxs as [ here | there ].
    + rewrite here.
      simpl.
      rewrite p1_y.
      rewrite not_p2_y.
      simpl.
      unfold "_ > _".
      unfold "_ < _".
      rewrite <- Nat.succ_le_mono.
      apply ListLen_impl.
      assumption.
    + simpl.
      generalize (p2_impl x).
      destruct (p2 x).
      * intro prf; rewrite (prf eq_refl).
        simpl.
        unfold "_ > _".
        rewrite <- Nat.succ_lt_mono.
        apply (IH y); auto.
      * intro prf.
        destruct (p1 x).
        { apply le_S.
          eapply IH; eauto. }
        { eapply IH; eauto. }
Qed.

Lemma ListFilter_le:
  forall {A: Type} (xs: list A) (p: A -> bool), (List.length (List.filter p xs) <= List.length xs)%nat.
Proof.
  intros A xs p.
  induction xs.
  - reflexivity.
  - simpl.
    destruct (p a).
    + simpl.
      rewrite <- (Nat.succ_le_mono).
      assumption.
    + apply le_S.
      assumption.
Qed.

Lemma ListForall_app:
  forall {A: Type} (xs ys: list A) (P: A -> Prop),
    List.Forall P xs -> List.Forall P ys -> List.Forall P (xs ++ ys).
Proof.
  intros A xs ys P all_xs all_ys.
  apply List.Forall_forall.
  intros x x_in.
  destruct (List.in_app_or _ _ _ x_in) as [ inl | inr ].
  - apply (proj1 (List.Forall_forall _ _) all_xs).
    assumption.
  - apply (proj1 (List.Forall_forall _ _) all_ys).
    assumption.
Qed.  