Require Import Coq.Vectors.Fin.
Require Import Coq.Vectors.Vector.

Require Import Logic.Eqdep_dec.
Require Import Arith.PeanoNat.
Require Import Arith.Peano_dec.

Import EqNotations.

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
  induction xs; intros ys x y.
  - admit.
  - admit.
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