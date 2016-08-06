Require Import Coq.Vectors.Fin.
Require Import Coq.Vectors.Vector.

Require Import Logic.Eqdep_dec.
Require Import Arith.PeanoNat.
Require Import Arith.Peano_dec.

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

Lemma map_Forall: forall {T} {n} (xs: t T n) (P: T -> Prop) f,
    Forall (fun x => P (f x)) xs -> Forall P (map f xs).
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

(*Lemma Forall_depAp: forall {T} {n} (xs: t T n) (P: T -> Prop) (R: T), P x) (S: T -> Prop),
    Forall (fun x => forall (prf: P x), S x) xs -> Forall R xs -> Forall S xs.
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
*)

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



