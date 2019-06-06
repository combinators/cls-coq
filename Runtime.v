Require Import PeanoNat.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Wellfounded.Inverse_Image.
Require Import Coq.Wellfounded.Lexicographic_Product.
From mathcomp Require Import all_ssreflect.
Require Import PreOrders.
Require Import Types.
Require Import Cover.
Require Import FCL.

Set Bullet Behavior "Strict Subproofs".

Delimit Scope it_scope with IT.
Open Scope it_scope.

Import EqNotations.

Section Runtime.
  Variable Combinator: finType.
  Variable Constructor: ctor.

  Fixpoint length (A: @IT Constructor) :=
    match A with
    | A1 -> A2 => (length A2).+1
    | A1 \cap A2 => maxn (length A1) (length A2)
    | _ => 1
    end.

  Lemma lengthS: forall A, 0 < length A.
  Proof.
    elim => //= A1 IH1 A2 IH2.
    apply: (@leq_trans (length A1)) => //.
      by apply: leq_maxl.
  Qed.    

  Lemma size_merge: forall (mss1 mss2: seq (seq (@MultiArrow Constructor))),
      seq.size (merge _ mss1 mss2) = maxn (seq.size mss1) (seq.size mss2).
  Proof.
    elim.
    - move => mss2 /=.
        by rewrite max0n.
    - move => // ms1 mss1 IH mss2.
      rewrite /=.
      case: mss2 => //= ms2 mss2.
      rewrite maxnSS.
      apply: f_equal.
        by apply: IH.
  Qed.


  Lemma splitsLength: forall (A: @IT Constructor), seq.size (splitTy A) <= length A.
  Proof.
    move => A.
    rewrite splitTy_slow_splitTy.
    elim: A => //.
    - move => A1 _ A2 IH /=.
      case: (isOmega A2) => //=.
        by rewrite size_map.
    - move => A IH__A B IH__B /=.
      case: (isOmega A && isOmega B) => //=.
      rewrite size_behead size_merge.
      apply: (@leq_ltn_trans (maxn (length A) (length B)).-1).
      + do 2 rewrite -subn1.
        apply: leq_sub2r.
        rewrite geq_max.
        apply /andP.
        split.
        * apply: (@leq_trans (length A)) => //.
            by apply: leq_maxl.
        * apply: (@leq_trans (length B)) => //.
            by apply: leq_maxr.
      + rewrite prednK => //.
        apply: (@leq_trans (length A)).
        * by apply: lengthS.
        * by apply: leq_maxl.
  Qed.

  Lemma sumn_bound {A: eqType}:
    forall (measure: A -> nat) (xs: seq A) (bound: nat),
      (forall x, x \in xs -> measure x <= bound) ->
      sumn (map measure xs) <= seq.size xs * bound.
  Proof.
    move => measure xs bound.
    elim: xs => //= x xs IH boundprf.
    move: (boundprf x (mem_head _ _)) => bound_head.
    rewrite mulSn.
    apply: leq_add => //.
    apply: IH.
    move => y inprf.
    apply: boundprf.
      by rewrite in_cons inprf orbT.
  Qed.

  Lemma splitsSize: forall (A: @IT Constructor) ms, ms \in (splitTy A) -> seq.size ms <= (size _ A).
  Proof.
    move => A.
    rewrite splitTy_slow_splitTy.
    elim: A => //=.
    - move => c A _ ms.
        by rewrite mem_seq1 => /eqP -> /=.
    - move => A IH__A B IH__B ms.
      case: (isOmega B) => //.
      rewrite in_cons => /orP [].
      + by move => /eqP -> /=.
      + move => /mapP [] ms2 /IH__B ms2_size ->.
        rewrite size_map.
        apply: leq_trans; first by apply: ms2_size.
          by apply: leq_addl.
    - move => A IH__A B IH__B ms.
        by rewrite mem_seq1 => /eqP -> /=.
    - move => A IH__A B IH__B ms.
      case: (isOmega A && isOmega B) => //.
      rewrite in_cons => /orP [].
      + by move => /eqP ->.
      + move => /mem_behead inprf.
        have: exists ms1 ms2, (ms1 \in splitTy_slow _ A \/ ms1 = [::]) /\
                         (ms2 \in splitTy_slow _ B \/ ms2 = [::]) /\
                         ms = ms1 ++ ms2.
        { clear IH__A IH__B.
          move: inprf.
          move: (splitTy_slow _ B).
          elim: (splitTy_slow _ A).
          - move => mss2 inprf.
            exists [::], ms.
            split; last split => //.
            + by right.
            + by left.
          - move => ms1 mss1 IH.
            case.
            + move => /= inprf.
              exists ms, [::].
              split; last split.
              * by left.
              * by right.
              * by rewrite cats0.
            + move => ms2 mss2 /=.
              rewrite in_cons.
              case /orP.
              * move => /eqP ->.
                exists ms1, ms2.
                split; last split => //.
                ** by left; apply mem_head.
                ** by left; apply mem_head.
              * move => /IH [] ms11 [] ms22 [] prf_ms11 [] prf_ms22 ms__eq.
                exists ms11, ms22.
                split; last split => //.
                ** case: prf_ms11; last by right.
                   rewrite in_cons => ->.
                     by left; rewrite orbT.
                ** case: prf_ms22; last by right.
                   rewrite in_cons => ->.
                     by left; rewrite orbT. }
        move => [] ms1 [] ms2 [] prf_ms1 [] prf_ms2 ->.
        rewrite size_cat.
        rewrite -addnA.
        apply: leq_trans; last by apply: leq_addl.
        apply: leq_add.
        * case: prf_ms1; last by move => ->.
            by move => /IH__A.
        * case: prf_ms2; last by move => ->.
            by move => /IH__B.
  Qed.

  Lemma size1: forall (A: @IT Constructor), 0 < size _ A.
  Proof. by case => //. Qed.

  Lemma splitsFlattenSize: forall (A: @IT Constructor), seq.size (flatten (splitTy A)) <= (length A) * (size _ A).
  Proof.
    move => A.
    rewrite splitTy_slow_splitTy.
    elim: A => //.
    - move => A IH__A B IH__B.
      rewrite /=.
      case: (isOmega B).
      + done.
      + rewrite /=.
        rewrite size_flatten /shape.
        apply: leq_ltn_trans; first apply: (sumn_bound _ _ (size _ B).+1).
        * move => _ /mapP [] ms inprf ->.
          rewrite size_map.
          apply: leq_trans; last by apply: leqnSn.
          apply: splitsSize.
            by rewrite splitTy_slow_splitTy.
        * rewrite size_map.
          apply: ltn_mul.
          ** rewrite -splitTy_slow_splitTy.
               by apply: splitsLength.
          ** rewrite -[(size _ B).+1]add1n.
             rewrite -addnA ltn_add2l.
             rewrite -add1n.
             apply: leq_add => //.
               by apply: size1.
    - move => A IH__A B IH__B.
      rewrite size_flatten /shape.
      apply: leq_trans; first apply: (sumn_bound _ _ (size _ (A \cap B))).
      * rewrite -splitTy_slow_splitTy.
          by move => ms /splitsSize.
      * apply: leq_mul => //.
        rewrite -splitTy_slow_splitTy.
          by apply: splitsLength.
  Qed.
End Runtime.    







