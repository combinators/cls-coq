From mathcomp Require Import all_ssreflect div.
Require Import PreOrders.
Require Import Types.
Require Import Cover.
Require Import FCL.
Require Import Coq.Lists.Streams.

Set Bullet Behavior "Strict Subproofs".
Import EqNotations.

Section TreeGrammarEnumeration.
  Variable Constructor: ctor.
  Variable Combinator: finType.

  Record FinSolutions : Type :=
    mkFS { card : nat;
           solutions : forall n, n < card -> @Term Combinator }.

  Definition fempty: FinSolutions :=
    mkFS 0 (fun n devil => False_rect _ (notF (rew (ltn0 n) in devil))).

  Lemma shiftsub: forall m n o, ~~(o < m) -> o < m + n -> o - m < n.
  Proof.
    move => m n o disprf prf.
    rewrite -(ltn_add2r m) addnC [X in _ < X]addnC subnKC => //.
    move: disprf.
      by rewrite -leqNgt.
  Qed.

  Definition fcat (fs1 fs2: FinSolutions): FinSolutions :=
    mkFS (card fs1 + card fs2)
         (fun n prf =>
            match (boolP (n < card fs1)) with
            | AltTrue prf' => solutions fs1 n prf'
            | AltFalse disprf => solutions fs2 (n - (card fs1)) (shiftsub _ _ _ disprf prf)
            end).

  Lemma shiftdiv: forall m n o, o < m * n -> (o %/ n) < m.
  Proof.
    move => m n o.
    case m0: (m == 0).
    - move: m0 => /eqP ->.
        by rewrite mul0n.
    - case n0: (n == 0).
      + move: n0 => /eqP ->.
          by rewrite muln0.
      + move => prf.
        rewrite ltn_divLR => //.
        move: n0 m0 prf.
          by case: n.
  Qed.

  Lemma shiftmod: forall m n o, o < m * n -> o %% n < n.
  Proof.
    move => m n o.
    case n0: (n == 0).
    - move: n0 => /eqP ->.
        by rewrite muln0.
    - rewrite ltn_pmod => //.
      move: n0.
        by case: n.
  Qed.

  Definition fapp (fs1 fs2: FinSolutions): FinSolutions :=
    mkFS (card fs1 * card fs2)
         (fun n prf =>
            (App (solutions fs1 (n %/ (card fs2)) (shiftdiv _ _ _ prf))
                 (solutions fs2 (n %% (card fs2)) (shiftmod _ _ _ prf)))).

  Definition Solutions := Stream FinSolutions.

  CoFixpoint sempty: Solutions := Cons fempty sempty.

  Fixpoint sofSeq (xss: seq FinSolutions): Solutions :=
    if xss is [:: xs & xss]
    then Cons xs (sofSeq xss)
    else sempty.

  CoFixpoint sreversals_corec
             (revss: seq FinSolutions)
             (xss: Solutions): Stream (seq FinSolutions) :=
    let withHead := [:: (hd xss) & revss] in
    Cons withHead (sreversals_corec withHead (tl xss)).

  Definition sreversals (xss: Solutions): Stream (seq FinSolutions) :=
    sreversals_corec [::] xss.

  Fixpoint sconvApp (xss: Solutions) (yss: seq FinSolutions): FinSolutions :=
    if yss is [:: ys & yss]
    then fcat (sconvApp (tl xss) yss) (fapp (hd xss) ys)
    else fempty.

  CoFixpoint sapp_corec (xss: Solutions) (yss: Stream (seq FinSolutions)) :=
    Cons (sconvApp xss (hd yss)) (sapp_corec xss (tl yss)).

  Definition sapp (xss: Solutions) (yss: Solutions) :=
    sapp_corec xss (sreversals yss).

  Definition fsingleton (t: @Term Combinator) : FinSolutions :=
    mkFS 1 (fun n prf => t).

  Definition ssingleton (t: @Term Combinator) : Solutions :=
    Cons (fsingleton t) sempty.

  Definition pay (s: Solutions): Solutions := Cons fempty s.

  CoFixpoint scat (xss yss: Solutions): Solutions :=
    Cons (fcat (hd xss) (hd yss)) (scat (tl xss) (tl yss)).

  Fixpoint sofSize (n: nat) (xss: Solutions): FinSolutions :=
    if n is n.+1 then sofSize n (tl xss) else hd xss.

  CoFixpoint addRule
             (r: @Rule Combinator Constructor)
             (xss: Stream (@IT Constructor -> FinSolutions)): Stream (@IT Constructor -> FinSolutions) :=
    match r with
    | RuleCombinator B c =>
      let: Cons xs xss := xss in
      Cons (fun A => if A == B then fcat (xs A) (fsingleton (Var c)) else (xs A)) xss
    | RuleApply B C D =>
      let xss' :=(addRule r (tl xss)) in 
      let css := map (fun xs => xs C) xss' in
      let dss := map (fun xs => xs D) xss' in
      let bss := sapp css dss in
      Cons (hd xss) (zipWith (fun xs bs A => if A == B then fcat (xs A) bs else (xs A)) xss' bss)
    | _ => xss
    end.


  Fixpoint enumerate (G: @TreeGrammar Combinator Constructor): Stream (@IT Constructor -> FinSolutions) :=
    match G with
    | [:: RuleCombinator B c & G] =>
      let: Cons xs xss := enumerate G
      Cons (fun A => if  A == B then fcat (hd (enumerate A G)) (fsingleton (Var c)) else hd (enumerate A G)) (tl (enumerate A G))
    | 
    | _ => sempty
    end.

End TreeGrammarEnumeration.


Section TestEnum.
  Definition Combinator := [finType of 'I_3].

  Definition t0 : @Term Combinator := Var (inord 0).
  Definition t1 : @Term Combinator := Var (inord 1).
  Definition t2 : @Term Combinator := Var (inord 2).

  Eval native_compute in (solutions _ (hd (scat _ (ssingleton _ t2) (sapp _ (ssingleton _ t0) (ssingleton _ t1)))) 0 isT).
End TestEnum.
 
*)


