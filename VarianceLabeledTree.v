Require Import Coq.Arith.PeanoNat.
Require Import Coq.Vectors.Fin.
Require Import Coq.Vectors.Vector.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Init.Wf.
Require Import Coq.Arith.Wf_nat.

Require Import VectorQuantification.

Import EqNotations.

Inductive Variance := Co | Contra | In.

Class LabelInfo (Label: Set) :=
  { labelArity : Label -> nat;
    successorVariance: forall (l: Label), Fin.t (labelArity l) -> Variance }.

Inductive VLTree (Label: Set) `{LabelInfo Label} (Var: Set): Set :=
| Node : forall (l: Label), t (VLTree Label Var) (labelArity l) -> VLTree Label Var
| Hole : Var -> VLTree Label Var.

Inductive VLTreeOrder (Label: Set) (LOrder: Label -> Label -> Prop) `{LabelInfo Label}:
  VLTree Label False -> VLTree Label False -> Prop :=
| NodesOrdered:
    forall l1 l2
      (arityEq: labelArity l1 = labelArity l2)
      (varianceEq: forall k, successorVariance l1 k = successorVariance l2 (rew arityEq in k))
      xs ys,
      LOrder l1 l2 ->
      VLForestOrder Label LOrder
                    (map (successorVariance l1) (positions (labelArity l1)))
                    xs (rew <- arityEq in ys) ->
      VLTreeOrder Label LOrder (Node _ _ l1 xs) (Node _ _ l2 ys)
with VLForestOrder (Label: Set) (LOrder: Label -> Label -> Prop) `{LabelInfo Label}:
       forall {n : nat}, t Variance n -> t (VLTree Label False) n -> t (VLTree Label False) n -> Prop :=
     | VLForestOrder_empty: VLForestOrder Label LOrder (nil _) (nil _) (nil _)
     | VLForestOrder_cons_co:
         forall x y n (vs : t Variance n) xs ys,
           VLTreeOrder Label LOrder x y ->
           VLForestOrder Label LOrder vs xs ys ->
           VLForestOrder Label LOrder (cons _ Co _ vs) (cons _ x _ xs) (cons _ y _ ys)
     | VLForestOrder_cons_contra:
         forall x y n (vs : t Variance n) xs ys,
           VLTreeOrder Label LOrder y x ->
           VLForestOrder Label LOrder vs xs ys ->
           VLForestOrder Label LOrder (cons _ Contra _ vs) (cons _ x _ xs) (cons _ y _ ys)
     | VLForestOrder_cons_in:
         forall x y n (vs : t Variance n) xs ys,
           VLTreeOrder Label LOrder x y ->
           VLTreeOrder Label LOrder y x ->
           VLForestOrder Label LOrder vs xs ys ->
           VLForestOrder Label LOrder (cons _ In _ vs) (cons _ x _ xs) (cons _ y _ ys).

Definition Variance_eq_dec (v1: Variance): forall v2, { v1 = v2 } + { v1 <> v2 } :=
  match v1 as v1' return forall v2, { v1' = v2 } + { v1' <> v2 } with
  | Co =>
    fun v2 =>
      match v2 with
      | Co => left (eq_refl Co)
      | _ => right (fun eq => eq_ind Co (fun y => match y with | Co => True | _ => False end) I _ eq)
      end
  | Contra =>
    fun v2 =>
      match v2 with
      | Contra => left (eq_refl Contra)
      | _ => right (fun eq => eq_ind Contra (fun y => match y with | Contra => True | _ => False end) I _ eq)
      end
  | In =>
    fun v2 =>
      match v2 with
      | In => left (eq_refl In)
      | _ => right (fun eq => eq_ind In (fun y => match y with | In => True | _ => False end) I _ eq)
      end
  end.

Fixpoint VLTree_rect' (Label: Set) (info: LabelInfo Label) (Var: Set) (P: VLTree Label Var -> Type)
         (IHVar: forall x, P (Hole _ _ x)) 
         (IH: forall (l: Label) (successors: t (VLTree Label Var) (labelArity l)),
             ForAll' P successors -> P (Node _ _ l successors))
         (tree: VLTree Label Var): P tree :=
  match tree with
  | Node _ _ l successors =>
    IH l _
       ((fix successor_rect (n: nat) (successors: t (VLTree Label Var) n): ForAll' P successors :=
           match successors with
           | nil _ => ForAll'_nil _
           | cons _ x n xs =>
             ForAll'_cons P _ _ (VLTree_rect' Label info Var P IHVar IH x) (successor_rect n xs)
           end) _ successors)
  | Hole _ _ x => IHVar x
  end.

Definition Tree_eq_dec (Label: Set) `{LabelInfo Label} (Var: Set)
      (Label_eq_dec: forall (l1 l2: Label), { l1 = l2 } + { l1 <> l2 })
      (Var_eq_dec: forall (alpha beta: Var), { alpha = beta } + { alpha <> beta }):
  forall (t1 t2: VLTree Label Var), { t1 = t2 } + { t1 <> t2 }.
Proof.
  intro t1.
  induction t1 as [ alpha | l1 ts1 IH ] using VLTree_rect'.
  - intro t2.
    destruct t2 as [ l2 ts2 | beta ].
    + right; intro devil; inversion devil.
    + destruct (Var_eq_dec alpha beta) as [ var_eq | not_var_eq ].
      * left; rewrite var_eq; reflexivity.
      * right; intro devil; inversion devil; contradiction.
  - intro t2.
    destruct t2 as [ l2 ts2 | beta ].
    + destruct (Label_eq_dec l1 l2) as [ label_eq | not_label_eq ];
        [ | right; intro devil; inversion devil; contradiction ].
      revert ts2.
      rewrite <- label_eq.
      clear label_eq.
      intro ts2.
      assert (children_eq_dec: { ts1 = ts2 } + { ts1 <> ts2 }).
      { induction IH as [ | ? ? ? prf prfs IH' ].
        - apply (fun r => case0 (fun xs => { _ = xs } + { _ <> xs }) r ts2).
          left; reflexivity.
        - apply (caseS' ts2); clear ts2; intros y ys.
          destruct (prf y) as [ y_eq | not_y_eq ];
            [ | right; intro devil; inversion devil; contradiction ].
          destruct (IH' ys) as [ ys_eq | not_ys_eq ].
          + left; rewrite y_eq; rewrite ys_eq; reflexivity.
          + right; intro devil.
            inversion devil as [ [ y_eq' ys_eq ] ].
            apply not_ys_eq.
            apply (vect_exist_eq _ _ ys_eq). }
      destruct children_eq_dec as [ children_eq | not_children_eq ].
      * left; rewrite children_eq; reflexivity.
      * right; intro devil.
        inversion devil as [ ts_eq ].
        apply not_children_eq.
        apply (vect_exist_eq _ _ (existT_fg_eq (t (VLTree Label Var)) labelArity _ _ _ ts_eq)).
    + right; intro devil; inversion devil.
Defined.

Fixpoint VLTree_size (Label: Set) `{LabelInfo Label} (Var: Set) (t: VLTree Label Var): nat :=
  match t with
  | Node _ _ _ xs =>
    S (fold_right (fun t max => Nat.max (VLTree_size _ _ t) max) xs 0)
  | Hole _ _ _  => 1
  end.

Lemma VLTree_size_lt (Label: Set) `{LabelInfo Label} (Var: Set):
  forall (l : Label) (xs: t (VLTree Label Var) (labelArity l)),
    Forall (fun t => VLTree_size _ _ t < VLTree_size _ _ (Node _ _ l xs)) xs.
Proof.
  intro l.
  simpl.
  generalize (labelArity l).
  intros n xs.
  induction xs as [ | x n xs IH ].
  - apply Forall_nil.
  - apply Forall_cons.
    + simpl.
      unfold "_ < _".
      rewrite <- (Nat.succ_le_mono).
      apply (Nat.le_max_l).
    + apply nth_Forall.
      intro k.
      generalize (Forall_nth _ _ IH k).
      simpl.
      unfold "_ < _".
      rewrite <- (Nat.succ_le_mono).
      rewrite <- (Nat.succ_le_mono). 
      intro prf.
      rewrite prf.
      apply (Nat.le_max_r).
Qed.
      
      
Fixpoint substitute {Label Var Var': Set} `{LabelInfo Label}
         (f : Var -> VLTree Label Var') (tree: VLTree Label Var): VLTree Label Var' :=
  match tree with
  | Node _ _ l successors => Node _ _ l (map (substitute f) successors)
  | Hole _ _ x => f x
  end.

Section VLOrderDec.
  Variable (Label: Set).
  Variable (LOrder: Label -> Label -> Prop).
  Variable (LOrder_dec: forall l1 l2, {LOrder l1 l2} + {LOrder l1 l2 -> False}).
  Context `{LabelInfo Label}.
  Context `{PreOrder _ LOrder}.
  
  Section VLForestOrderDec.
    Variable max_size: nat.
    Variable VLTreeOrder_dec: forall t1 t2,
      max (VLTree_size _ _ t1) (VLTree_size _ _ t2) < max_size ->
      { VLTreeOrder Label LOrder t1 t2 } + { VLTreeOrder Label LOrder t1 t2 -> False }.
    Fixpoint VLForestOrder_dec
             {n: nat} (variances: t Variance n) (xs ys: t (VLTree Label False) n) {struct xs}:
      Forall (fun x => VLTree_size _ _ x < max_size) xs ->
      Forall (fun y => VLTree_size _ _ y < max_size) ys ->
      { VLForestOrder Label LOrder variances xs ys } + { VLForestOrder Label LOrder variances xs ys -> False }.
    Proof.  
      revert variances ys.
      case xs as [ | x n xs ].
      - intros variances ys.
        apply (fun r => case0 (fun vs => _ -> _ -> { VLForestOrder Label LOrder vs _ _ } +
                                           { VLForestOrder Label LOrder vs _ _ -> False})
                           r variances).
        apply (fun r => case0 (fun ys => _ -> _ -> { VLForestOrder Label LOrder _ _ ys } +
                                           { VLForestOrder Label LOrder _ _ ys -> False})
                           r ys).
        intros.
        left.
        apply VLForestOrder_empty.
      - intros variances ys.
        apply (caseS' variances); clear variances; intros variance variances.
        apply (caseS' ys); clear ys; intros y ys.
        intros xsok ysok.
        assert (xok: VLTree_size _ _ x < max_size).
        { inversion xsok; assumption. }
        assert (yok: VLTree_size _ _ y < max_size).
        { inversion ysok; assumption. }
        assert (xyok: max (VLTree_size _ _ x) (VLTree_size _ _ y) < max_size).
        { apply Nat.max_lub_lt; assumption. }
        assert (yxok: max (VLTree_size _ _ y) (VLTree_size _ _ x) < max_size).
        { rewrite Nat.max_comm; assumption. }
        generalize (append_Forall2 _ (cons _ x _ (nil _)) xs xsok); clear xsok; intro xsok.
        generalize (append_Forall2 _ (cons _ y _ (nil _)) ys ysok); clear ysok; intro ysok.
        destruct variance.
        + destruct (VLTreeOrder_dec x y xyok) as [ xy | not_xy ].
          * destruct (VLForestOrder_dec _ variances xs ys xsok ysok) as [ | not_xsys ].
            { left; apply VLForestOrder_cons_co; assumption. }
            { right; intro devil; inversion devil as [
                                                    | ? ? ? ? ? ? ? prfs n_eq [ vs_eq ] [ x_eq xs_eq ] [ y_eq ys_eq ]
                                                    | | ].
              apply not_xsys.
              rewrite (vect_exist_eq _ _ vs_eq) in prfs.
              rewrite (vect_exist_eq _ _ xs_eq) in prfs.
              rewrite (vect_exist_eq _ _ ys_eq) in prfs.
              assumption. }
          * right; intro devil; inversion devil; contradiction.
        + destruct (VLTreeOrder_dec y x yxok) as [ yx | not_yx ].
          * destruct (VLForestOrder_dec _ variances xs ys xsok ysok) as [ | not_xsys ].
            { left; apply VLForestOrder_cons_contra; assumption. }
            { right; intro devil; inversion devil as [ |
                                                       | ? ? ? ? ? ? ? prfs n_eq [ vs_eq ] [ x_eq xs_eq ] [ y_eq ys_eq ]
                                                       | ].
              apply not_xsys.
              rewrite (vect_exist_eq _ _ vs_eq) in prfs.
              rewrite (vect_exist_eq _ _ xs_eq) in prfs.
              rewrite (vect_exist_eq _ _ ys_eq) in prfs.
              assumption. }
          * right; intro devil; inversion devil; contradiction.
        + destruct (VLTreeOrder_dec x y xyok) as [ xy | not_xy ];
            destruct (VLTreeOrder_dec y x yxok) as [ yx | not_yx ];
            try solve [ right; intro devil; inversion devil; contradiction ].
          destruct (VLForestOrder_dec _ variances xs ys xsok ysok) as [ | not_xsys ].
          * left; apply VLForestOrder_cons_in; assumption.
          * right; intro devil; inversion devil as [ |
                                                     |
                                                     | ? ? ? ? ? ? ? ? prfs n_eq
                                                         [ vs_eq ] [ x_eq xs_eq ] [ y_eq ys_eq ]
                                                   ].
            apply not_xsys.
            rewrite (vect_exist_eq _ _ vs_eq) in prfs.
            rewrite (vect_exist_eq _ _ xs_eq) in prfs.
            rewrite (vect_exist_eq _ _ ys_eq) in prfs.
            assumption.
    Defined.
  End VLForestOrderDec.

  Definition VLTreeOrder_dec_step
             (t1 t2: VLTree Label False)
             (VLTreeOrder_dec_rec:
                forall t1' t2',
                  max (VLTree_size _ _ t1') (VLTree_size _ _ t2') < max (VLTree_size _ _ t1) (VLTree_size _ _ t2) ->
                  { VLTreeOrder Label LOrder t1' t2' } + { VLTreeOrder Label LOrder t1' t2' -> False }):    
    { VLTreeOrder Label LOrder t1 t2 } + { VLTreeOrder Label LOrder t1 t2 -> False }.
  Proof.
    case t1 as [ l1 ts1 | ]; [ | contradiction ].
    case t2 as [ l2 ts2 | ]; [ | contradiction ].
    assert (ts1_lt:
              Forall (fun x => VLTree_size _ _ x < max (VLTree_size _ _ (Node _ _ l1 ts1))
                                                    (VLTree_size _ _ (Node _ _ l2 ts2)))
                     ts1).
    { apply nth_Forall.
      intro k.
      generalize (Forall_nth _ _ (VLTree_size_lt _ _ l1 ts1) k).
      unfold "_ < _".
      intro prf.
      rewrite prf.
      apply Nat.le_max_l. }
    assert (ts2_lt:
              Forall (fun y => VLTree_size _ _ y < max (VLTree_size _ _ (Node _ _ l1 ts1))
                                                    (VLTree_size _ _ (Node _ _ l2 ts2)))
                     ts2).
    { apply nth_Forall.
      intro k.
      generalize (Forall_nth _ _ (VLTree_size_lt _ _ l2 ts2) k).
      unfold "_ < _".
      intro prf.
      rewrite prf.
      apply Nat.le_max_r. }    
    destruct (Nat.eq_dec (labelArity l1) (labelArity l2))
      as [ arityEq | ];
      [ | right; intro devil; inversion devil; contradiction ].
    assert (varianceEq: { forall k, successorVariance l1 k = successorVariance l2 (rew arityEq in k) } +
                        { (forall k, successorVariance l1 k = successorVariance l2 (rew arityEq in k)) -> False }).
    { destruct (Vector_eq_dec Variance_eq_dec
                              (map (successorVariance l1) (positions (labelArity l1)))
                              (rew <- [t Variance] arityEq in (map (successorVariance l2)
                                                                  (positions (labelArity l2)))))
        as [ eq | ineq ].
      - left.
        intro k.
        generalize (f_equal (fun xs => nth xs k) eq).
        rewrite (nth_map _ _ _ _ eq_refl).
        unfold eq_rect_r.
        rewrite (nth_k).
        rewrite (nth_map _ _ _ _ eq_refl).
        rewrite positions_spec.
        rewrite positions_spec.
        assert (eq_sym_eq: forall n m (eq: n = m) (k: Fin.t n), rew <- [Fin.t] eq_sym eq in k = rew eq in k).
        { intros n m.
          unfold eq_rect_r.
          destruct n; destruct m; intro eq'; inversion eq' as [ eq'' ].
          - intro k'.
            rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ eq').
            rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ (eq_sym (eq_sym eq'))).
            reflexivity.
          - revert eq'.
            rewrite eq''.
            intro eq'.
            intro k'.
            rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ eq').
            rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ (eq_sym (eq_sym eq'))).
            reflexivity. }
        rewrite eq_sym_eq.
        intro; assumption.
      - right; intro devil.
        apply ineq.
        revert devil.
        clear ...
        generalize (successorVariance l1).
        intro succVar.
        generalize (successorVariance l2).
        intro succVar2.
        unfold eq_rect_r.
        destruct (labelArity l1) as [ | m ]; destruct (labelArity l2) as [ | n ];
          try solve [ inversion arityEq ].
        + rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ (eq_sym arityEq)).
          intros; reflexivity.
        + inversion arityEq as [ arityEq' ].
          revert arityEq succVar.
          rewrite arityEq'.
          intro arityEq.
          rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ (eq_sym arityEq)).
          intros succVar succVarEq'.
          assert (succVarEq: forall k, succVar k = succVar2 k).
          { intro k.
            generalize (succVarEq' k).
            rewrite <- (eq_rect_eq_dec (Nat.eq_dec) _ _ arityEq).
            intro; assumption. }
          revert succVarEq.
          clear ...
          revert succVar succVar2.
          induction n as [ | n IH ].
          * intros; simpl.
            rewrite (succVarEq F1).
            reflexivity.
          * intros succVar succVar2 succVarEq.
            simpl.
            rewrite (succVarEq F1).
            apply f_equal.
            generalize (IH (fun k => succVar (FS k)) (fun k => succVar2 (FS k))
                           (fun k => succVarEq (FS k))).
            rewrite (map_fg).
            rewrite (map_fg _ succVar2).
            simpl; intro; assumption. }
    inversion varianceEq as [ varianceEq' | varianceInEq ].
    - destruct (LOrder_dec l1 l2) as [ l1l2 | ]; [ | right; intro devil; inversion devil; contradiction ].
      rewrite <- (rewrite_vect _ (eq_sym arityEq) ts2) in ts2_lt.
      fold (eq_rect_r (t (VLTree Label False)) ts2 arityEq) in ts2_lt.
      generalize (VLForestOrder_dec _ VLTreeOrder_dec_rec
                    (map (successorVariance l1) (positions (labelArity l1)))
                    ts1 (rew <- arityEq in ts2)
                    ts1_lt ts2_lt).
      intro successor_dec.
      inversion successor_dec as [ ts1ts2 | not_ts1ts2 ].
      + left; eapply NodesOrdered; eassumption.
      + right; intro devil.
        inversion devil as [ ? ? ? ? ? ? ? prfs [ l1_eq ts1_eq ]  [ l2_eq ts2_eq ] ].
        apply not_ts1ts2.
        rewrite (vect_exist_eq _ _ (existT_fg_eq (t (VLTree Label False)) labelArity l1 _ _ ts1_eq)) in prfs.
        rewrite (vect_exist_eq _ _ (existT_fg_eq (t (VLTree Label False)) labelArity l2 _ _ ts2_eq)) in prfs.
        rewrite (UIP_dec (Nat.eq_dec) _ arityEq) in prfs.
        exact prfs.
    - right; intro devil.
      inversion devil as [ ? ? arityEq' varianceEq'' ].
      apply varianceInEq.
      intro k.
      generalize (varianceEq'' k).
      rewrite (UIP_dec (Nat.eq_dec)  arityEq arityEq').
      intro; assumption.
  Defined.

  Lemma WF_VLTree_size_max:
    well_founded (fun (xy x'y': VLTree Label False * VLTree Label False) =>
                    max (VLTree_size _ _ (fst xy)) (VLTree_size _ _ (snd xy)) <
                    max (VLTree_size _ _ (fst x'y')) (VLTree_size _ _ (snd x'y'))).
  Proof.
    apply well_founded_ltof.
  Qed.   
  
  Definition VLTreeOrder_dec (t1 t2: VLTree Label False):
    { VLTreeOrder Label LOrder t1 t2 } + { VLTreeOrder Label LOrder t1 t2 -> False } :=
    Fix_F_2 _ VLTreeOrder_dec_step (WF_VLTree_size_max (t1, t2)).
End VLOrderDec.

Instance VLOrderRefl (Label: Set) (LOrder: Label -> Label -> Prop)
         `{LabelInfo Label}
         `{Reflexive _ LOrder}: Reflexive (VLTreeOrder Label LOrder).
Proof.
  unfold Reflexive.
  intro tree.
  induction tree as [ alpha | l ts IH ] using VLTree_rect';
    [ contradiction | ].
  apply (NodesOrdered _ _ l l eq_refl).
  - simpl; intro k; reflexivity.
  - reflexivity.
  - unfold eq_rect_r.
    simpl.
    revert ts IH.
    generalize (map (successorVariance l) (positions (labelArity l))).
    generalize (labelArity l).
    clear ...
    intros n variances ts IH.
    induction IH as [ | t n ts prf prfs IH ].
    + apply (fun r => case0 (fun vs => VLForestOrder _ _ vs _ _) r variances).
      apply VLForestOrder_empty.
    + apply (caseS' variances); clear variances; intros variance variances.
      destruct variance.
      * apply VLForestOrder_cons_co; auto.
      * apply VLForestOrder_cons_contra; auto.
      * apply VLForestOrder_cons_in; auto.
Qed.


Lemma VLTree_size_order
      (Label: Set) (LOrder: Label -> Label -> Prop)
      `{LabelInfo Label}:
  forall t1 t2, VLTreeOrder Label LOrder t1 t2 -> VLTree_size _ _ t1 = VLTree_size _ _ t2.
Proof.
  intros t1 t2.
  apply (fun tgt =>
           @Fix_F_2 _ _ (fun x y => max (VLTree_size _ _ (fst x)) (VLTree_size _ _ (snd x)) <
                                 max (VLTree_size _ _ (fst y)) (VLTree_size _ _ (snd y)))
                    (fun x y => VLTreeOrder Label LOrder x y -> VLTree_size Label False x = VLTree_size Label False y)
                    tgt t1 t2 (WF_VLTree_size_max _ (t1, t2))).
  clear t1 t2.
  intros t1 t2 IH.
  destruct t1 as [ l1 ts1 | alpha];
    [ | intro devil; inversion devil ];
    destruct t2 as [ l2 ts2 | beta ];
    [ | intro devil; inversion devil ].
  simpl.
  intro orderprf.
  inversion orderprf as [ ? ? arityEq varianceEq ? ? labelOrder forestOrder  [ l1_eq ts1_eq ] [ l2_eq ts2_eq ]].
  rewrite (vect_exist_eq _ _ (existT_fg_eq (t (VLTree Label False)) (labelArity) _ _ _ ts1_eq)) in forestOrder.
  rewrite (vect_exist_eq _ _ (existT_fg_eq (t (VLTree Label False)) (labelArity) _ _ _ ts2_eq)) in forestOrder.
  apply f_equal.
  generalize (VLTree_size_lt _ _ l1 ts1).
  generalize (VLTree_size_lt _ _ l2 ts2).
  clear orderprf ts1_eq ts2_eq varianceEq.
  revert ts1 arityEq ts2 IH forestOrder.
  clear ...
  simpl.
  generalize (map (successorVariance l1) (positions (labelArity l1))).
  generalize (labelArity l1).
  intros n variances ts1 arityEq.
  rewrite <- arityEq.
  clear arityEq.
  intros ts2 IH orderprf ts2ok ts1ok.
  assert (argSizeEq: Forall2 (fun x y => VLTree_size Label False x = VLTree_size Label False y) ts1 ts2).
  { apply nth_Forall2.
    intro k.
    assert (kthorder: (VLTreeOrder _ LOrder (nth ts1 k) (nth ts2 k)) \/
                      (VLTreeOrder _ LOrder (nth ts2 k) (nth ts1 k))).
    { revert orderprf.
      clear ...
      induction k as [ | n k IH ].
      - apply (caseS' ts1); clear ts1; intros t1 ts1.
        apply (caseS' ts2); clear ts2; intros t2 ts2.
        intro orderprf.
        simpl.
        inversion orderprf; solve [ left; assumption | right; assumption ].
      - apply (caseS' ts1); clear ts1; intros t1 ts1.
        apply (caseS' ts2); clear ts2; intros t2 ts2.
        apply (caseS' variances); clear variances; intros variance variances.
        simpl.
        intro orderprf.
        inversion orderprf as [
                             | ? ? ? ? ? ? ? prfs n_eq [ v_eq vs_eq ] [ l1_eq ts1_eq ] [l2_eq ts2_eq ]
                             | ? ? ? ? ? ? ? prfs n_eq [ v_eq vs_eq ] [ l1_eq ts1_eq ] [l2_eq ts2_eq ]
                             | ? ? ? ? ? ? ? ? prfs n_eq [ v_eq vs_eq ] [ l1_eq ts1_eq ] [l2_eq ts2_eq ] ];
          rewrite (vect_exist_eq _ _ vs_eq) in prfs;
          rewrite (vect_exist_eq _ _ ts1_eq) in prfs;
          rewrite (vect_exist_eq _ _ ts2_eq) in prfs;
          eapply IH; eassumption. }
    destruct kthorder.
    - apply IH.
      + unfold "_ < _".
        apply (proj1 (Nat.succ_le_mono _ _ )).
        apply (Nat.max_le_compat).
        * apply (proj2 (Nat.succ_le_mono _ _) (Forall_nth _ _ ts1ok k)).
        * apply (proj2 (Nat.succ_le_mono _ _) (Forall_nth _ _ ts2ok k)).
      +  assumption.
    - apply eq_sym.
      apply IH.
      + unfold "_ < _".
        apply (proj1 (Nat.succ_le_mono _ _ )).
        rewrite (Nat.max_comm _ _).
        apply (Nat.max_le_compat).
        * apply (proj2 (Nat.succ_le_mono _ _) (Forall_nth _ _ ts1ok k)).
        * apply (proj2 (Nat.succ_le_mono _ _) (Forall_nth _ _ ts2ok k)).
      + assumption. }
  revert argSizeEq.
  clear ...
  intro argSizeEq.
  induction argSizeEq as [ | n t1 t2 ts1 ts2 hd_eq IH ].
  - reflexivity.
  - simpl.
    rewrite hd_eq.
    apply f_equal.
    assumption.
Qed.


(* TODO: *)
Instance VLOrderTrans (Label: Set) (LOrder: Label -> Label -> Prop)
         `{LabelInfo Label}
         `{Transitive _ LOrder}: Transitive (VLTreeOrder Label LOrder).
Proof.
  unfold Transitive.
  intro t1.
  destruct t1 as [ l1 ts1 | alpha];
    [ | intros ? ? devil; inversion devil ].
  - intros t2 t3 t1t2 t2t3. 
    inversion t1t2 as [ ? l2 arityEq12 varianceEq12 ? ts2 lOrder12 forestOrder12 [ t1_eq ts1_eq ] [ t2_eq ] ].
    rewrite (vect_exist_eq _ _ (existT_fg_eq _ _ _ _ _ ts1_eq)) in forestOrder12.
    clear ts1_eq xs.
    inversion t2t3 as [ l2' l3 arityEq23 varianceEq23 ts2' ts3 lOrder23 forestOrder23 [ t2_eq' ] [ t3_eq ]].
    rewrite <- t2_eq' in t2_eq.
    inversion t2_eq as [ [ l2_eq ts2_eq ] ].
    clear t2_eq t2_eq'.
    assert (arityEq23' : labelArity l2 = labelArity l3).
    { rewrite l2_eq; assumption. }
    assert (varianceEq23' : forall k : Fin.t (labelArity l2),
               successorVariance l2 k = successorVariance l3 (rew [Fin.t] arityEq23' in k)).
    { revert varianceEq23.
      revert l2_eq.
      clear ...
      intro l2_eq.
      revert arityEq23'.
      rewrite l2_eq.
      intros arityEq23'.
      rewrite (UIP_dec (Nat.eq_dec) arityEq23' arityEq23).
      intro; assumption. }
    assert (lOrder23': LOrder l2 l3).
    { rewrite l2_eq; assumption. }
    assert (forestOrder23':
              VLForestOrder Label LOrder (map (successorVariance l2) (positions (labelArity l2))) ts2
                            (rew <- [t (VLTree Label False)] arityEq23' in ts3)).
    { clear varianceEq23' varianceEq23 forestOrder12.
      revert l2_eq ts2 ts2' ts2_eq arityEq23 arityEq23' forestOrder23.
      clear ...
      intro l2_eq.
      rewrite l2_eq.
      intros ts2 ts2' ts2_eq.
      rewrite (vect_exist_eq _ _ (existT_fg_eq (t (VLTree Label False)) (labelArity) _ _ _ ts2_eq)).
      intros arityEq23 arityEq23'.
      rewrite (UIP_dec (Nat.eq_dec) arityEq23 arityEq23').
      intros; assumption. }
    clear t1t2 t2t3 arityEq23 varianceEq23 forestOrder23 t3_eq ts2_eq.
    revert arityEq23' arityEq12 ts1 ts2 ts3 varianceEq12 varianceEq23' forestOrder12 forestOrder23'.
    clear ...
    generalize (successorVariance l2).
    induction (labelArity l2).
    + admit.
    + 
    
    intro  arityEq12.
    
    rewrite <- arityEq12.
    unfold eq_rect_r at 1.
    simpl.
    clear arityEq12.
    
    induction (labelArity l1).
    
    intros succVar_l2 arityEq23.
    revert succVar_l2.
    generalize (successorVariance l3).
    intro succVar_l3.
    
    rewrite <- arityEq23.
    
    
    apply (NodesOrdered _ _ l1 l3 (eq_trans arityEq12 arityEq23')).
    + intro k.
      rewrite (eq_trans (varianceEq12 k) (varianceEq23' (rew arityEq12 in k))).
      apply f_equal.
      clear ...
      rewrite <- arityEq23'.
      simpl.
      rewrite <- arityEq12.
      simpl.
      reflexivity.
    + transitivity l2; assumption.
    + clear ts2_eq.
      revert arityEq23' ts2 forestOrder12 forestOrder23' varianceEq12 varianceEq23'.
      clear ...
      generalize (successorVariance l2).
      rewrite <- arityEq12.
      unfold eq_rect_r.
      simpl.
      intros succVar2 arityEq23'.
      generalize (successorVariance l3).
      revert ts3.
      rewrite <- arityEq23'.
      simpl.
      intros ts3 succVar3 ts2  forestOrder12 forestOrder23 succVar2_eq succVar3_eq.
      assert (varEq: map (successorVariance l1) (positions (labelArity l1)) =
                     map succVar2 (positions (labelArity l1))).
      { apply map_extensional.
        intro k.
        rewrite (succVar2_eq k).
        reflexivity. }
      rewrite <- varEq in forestOrder23.
      revert ts1 ts2 ts3 forestOrder12 forestOrder23.
      clear ...
      generalize (map (successorVariance l1)).
      intros forestOrder12.
      revert 
      induction forestOrder12.
      * intros; assumption.
      * apply (caseS' ts3); clear ts3; intros t3 ts3.
        intros forestOrder23 IH.
        inversion forestOrder23 as [ | ? ? ? ? ? ? prf prfs n_eq [ var_eq ] [ y_eq ys_eq ] [ t3_eq ts3_eq ] | | ].
        apply VLForestOrder_cons_Co.
*)