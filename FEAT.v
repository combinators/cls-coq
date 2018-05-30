Require Import Coq.Lists.List.
Require Import Coq.NArith.BinNat.
Require Import Coq.Logic.Eqdep_dec.
Import ListNotations.
Import EqNotations.

Structure Finite (A: Type): Type :=
  { cardinality: N;
    index : forall (n : N), N.lt n cardinality -> A }.

Arguments cardinality {_} _.
Arguments index {_} _ _ _.

Lemma right_index_le:
  forall n k j, N.lt n (k + j) -> N.le k n -> N.lt (n - k) j.
Proof.
  intros n k j n_lt n_ge.
  rewrite N.add_comm in n_lt.
  destruct (N.lt_decidable (n - k) j) as [ | devil ]; [ assumption | ].
  generalize (proj2 (N.le_ngt _ _) devil).
  intro devil'.
  apply False_rect.  
  apply (N.lt_irrefl n).
  assert (n_lt' : N.lt n (n - k + k)).
  { apply (N.lt_le_trans _ _ _ n_lt).
    apply (N.add_le_mono_r).
    assumption. }
  rewrite (N.sub_add k n n_ge) in n_lt'.
  exact n_lt'.
Qed.

Lemma lt_dec: forall n m, { N.lt n m } + { N.le m n }.
Proof.
  intros n m.
  destruct (N.ltb n m) eqn:p.
  - left; apply N.ltb_lt; assumption.
  - right; intro devil.
    generalize (proj2 (N.ltb_lt _ _) (proj1 (N.compare_gt_iff _ _) devil)).
    intro p'.
    rewrite p' in p.
    inversion p.
Defined.

Definition finite_app {A: Type} (xs: Finite A) (ys: Finite A): Finite A :=
  {| cardinality := cardinality xs + cardinality ys;
     index n nprf :=
       match lt_dec n (cardinality xs) with
       | left is_lt => index xs n is_lt
       | right is_ge => index ys (n - (cardinality xs)) (right_index_le _ _ _
                                                                        nprf is_ge)
       end |}.


Definition finite_prod {A B: Type} (xs: Finite A) (ys: Finite B): Finite (A * B) :=
  {| cardinality := cardinality xs * cardinality ys;
     index n nprf :=
       match N.eq_dec (cardinality ys) 0 with
       | left eq => False_rect (A * B)
                              (N.nlt_0_r n (rew [fun x => N.lt n x] (N.mul_0_r (cardinality xs)) in
                                               rew [fun x => N.lt n ((cardinality xs) * x)] eq in nprf))
       | right ineq =>
         let (q, r) := N.div_eucl n (cardinality ys) in
         (index xs (n / cardinality ys) (N.div_lt_upper_bound n (cardinality ys) (cardinality xs) ineq
                                           (rew (N.mul_comm _ _) in nprf)),
          index ys (n mod (cardinality ys))  (N.mod_upper_bound _ _ ineq))
       end |}.

Definition finite_singleton {A: Type} (x: A): Finite A :=
  {| cardinality := 1;
     index n nprf := x |}.

Definition finite_empty {A: Type}: Finite A :=
  {| cardinality := 0;
     index n nprf := False_rect A (N.nlt_0_r n nprf) |}.

Definition map_finite {A B: Type} (f : A -> B) (xs: Finite A): Finite B :=
  {| cardinality := cardinality xs;
     index n nprf := f (index xs n nprf) |}.

  
CoInductive Enumeration (A : Type): Type :=
| Cons : A -> Enumeration A -> Enumeration A
| Stop : Enumeration A.

Arguments Cons {_} _ _.
Arguments Stop {_}.


Definition forever {A: Type} (x: A): Enumeration A :=
  (cofix go: Enumeration A := Cons x go).

Definition reversals {A: Type} (e: Enumeration A): Enumeration (list A) :=
  (cofix go (rev: list A) (xs: Enumeration A) :=
     match xs with
     | Stop => Stop
     | Cons x xs => Cons (x :: rev) (go (x :: rev) xs)
     end) nil e.


Definition tails {A: Type} (xs: Enumeration A): Enumeration (Enumeration A) :=
  (cofix go (xs: Enumeration A): Enumeration (Enumeration A) :=
     match xs with
     | Stop => Cons Stop Stop
     | Cons x xs => Cons (Cons x xs) (go xs)
     end) xs.

Definition map {A B: Type} (f: A -> B) (xs: Enumeration A): Enumeration B :=
  (cofix go (xs: Enumeration A): Enumeration B :=
     match xs with
     | Stop => Stop
     | Cons x xs => Cons (f x) (go xs)
     end) xs.

Definition conv_cardinality {A B: Type} (xss: Enumeration (Finite A)) (yss: list (Finite B)) (start: N) :=
   snd
     (fold_left
        (fun (s : Enumeration (Finite A) * N) (ys : Finite B) =>
         let (y, r) := s in
         match y with
         | Cons xs xss => (xss, (r + cardinality xs * cardinality ys)%N)
         | Stop => s
         end) yss (xss, start)).

Definition conv_cardinality_eq {A B: Type}:
  forall (xss: Enumeration (Finite A)) (yss: list (Finite B)),
   conv_cardinality xss yss 0 =
   cardinality
     (snd
        (fold_left
           (fun (s : Enumeration (Finite A) * Finite (A * B)) (ys : Finite B)
            =>
            let (y, r) := s in
            match y with
            | Cons xs xss => (xss, finite_app r (finite_prod xs ys))
            | Stop => s
            end) yss (xss, finite_empty))).
Proof.
  intros xss yss.
  unfold conv_cardinality.
  generalize (eq_refl: 0%N = cardinality (@finite_empty (A*B))).
  generalize (@finite_empty (A*B)).
  generalize 0%N.
  revert xss.
  induction yss as [ | ys yss IH ];
    intros xss n r card_eq.
  - assumption.
  - destruct xss as [ xs xss | ].
    + simpl.
      apply IH.
      simpl.
      rewrite card_eq.
      reflexivity.
    + simpl.
      apply IH.
      exact card_eq.
Qed.

Lemma conv_cardinality_monotonic {A B: Type}:
  forall (xss: Enumeration (Finite A)) (yss: list (Finite B)) (start k: N),
    (start > k)%N -> (conv_cardinality xss yss start > k)%N.
Proof.
  intros xss yss.
  revert xss.
  induction yss as [ | ys yss IH ]; intros xss start k prf.
  - assumption.
  - unfold conv_cardinality.
    simpl.
    destruct xss as [ | xs xss ];
      apply IH;
      apply (N.lt_gt);
      apply (N.lt_le_trans _ _ _ (N.gt_lt _ _ prf)).
    + apply (N.le_add_r).
    + reflexivity.
Qed.     

Definition conv {A B: Type} (xss: Enumeration (Finite A)) (yss: list (Finite B)): Finite (A * B)%type :=
  {| cardinality := conv_cardinality xss yss 0;
     index n inprf :=
       index (snd (fold_left (fun s ys =>
                                match s with
                                | (Stop, _) => s
                                | (Cons xs xss, r) => (xss, finite_app r (finite_prod xs ys))
                                end)
                             yss (xss, finite_empty))) n (rew conv_cardinality_eq _ _ in inprf) |}.


Definition prod' {A B: Type}
           (xs: Enumeration (Finite A))
           (yss: Enumeration (list (Finite B))): Enumeration (Finite (A * B)) :=
  match xs, yss with
  | Cons x xs', Cons ys yss =>
    (cofix goY (ry: list (Finite B)) (rys: Enumeration (list (Finite B))): Enumeration (Finite (A * B)) :=
       Cons (conv xs ry)
            (match rys with
             | Stop => map (fun ry' => conv ry' ry) (tails xs')
             | Cons ry' rys' => goY ry' rys'
             end)) ys yss
  | _, _ => Stop
  end.

Definition prod {A B: Type} (xs: Enumeration (Finite A)) (ys: Enumeration (Finite B)):
  Enumeration (Finite (A * B)) := prod' xs (reversals ys).

Definition app {A: Type} (xs ys: Enumeration (Finite A)): Enumeration (Finite A) :=
  (cofix go (xs ys: Enumeration (Finite A)): Enumeration (Finite A) :=
     match xs, ys with
     | Cons x xs', Cons y ys' => Cons (finite_app x y) (go xs' ys')
     | Cons x xs', Stop => Cons x xs'
     | Stop, Cons y ys' => Cons y ys'
     | Stop, Stop => Stop
     end) xs ys.

Definition empty {A: Type}: Enumeration (Finite A) := Cons (finite_empty) Stop.

Definition singleton {A: Type} (x: A): Enumeration (Finite A) :=
  Cons (finite_singleton x) Stop.

Definition pay {A: Type} (e: Enumeration (Finite A)): Enumeration (Finite A) :=
  Cons (finite_empty) e.

Definition hd {A: Type} (xs: Enumeration A): option A :=
  match xs with
  | Cons x _ => Some x
  | Stop => None
  end.

Definition tl {A: Type} (xs: Enumeration A): Enumeration A :=
  match xs with
  | Stop => Stop
  | Cons _ xs => xs
  end.

Definition skip {A: Type} (n: N) (xs: Enumeration A): Enumeration A :=
  @N.peano_rect
    (fun _ => Enumeration A -> Enumeration A)
    (fun xs => xs)
    (fun n r xs => match xs with | Stop => Stop | Cons _ xs => r xs end) n xs.

Definition force_enum {A: Type} (x: Enumeration A): Enumeration A :=
  match x with
  | Stop => Stop
  | Cons x xs => Cons x xs
  end.

Lemma force_enum_eq {A: Type}: forall (x: Enumeration A), x = force_enum x.
Proof.
  intro x.
  destruct x; reflexivity.
Qed.

Lemma skip_Stop {A: Type}:
  forall n, skip n (@Stop A) = Stop.
Proof.
  intro n.
  induction n as [ | n IH] using N.peano_ind.
  - reflexivity.
  - unfold skip.
    rewrite (N.peano_rect_succ).
    reflexivity.
Qed.

Definition nth_error {A: Type} (n: N) (xs: Enumeration A): option A :=
  hd (skip n xs).

Lemma skip_succ_tl {A: Type}:
  forall n (xs: Enumeration A),
    skip (N.succ n) xs = tl (skip n xs).
Proof.
  intros n.
  induction n as [ | n IH ] using N.peano_ind;
    intro xs.
  - reflexivity.
  - unfold skip.
    rewrite (N.peano_rect_succ).
    generalize (IH (tl xs)).
    destruct xs.
    + simpl.
      unfold skip.
      intro eq.
      rewrite eq.
      rewrite (N.peano_rect_succ).
      reflexivity.
    + fold (skip (N.succ n) (@Stop A)).
      intro; rewrite skip_Stop; reflexivity.
Qed.

Lemma skip_tl_succ {A: Type}:
  forall n (xs: Enumeration A),
    skip (N.succ n) xs = skip n (tl xs).
Proof.
  intros n.
  induction n as [ | n IH ] using N.peano_ind;
    intro xs.
  - reflexivity.
  - unfold skip at 1.
    rewrite (N.peano_rect_succ).
    destruct xs as [ x xs | ].
    + fold (skip (N.succ n) xs).
      reflexivity.
    + simpl.
      rewrite (skip_Stop (N.succ n)).
      reflexivity.
Qed.

Lemma skip_zero {A: Type}:
  forall (xs: Enumeration A), skip 0 xs = xs.
Proof.
  intro xs.
  unfold skip.
  rewrite N.peano_rect_base.
  reflexivity.
Qed.

Lemma app_tl {A: Type}:
  forall (xs ys: Enumeration (Finite A)), tl (app xs ys) = app (tl xs) (tl ys).
Proof.
  intros xs ys.
  destruct xs as [ x xs | ]; destruct ys as [ y ys | ].
  - reflexivity.
  - simpl.
    rewrite (force_enum_eq (app _ _)).
    simpl.
    do 2 rewrite (force_enum_eq xs) at 1.
    reflexivity.    
  - simpl.
    rewrite (force_enum_eq (app _ _)).
    simpl.
    do 2 rewrite (force_enum_eq ys) at 1.
    reflexivity.
  - simpl.
    rewrite (force_enum_eq (app _ _)).
    reflexivity.
Qed.
    

Lemma app_spec_nth {A: Type}:
  forall n (xs ys: Enumeration (Finite A)),
    nth_error n (app xs ys) = match nth_error n xs, nth_error n ys with
                              | Some x, Some y => Some (finite_app x y)
                              | Some x, _ => Some x
                              | _, Some y => Some y
                              | _, _ => None
                              end.
Proof.
  intros n.
  induction n as [ | n IH ] using N.peano_ind;
    intros xs ys.
  - destruct xs as [ x xs | ];
      destruct ys as [ y ys | ];
      reflexivity.
  - unfold nth_error.
    repeat rewrite skip_tl_succ.
    fold (nth_error n (tl (app xs ys))).
    fold (nth_error n (tl xs)).
    fold (nth_error n (tl ys)).
    rewrite app_tl.
    apply IH.
Qed.

Definition FiniteEq {A: Type} (x y: Finite A) :=
  { eq: cardinality x = cardinality y |  forall k p, index x k p = index y k (rew eq in p) }.

Lemma FiniteEq_refl {A: Type}: forall (x: Finite A), FiniteEq x x.
Proof.
  intro x.
  exists eq_refl; reflexivity.
Qed.

Lemma FiniteEq_sym {A: Type}: forall (x y: Finite A), FiniteEq x y -> FiniteEq y x.
Proof.
  intros x y prf.
  destruct prf as [ eq index_eq ].
  destruct x as [ cx indexx ]; destruct y as [ cy indexy ].
  revert index_eq.
  exists (eq_sym eq).
  simpl in *.
  revert indexx indexy index_eq.
  rewrite <- eq.
  simpl.
  intros; auto.
Qed.

Lemma FiniteEq_trans {A: Type}: forall (x y z: Finite A), FiniteEq x y -> FiniteEq y z -> FiniteEq x z.
Proof.
  intros [cx indexx] [cy indexy] [cz indexz] [cxy_eq indexxy_eq] [cyz_eq indexyz_eq].
  simpl in *.
  exists (eq_trans cxy_eq cyz_eq).
  simpl.
  intros k p.
  rewrite (indexxy_eq k p).
  clear indexxy_eq.
  revert indexyz_eq.
  revert indexy cyz_eq.
  rewrite <- cxy_eq.
  intros indexy cyz_eq.
  revert indexz.
  rewrite <- cyz_eq.
  intros; auto.
Qed.

Lemma finite_empty_eq {A: Type}:
  forall (x: Finite A), cardinality x = 0%N -> FiniteEq x finite_empty.
Proof.
  intros x card_eq.
  exists card_eq.
  destruct x as [ cx indexx ].
  simpl in *.
  revert indexx.
  rewrite card_eq.
  intros indexx k p.
  apply False_rect.
  apply (N.nlt_0_r _ p).
Qed.

Lemma finite_app_eq {A: Type}:
  forall (xs ys xs' ys': Finite A), FiniteEq xs xs' -> FiniteEq ys ys' -> FiniteEq (finite_app xs ys) (finite_app xs' ys').
Proof.
  intros [ cxs idxxs ] [ cys idxys ] [ cxs' idxxs' ] [ cys' idxys' ] [ cxs_eq idxxs_eq ] [ cys_eq idxys_eq ].
  simpl in *.
  exists (f_equal2 (N.add) cxs_eq cys_eq).
  simpl.
  revert idxxs idxys idxxs_eq idxys_eq.
  rewrite cxs_eq.
  rewrite cys_eq.
  rewrite (UIP_dec N.eq_dec (f_equal2 _ _ _) eq_refl).
  simpl.
  intros idxxs idxys idxxs_eq idxys_eq k p.
  destruct (lt_dec k cxs'); auto.
Qed.

Lemma finite_prod_eq {A B: Type}:
  forall (xs: Finite A) (ys: Finite B) xs' ys',
    FiniteEq xs xs' -> FiniteEq ys ys' -> FiniteEq (finite_prod xs ys) (finite_prod xs' ys').
Proof.
  intros [ cxs idxxs ] [ cys idxys ] [ cxs' idxxs' ] [ cys' idxys' ] [ cxs_eq idxxs_eq ] [ cys_eq idxys_eq ].
  simpl in *.
  exists (f_equal2 (N.mul) cxs_eq cys_eq).
  simpl.
  revert idxxs idxys idxxs_eq idxys_eq.
  rewrite cxs_eq.
  rewrite cys_eq.
  rewrite (UIP_dec N.eq_dec (f_equal2 _ _ _) eq_refl).
  simpl.
  intros idxxs idxys idxxs_eq idxys_eq k p.
  destruct (N.eq_dec cys' 0).
  -  reflexivity.
  - rewrite idxxs_eq.
    rewrite idxys_eq.
    reflexivity.
Qed.

          
Lemma UNLT { x y : N }: forall (p1 p2: (x < y)%N), p1 = p2.
Proof.
  intros p1 p2.
  unfold N.lt in *.
  apply UIP_dec.
  intros c1 c2;
    destruct c1;
    destruct c2;
    try solve [ left; reflexivity | right; intro devil; inversion devil ].
Qed.


Lemma finite_app_empty_l {A: Type}:
  forall (ys xs: Finite A), FiniteEq ys finite_empty ->  FiniteEq (finite_app ys xs) xs.
Proof.
  intros ys xs [ ys_card ys_index ].
  assert (card_eq: cardinality (finite_app ys xs) = cardinality xs).
  { simpl.
    rewrite ys_card.
    reflexivity. }
  exists (card_eq).
  intros k p.
  simpl.
  destruct (lt_dec k 0) as [ devil | p' ].
  + apply False_rect; apply (N.nlt_0_r _ devil).
  + destruct (lt_dec k (cardinality ys)) as [ devil | p'' ].
    * apply False_rect; rewrite ys_card in devil; apply (N.nlt_0_r _ devil).
    * match goal with
      |[|- index _ _ ?p'' = _] =>
       generalize p''
      end.
      clear p'.
      revert card_eq p p''.
      simpl.
      rewrite ys_card.
      simpl.
      rewrite (N.sub_0_r).
      intro card_eq.
      rewrite card_eq.
      intros p p' p''.
      apply f_equal.
      apply UNLT.
Qed.

Lemma finite_app_empty_r {A: Type}:
  forall (xs ys: Finite A), FiniteEq ys finite_empty -> FiniteEq (finite_app xs ys) xs.
Proof.
  intros xs ys [ ys_card ys_index ].
  assert (card_eq: cardinality (finite_app xs ys) = cardinality xs).
  { simpl.
    rewrite ys_card.
    simpl.
    rewrite (N.add_0_r).
    reflexivity. }
  exists (card_eq).
  intros k p.
  simpl.
  destruct (lt_dec k (cardinality xs)) as [ p' | p' ].
  + apply f_equal.
    apply UNLT.
  + match goal with
    |[|- index _ _ ?prf = _ ] =>
     generalize prf; intro devil
    end.
    apply False_rect.
    rewrite ys_card in devil.
    apply (N.nlt_0_r _ devil).
Qed.
      

Lemma finite_conv_eq {A B: Type}:
  forall (xs: Enumeration (Finite A)) (ys zs: list (Finite B)),
    Forall2 FiniteEq ys zs ->
    FiniteEq (conv xs ys) (conv xs zs).
Proof.
  intros xs ys zs prf.
  assert (card_eq: conv_cardinality xs ys 0%N = conv_cardinality xs zs 0%N).
  { unfold conv_cardinality.
    assert (card_eq': Forall2 (fun y z => cardinality y = cardinality z) ys zs).
    { induction prf as [ | y z ys zs yz_eq prf IH ].
      - constructor.
      - constructor.
        + inversion yz_eq; assumption.
        + assumption. }
    clear prf.
    revert xs.
    generalize (0%N).    
    induction card_eq' as [ | y z ys zs yz_eq prf IH ].
    - intros; reflexivity.
    - intros n xs.
      simpl.
      rewrite yz_eq.
      destruct xs as [ x xs | ]; apply IH. }
  exists card_eq.
  simpl.
  generalize (conv_cardinality_eq xs ys).
  generalize (conv_cardinality_eq xs zs).
  rewrite <- card_eq.
  simpl.
  generalize (conv_cardinality xs ys 0).
  match goal with
  |[|- forall n eq1 eq2 k p,  index (snd (?f _ (_, ?empt))) _ _ = _] =>
   set (P := fun xs s1 s2 =>
               forall n
                 (eq1: n = cardinality (snd (f zs (xs, s1))))
                 (eq2: n = cardinality (snd (f ys (xs, s2))))
                 k p,
                 index (snd (f ys (xs, s2))) k (rew [N.lt k] eq2 in p) =
                 index (snd (f zs (xs, s1))) k (rew [N.lt k] eq1 in p));
     fold (P xs finite_empty finite_empty)
  end.
  remember finite_empty as s1 eqn:s1_eq.
  rewrite s1_eq at 2.
  remember finite_empty as s2 eqn:s2_eq.
  assert (s_eq: FiniteEq s2 s1).
  { rewrite s1_eq; apply FiniteEq_refl. }
  clear s1_eq s2_eq.
  revert s1 s2 s_eq.
  unfold P.
  clear P card_eq.
  generalize xs.
  clear xs.
  induction prf as [ |  y z ys zs yz_eq yszs_eq IH ].
  - simpl.
    intros xs [ cs1 idxs1 ] [ cs2 idxs2 ] [ cs_eq idxs_eq ].
    simpl in *.
    revert idxs2 idxs_eq.
    rewrite cs_eq.
    intros idxs2 idxs_eq n eq1 eq2.
    simpl in idxs_eq.
    rewrite (UIP_dec N.eq_dec eq2 eq1).
    rewrite eq1.
    assumption.
  - intros xs s1 s2 s_eq n eq1 eq2 k p.
    simpl.
    destruct xs.
    + eapply IH.
      apply finite_app_eq.
      * assumption.
      * apply finite_prod_eq;
          [ apply FiniteEq_refl | assumption ].
    + eapply IH.
      assumption.
Qed. 

CoInductive ObservableEq {A: Type}: Enumeration (Finite A) -> Enumeration (Finite A) -> Prop :=
| StopEq : ObservableEq Stop Stop
| ConsEq : forall x y xs ys, FiniteEq x y -> ObservableEq xs ys -> ObservableEq (Cons x xs) (Cons y ys)
| ConsStopEq: forall x xs, FiniteEq x finite_empty -> ObservableEq xs Stop -> ObservableEq (Cons x xs) Stop
| StopConsEq: forall y ys, FiniteEq y finite_empty -> ObservableEq Stop ys -> ObservableEq Stop (Cons y ys).

Lemma ObservableEq_refl {A: Type}: forall (xs: Enumeration (Finite A)), ObservableEq xs xs.
Proof.
  cofix ObservableEq_refl.
  intros xs.
  destruct xs.
  - constructor; [ | auto ].
    apply FiniteEq_refl.
  - constructor.
Qed.

Lemma ObservableEq_sym {A: Type}: forall (xs ys: Enumeration (Finite A)), ObservableEq xs ys -> ObservableEq ys xs.
Proof.
  cofix ObservableEq_sym.
  intros xs ys prf.
  destruct prf; constructor; auto.
  apply FiniteEq_sym; assumption.
Qed.

Lemma ObservableEq_trans {A: Type}: forall (xs ys zs: Enumeration (Finite A)),
    ObservableEq xs ys -> ObservableEq ys zs -> ObservableEq xs zs.
Proof.
  cofix ObservableEq_trans.
  intros xs ys zs p1.
  destruct p1; intro p2;
    try solve [ auto ];
    inversion p2; constructor; try solve [ eauto ].
  - eapply FiniteEq_trans; eassumption.
  - eapply FiniteEq_trans; eassumption.
  - eapply FiniteEq_trans; [ eassumption | apply FiniteEq_sym; eassumption ].
  - eapply FiniteEq_trans; [ apply FiniteEq_sym; eassumption | eassumption ].
Qed.


Fixpoint prepend {A: Type} (xs: list A) (ys: Enumeration A) :=
  match xs with
  | [] => ys
  | x :: xs => Cons x (prepend xs ys)
  end.

Lemma prepend_app {A: Type}: forall (xs: list A) xs' ys, prepend xs (prepend xs' ys) = prepend (xs ++ xs') ys.
Proof.
  intros xs.
  induction xs as [ | x xs IH ];
    intros xs' ys.
  - reflexivity.
  - simpl.
    apply f_equal.
    auto using IH.
Qed.

Lemma conv_cons_empty {A B: Type}:
  forall (p: Finite A) (xs: Enumeration (Finite A)) (ys: list (Finite B)),
    FiniteEq (conv (Cons p xs) (finite_empty :: ys))
             (conv xs ys).
Proof.
  intros p xs ys.
  match goal with
  |[|- FiniteEq ?lhs ?rhs] =>
   assert (card_eq: cardinality lhs = cardinality rhs)
  end.
  { simpl.
    unfold conv_cardinality.
    simpl.
    rewrite (N.mul_0_r).
    reflexivity. }
  exists (card_eq).
  simpl.
  simpl in card_eq.
  generalize (conv_cardinality_eq xs ys).
  generalize (conv_cardinality_eq (Cons p xs) (finite_empty :: ys)).
  rewrite <- card_eq.
  simpl.
  intro e.
  rewrite e.
  simpl.
  clear e card_eq.
  revert xs.
  assert (s_eq: FiniteEq (finite_app finite_empty (finite_prod p (@finite_empty B))) finite_empty).
  { exists (N.mul_0_r _).
    simpl.
    intros k devil.
    apply False_rect.
    rewrite (N.mul_0_r _) in devil.
    apply (N.nlt_0_r _ devil). }
  revert s_eq.
  generalize (finite_app finite_empty (finite_prod p (@finite_empty B))).
  generalize (@finite_empty (A * B)).
  induction ys as [ | y ys IH ].
  - simpl.
    intros xs ys [ ? xys_eq ] ? ? k k_lt.
    rewrite (xys_eq k k_lt).
    apply f_equal.
    rewrite (UIP_dec N.eq_dec x e).
    reflexivity.
  - intros xs ys' xy_eq zs ? k k_lt.
    simpl.
    destruct zs as [ z zs | ].
    + eapply IH.
      apply finite_app_eq; [ assumption | apply FiniteEq_refl ].
    + eapply IH.
      assumption.
Qed.

      
Lemma conv_prepend_empty {A B: Type}:
  forall (ps: list (Finite A)) (xs: Enumeration (Finite A)) (ys: list (Finite B)),
    FiniteEq (conv (prepend ps xs) ((repeat finite_empty (length ps)) ++ ys))
             (conv xs ys).
Proof.
  intro ps.
  induction ps as [ | p ps IH ];
    intros xs ys.
  - apply FiniteEq_refl.
  - simpl prepend.
    simpl repeat.
    simpl "_ ++ _".
    eapply FiniteEq_trans.
    + apply (conv_cons_empty p (prepend ps xs) (repeat finite_empty (length ps) ++ ys)).
    + apply IH.
Qed.

Lemma conv_Stop {A B: Type}:
  forall (xs: list (Finite B)), FiniteEq (conv (@Stop (Finite A)) xs) finite_empty.
Proof.
  intro xs.
  induction xs as [ | x xs IH ].
  - apply finite_empty_eq.
    reflexivity.
  - destruct IH as [ card_eq index_eq ].
    exists (card_eq).
    intros k devil.
    apply False_rect.
    simpl in *.
    unfold conv_cardinality in *.
    simpl in devil.
    rewrite card_eq in devil.
    apply (N.nlt_0_r _ devil).
Qed.  

Lemma map_conv_Stop {A B: Type}:
  forall (xs: Enumeration (list (Finite B))), ObservableEq (map (conv Stop) xs) (@Stop (Finite (A * B))).
Proof.
  cofix map_conv_Stop.
  intro xs.
  destruct xs as [ x xs | ].
  - rewrite (force_enum_eq (map _ _)); simpl.
    constructor.
    + apply conv_Stop.
    + apply map_conv_Stop.
  - rewrite (force_enum_eq (map _ _)); simpl.
    apply ObservableEq_refl.
Qed.    

Lemma conv_empty {A B: Type}:
  forall (xs: Enumeration (Finite A)) (ys: list (Finite B)),
    Forall (FiniteEq finite_empty) ys ->
    FiniteEq finite_empty (conv xs ys).
Proof.
  intros xs ys prfs.
  apply FiniteEq_sym.
  apply finite_empty_eq.
  unfold conv.
  unfold conv_cardinality.
  simpl.
  revert xs prfs.
  induction ys as [ | y ys IH ].
  - intros; reflexivity.
  - intros xs prfs.
    simpl.
    inversion prfs as [ | y' ys' [ y_card y_idx ] ys_empty ].
    simpl in y_card.
    destruct xs; [ rewrite <- y_card; rewrite (N.mul_0_r _); apply IH  | apply IH ];
      assumption.
Qed.

Lemma repeat_comm {A: Type}: forall n (x: A), x :: repeat x n = repeat x n ++ [x].
Proof.
  intros n x.
  induction n as [ | n IH ].
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Lemma Forall2_comm {A: Type}:
  forall (P : A -> A -> Prop) xs ys,
    (forall x y, P x y -> P y x) ->
    Forall2 P xs ys ->
    Forall2 P ys xs.
Proof.
  intros P xs ys comm prf.
  induction prf as [ | x y hd tl IH ];
    constructor; auto.
Qed.

Lemma map_conv_empty_prefix {A B: Type}:
  forall (prefix: list (Finite A)) (xs: Enumeration (Finite A)) (ys: list (Finite B)),
    ObservableEq (map (fun x => conv x ys) (tails xs))
                 (map (fun x => conv x (List.repeat finite_empty (length prefix) ++ ys)) (tails (prepend prefix xs))).
Proof.
  cofix map_conv_empty_prefix.
  intros prefix xs ys.
  destruct xs as [ x xs | ]; destruct prefix as [ | p ps ].
  - apply ObservableEq_refl.
  - rewrite (force_enum_eq (prepend (p::ps) _)).
    simpl.
    rewrite (force_enum_eq (tails (Cons p _))).
    simpl.
    fold (tails (prepend ps (Cons x xs))).
    rewrite (force_enum_eq (map _ (Cons (Cons _ _) _))).
    simpl.
    fold (map (fun ry' => conv ry' (finite_empty:: repeat finite_empty (length ps) ++ ys))
              (tails (prepend ps (Cons x xs)))).
    rewrite (force_enum_eq (tails (Cons x xs))).
    simpl.
    fold (tails xs).
    rewrite (force_enum_eq (map _ (Cons (Cons x _) (tails _)))).
    simpl.
    fold (map (fun ry' => conv ry' ys) (tails xs)).
    constructor.
    + apply FiniteEq_sym.
      rewrite (eq_refl : Cons p (prepend ps (Cons x xs)) = prepend (p :: ps) (Cons x xs)).
      rewrite (List.app_comm_cons).
      rewrite (eq_refl : finite_empty :: repeat finite_empty (length ps) =
                         repeat (@finite_empty B) (length (p::ps))).
      eapply conv_prepend_empty.
    + assert (eq: prepend ps (Cons x xs) = prepend (ps ++ [x]) xs);
        [ apply (prepend_app ps [x]) | rewrite eq; clear eq ].
      assert (eq: @finite_empty B :: repeat finite_empty (length ps) ++ ys =
                  repeat finite_empty (length (ps ++ [x])) ++ ys).
      { rewrite (List.app_length).
        rewrite (PeanoNat.Nat.add_comm).
        reflexivity. }
      rewrite eq; clear eq.
      apply map_conv_empty_prefix.
  - apply ObservableEq_refl.
  - rewrite (force_enum_eq (prepend (p::ps) _)).
    simpl.
    rewrite (force_enum_eq (tails (Cons p _))).
    simpl.
    fold (tails (prepend ps Stop)).
    rewrite (force_enum_eq (map _ (Cons (Cons _ _) _))).
    simpl.
        fold (map (fun ry' => conv ry' (finite_empty:: repeat finite_empty (length ps) ++ ys))
              (tails (prepend ps Stop))).
    rewrite (force_enum_eq (tails Stop)).
    simpl.
    rewrite (force_enum_eq (map _ (Cons Stop Stop))).
    simpl.
    rewrite (force_enum_eq (_ Stop)).
    simpl.
    constructor.
    + rewrite (List.app_comm_cons).
      apply FiniteEq_sym.
      rewrite (eq_refl : Cons p (prepend ps Stop) = prepend (p :: ps) Stop).
      rewrite (eq_refl : finite_empty :: repeat finite_empty (length ps) =
                         repeat (@finite_empty B) (length (p::ps))).
      eapply conv_prepend_empty.
    + clear ...
      rewrite (List.app_comm_cons).
      rewrite repeat_comm.
      rewrite <- (List.app_assoc).
      simpl.
      revert ys.
      induction ps as [ | p ps IH ]; intro ys.
      * simpl.
        rewrite (force_enum_eq (map _ _)); simpl.
        rewrite (force_enum_eq (_ Stop)); simpl.
        constructor; [ | constructor ].
        apply conv_Stop.
      * rewrite (force_enum_eq (map _ _)); simpl.
        fold (tails (prepend ps Stop)).
        fold (map (fun ry' => conv ry' (finite_empty::repeat finite_empty (length ps) ++ finite_empty :: ys))
                  (tails (prepend ps Stop))).
        constructor.
        { eapply FiniteEq_trans.
          - rewrite (eq_refl : Cons p (prepend ps Stop) = prepend (p::ps) Stop).
            rewrite (List.app_comm_cons).
            rewrite (eq_refl : @finite_empty B :: repeat finite_empty (length (ps)) =
                               repeat finite_empty (length (p::ps))).
            eapply conv_prepend_empty.
          - apply conv_Stop. }
        { rewrite (List.app_comm_cons).
          rewrite repeat_comm.
          rewrite <- (List.app_assoc).
          simpl.
          apply IH. }
Qed.
  
Lemma prod_spec_nth {A B: Type}:
  forall (xs: Enumeration (Finite A)) (ys: Enumeration (Finite B)),
    ObservableEq (prod xs ys) (map (conv xs) (reversals (app ys (forever finite_empty)))).
Proof.
  unfold prod.
  unfold prod'.
  intros xs ys.
  destruct xs as [ x xs | ].
  - destruct ys as [ y ys | ].
    + rewrite (force_enum_eq (app _ _)).
      simpl.
      fold (forever (@finite_empty B)).
      fold (app ys (forever finite_empty)).
      rewrite (force_enum_eq (reversals (Cons _ _))).
      simpl.
      assert (revs_eq: Forall2 FiniteEq [y] [finite_app y finite_empty]).
      { constructor; [ | constructor ].
        exists (eq_sym (N.add_0_r _)).
        destruct y as [ cy idxy ].
        simpl.
        intros k p.
        destruct (lt_dec k cy).
        - apply f_equal; apply UNLT.
        - match goal with [|- _ = False_rect _ ?devil] => exact (False_ind _ devil) end. }
      match goal with
      |[|- ObservableEq ?lhs ?rhs ] =>
       rewrite (force_enum_eq lhs); rewrite (force_enum_eq rhs); simpl
      end.
      constructor.
      * apply finite_conv_eq; assumption.
      * match goal with
        |[|- ObservableEq (match match ys with
                                | Cons _ _ => Cons _ (?f _ _)
                                | _ => _ end with
                          | _ => _ end) _ ] =>
         set (P := fun xs ys => f xs ys)
        end.
        match goal with
        |[|- ObservableEq (match ?r with | _ => _ end) _ ] =>
         assert (eq: r = P [y] ys); [ rewrite (force_enum_eq (P _ _)); destruct ys; reflexivity | ];
           rewrite eq; clear eq
        end.
        revert revs_eq.
        generalize [y] [finite_app y finite_empty].
        clear y.
        revert ys.
        cofix prod_spec_nth.
        intros ys rys rys' revs_eq.
        destruct ys as [ y ys | ].
        { simpl.
          match goal with
          |[|- ObservableEq ?lhs ?rhs ] =>
           rewrite (force_enum_eq lhs); rewrite (force_enum_eq rhs); simpl
          end.
          constructor.
          - apply finite_conv_eq.
            constructor; [ | assumption ].
            apply FiniteEq_sym.
            apply finite_app_empty_r.
            apply FiniteEq_refl.
          - apply prod_spec_nth.
            constructor; [  | assumption ].
            apply FiniteEq_sym.
            apply finite_app_empty_r.
            apply FiniteEq_refl. }
        { simpl.
          fold (map (conv (Cons x xs)) (P rys' (app Stop (forever finite_empty)))).
          rewrite (force_enum_eq (app Stop _)).
          simpl.
          fold (forever (@finite_empty B)).
          assert (eq: forever (@finite_empty B) = Cons finite_empty (forever finite_empty)).
          { rewrite (force_enum_eq (forever (@finite_empty B))) at 1.
            reflexivity. }
          rewrite <- eq; clear eq.
          assert (eq: ObservableEq
                    (map (fun ry' => conv ry' rys) (tails xs))
                    (map (fun ry' => conv ry' (finite_empty :: rys)) (tails (Cons x xs)))).
          { clear ...
            fold ([finite_empty] ++ rys).
            fold (repeat (@finite_empty B) 1).
            rewrite (eq_refl : Cons x xs = prepend [x] xs).
            apply (map_conv_empty_prefix [x]). }
          eapply (ObservableEq_trans); [ exact eq | ]; clear eq.
          revert revs_eq.
          clear ...
          generalize (Cons x xs).
          clear x xs.
          intros xs.
          rewrite (force_enum_eq (map (conv xs) _)).
          simpl.
          fold (forever (@finite_empty B)).
          fold (P (finite_empty::rys') (forever (@finite_empty B))).
          fold (map (conv xs) (P (finite_empty::rys') (forever (@finite_empty B)))).
          intro revs_eq.
          assert (revs_eq': Forall2 FiniteEq (finite_empty::rys) (finite_empty::rys')).
          { constructor; [ apply FiniteEq_refl | assumption ]. }
          revert revs_eq'.
          clear revs_eq.
          generalize (finite_empty :: rys').
          generalize (finite_empty :: rys).
          clear rys rys'.
          intros rys rys' revs_eq.
          match goal with
          |[|- ObservableEq ?lhs' ?rhs' ] =>
           remember lhs' as lhs eqn:lhs_eq';
             assert (lhs_eq: ObservableEq lhs' lhs); [ rewrite lhs_eq'; apply ObservableEq_refl | ];
               rewrite lhs_eq';
               apply (ObservableEq_trans lhs' lhs rhs' lhs_eq);
               clear lhs_eq'; revert lhs lhs_eq
          end.
          revert xs rys rys' revs_eq.
          cofix prod_spec_nth.
          intros xs rys rys' revs_eq.
          rewrite (force_enum_eq (map _ (tails _))); simpl.
          destruct xs as [ x xs | ].
          - fold (tails xs).
            fold (map (fun ry' => conv ry' rys) (tails xs)).
            rewrite (force_enum_eq (map (conv (Cons _ _)) _)); simpl.
            fold (forever (@finite_empty B)).
            fold (P (finite_empty :: rys') (forever (@finite_empty B))).
            fold (map (conv (Cons x xs)) (P (finite_empty :: rys') (forever (@finite_empty B)))).
            rewrite (eq_refl: Cons x xs = prepend [x] xs).
            rewrite (eq_refl: finite_empty :: rys' = (repeat finite_empty (length [x])) ++ rys').
            intros lhs lhs_eq.
            
            destruct lhs.
            + constructor.
              * inversion lhs_eq.
                apply FiniteEq_sym.
                simpl prepend.
                eapply (FiniteEq_trans); [ | eassumption ].
                apply finite_conv_eq.
                apply (Forall2_comm _ _ _ FiniteEq_sym).
                assumption.
              * apply (prod_spec_nth _ (repeat finite_empty (length [x]) ++ rys)).
                { constructor; [ apply FiniteEq_refl | assumption ]. }
                inversion lhs_eq.
                eapply ObservableEq_trans; [ | eassumption ].
                apply ObservableEq_sym.
                apply (map_conv_empty_prefix).
            + constructor.
              * inversion lhs_eq.
                simpl prepend.
                eapply (FiniteEq_trans); [ | eassumption ].
                apply finite_conv_eq.
                apply (Forall2_comm _ _ _ FiniteEq_sym).
                assumption.
              * apply (prod_spec_nth _ (repeat finite_empty (length [x]) ++ rys)).
                { constructor; [ apply FiniteEq_refl | assumption ]. }
                inversion lhs_eq.
                eapply ObservableEq_trans; [ | eassumption ].
                apply ObservableEq_sym.
                apply (map_conv_empty_prefix).
          - intros lhs lhs_eq.
            eapply ObservableEq_trans; [ eapply ObservableEq_sym; eassumption | ].
            constructor.
            + apply finite_conv_eq; assumption.
            + rewrite (force_enum_eq (_ Stop)); simpl.
              apply ObservableEq_sym.
              apply map_conv_Stop. }
    + simpl.
      rewrite (force_enum_eq (app Stop _)); simpl.
      fold (forever (@finite_empty B)).
      assert (eq: Cons finite_empty (forever (@finite_empty B)) = forever (finite_empty)).
      { rewrite (force_enum_eq (forever finite_empty)) at 2.
        reflexivity. }
      rewrite eq; clear eq.
      apply ObservableEq_sym.
      generalize (Cons x xs).
      clear x xs.
      unfold reversals.
      assert (all_empty: Forall (FiniteEq finite_empty) (@nil (Finite B))); [ constructor | revert all_empty ].
      generalize (@nil (Finite B)).
      cofix prod_spec_nth.
      intros rys all_empty xs.
      rewrite (force_enum_eq (map _ _)).      
      constructor.
      * apply finite_empty_eq.
        destruct (conv_empty xs _ (Forall_cons _ (FiniteEq_refl _) all_empty)) as [ card_eq _ ].
        rewrite <- card_eq.
        reflexivity.
      * fold (forever (@finite_empty B)).
        match goal with
        |[|- ObservableEq (_ (?f ?x ?y)) _] =>
         fold (map (conv xs) (f x y))
        end.
        apply prod_spec_nth.
        constructor; [ apply FiniteEq_refl | assumption ].
  - apply ObservableEq_sym.
    apply map_conv_Stop.
Qed.

(* I'm here *)




Lemma prod_spec_nth {A B: Type}:
  forall n (xs: Enumeration (Finite A)) (ys: Enumeration (Finite B)),
    
    
    match nth_error n (prod xs ys), nth_error n (map (conv xs) (reversals (app ys (forever finite_empty)))) with
    | Some f1, Some f2 => FiniteEq f1 f2
    | None, None => True
    | Some x, None => FiniteEq x finite_empty
    | None, Some y => FiniteEq finite_empty y
    end.                     
Proof.
  intro n.
  unfold nth_error.
  unfold prod.
  unfold prod'.
  unfold map.
  unfold reversals.
  
  
  destruct ys as [ y ys | ].
  + unfold app.
    match goal with
    |[|- context [ ?f (Cons y ys) (forever finite_empty) ] ] =>
     rewrite (force_enum_eq (f (Cons y ys) (forever finite_empty)))
    end.
    simpl.
    match goal with
    |[|- context [ ?f (Cons (finite_app y finite_empty) ?r)] ] =>
     rewrite (force_enum_eq (f (Cons (finite_app y finite_empty) r)))
    end.
    simpl.
  
  induction n as [ | n IH ] using N.peano_ind;
    intros xs ys.
  - destruct xs as [ x xs | ]; destruct ys as [ y ys | ].
    + simpl.
      apply finite_conv_eq.
      constructor; [ | constructor ].
      exists (eq_sym (N.add_0_r (cardinality y))).
      destruct y as [ cy idxy ].
      simpl.
      intros k p.
      destruct (lt_dec k cy).
      * rewrite (UNLT p l).
        reflexivity.
      * match goal with |[|- _ = False_rect _ ?devil ] => exact (False_ind _ devil) end.
    + simpl.
      unfold conv.
      unfold conv_cardinality.
      simpl.
      exists (eq_sym (N.mul_0_r (cardinality x))).
      simpl.
      intros k p.
      apply (False_rect _ (N.nlt_0_r _ p)).
    + simpl.
      exists (eq_refl).
      intros k p.
      apply (False_rect _ (N.nlt_0_r _ p)).
    + simpl.
      exists (eq_refl).
      intros k p.
      apply (False_rect _ (N.nlt_0_r _ p)).
  - simpl.
    
    
    destruct xs as [ x xs | ]; destruct ys as [ y ys | ].
    + match goal with
      |[|- match hd (skip _ (_ _ ?rys)) with |_ => _ end] =>
       assert (rys_eq: rys = reversals (Cons y ys))
      end.
      * unfold reversals.
        rewrite (force_enum_eq).
        simpl.
      fold (Cons [y] (reversals ys)).
      unfold skip.
      rewrite (N.peano_rect_succ).
      
      eapply IH.



Definition nth_conv {A B: Type} n (xs: Enumeration (Finite A)) (ys: Enumeration (Finite B)):
  option (Finite (A * B)) :=
  N.recursion (match nth_error 0 xs, nth_error n ys with
               | Some x, Some y => Some (finite_app finite_empty (finite_prod x y))
               | _, _ => None
               end)
              (fun m r =>
                 match r, (match nth_error m xs, nth_error (n - m)%N ys with
                           | Some x, Some y => Some (finite_prod x y)
                           | _, _ => None
                           end) with
                 | Some x, Some y => Some (finite_app x y)
                 | Some x, _ => Some x
                 | None, Some y => Some y
                 | None, None => None
                 end) n.

Lemma peano_rect_ext:
  forall n P f g x,
    (forall n p, f n p = g n p) ->
    N.peano_rect P x f n = N.peano_rect P x g n.
Proof.
  intros n P f g x fg_eq.
  induction n as [ | n IH ] using N.peano_ind.
  - reflexivity.
  - do 2 rewrite (N.peano_rect_succ).
    rewrite IH.
    apply fg_eq.
Qed.    

Lemma nth_conv_Stop_ys {A B: Type}:
  forall n (xs: Enumeration (Finite A)),
    @nth_conv A B n xs Stop = None.
Proof.
  intros n.
  unfold nth_conv.
  unfold nth_error.
  rewrite (skip_Stop).
  simpl.
  induction n as [ | n IH ] using N.peano_ind;
    intro xs.
  - simpl; destruct (hd xs); reflexivity.
  - unfold N.recursion.
    rewrite (N.peano_rect_succ).
    unfold nth_error.
    rewrite (skip_Stop).
    simpl.
    match goal with
    |[|- match ?r with | _ => _ end = _] =>
     assert (r_eq: r = None); [ | rewrite r_eq ]
    end.
    + rewrite <- (IH xs) at 1.
      unfold N.recursion.
      match goal with
      |[|- N.peano_rect ?P ?x ?f ?m = N.peano_rect _ _ ?g _] =>
       apply (peano_rect_ext m P f g x)
      end.
      intros k p.
      repeat rewrite skip_Stop.
      reflexivity.
    + destruct (hd (skip n xs)); reflexivity.
Qed.

Lemma nth_conv_Stop_xs {A B: Type}:
  forall n (ys: Enumeration (Finite B)),
    @nth_conv A B n Stop ys = None.
Proof.
  intros n.
  unfold nth_conv.
  unfold nth_error.
  rewrite (skip_Stop).
  simpl. 
  induction n as [ | n IH ] using N.peano_ind;
    intro ys.
  - simpl; reflexivity.
  - unfold N.recursion.
    rewrite (N.peano_rect_succ).
    unfold nth_error.
    rewrite (skip_Stop).
    simpl.
    match goal with
    |[|- match ?r with | _ => _ end = _] =>
     assert (r_eq: r = None); [ | rewrite r_eq; reflexivity ]
    end.
    rewrite <- (IH ys) at 2.
    unfold N.recursion.
    match goal with
    |[|- N.peano_rect ?P ?x ?f ?m = N.peano_rect _ _ ?g _] =>
     apply (peano_rect_ext m P f g x)
    end.
    intros k p.
    repeat rewrite skip_Stop.
    reflexivity.
Qed.



Definition pad {A: Type} (n: N) (xs: list (Finite A)): list (Finite A) :=
  snd (N.peano_rect _ (xs, xs)
                    (fun _ s =>
                       match s with
                       | ([], r) => ([], finite_empty :: r)
                       | (x::xs, r) => (xs, r)
                       end) n).

Definition nth_reversals {A: Type} (n: N) (xs: Enumeration (Finite A)): list (Finite A) :=
  pad n (

Definition nth_conv_pad {A B: Type} (n: N) (xs: Enumeration (Finite A)) (ys: list (Finite B)):
  option (Finite (A * B)) :=
  match xs with 
  | Stop => None
  | Cons x xs => Some (conv (Cons x xs) (pad n ys))
  end.


Lemma nth_prod' {A B: Type}:
  forall n (xs: Enumeration (Finite A)) (yss: Enumeration (list (Finite B))),
    nth_error n (prod' xs yss) =
    match nth_error n yss with
    | Some ys => nth_conv_pad n xs ys
    | None => None
    end.
Proof.
  intro n.
  unfold prod'.
  unfold nth_error.
  destruct yss as [ ys yss | ];
    [ | destruct xs; repeat rewrite (skip_Stop); reflexivity ]. 
  revert xs ys yss.
  induction n as [ | n IH ] using N.peano_ind;
    intros xs ys yss.
  - do 2 rewrite (skip_zero).
    destruct xs as [ x xs | ]; reflexivity.
  - do 2 (rewrite skip_tl_succ).
    destruct xs as [ x xs | ].
    + simpl.
      destruct yss as [ ys' yss | ].
      * rewrite (IH (Cons x xs) ys').
        simpl.
        admit.
      * rewrite (skip_Stop); simpl.
        
      
      

Lemma prod_spec_nth {A: Type}:
  forall n (xs ys: Enumeration (Finite A)),
    nth_error n (prod xs ys) = nth_conv n xs ys.
Proof.
  intros n xs ys.
  destruct xs as [ x xs | ];
      destruct ys as [ y ys | ];
      try solve [ simpl;
                  unfold nth_error; rewrite skip_Stop;
                  rewrite nth_conv_Stop_xs || rewrite nth_conv_Stop_ys; reflexivity ].
  unfold prod.
  
  
  simpl.
  

  
  destruct xs; destruct ys
  
  intro n.
  induction n as [ | n IH ] using N.peano_ind.
  - intros xs ys.
    simpl.
    unfold nth_error.
    repeat rewrite skip_zero.
    unfold prod.
    unfold prod'.
    unfold reversals.
    destruct xs as [ x xs | ]; destruct ys as [ y ys | ];
      simpl; try solve [ reflexivity ].
    unfold conv.
    unfold conv_cardinality.
    simpl.
    unfold finite_prod.
    unfold finite_app.
    unfold finite_empty.
    simpl.
    apply f_equal.
    apply f_equal.
    rewrite (UIP_dec (N.eq_dec) (conv_cardinality_eq (Cons x xs) [y]) eq_refl).
    reflexivity.
  - intros xs ys.
    destruct xs as [ x xs | ];
      destruct ys as [ y ys | ];
      try solve [ simpl;
                  unfold nth_error; rewrite skip_Stop;
                  rewrite nth_conv_Stop_xs || rewrite nth_conv_Stop_ys; reflexivity ].
    generalize (N.succ n).
    clear ...
    intro n.
    unfold nth_conv.
    induction n as [ | n IH ] using N.peano_ind.
    + unfold nth_error.
      simpl.
      admit.
    + 
    
    unfold nth_error.
    rewrite (skip_tl_succ).
    generalize (IH xs ys).
    unfold nth_conv.
    unfold N.recursion.
    rewrite (N.peano_rect_succ).
    intro p.
    rewrite <- p.
    generalize (
    
  

Inductive Future {A: Type} (P : Enumeration A -> Prop): Enumeration A -> Prop :=
| Now: forall xs, P xs -> Future P xs
| Then: forall x xs,  Future P xs ->  Future P (Cons x xs).
Arguments Now {_} {_} _ _.
Arguments Then {_} {_} _ _ _.

CoInductive Always {A: Type} (P : Enumeration A -> Prop): Enumeration A -> Prop :=
| Ending: Always P Stop
| GoOn: forall x xs, P (Cons x xs) -> Always P xs -> Always P (Cons x xs).
Arguments Ending {_} {_}.
Arguments GoOn {_} {_} _ _ _ _.

Lemma Always_Cons {A: Type} {P: Enumeration A -> Prop}:
  forall (P': A -> Enumeration A -> Prop),
    (forall x xs, P (Cons x xs) -> Always P xs -> P' x xs) ->
    forall x xs, Always P (Cons x xs) -> P' x xs.
Proof.
  intros P' H x xs prf.
  remember (Cons x xs) as xxs eqn:xxs_eq.
  destruct prf.
  - inversion xxs_eq.
  - inversion xxs_eq as [ [ x_eq xs_eq ] ].
    rewrite x_eq in *.
    rewrite xs_eq in *.
    apply H; assumption.
Qed.
  
Definition NonEmptyHeadOrEnd {A: Type} (e: Enumeration (Finite A)): Prop :=
   match e with
   | Stop => True
   | Cons xs xss => (cardinality xs > 0%N)%N
   end.

Definition Productive {A: Type}: Enumeration (Finite A) -> Prop :=
  Always (Future NonEmptyHeadOrEnd).



Lemma NonEmptyHeadOrEmpty_not_empty_head {A: Type}:
  forall (x: Finite A) xs, NonEmptyHeadOrEnd (Cons x xs) -> (cardinality x <= 0%N)%N -> False.
Proof.
  intros x xs prf devil.
  simpl in prf.
  generalize (N.lt_le_trans _ _ _ (N.gt_lt _ _ prf) devil).
  apply N.nlt_0_r.
Qed.

Definition Future_inv {A: Type} {P: Enumeration A -> Prop}:
  forall x xs, Future P (Cons x xs) -> (P (Cons x xs) -> False) -> Future P xs :=
  fun x xs f =>
    match f in Future _ xs'
          return (P xs' -> False) -> Future P (match xs' with
                                         | Stop => Stop
                                         | Cons _ xs => xs end) with
    | Now _ p => fun not_p => match (not_p p) with end
    | Then _ _ f' => fun _ => f'
    end.

Definition skipToNext {A: Type}
           (e: Enumeration (Finite A))
           (hasNext: Future NonEmptyHeadOrEnd e)
           (productive: Productive e) (size: N):
  (option (N * (Finite A))) * { e: Enumeration (Finite A) | Productive e } :=
  (fix skipToNext_rec (e: Enumeration (Finite A)) (hasNext: Future NonEmptyHeadOrEnd e):
     Productive e -> N -> (option (N * (Finite A))) * { e: Enumeration (Finite A) | Productive e } :=
     match e with
     | Stop => fun _ _ _ => (None, exist _ Stop Ending)
     | Cons x xs =>
       fun (hn: Future NonEmptyHeadOrEnd (Cons x xs)) p size =>
         match (lt_dec 0 (cardinality x)) with
         | left _ => (Some (size, x),
                     exist _ xs (Always_Cons (fun _ xs => Productive xs)
                                             (fun x xs _ p => p) x xs p))
         | right is_geq =>
           skipToNext_rec xs
                          (Future_inv _ _ hn (fun devil => NonEmptyHeadOrEmpty_not_empty_head _ _ devil is_geq))
                          (Always_Cons (fun _ xs => Productive xs)
                                       (fun x xs _ p => p) x xs p)
                          (N.succ size)
         end
     end hasNext) e hasNext productive size.

Definition values {A: Type} (e: Enumeration (Finite A)) (p: Productive e): Enumeration (N * (Finite A)) :=
  (cofix go (e: Enumeration (Finite A)): N -> Productive e -> Enumeration (N * (Finite A)) :=
     match e with
     | Stop => fun _ _ => Stop
     | Cons x xs =>
       fun size p =>
         let (hd, r) := skipToNext (Cons x xs)
                                   (Always_Cons (fun x xs => Future NonEmptyHeadOrEnd (Cons x xs))
                                                (fun x xs hasNext _ => hasNext) x xs p) p size in
         match hd with
         | None => Stop
         | Some (size', f) =>
           Cons (size', f) (go (proj1_sig r) (N.succ size') (proj2_sig r))
         end
     end) e 0%N p.


Lemma skipToNext_nonempty {A: Type}:
  forall (e: Enumeration (Finite A)) hasNext p size size' f,
    fst (skipToNext e hasNext p size) = Some (size', f) ->
    (cardinality f > 0%N)%N.
Proof.
  fix skipToNext_nonempty_rec 2.
  intros e hasNext.
  case hasNext as [ xs prf | f' xs thenprf ].
  - case xs as [ f' xs | ].
    + simpl in *.
      destruct (lt_dec 0 (cardinality f'));
        simpl; intros p size size' f eq.
      * inversion eq as [ [ size_eq f_eq ] ].
        rewrite <- f_eq.
        apply (N.lt_gt).
        assumption.
      * apply False_ind.
        apply (NonEmptyHeadOrEmpty_not_empty_head f' xs prf l).
    + intros p size size' f eq.
      inversion eq.
  - simpl in *.
    destruct (lt_dec 0 (cardinality f'));
      simpl; intros p size size' f eq.
    + inversion eq as [ [ size_eq f_eq ] ].
      rewrite <- f_eq.
      apply (N.lt_gt).
      assumption.
    + eapply skipToNext_nonempty_rec.
      exact eq.
Qed.

Lemma skipToNext_empty {A: Type}:
  forall (e: Enumeration (Finite A)) hasNext p size,
    fst (skipToNext e hasNext p size) = None ->
    proj1_sig (snd (skipToNext e hasNext p size)) = Stop.
Proof.
  fix skipToNext_nonempty_rec 2.
  intros e hasNext.
  case hasNext as [ xs prf | f' xs thenprf ].
  - case xs as [ f' xs | ].
    + simpl in *.
      destruct (lt_dec 0 (cardinality f'));
        simpl; intros p size eq.
      * inversion eq.
      * apply False_ind.
        apply (NonEmptyHeadOrEmpty_not_empty_head f' xs prf l).
    + intros p size eq.
      reflexivity.
  - simpl in *.
    destruct (lt_dec 0 (cardinality f'));
      simpl; intros p size eq.
    + inversion eq.
    + eapply skipToNext_nonempty_rec.
      exact eq.
Qed.

Lemma values_nonempty {A: Type}:
  forall (e: Enumeration (Finite A)) p,
    Always (NonEmptyHeadOrEnd) (map snd (values e p)).
Proof.
  unfold values.
  generalize 0%N.
  cofix values_nonempty.
  intros n e.
  destruct e as [ x xs | ];
    intro p.
  - match goal with
    |[|- Always _ (map snd ?xs)] =>
     rewrite (force_enum_eq xs)
    end.
    simpl.
    match goal with
    |[|- Always _ (map _ match (let (_, _) := skipToNext ?e ?hasNext ?p' ?size 
                               in _) with
                        | _ => _
                        end)] =>
     generalize (skipToNext_nonempty e hasNext p' size);
       generalize (skipToNext_empty e hasNext p' size);
       destruct (skipToNext e hasNext p' size) as [ [ [f' size'] | ] rest ]
    end.
    + rewrite (force_enum_eq (map snd _)).
      simpl.
      intros pstop phd.
      constructor.
      * apply (phd _ _ eq_refl).
      * apply values_nonempty.
    + intros.
      rewrite (force_enum_eq (map snd _)).
      simpl.
      constructor.
  - rewrite (force_enum_eq (map snd _)).
    simpl.
    constructor.
Qed.

Definition nth_error {A: Type} (e: Enumeration (Finite A)) (is_productive: Productive e) (n: N): option A :=
  @N.peano_rect
    (fun _ => N -> Enumeration (Finite A) -> option A)
    (fun _ _ => None)
    (fun fuel' nth_error_rec => fun n xs =>
       match xs with
       | Cons x xs =>
         match lt_dec n (cardinality x) with
         | left is_lt => Some (index x n is_lt)
         | right _ => nth_error_rec (n - cardinality x)%N xs
         end
       | Stop => None
       end) n n (map snd (values e is_productive)).


Lemma productive_singleton {A: Type}: forall (x: A), Productive (singleton x).
Proof.
  intro x; repeat constructor.
Qed.

Lemma productive_app {A: Type}:
  forall (xs ys: Enumeration (Finite A)), Productive xs -> Productive ys -> Productive (app xs ys).
Proof.
  cofix productive_app.
  intros xs.
  destruct xs as [ x xs | ].
  - intro ys.
    destruct ys as [ y ys | ].
    + intros p1 p2.
      inversion p1 as [ | x' xs' future_xs productive_xs ].
      inversion p2 as [ | y' ys' future_ys productive_ys ].
      rewrite (force_enum_eq (app (Cons x xs) (Cons y ys))).
      simpl.
      constructor.
      * revert future_xs future_ys.
        clear...
        generalize (force_enum_eq (app (Cons x xs) (Cons y ys))).
        simpl.
        intro force_eq; rewrite <- force_eq; clear force_eq.
        generalize (Cons x xs); clear x xs.
        intros xs future_xs.
        generalize (Cons y ys); clear y ys.
        induction future_xs as [ f nowprf | f xs' thenprf IH ];
          intros ys future_ys.
        { destruct f as [ x xs | ].
          - rewrite (force_enum_eq (app _ _)).
            constructor.
            simpl.
            simpl in nowprf.
            destruct ys.
            + simpl.
              apply (N.lt_gt).
              apply (N.add_pos_l).
              apply (N.gt_lt).
              assumption.
            + assumption.
          - rewrite (force_enum_eq (app _ _)).
            simpl.
            destruct ys; assumption. }
        { destruct future_ys as [ g nowprf | g ys' thenprf' ];
            rewrite (force_enum_eq (app _ _)).
          - destruct g.
            + simpl.
              apply Now.
              apply (N.lt_gt).
              apply (N.add_pos_r).
              apply (N.gt_lt).
              assumption.
            + simpl.
              apply Then.
              assumption.
          - apply Then.
            apply (IH ys' thenprf'). }
      * apply (productive_app _ _ productive_xs productive_ys).
    + intros p1 p2.
      rewrite (force_enum_eq (app (Cons x xs) Stop)).
      simpl.
      assumption.
  - intros ys p1 p2.
    rewrite (force_enum_eq (app Stop ys)).
    simpl.
    destruct ys; assumption.
Qed.


(*CoInductive enum_eq {A: Type}: forall (xs ys: Enumeration A), Prop :=
| enum_eq_stop: enum_eq Stop Stop
| enum_eq_cons: forall x y xs ys, x = y -> enum_eq xs ys -> enum_eq (Cons x xs) (Cons y ys).

Lemma enum_eq_refl {A: Type}: forall (xs: Enumeration A), enum_eq xs xs.
Proof.
  cofix enum_eq_refl.
  intro xs.
  destruct xs as [ x xs | ].
  - constructor; [ reflexivity | apply enum_eq_refl ].
  - constructor.
Qed.

Lemma enum_eq_sym {A: Type}: forall (xs ys: Enumeration A), enum_eq xs ys -> enum_eq ys xs.
Proof.
  cofix enum_eq_sym.
  intros xs ys prf.
  destruct prf.
  - constructor.
  - constructor; [ apply eq_sym; assumption | apply enum_eq_sym; assumption ].
Qed.

Lemma enum_eq_trans {A: Type}: forall (xs ys zs: Enumeration A), enum_eq xs ys -> enum_eq ys zs -> enum_eq xs zs.
Proof.
  cofix enum_eq_trans.
  intros xs ys zs p1.
  inversion p1;
    intro p2;
    inversion p2;
    constructor.
  - etransitivity; eassumption.
  - eapply enum_eq_trans; eassumption.
Qed.  

Lemma prod'_map_eq {A B: Type}:
  forall (xs: Enumeration (Finite A))
    (yss: Enumeration (list (Finite B))),
    enum_eq (prod' xs yss) (map (conv xs) yss).
Proof.
  unfold prod'.
  unfold map.
  intros xs yss.
  destruct xs as [ x xs | ].
  - revert yss.
    cofix prod'_map_eq.
    intros yss.
    rewrite (force_enum_eq _).
    destruct yss as [ ys yss | ].
    + rewrite (force_enum_eq (_ (Cons ys yss))).
      simpl.
      constructor.
      * reflexivity.
      *
      destruct yss.
      * constructor; [ reflexivity | auto ].
      * constructor; [ reflexivity | ].
        exact 
        
        
      constructor.
      * reflexivity.
      * prod'_map_eq.
        
      
*)      

Definition NonEmptyHeadList {A: Type} (e: Enumeration (list (Finite A))): Prop :=
   match e with
   | Cons xs xss => Exists (fun f => cardinality f > 0%N)%N xs
   | _ => False
   end.

Lemma productive_reversals {A: Type}:
  forall (xs: Enumeration (Finite A)),
    Future NonEmptyHeadOrEnd xs -> Future (Always NonEmptyHeadList) (reversals xs).
Proof.
  unfold reversals.
  intros xs prf.
  generalize (@nil (Finite A)).
  induction prf as [ xs nowprf | x xs thenprf IH ].
  - left.
    unfold NonEmptyHeadOrEnd in nowprf.
    destruct xs as [ x xs | ].
    + rewrite (force_enum_eq (_ (Cons _ xs))).
      simpl.
      assert (inprf: List.In x (x :: l)); [ left; reflexivity | ].
      revert inprf.      
      generalize (x::l).
      clear l.
      revert xs.
      cofix nonempty.
      intros xs rec inprf.
      constructor.
      * simpl.
        apply Exists_exists.
        eexists; split; eassumption.
      * destruct xs as [ x' xs | ].
        { rewrite force_enum_eq.
          simpl.
          apply nonempty.
          right; assumption. }
        { rewrite force_enum_eq; constructor. }
    + rewrite force_enum_eq; constructor.
  - intro l.
    rewrite force_enum_eq.
    right.
    apply IH.
Qed.

(*Definition InEnumeration {A: Type} (x: A) (xs: Enumeration (Finite A)): Prop :=
  Future (fun s => match s with
                | Stop => False
                | Cons f xs => exists n (prf: (n < cardinality f)%N), index f n prf = x
                end) xs.

Lemma in_reversals {A: Type}:
  forall (x: A) xs, InEnumeration x xs ->
               Always (Future (fun s => match s with
                                     | Stop => False
                                     | Cons xs xxs =>
                                       Exists (fun f => exists n (prf: (n < cardinality f)%N), index f n prf = x) xs
                                     end)) (reversals xs).
Proof.
  intros x.
  intros xs inprf.
  induction inprf as [ xs nowprf | x' xs thenprf IH ].
  - unfold reversals.
    generalize (@nil (Finite A)).
    revert xs nowprf.
    cofix prf.
    intros xs nowprf rev.
    destruct xs as [ x' xs | ].
    + rewrite (force_enum_eq _).
      constructor.
      * left; left; assumption.
      * destruct xs.
        { apply prf.
          assumption.
        
  


Lemma in_prod {A B: Type}:
  forall (x: A) (xs: Enumeration (Finite A)),
    InEnumeration x xs ->
    forall (y: B) (ys: Enumeration (Finite B)),
      InEnumeration y ys -> InEnumeration (x, y) (prod xs ys).
Proof.
  unfold prod.
  unfold prod'.
  
  intros x xs
*)

Lemma conv_empty {A B: Type}:
  forall (ys: list (Finite B)), conv (@Stop (Finite A)) ys = finite_empty.
Proof.
  intros ys.
  induction ys as [ | y ys IH ].
  - unfold conv.
    simpl.
    unfold finite_empty.
    rewrite (UIP_dec (N.eq_dec) (conv_cardinality_eq Stop []) eq_refl).
    reflexivity.
  - unfold conv in *.
    simpl.
    rewrite (UIP_dec (N.eq_dec) (conv_cardinality_eq Stop (y::ys)) (conv_cardinality_eq Stop ys)).
    assumption.
Qed.

 

Lemma productive_goY {A B: Type}:
  forall (x: Finite A) xs (yr: list (Finite B)) yrs ,
    Future NonEmptyHeadOrEnd (Cons x xs) ->
    Always (Future NonEmptyHeadOrEnd) xs ->
    Exists (fun f => (cardinality f > 0)%N) yr ->
    Always NonEmptyHeadList (Cons yr yrs) ->
    Future NonEmptyHeadOrEnd
           (Cons (conv (Cons x xs) yr)
                 ((cofix goY (ry : list (Finite B)) (rys : Enumeration (list (Finite B))):
                     Enumeration (Finite (A * B)) :=
                     Cons (conv (Cons x xs) ry)
                          match rys with
                          | Cons ry' rys' => goY ry' rys'
                          | Stop => map (fun ry' : Enumeration (Finite A) => conv ry' ry) (tails xs)
                          end) yr yrs)).
Proof.
  intros x xs yr yrs.
  remember (Cons x xs) as xxs eqn:xxs_eq.
  assert (tails_eq: tails xs = match xxs with | Cons x xs => tails xs | _ => Stop end);
    [ rewrite xxs_eq; reflexivity | ].
  rewrite tails_eq.
  intros future_xxs productive_xs.
  assert (productive_tlxxs: match xxs with | Cons x xs => Productive xs | Stop => False end);
    [ rewrite xxs_eq; assumption | ].
  clear productive_xs.
  revert yr yrs productive_tlxxs.
  clear x xs xxs_eq tails_eq.
  induction future_xxs as [ xxs nowprf | x' xs' thenprf IH ].
  - intros yr yrs productive_tlxxs  productive_yr.
    destruct xxs as [ x xs | ]; [ | contradiction ].
    revert productive_tlxxs. (* FIXME: Cons in lemma definition is too much *)
    match goal with
    |[|- _ -> _ -> Future _ (Cons _ (?f _ _))] =>
     match goal with
     |[|- _ -> _ -> Future _ ?g] =>
      assert (fold_go: g = f yr yrs)
     end
    end.
    { 
    
    induction productive_yr as [ yr_hd yr_tl yr_hd_nonempty | yr_hd yr_tl yr_tl_productive IH ].
    + intros.
      left.
      simpl.
      unfold conv_cardinality.
      simpl.
      apply conv_cardinality_monotonic.
      apply (N.lt_gt).
      apply (N.mul_pos_pos); apply (N.gt_lt); assumption.
    + intros yrs productive_xs productive_yryrs.
      right.
      apply I
    
    
    
  
(*    ys : Enumeration (list (Finite A))
  productive_yrs : Always NonEmptyHeadList ys
  yr, yr' : list (Finite A)
  yrs' : Enumeration (list (Finite A))
  yr_nonempty : Exists (fun f : Finite A => (cardinality f > 0)%N) yr
  productive_yrs' : Always NonEmptyHeadList (Cons yr' yrs')
  yr_eq : Cons yr (Cons yr' yrs') = ys
  x : Finite A
  xs : Enumeration (Finite A)
  future_xxs : Future NonEmptyHeadOrEnd (Cons x xs)
  productive_xs : Always (Future NonEmptyHeadOrEnd) xs
                         ============================

                         
  -> Future NonEmptyHeadOrEnd
           (Cons (conv (Cons x xs) yr)
                 ((cofix goY (ry : list (Finite A)) (rys : Enumeration (list (Finite A))) : Enumeration (Finite (A * A)) :=
                     Cons (conv (Cons x xs) ry)
                          match rys with
                          | Cons ry' rys' => goY ry' rys'
                          | Stop => map (fun ry' : Enumeration (Finite A) => conv ry' ry) (tails xs)
                          end) yr' yrs'))*)



(*Proof.
  intros A B.
  unfold conv.
  unfold conv_cardinality.
  simpl.
  intros x xs ys.
  revert x xs.
  generalize (0%N) at 2.
  induction ys as [ | y ys IH ].
  - intros ? ? ? ? devil; inversion devil.
  - intros n x xs future_xs ex_prf.
    inversion ex_prf as [ y' ys' here [ p p' ] | y' ys' there [ p p' ] ];
      clear y' ys' p p' ex_prf.
    + simpl.
      destruct future_xs.
      * 
    + simpl.
      inversion future_xs as [ xs' nowprf [ p ] | x' xs' thenprf [ p p' ] ];
        [ clear xs' p | clear future_xs x' xs' p p'].
      * simpl.
        admit.
      * destruct thenprf.*)
        
    

Lemma productive_prod {A B: Type}:
  forall (xs: Enumeration (Finite A)) (ys: Enumeration (Finite B)),
    Productive xs -> Productive ys -> Productive (prod xs ys).
Proof.
  intros xs.
  destruct xs as [ x xs | ].
  - intro ys.
    destruct ys as [ y ys | ].
    + intros p1 p2.
      unfold prod in *.
      unfold prod' in *.
      inversion p1 as [ | x' xs' future_x productive_xs [x'_eq xs'_eq] ].
      clear p1 x'_eq xs'_eq.
      revert x xs future_x productive_xs.
      inversion p2 as [ | y' ys' future_y productive_ys [y'_eq ys'_eq] ].
      generalize (productive_reversals _ future_y).
      generalize (reversals (Cons y ys)).
      clear ...
      intros yrs yrs_productive.
      induction yrs_productive as [ yrs nowprf | yr yrs thenprf IH ].
      * revert yrs nowprf.
        cofix productive_prod'.
        intros ys productive_yrs.
        inversion productive_yrs as [ | yr yrs yr_nonempty productive_yrs' [yr_eq yrs_eq] ];
          [ intros; constructor | ].
        intros x xs future_xxs productive_xs.
        destruct yrs as [ yr' yrs' | ].
        { rewrite force_enum_eq; simpl.
          constructor.
          - simpl in yr_nonempty.
            unfold conv.
            admit.
          - apply (productive_prod' (Cons yr' yrs') productive_yrs' x xs future_xxs productive_xs). }
        { rewrite force_enum_eq; simpl.
          admit. }        
      * intros x xs future_xxs productive_xs.
        generalize (IH _ _ future_xxs productive_xs).
        intro productive_rs.
        inversion productive_rs as [ rs_eq   | r rs' future_rrs productive_rs' [r_eq rs_eq] ].
        { destruct yrs as [ yr' yrs | ].
          - rewrite force_enum_eq in rs_eq; simpl in rs_eq.
            inversion rs_eq.
          - rewrite force_enum_eq; simpl.
            admit. }
        { destruct yrs as [ yr' yrs | ].
          - rewrite force_enum_eq; simpl.
            right; [ | assumption ].
            rewrite r_eq in future_rrs.
            right; assumption.
          - inversion r_eq. }
    + intros; constructor.
  - intros; constructor.
      
(*      
      destruct rys as [ yr yrs | ].
      * intro 

        revert yr yrs.
        
        
        cofix goY_prod.
        intros yr yrs yrs_productive x xs future_xxs productive_xs.
        rewrite (force_enum_eq _); simpl.
        constructor.
        { inversion yrs_productive as [ | y' ys' future_yryrs productive_yrs [y'_eq ys'_eq] ].
          clear rys_productive y'_eq ys'_eq productive_yrs.
          match goal with
          |[|- Future _ (Cons _ (match _ with | Cons _ _ => ?f _ _ | _ => _ end)) ] =>
           set (go' := fun xs => match xs with | Cons yr' yrs' => f yr' yrs' | Stop => Stop end);
             match goal with
             |[|- Future _ ?rhs] =>
              assert (eq: go' (Cons yr yrs) = rhs);
                [ exact (force_enum_eq (go' (Cons yr yrs))) | ];
                simpl; rewrite <- eq; clear eq
             end
          end.
          revert future_yryrs x xs go' future_xxs productive_xs.
          clear ...
          generalize (Cons yr yrs).
          clear yr yrs.
          intros yryrs future_yryrs.
          induction future_yryrs as [ yryrs nowprf | yr' yrs' thenprf IH ];
            intros x xs go' future_xxs productive_xs.
          - destruct yryrs as [ yr yrs | ]; [ | constructor; trivial ].
            unfold go'.
            rewrite (force_enum_eq _); simpl.
            simpl in nowprf.
            left; apply productive_conv; assumption.
          - unfold go'.
            rewrite (force_enum_eq _); simpl.
            right.
            generalize (IH _ _ future_xxs productive_xs).
            destruct yrs' as [ yr'' yrs' | ].
            + intro; assumption.
            + intros _.
              admit. }
        { inversion rys_productive as [ | y' ys' future_yryrs productive_yrs [y'_eq ys'_eq] ].
          destruct yrs as [ yr' yrs' | ].
          - exact (goY_prod yr' yrs' productive_yrs x xs future_xxs productive_xs).
          - Guarded.
      * constructor.
    + intros; constructor.
  - intros; constructor.*)
Qed.