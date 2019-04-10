From mathcomp Require Import all_ssreflect.
Require Import PreOrders.
Require Import Types.
Require Import Cover.
Require Import FCL.
Require Import DependentFixpoint.

Set Bullet Behavior "Strict Subproofs".

Delimit Scope it_scope with IT.
Open Scope it_scope.

Delimit Scope alg_scope with ALG.
Open Scope alg_scope.

Import EqNotations.

Notation "[ 'sort' c <= d ]" := (lessOrEqual c d) (at level 0, c at next level): alg_scope.

Module SignatureFamily.
  Record mixin_of (I: Type) (S: preOrdered) (O: finType): Type :=
    Mixin {
        arity: I -> O -> nat;
        dom: forall i o, (arity i o).-tuple S;
        range: I -> O -> S;
      }.
  Section ClassDef.
    Structure class_of (I: Type) (S: Type) (O: Type) :=
      Class {
          sort_base: PreOrdered.class_of S;
          operation_base: Finite.class_of O;  
          mixin: mixin_of I
                   (PreOrdered.Pack S sort_base)
                   (@Finite.Pack O operation_base)
        }.
    Local Coercion operation_base : class_of >-> Finite.class_of.
    Local Coercion sort_base : class_of >-> PreOrdered.class_of.
    Structure type I := Pack { sort_sort : Type; operation_sort: Type; _ : class_of I sort_sort operation_sort }.
    Variables (I: Type) (S: Type) (O: Type) (sigFam: type I).
    Definition class := let: Pack _ _ c as sigFam' := sigFam return class_of I
                                                                             (sort_sort I sigFam')
                                                                             (operation_sort I sigFam')
                        in c.
    Definition clone c of phant_id class c := @Pack S O c.
    Let xSort := (let: Pack S _ _ := sigFam in S).
    Let xOperation := (let: Pack _ O _ := sigFam in O).
    Notation xclass := (class : class_of I xSort xOperation).
    Definition pack b0 b1 (m0: mixin_of I (PreOrdered.Pack S b1) (@Finite.Pack O b0)) :=
      fun bSort bsort & phant_id (PreOrdered.class bSort) bsort =>
        fun bOperation boperation & phant_id (Finite.class bOperation) boperation =>
          fun m & phant_id m0 m => Pack I S O (@Class I S O bsort boperation m).

    Definition operationEqType := Eval hnf in @Equality.Pack xOperation xclass.
    Definition operationChoiceType := Eval hnf in  @Choice.Pack xOperation xclass.
    Definition operationCountType := Eval hnf in  @Countable.Pack xOperation xclass.
    Definition finType := Eval hnf in  @Finite.Pack xOperation xclass.

    Definition sortEqType := Eval hnf in @Equality.Pack xSort (PreOrdered.base _ xclass).
    Definition ctorCountType := Eval hnf in @Countable.Pack xSort (PreOrdered.base _ xclass).
    Definition preOrdered := Eval hnf in  @PreOrdered.Pack xSort xclass.
  End ClassDef.

  Module Import Exports.
    Coercion mixin: class_of >-> mixin_of.
    Coercion preOrdered : type >-> PreOrdered.type.
    Canonical preOrdered.
    Coercion finType: type >-> Finite.type.
    Canonical finType.

    Notation sigFam := type.
    Notation SignatureFamilyMixin := Mixin.
    Notation SignatureFamilyType I S O m := (@pack I S O _ _ m _ _ id _ _ id m id).
    Notation "[ 'sigFam' I 'of' S ',' O 'for' sigFam ]" :=
      (@clone I S O sigFam _ idfun)
        (at level 0, format "[ 'sigFam' I 'of' S ',' O 'for' sigFam ]") : form_scope.
    Notation "[ 'sigFam' I 'of' S ',' O ]" :=
      (@clone I S O _ _ id) (at level 0, format "[ 'sigFam' I 'of' S ',' O ]") : form_scope.
  End Exports.
End SignatureFamily.

Export SignatureFamily.Exports.

Definition sort {I: Type} (Sigma: sigFam I): preOrdered :=
  SignatureFamily.preOrdered I Sigma.
Definition operation {I: Type} (Sigma: sigFam I): finType :=
  SignatureFamily.finType I (Sigma).
Definition arity {I: Type} (Sigma: sigFam I): I -> operation Sigma -> nat :=
  SignatureFamily.arity _ _ _ (SignatureFamily.class I Sigma).
Definition dom {I: Type} (Sigma: sigFam I): forall (i: I) (o: operation Sigma), (arity Sigma i o).-tuple (sort Sigma) :=
  SignatureFamily.dom _ _ _ (SignatureFamily.class I Sigma).
Definition range {I: Type} (Sigma: sigFam I): I -> operation Sigma -> (sort Sigma) :=
  SignatureFamily.range _ _ _ (SignatureFamily.class I Sigma).


Definition sigFamSpec_Mixin {I: Type} {S: preOrdered} {O: finType} (spec: I -> O -> (seq S * S)):
  SignatureFamily.mixin_of
    I (PreOrdered.Pack S (PreOrdered.class S))
    (Finite.Pack (Finite.class O)).
Proof.
  move: spec.
  case: O => T1 o.
  case: S => S c.
  move => spec.
  by exact: (@SignatureFamily.Mixin
               I (PreOrdered.Pack S c) (Finite.Pack o)
               (fun i o => seq.size (spec i o).1)
               (fun i o =>
                  let res := (spec i o).1 in
                  @Tuple (seq.size res) S res (eq_refl _))
               (fun i o => (spec i o).2)).
Defined.

Definition SigSpec I S O : Type := I -> O -> (seq S * S).
Definition sigFamSpec_Type {I: Type} {S: preOrdered} {O: finType} (spec: SigSpec I S O) :=
  Eval hnf in SignatureFamilyType I S O (sigFamSpec_Mixin spec).

Record F {I: Type} (Sigma: sigFam I) (C: (sort Sigma) -> Type) (s: sort Sigma): Type :=
    mkF {
        index: I;
        op: operation Sigma;
        args: {ffun forall n, C (tnth (dom Sigma index op) n) };
        range_cond: [sort (range Sigma index op) <= s]
      }.

Arguments mkF [I] [Sigma] [C] [s].
Arguments index [I] [Sigma] [C] [s].
Arguments op [I] [Sigma] [C] [s].
Arguments args [I] [Sigma] [C] [s].
Arguments range_cond [I] [Sigma] [C] [s].


Section SignatureFunctor.
  Variable I : Type.
  Variable Sigma: sigFam I.
  Variable C D: (sort Sigma) -> Type.
  Definition fmap (f: forall s, C s -> D s): forall s, F Sigma C s -> F Sigma D s :=
    fun s x => mkF (index x) (op x) [ffun n => f (tnth (dom Sigma (index x) (op x)) n) (args x n)] (range_cond x).
End SignatureFunctor.

Arguments fmap [I] [Sigma] [C D].

Section SignatureFunctorProps.
  Variable I : Type.
  Variable Sigma: sigFam I.
  Variable C D E: (sort Sigma) -> Type.

  Lemma fmap_id: forall s, fmap (fun s => (@id (C s))) s =1 id.
  Proof.
    move => s.
    rewrite /fmap.
    case => /= *.
    apply f_equal2 => //.
    apply ffunP.
    move => x.
      by rewrite ffunE.
  Qed.

  Lemma fmap_comp: forall (f: forall s, D s -> E s) (g: forall s, C s -> D s) s, fmap (fun s => f s \o g s) s =1 fmap f s \o fmap g s.
  Proof.
    move => f g s.
    rewrite /fmap /=.
    case => /= *.
    apply f_equal2 => //.
    apply ffunP.
    move => x.
      by do 3 rewrite ffunE.
  Qed.
End SignatureFunctorProps.

Module SigmaAlgebra.
  Record mixin_of (I: Type) (Sigma: sigFam I) (C: (sort Sigma) -> Type): Type :=
    Mixin { action: forall s, F Sigma C s -> C s }.
  Section ClassDef.
    Notation class_of := mixin_of.
    Structure type I Sigma := Pack { carrier_sort : (sort Sigma) -> Type; _ : class_of I Sigma carrier_sort }.
    Variables (I: Type) (Sigma: sigFam I) (C: (sort Sigma) -> Type) (alg: type I Sigma).
    Definition class := let: Pack _ c as alg' := alg return class_of I Sigma (carrier_sort I Sigma alg') in c.
    Definition clone c of phant_id class c := @Pack I Sigma C c.
    Let xCarrier := (let: Pack C _ := alg in C).
    Notation xclass := (class : class_of I xCarrier).
    Definition pack (m0: mixin_of I Sigma C) :=
          fun m & phant_id m0 m => Pack I Sigma C m.

    Definition carrier := Eval hnf in xCarrier.
  End ClassDef.

  Module Import Exports.
    Coercion carrier : type >-> Funclass.
    Coercion action : mixin_of >-> Funclass.
    
    Notation sigAlg := (type _).
    Notation Mixin := Mixin.
    Notation AlgebraType I Sigma C m := (@pack I Sigma C m m id).
    Notation "[ 'sigAlg' Sigma 'on' C 'for' sigAlg ]" :=
      (@clone _ Sigma C sigAlg _ idfun)
        (at level 0, format "[ 'sigAlg' Sigma 'on' C 'for' sigAlg ]") : form_scope.
    Notation "[ 'sigAlg' Sigma 'on' C ]" :=
      (@clone _ Sigma C _ _ id) (at level 0, format "[ 'sigAlg' Sigma 'on' C ]") : form_scope.
  End Exports.
End SigmaAlgebra.

Export SigmaAlgebra.Exports.

Definition carrier {I: Type} {Sigma: sigFam I} (alg: sigAlg Sigma): sort Sigma -> Type  :=
  SigmaAlgebra.carrier I Sigma alg.
Definition action {I: Type} {Sigma: sigFam I} (alg: sigAlg Sigma): forall s, F Sigma (carrier alg) s -> (carrier alg) s :=
  SigmaAlgebra.action I (Sigma) (carrier alg) (SigmaAlgebra.class I Sigma alg).

Coercion action: sigAlg >-> Funclass.

Module SigmaCoAlgebra.
  Record mixin_of (I: Type) (Sigma: sigFam I) (C: (sort Sigma) -> Type): Type :=
    Mixin { coaction: forall s, C s -> F Sigma C s }.
  Section ClassDef.
    Notation class_of := mixin_of.
    Structure type I Sigma := Pack { carrier_sort : (sort Sigma) -> Type; _ : class_of I Sigma carrier_sort }.
    Variables (I: Type) (Sigma: sigFam I) (C: (sort Sigma) -> Type) (coAlg: type I Sigma).
    Definition class := let: Pack _ c as coAlg' := coAlg return class_of I Sigma (carrier_sort I Sigma coAlg') in c.
    Definition clone c of phant_id class c := @Pack I Sigma C c.
    Let xCarrier := (let: Pack C _ := coAlg in C).
    Notation xclass := (class : class_of I xCarrier).
    Definition pack (m0: mixin_of I Sigma C) :=
          fun m & phant_id m0 m => Pack I Sigma C m.

    Definition carrier := Eval hnf in xCarrier.
  End ClassDef.

  Module Import Exports.
    Coercion carrier : type >-> Funclass.
    Coercion coaction : mixin_of >-> Funclass.
    
    Notation sigCoAlg := (type _).
    Notation Mixin := Mixin.
    Notation CoAlgebraType I Sigma C m := (@pack I Sigma C m m id).
    Notation "[ 'sigCoAlg' Sigma 'on' C 'for' sigCoAlg ]" :=
      (@clone I Sigma C sigCoAlg _ idfun)
        (at level 0, format "[ 'sigCoAlg' Sigma 'on' C 'for' sigCoAlg ]") : form_scope.
    Notation "[ 'sigCoAlg' Sigma 'on' C ]" :=
      (@clone I Sigma C _ _ id) (at level 0, format "[ 'sigCoAlg' Sigma 'on' C ]") : form_scope.
  End Exports.
End SigmaCoAlgebra.

Export SigmaCoAlgebra.Exports.

Definition cocarrier {I: Type} {Sigma: sigFam I} (coAlg: sigCoAlg Sigma): sort Sigma -> Type  :=
  SigmaCoAlgebra.carrier I Sigma coAlg.
Definition coaction {I: Type} {Sigma: sigFam I} (coAlg: sigCoAlg Sigma):
  forall s, cocarrier coAlg s -> F Sigma (cocarrier coAlg) s :=
  SigmaCoAlgebra.coaction I (Sigma) (cocarrier coAlg) (SigmaCoAlgebra.class I Sigma coAlg).

Coercion coaction: sigCoAlg >-> Funclass.

Inductive AlgGen {I: Type} (Sigma: sigFam I) (h: sigAlg Sigma) (s: sort Sigma): carrier h s -> Prop :=
| Gen : forall (x: F Sigma (carrier h) s),
    (forall n, AlgGen Sigma h (tnth (dom Sigma (index x) (op x)) n) (args x n)) ->
    AlgGen Sigma h s (action h s x).

Section CanonicalAlgebraMorphism.
  Variable I: Type.
  Variable Sigma: sigFam I.
  Variables h g: sigAlg Sigma.
  Variable h_inv: forall s, carrier h s -> F Sigma (carrier h) s.

  Variable A: Type.
  Variable measure: forall (s: sort Sigma), carrier h s -> A.
  Variable R: A -> A -> Prop.
  Hypothesis R_wf: well_founded R.

  Hypothesis h_inv_dec: forall s x n, R (measure _ (args (h_inv s x) n)) (measure s x).

  Definition fmap_dec (m1: A) (f: forall s2 (y: carrier h s2), R (measure s2 y) m1 -> carrier g s2):
    forall s (x: F Sigma (carrier h) s), (forall n, R (measure _ (args x n)) m1) -> F Sigma (carrier g) s :=
    fun s x prfs => mkF (index x) (op x) [ffun n => f (tnth (dom Sigma (index x) (op x)) n)
                                                  (args x n) (prfs n)] (range_cond x).

  Definition canonical_morphism: forall s, carrier h s -> carrier g s :=
    DepFix A R R_wf (sort Sigma) (carrier h) (fun s _ => carrier g s) measure
           (fun s x canonical_morphism_rec =>
              action g s (fmap_dec (measure s x) canonical_morphism_rec s (h_inv s x) (h_inv_dec s x))).
          
  
  Lemma canonical_morphism_commutes:
    forall s (x: carrier h s), canonical_morphism s x = action g s (fmap (canonical_morphism) s (h_inv s x)).
  Proof.
    move => s x.
    rewrite /canonical_morphism /DepFix /=.
    case: (R_wf (measure s x)) => prf /=.
    apply: f_equal.
    rewrite /fmap /fmap_dec -/canonical_morphism.
    apply: (f_equal2 (mkF (index (h_inv s x)) (op (h_inv s x)))) => //.
    apply: eq_dffun.
    move => y /=.
    apply: (fun f eqprf => Fix_F_inv A R (sort Sigma) (carrier h) (fun s _ => carrier g s) measure f eqprf
                      (tnth (dom Sigma (index (h_inv s x)) (op (h_inv s x))) y)
                      ((args (h_inv s x)) y)
                      (prf (measure (tnth (dom Sigma (index (h_inv s x)) (op (h_inv s x))) y)
                                      ((args (h_inv s x)) y)) (h_inv_dec s x y))
                      (R_wf (measure (tnth (dom Sigma (index (h_inv s x)) (op (h_inv s x))) y)
                                     ((args (h_inv s x)) y)))).
    move => *.
    apply: f_equal => //.
    apply: f_equal2 => //.
    apply ffunP.
    move => z.
      by do 2 rewrite ffunE.
  Qed.

  Variable hC: forall s, cancel (action h s) (h_inv s).
  Variable h_invC: forall s, cancel (h_inv s) (action h s).

  Lemma canonical_morphism_alg_morphism:
    forall s, canonical_morphism s \o (action h s) =1 (action g s) \o fmap (canonical_morphism) s.
  Proof.
    move => s x.
    rewrite /=.
    rewrite canonical_morphism_commutes.
      by rewrite hC.
  Qed.

  Lemma canonical_morphism_unique:
    forall (m: forall s, carrier h s -> carrier g s) 
      (is_alg_mor_m: forall s, m s \o (action h s) =1 (action g s) \o fmap m s),
    forall s, canonical_morphism s =1 m s.
  Proof.
    move => m is_alg_mor_m s x.
    rewrite canonical_morphism_commutes.
    apply: (fun f_rec => Fix_F A R (sort Sigma) (carrier h)
                            (fun s x => action g s (fmap canonical_morphism s (h_inv s x))  = m s x)
                            measure f_rec s x (R_wf (measure s x))).
    move: s x => _ _.
    move => s x IH.
    suff: (fmap canonical_morphism s (h_inv s x) = fmap m s (h_inv s x)).
    { move => ->.
      move: (is_alg_mor_m s (h_inv s x)).
      rewrite /= => <-.
        by rewrite h_invC. }
    rewrite /fmap.
    apply: f_equal2 => //.
    apply ffunP.
    move => n.
    do 2 rewrite ffunE.
    rewrite canonical_morphism_commutes.
    apply: IH.
      by apply: h_inv_dec.
  Qed.

  Lemma canonical_morphism_sound:
    forall s x, AlgGen Sigma g s (canonical_morphism s x).
  Proof.
    move => s x.
    rewrite canonical_morphism_commutes.
    apply: (fun f_rec => Fix_F A R (sort Sigma) (carrier h)
                            (fun s x => AlgGen Sigma g s (action g s (fmap canonical_morphism s (h_inv s x))))
                            measure f_rec s x (R_wf (measure s x))).
    move: s x => _ _.
    move => s x.
    move: (h_inv_dec s x).
    case: (h_inv s x) => /= i o args range_prf dec_prf IH.
    rewrite /fmap /=.
    constructor.
    move => /= n.
    rewrite ffunE.
    rewrite canonical_morphism_commutes.
    apply: IH.
      by apply: dec_prf.
  Qed.

   Lemma canonical_morphism_complete:
    forall s x, AlgGen Sigma g s x -> exists y, canonical_morphism s y = x.
  Proof.
    move => s x prf.
    elim: s x / prf.
    move => s x prfs IH.
    have: (exists f: {ffun forall n, carrier h (tnth (dom Sigma (index x) (op x)) n) },
              forall n, canonical_morphism (tnth (dom Sigma (index x) (op x)) n) (f n) = (args x) n).
    { move: IH.
      clear ...
      move: x => [] /= idx op args _ prf.
      move: (fin_all_exists prf) => [] f f_prf.
      exists (finfun f).
      move => n.
      rewrite ffunE.
      apply: f_prf. }
    move => [] args' args'_prf.
    exists (action h s (mkF (index x) (op x) args' (range_cond x))).
    move: (canonical_morphism_alg_morphism s (mkF (index x) (op x) args' (range_cond x))).
    rewrite /= => ->.
    apply f_equal.
    rewrite /fmap /=.
    move: args' args'_prf.
    clear...
    case: x => /= i o args range_cond args' args'_prf.
    apply: f_equal2 => //.
    apply ffunP.
    move => n.
    rewrite ffunE.
      by apply: args'_prf.
  Qed.
End CanonicalAlgebraMorphism.

Section FCLAlgebra.
  Variable I: finType.
  Variable Sigma: sigFam I.

  Definition Combinator: finType := sum_finType I (operation Sigma).
  Definition Constructor: ctor := sum_preOrderedType (diag_preOrderedType I) (sort Sigma).

  Definition Gamma__I : {ffun I -> @IT Constructor} :=
    [ffun i => Ctor (inl i) (Omega)].

  Definition embed (s: sort Sigma): @IT Constructor := @Ctor Constructor (inr s) Omega.
  Definition unembed (A: @IT Constructor): option (sort Sigma) :=
    if A is Ctor (inr s) Omega then Some s else None.

  Lemma embed_unembed: pcancel embed unembed.
  Proof. done. Qed.

  Lemma embed_le: forall s1 s2, [sort s1 <= s2] -> [bcd (embed s1) <= embed s2].
  Proof.
    move => s1 s2 prf.
      by apply: BCD__CAx.
  Qed.

  Definition typeAtIndex (o: operation Sigma) (i: I) : @IT Constructor :=
    (Gamma__I i) -> (mkArrow (rev (map embed (dom Sigma i o)), embed (range Sigma i o))).

  Definition Gamma__Sigma : {ffun (operation Sigma) -> @IT Constructor} :=
    [ffun o => \bigcap_(A_i <- map (typeAtIndex o) (enum I)) A_i].

  Definition Gamma: {ffun Combinator -> @IT Constructor} :=
    [ffun c => match c with
              | inl idx => Gamma__I idx
              | inr o => Gamma__Sigma o
              end].

  Definition C__FCL (s: sort Sigma) := { M : @Term Combinator | [FCL Gamma |- M : embed s] }.

  Definition termAction__FCL (s: sort Sigma) (x: F Sigma C__FCL s): @Term Combinator :=
    let: mkF i o args rangeprf := x in
    revApply (Var (inr o) @ (Var (inl i)))
             (rev (map (fun n => sval (args n)) (enum ('I_(arity Sigma i o))))).

  Lemma proofAction__FCL: forall s x, [FCL Gamma |- termAction__FCL s x : embed s].
  Proof.
    move => s [] i o args range_prf.
    have size_eq: (seq.size (rev (map (fun n => sval (args n)) (enum 'I_(arity Sigma i o)))) =
                   seq.size (rev (map embed (dom Sigma i o)))).
    { do 2 rewrite size_rev size_map.
        by rewrite -cardE card_ord size_tuple. }
    apply: (FCL__Sub (embed (range Sigma i o))); last by apply: embed_le.    
    apply: (FCL__App Gamma (@Var Combinator (inr o) @ Var (inl i))
                   (rev (map (fun n => sval (args n)) (enum ('I_(arity Sigma i o)))))
                   (rev (map embed (dom Sigma i o)), embed (range Sigma i o))) => //.
    rewrite /=.
    move => n.
    case arity0: (n < (arity Sigma i o)).
    - rewrite nth_rev; last first.
      { by rewrite size_map -cardE card_ord. }
      rewrite nth_rev; last first.
      { by rewrite size_map size_tuple. }
      rewrite (nth_map s); last first.
      { by rewrite size_map size_tuple -subn_gt0 subnBA // addnC -addnBA // subnn. }
      rewrite (nth_map (Ordinal arity0)); last first.
      { rewrite size_map size_tuple card_ord -subn_gt0 subnBA // addnC -addnBA // subnn. }
      rewrite size_map.
      move: (args
               (nth (Ordinal arity0)
                    (enum 'I_(arity Sigma i o))
                    (seq.size (enum 'I_(arity Sigma i o)) - n.+1))).
      move => [] M /=.
      rewrite (tnth_nth s).
      rewrite (@nth_enum_ord _ (Ordinal arity0) ((seq.size (enum 'I_(arity Sigma i o)) - n.+1))); last first.
      { by rewrite -cardE card_ord -subn_gt0 subnBA // addnC -addnBA // subnn. }
      move: size_eq.
        by rewrite size_rev size_rev size_map => ->.
    - rewrite nth_default; last first.
      { by rewrite size_rev size_map -cardE card_ord leqNgt arity0. }
      rewrite nth_default; last first.
      { by rewrite size_rev size_map size_tuple leqNgt arity0. }
      apply: FCL__MP; last by apply: FCL__Var.
      apply: FCL__Sub; first by apply: FCL__Var.
      rewrite /Gamma ffunE /Gamma__Sigma ffunE ffunE.
      apply: BCD__Trans.
      + apply: (bcd_subset_f _ id _ [:: typeAtIndex o i]).
        move => x.
        rewrite mem_seq1.
        move => /eqP ->.
        apply /mapP.
        exists i => //.
          by rewrite mem_enum.
      + rewrite /= /typeAtIndex.
          by apply: BCD__Sub.
  Qed.

  Definition action__FCL (s: sort Sigma) (x: F Sigma C__FCL s): C__FCL s :=
    exist _ (termAction__FCL s x) (proofAction__FCL s x).

  Definition termCoAction__FCL (s: sort Sigma) (x: C__FCL s): seq (@Term Combinator) :=
    behead (unapply (sval x)).2.

  Lemma mkArrow__Omega {C: ctor}: forall srcs (A: @IT C), isOmega (mkArrow (srcs, A)) = isOmega A.
  Proof.
    elim /last_ind => // srcs src IH.
    move => A /=.
    rewrite mkArrow_rcons /=.
      by apply: IH.
  Qed.

  Lemma unapplyNotIndex: forall s (x: C__FCL s), if (unapply (sval x)).1 is (inl _) then False else True.
  Proof.
    move => s [] M.
    rewrite -(unapply_revapply M) /= revapply_unapply.
    move => /FCL__invApp [] srcs [] size__eq /(fun prf => prf (seq.size srcs)).
    rewrite nth_default; last by rewrite size__eq.
    rewrite nth_default //.
    case: (unapply M).1 => //.
    move => i /minimalType_minimal.
    move: size__eq => _.
    elim /last_ind: srcs.
    - move => /subty_complete.
      rewrite /mkArrow /= /embed /= ffunE /Gamma__I ffunE.
      move => /SubtypeMachine_inv /= /(fun prf => prf (fun i r => if r is Return true then false else true)) res.
        by move: (res (fun _ _ => isT)).
    - move => srcs src _.
      rewrite mkArrow_rcons.
      move => /subty_complete.
      rewrite /= /Gamma ffunE /Gamma__I ffunE.
      move => /SubtypeMachine_inv /(fun prf => prf (fun i r => if r is Return true then false else true)) res.
      suff: false by done.
      apply: res.
      move => Delta r'.
      rewrite /cast /= mkArrow__Omega /=.
      move => /emptyDoneTgt -> /=.
      case: r' => //.
      move => /Omega__subty.
      rewrite mkArrow__Omega /=.
      move => res.
        by apply: res.
  Qed.

  Definition opCoAction__FCL (s: sort Sigma) (x: C__FCL s): operation Sigma :=
    match (unapply (sval x)).1 as o return (if o is (inl _) then False else True) -> operation Sigma with
    | inl _ => False_rect _
    | inr o => fun _ => o
    end (unapplyNotIndex s x).

  Lemma 

  Lemma indexType_sound: forall M i, [FCL Gamma |- M : @Ctor Constructor (inl i) Omega] -> M = (@Var Combinator (inl i)).
  Proof.
    move => M i.
    move A__eq: (@Ctor Constructor (inl i) Omega) => A prf.
    move: i A__eq.
    elim /FCL_normalized_ind: M A /prf.
    - case.
      + move => i1 i2.
        rewrite /Gamma ffunE /Gamma__I ffunE.
          by move => [] ->.
      + move => o i.
        rewrite /Gamma ffunE /Gamma__Sigma ffunE.
          by case: (enum I) => // ? [] //.
    - move => c A IH prf i A__eq.
      apply: IH.
      move: prf.
      rewrite -A__eq /Gamma ffunE.
      case: c.
      + move => i2.
        rewrite /Gamma__I ffunE.
        move => /subty_complete /SubtypeMachine_inv /=.
        move => /(fun prf => prf (fun i r => if (i, r) is ([subty (Ctor (inl i1) Omega) of (Ctor (inl i2) Omega)], Return true)
                                      then i2 = i1 else True)) => res.
        apply: f_equal2 => //.
        apply: f_equal.
        apply: res.
        rewrite /cast /=.
        case res: (i2 == i).
        * rewrite (eqP res) preorder_reflexive.
            by case.
        * by rewrite /[sort _ <= _] /= /[sort _ <= _] /= res.
      + move => o /subty_complete /SubtypeMachine_inv /(fun prf => prf (fun i r => if r is Return true then false else true)) res.
        suff: false by done.
        apply: res.
        rewrite /Gamma__Sigma ffunE.
        suff: nilp (cast (@Ctor Constructor (inl i) Omega) (\bigcap_(A_i <- map (typeAtIndex o) (enum I)) A_i)) by move => ->.
        rewrite slow_cast_cast.
        elim: (enum I) => // idx idxs.
          by case: idxs => [].
    - 


      



  Lemma indexType_src: forall o N Ns A, ~~isOmega A -> [FCL Gamma |- revApply (Var (inr o)) Ns : A] -> 

  Lemma unapplyIsIndex: forall s (x: C__FCL s), if (unapply (sval x)).2 is [:: (Var (inl _)) & _] then True else False.
  Proof.
    move => s x.
    move: (unapplyNotIndex s x).
    case x => M.
    rewrite -(unapply_revapply M) /= revapply_unapply.
    move => /FCL__invApp [] srcs [] size__eq.
    case: (unapply M).1 => // o.
    move: size__eq.
    case: (unapply M).2.
    - case: srcs => // _.
      move => /(fun prf => prf 0) /=.
      move => /minimalType_minimal /=.
      rewrite /mkArrow /= /Gamma ffunE /Gamma__Sigma ffunE /embed.
      move => /subty_complete /SubtypeMachine_inv /= /(fun prf => prf (fun i r => if r is Return true then false else true)) res.
      suff: false by done.
      apply: res.
      suff: (nilp (cast (@Ctor Constructor (inr s) Omega) (\bigcap_(A_i <- map (typeAtIndex o) (enum I)) A_i))) by move ->.
      rewrite slow_cast_cast.
      elim (enum I) => // idx idxs.
        by case: idxs.
    - case: srcs => // src srcs.
      move => N Ns _ prf.
      have src__geq: [src 

      
      


      

  

  Lemma proofCoAction__FCL (s: sort Sigma) (x: C__FCL s):
    forall n, [FCL Gamma |- (nth (opCoAction__FCL s x) (termCoAction__FCL s x) n) :
                       (nth (Gamma (opCoAction__FCL s x)) (dom Sigma )
                                                                                                                                  

    let: mkF i o args rangeprf := x in
    revApply (Var (inr o) @ (Var (inl i)))
             (rev (map (fun n => sval (args n)) (enum ('I_(arity Sigma i o))))).





                           


  


