From mathcomp Require Import all_ssreflect.

Set Bullet Behavior "Strict Subproofs".

Module PreOrdered.
  Definition preorder (preOrdered: Type) := (preOrdered -> preOrdered -> bool)%type.
  Definition preorder_reflexive (preOrdered: Type) (lessOrEqual: preorder preOrdered): Type :=
    forall c, lessOrEqual c c = true.

  Definition preorder_transitive (preOrdered: Type) (lessOrEqual: preorder preOrdered): Type :=
    forall (c: preOrdered) (d: preOrdered) (e: preOrdered),
      lessOrEqual c d && lessOrEqual d e ==> lessOrEqual c e.

  Record mixin_of (preOrdered: Type): Type :=
    Mixin {
        lessOrEqual : preorder preOrdered;
        _: preorder_reflexive preOrdered lessOrEqual;
        _: preorder_transitive preOrdered lessOrEqual
      }.

  Section ClassDef.
    Record class_of (C: Type) :=
      Class {
          base: Countable.class_of C;
          mixin: mixin_of C
        }.
    Local Coercion base : class_of >-> Countable.class_of.
    Structure type: Type := Pack { sort : Type; _ : class_of sort }.
    Local Coercion sort : type >-> Sortclass.
    Variables (T: Type) (cPreOrdered: type).
    Definition class := let: Pack _ c as cPreOrdered' := cPreOrdered return class_of cPreOrdered' in c.
    Definition clone c of phant_id class c := @Pack T c.
    Let xT := let: Pack T _ := cPreOrdered in T.
    Notation xclass := (class : class_of xT).
    Definition pack m :=
      fun b bT & phant_id (Countable.class bT) b => Pack _ (@Class T b m).
    Definition eqType := Eval hnf in @Equality.Pack cPreOrdered xclass.
    Definition choiceType := Eval hnf in  @Choice.Pack cPreOrdered xclass.
    Definition countType := Eval hnf in @Countable.Pack cPreOrdered xclass.
  End ClassDef.

  Module Import Exports.
    Coercion base : class_of >-> Countable.class_of.
    Coercion mixin: class_of >-> mixin_of.
    Coercion sort : type >-> Sortclass.
    Coercion eqType : type >-> Equality.type.
    Canonical eqType.
    Coercion choiceType : type >-> Choice.type.
    Canonical choiceType.
    Coercion countType : type >-> Countable.type.
    Canonical countType.

    Notation preOrdered := type.
    Notation PreOrderedType C m := (@pack C m _ _ id).
    Notation PreOrderedMixin := Mixin.

    Notation "[ 'preOrderedType' 'of' T 'for' cT ]" :=
      (@clone T cT _ idfun) (at level 0, format "[ 'preOrderedType' 'of' T 'for' cT ]") : form_scope.
    Notation "[ 'preOrderedType' 'of' T ]" :=
      (@clone T _ _ id) (at level 0, format "[ 'preOrderedType' 'of' T ]") : form_scope.
  End Exports.
End PreOrdered.
Export PreOrdered.Exports.

Definition lessOrEqual c := PreOrdered.lessOrEqual _ (PreOrdered.class c).
Arguments lessOrEqual [c].

Lemma preorder_reflexive c: PreOrdered.preorder_reflexive _ (@lessOrEqual c).
Proof. by case c => ? [] ? []. Qed.
Arguments preorder_reflexive [c].
Lemma preorder_transitive c: PreOrdered.preorder_transitive _ (@lessOrEqual c).
Proof. by case c => ? [] ? []. Qed.
Arguments preorder_transitive [c].

Section NatPreOrdered.
  Lemma leq_transb: forall (m n p: nat), (m <= n) && (n <= p) ==> (m <= p).
  Proof.
    move => m n p.
    move: (@leq_trans n m p).
    case (m <= n) => //=.
    case (n <= p) => //= prf.
      by apply: prf.
  Qed.

  Definition nat_preOrderedMixin := PreOrdered.Mixin nat leq leqnn leq_transb.
  Canonical nat_preOrderedType := Eval hnf in PreOrderedType nat nat_preOrderedMixin.
End NatPreOrdered.

Section DiagCountTypePreOrdered.
  Variable T: countType.  

  Lemma eqop_refl: PreOrdered.preorder_reflexive _ (@eq_op T).
  Proof.
    move => x.
      by rewrite eq_refl.
  Qed.

  Lemma eqop_trans: PreOrdered.preorder_transitive _ (@eq_op T).
  Proof.
    move => x y z.
    apply /implyP.
      by move => /andP [] /eqP ->.
  Qed.

  Definition diag_preOrderedMixin := PreOrdered.Mixin T eq_op eqop_refl eqop_trans.
  Definition diag_preOrderedType := Eval hnf in PreOrderedType T diag_preOrderedMixin.
End DiagCountTypePreOrdered.
