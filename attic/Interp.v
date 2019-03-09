Require Import PeanoNat.
From mathcomp Require Import all_ssreflect.

Set Bullet Behavior "Strict Subproofs".

Import EqNotations.

Require Import Types.

(*

Module Constructor.
  Definition ctor_preorder (ctor: countType) := (ctor -> ctor -> bool)%type.
  Definition preorder_reflexive (ctor: countType) (lessOrEqual: ctor_preorder ctor): Type :=
    forall c, lessOrEqual c c = true.

  Definition preorder_transitive (ctor: countType) (lessOrEqual: ctor_preorder ctor): Type :=
    forall (c: ctor) (d: ctor) (e: ctor),
      lessOrEqual c d && lessOrEqual d e ==> lessOrEqual c e.

  Record mixin_of (ctor: countType): Type :=
    Mixin {
        lessOrEqual : ctor_preorder ctor;
        _: preorder_reflexive ctor lessOrEqual;
        _: preorder_transitive ctor lessOrEqual
      }.
  Notation class_of := mixin_of (only parsing).
  Section ClassDef.
    Structure type := Pack { sort : countType; _ : class_of sort }.
    Variables (ctor: countType) (cCtor: type).
    Definition class := let: Pack _ c := cCtor return class_of (sort cCtor) in c.
    Definition pack c := @Pack ctor c.
    Definition clone c & phant_id class c := Pack ctor c.
  End ClassDef.
  Module Exports.
    Coercion sort : type >-> countType.
    Notation ctor := type.
    Notation CtorMixin := Mixin.
    Notation CtorType C m := (@pack C m).
    Notation "[ 'ctorMixin' 'of' ctor ]" :=
      (class _ : mixin_of ctor) (at level 0, format "[ 'ctorMixin' 'of' ctor ]") : form_scope.
    Notation "[ 'ctorType' 'of' ctor 'for' C ]" :=
      (@clone ctor C _ idfun id) (at level 0, format "[ 'ctorType' 'of' ctor 'for' C ]") : form_scope.
    Notation "[ 'ctorType' 'of' C ]" :=
      (@clone ctor _ _ id id) (at level 0, format "[ 'ctorType' 'of' C ]") : form_scope.
  End Exports.
End Constructor.
Export Constructor.Exports.


 *)

Section PolyCat.
  Definition polyFun (args: seq Type) (tgt: Type): Type :=
    (fix polyFun_rec (args: seq Type): Type :=
       match args with
       | [::] => tgt
       | [:: arg & args'] => (arg -> polyFun_rec args')%type
       end) args.

  Definition IndexedPolyFunctor (Idx: Type): Type := Idx -> seq Type -> Type.

  Definition functorAction (Idx: Type) (F: IndexedPolyFunctor Idx): Type :=
    forall idx args1 args2, (forall R, (polyFun args2 (R args2)) -> polyFun args1 (R args2)) -> F idx args1 -> F idx args2.

  Definition PolyId (args: seq Type) (pid: forall R, (polyFun args (R args)) -> polyFun args (R args)): Type :=
    forall R cont, (fix PolyID_rect (args: seq Type) (T: Type):  polyFun args T -> polyFun args T -> Type :=
                 match args with
                 | [::] => fun f1 f2 => f1 = f2
                 | [:: arg & args'] => fun f1 f2 => forall (x: arg), PolyID_rect args' T (f1 x) (f2 x)
                 end) args (R args) (pid R cont) cont.

  Definition functorAction_id
             (Idx: Type)
             (F: IndexedPolyFunctor Idx)
             (fmap: functorAction Idx F): Type :=
    forall args idx pid, PolyId args pid -> forall x, fmap idx args args pid x = x.
  Definition functorAction_comp
             (Idx: Type)
             (F: IndexedPolyFunctor Idx)
             (fmap: functorAction Idx F): Type :=
    forall idx args1 args2 args3 f g x,
      fmap idx args2 args3 g (fmap idx args1 args2 f x) = fmap idx args1 args3 (fun R cont => f _ (g R cont)) x.

  Definition naturalTransformationAction
             (Idx: Type)
             (F: IndexedPolyFunctor Idx)
             (i1 i2: ): Type :=
    forall t, interp a t -> interp b t.

  Definition naturalTransformationAction_law
             (Constructor: ctor)
             (interp: constructorInterpretation Constructor)
             (fmap: functorAction Constructor interp)
             (fmap_id: functorAction_id Constructor interp fmap)
             (fmap_comp: functorAction_comp Constructor interp fmap)
             (a b: Constructor)
             (natAct: naturalTransformationAction Constructor interp a b): Type :=
    forall t1 t2 (f: t1 -> t2) x, natAct t2 (fmap a t1 t2 f x) = fmap b t1 t2 f (natAct t1 x).




Section ConstructorSemantics.
  Definition constructorInterpretation (Constructor: ctor): Type := Constructor -> Type -> Type.



  Definition functorAction (Constructor: ctor) (interp: constructorInterpretation Constructor): Type :=
    forall a t1 t2, (t1 -> t2) -> interp a t1 -> interp a t2.

  Definition functorAction_id
             (Constructor: ctor)
             (interp: constructorInterpretation Constructor)
             (fmap: functorAction Constructor interp): Type :=
    forall a t (f: t -> t), (forall x, f x = x) -> forall x, fmap a t t f x = x.
  Definition functorAction_comp
             (Constructor: ctor)
             (interp: constructorInterpretation Constructor)
             (fmap: functorAction Constructor interp): Type :=
    forall a t1 t2 t3 (f: t1 -> t2) (g: t2 -> t3) x,
      fmap a t2 t3 g (fmap a t1 t2 f x) = fmap a t1 t3 (g \o f) x.

  Definition naturalTransformationAction
             (Constructor: ctor)
             (interp: constructorInterpretation Constructor)
             (a b : Constructor): Type :=
    forall t, interp a t -> interp b t.

  Definition naturalTransformationAction_law
             (Constructor: ctor)
             (interp: constructorInterpretation Constructor)
             (fmap: functorAction Constructor interp)
             (fmap_id: functorAction_id Constructor interp fmap)
             (fmap_comp: functorAction_comp Constructor interp fmap)
             (a b: Constructor)
             (natAct: naturalTransformationAction Constructor interp a b): Type :=
    forall t1 t2 (f: t1 -> t2) x, natAct t2 (fmap a t1 t2 f x) = fmap b t1 t2 f (natAct t1 x).

  Definition conversion
             (Constructor: ctor)
             (interp: constructorInterpretation Constructor): Type :=
    forall a b, [ ctor a <= b] -> naturalTransformationAction Constructor interp a b.

  Definition conversion_lawful
             (Constructor: ctor)
             (interp: constructorInterpretation Constructor)
             (convert: conversion Constructor interp)
             (fmap: functorAction Constructor interp)
             (fmap_id: functorAction_id Constructor interp fmap)
             (fmap_comp: functorAction_comp Constructor interp fmap): Type :=
    forall a b leq__ab,
      naturalTransformationAction_law Constructor interp fmap fmap_id fmap_comp a b (convert a b leq__ab).
  Definition conversion_invariant
             (Constructor: ctor)
             (interp: constructorInterpretation Constructor)
             (convert: conversion Constructor interp): Type :=
    forall a b (leq1__ab leq2__ab: [ ctor a <= b]) t x, convert a b leq1__ab t x = convert a b leq2__ab t x.

  Definition conversion_id
             (Constructor: ctor)
             (interp: constructorInterpretation Constructor)
             (convert: conversion Constructor interp): Type :=
    forall a t x, (convert a a (preorder_reflexive a) t x) = x.

  Definition conversion_trans
             (Constructor: ctor)
             (interp: constructorInterpretation Constructor)
             (convert: conversion Constructor interp): Type :=
    forall a b c leq__ab leq__bc t x,  convert b c leq__bc t (convert a b leq__ab t x) =
                              convert a c (elimTF implyP (preorder_transitive a b c) (introTF (c := true) andP (conj leq__ab leq__bc))) t x.



  Definition distribution (Constructor: ctor) (interp: constructorInterpretation Constructor): Type :=
    forall a t1 t2, interp a t1 -> interp a t2 -> interp a (t1 * t2)%type.

  Definition convert_id
             (Constructor: ctor)
             (interp: constructorInterpretation Constructor)
             (convert: conversion Constructor interp): Type :=
    forall a b (leq__ab: [ ctor a <= b]) (leq__ba: [ ctor b <= a]) t x, convert b a leq__ba t (convert a b leq__ab t x) = x.




