Require Import Coq.Vectors.Fin.
Require Import Coq.Vectors.Vector.
Require Import Coq.Arith.PeanoNat.

Require Import SigmaAlgebra.
Require Import VarianceLabeledTree.

Inductive Ty: Set :=
| Const : nat -> Ty
| Arrow : Ty -> Ty -> Ty
| BoxTy : Ty -> Ty.

Inductive LambdaBox: forall {n m} (Delta: Fin.t n -> Ty) (Gamma: Fin.t m -> Ty), Ty -> Type :=
| Var : forall {n m : nat} (Delta: Fin.t n -> Ty) (Gamma: Fin.t m -> Ty) x, LambdaBox Delta Gamma (Gamma x)
| MVar : forall {n m: nat} (Delta: Fin.t n -> Ty) (Gamma: Fin.t m -> Ty) u, LambdaBox Delta Gamma (Delta u)
| App : forall {n m: nat} (Delta: Fin.t n -> Ty) (Gamma: Fin.t m -> Ty) sigma tau,
    LambdaBox Delta Gamma (Arrow sigma tau) ->
    LambdaBox Delta Gamma sigma ->
    LambdaBox Delta Gamma tau
| Lam : forall {n m: nat} (Delta: Fin.t n -> Ty) (Gamma: Fin.t (S m) -> Ty) tau,
    LambdaBox Delta Gamma tau ->
    LambdaBox Delta (fun x => Gamma (FS x)) (Arrow (Gamma F1) tau)
| MLam : forall {n m: nat} (Delta: Fin.t (S n) -> Ty) (Gamma: Fin.t m -> Ty) tau,
    LambdaBox Delta Gamma tau ->
    LambdaBox (fun x => Delta (FS x)) Gamma (Arrow (Delta F1) tau)
| Box: forall {n: nat} (Delta: Fin.t n -> Ty) (Gamma: Fin.t 0 -> Ty) tau,
    LambdaBox Delta Gamma tau ->
    LambdaBox Delta Gamma (BoxTy tau)
| LetBox: forall {n m: nat} (Delta: Fin.t (S n) -> Ty) (Gamma: Fin.t m -> Ty) sigma,
    LambdaBox (fun x => Delta (FS x)) Gamma (BoxTy (Delta F1)) ->
    LambdaBox Delta Gamma sigma ->
    LambdaBox (fun x => Delta (FS x)) Gamma sigma.

Section ClosedImplementations.
  Variable EmptyContext : Fin.t 0 -> Ty.
  Definition Implementations := list { ty : _ & LambdaBox EmptyContext EmptyContext (BoxTy ty) }.

  Inductive TyConstr: Set :=
  | TyConstr_Const : nat -> TyConstr
  | TyConstr_Arrow : TyConstr
  | TyConstr_Box : TyConstr
  | TyConstr_BlackBox : TyConstr.

  Lemma TyConstr_eq_dec: forall (x y: TyConstr), { x = y } + { x <> y }.
  Proof.
    intros x y;
      destruct x as [ n | | | ];
      destruct y as [ m | | | ];
      solve [ left; reflexivity
            | right; intro devil; inversion devil
            | destruct (Nat.eq_dec n m) as [ eq | ineq ];
              [ left; rewrite eq; reflexivity
              | right; intro devil; inversion devil; contradiction ] ].
  Qed.              

  Instance TyConstrInfo : LabelInfo TyConstr :=
    {| labelArity :=
         fun (constr: TyConstr) =>
           match constr with
           | TyConstr_Const _ => 0
           | TyConstr_Arrow => 2
           | TyConstr_Box => 1
           | TyConstr_BlackBox => 1
           end;
       successorVariance := fun _ _ => In |}.

  Definition tyConstrOrder := @eq TyConstr.
  
  Inductive SigVar : Set := alpha | beta.
  Lemma SigVar_eq_dec: forall (x y: SigVar), { x = y } + { x <> y }.
  Proof.
    intros x y;
      destruct x;
      destruct y;
      solve [ left; reflexivity | right; intro devil; inversion devil ].
  Qed.

  Inductive SigOp (from: Implementations): Set :=
  | TermOp : forall impl, List.In impl from -> SigOp from
  | ApplyOp : SigOp from
  | MApplyOp : SigOp from.

  Definition applyDom : t (VLTree TyConstr SigVar) 2 :=
    cons _ (Node _ _ TyConstr_Arrow (cons _ (Hole _ _ alpha) _ (cons _ (Hole _ _ beta) _ (nil _))))
         _ (cons _ (Hole _ _ alpha) _ (nil _)).

  Definition applyRange : VLTree TyConstr SigVar := (Hole _ _ beta).
  Definition mapplyRange : VLTree TyConstr SigVar :=
    Node _ _ TyConstr_Box
         (cons _ (Hole _ _ beta) _ (nil _)).
  
  Definition mapplyDom : t (VLTree TyConstr SigVar) 2 :=
    cons _ (Node _ _ TyConstr_Box
                 (cons _ (Node _ _ TyConstr_Arrow (cons _ (Hole _ _ alpha) _ (cons _ (Hole _ _ beta) _ (nil _))))
                       _ (nil _)))
         _ (cons _ (Node _ _ TyConstr_Box
                         (cons _ (Hole _ _ alpha) _ (nil _))) _ (nil _)).

  Fixpoint typeToSort (ty: Ty) (Var : Set): VLTree TyConstr Var :=
    match ty with
    | Const n => Node _ _ (TyConstr_Const n) (nil _)
    | Arrow sigma tau =>
      Node _ _ TyConstr_Arrow
           (cons _ (typeToSort sigma Var) _
                 (cons _ (typeToSort tau Var) _ (nil _)))
    | BoxTy sigma =>
      Node _ _ TyConstr_Box
           (cons _ (typeToSort sigma Var) _ (nil _))
    end.

     
  Definition MakeSignature (from: Implementations): Signature (VLTree TyConstr) SigVar (SigOp from) :=
    {| arity :=
         fun op =>
           match op with
           | TermOp _ _ _ => 0
           | ApplyOp _ => 2
           | MApplyOp _ => 2
           end;
       domain :=
         fun op =>
           match op as op' return t (VLTree TyConstr SigVar) (match op' with
                                                              | TermOp _ _ _ => 0
                                                              | ApplyOp _ => 2
                                                              | MApplyOp _ => 2
                                                              end) with
           | TermOp _ _ _ => nil _
           | ApplyOp _ => applyDom
           | MApplyOp _ => mapplyDom
           end;
       range :=
         fun op =>
           match op with
           | TermOp _ impl _ => typeToSort (projT1 impl) SigVar
           | ApplyOp _ => applyRange
           | MApplyOp _ => mapplyRange
           end |}.
             
  
  Fixpoint sortToType (s: VLTree TyConstr EmptySet): Ty :=
    match s with
    | Node _ _ (TyConstr_Const n) _ => Const n
    | Node _ _ TyConstr_Arrow (cons _ sigma _ (cons _ tau _ _)) =>
      Arrow (sortToType sigma) (sortToType tau)
    | Node _ _ TyConstr_Box (cons _ sigma _ _) =>
      BoxTy (sortToType sigma)
    | _ => Const 0
    end.

  Definition Carrier: VLTree TyConstr EmptySet -> Type :=
    fun s => LambdaBox EmptyContext EmptyContext (sortToType s).    
  
End ClosedImplementations.
  
    
    