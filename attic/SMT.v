Require Import PeanoNat.
From mathcomp Require Import all_ssreflect all_algebra.

Set Bullet Behavior "Strict Subproofs".

Delimit Scope it_scope with IT.
Local Open Scope it_scope.

Import EqNotations.
Import intOrdered.

Section Grammar.
  Variable Terminal : finType.
  Variable NonTerminal: finType.

  Inductive RHS :=
  | P_App : Terminal -> seq NonTerminal -> RHS.
  

  Inductive Term :=
  | App: Terminal -> seq Term -> Term.

  Definition word (S: NonTerminal) (P: {ffun NonTerminal -> seq RHS}) (t: Term) : bool :=
    (fix word (t: Term): NonTerminal -> bool :=
       match t with
       | App C Ms =>
         fun T =>
           has (fun p => let: (P_App C' As) := p in
                      [&& (C == C'),
                       (size Ms == size As) &
                       all id (allpairs word Ms As)]) (P T)
       end) t S.
End Grammar.

Arguments P_App [Terminal NonTerminal].
Arguments word [Terminal NonTerminal].
Hint Constructors RHS.

Section SMT.
  Variable var: countType.

  Structure Model :=
    { functions : var -> int -> int;
      constants: var -> int }.

  Definition updateConstant (x: var) (v: int) (M: Model): Model :=
    {| functions := functions M;
       constants := fun y => if x == y then v else constants M y |}.

  Inductive Formula : Type :=
  (** Arithmetic **)
  | Const : int -> Formula
  | IVar : var -> Formula
  | Add : Formula -> Formula -> Formula
  (** Int valued unary functions **)
  | IFun : var -> Formula -> Formula
  (** Bools **)
  | BTrue: Formula
  | BFalse: Formula
  | And : Formula -> Formula -> Formula
  | XOr : Formula -> Formula -> Formula
  | Equiv: Formula -> Formula -> Formula
  | Implies : Formula -> Formula -> Formula
  | LT : Formula -> Formula -> Formula
  | IEqual : Formula -> Formula -> Formula
  | IAll : var -> Formula -> Formula.

  Inductive Result :=
  | B : bool -> Result
  | I : int -> Result.

  Inductive SMT (M: Model): Formula -> Result -> Prop :=
  | SMT_Const: forall n, SMT M (Const n) (I n)
  | SMT_Var: forall x, SMT M (IVar x) (I (constants M x))
  | STM_Add: forall A B r1 r2,
      SMT M A (I r1) -> SMT M B (I r2) -> SMT M (Add A B) (I (r1 + r2))
  | SMT_IFun: forall f idx i,
      SMT M idx (I i) -> SMT M (IFun f idx) (I (functions M f i))
  | SMT_BTrue: SMT M BTrue (B true)
  | SMT_BFalse: SMT M BFalse (B false)
  | SMT_And: forall L R r1 r2, SMT M L (B r1) -> SMT M R (B r2) -> SMT M (And L R) (B (r1 && r2))
  | SMT_XOr: forall L R r1 r2, SMT M L (B r1) -> SMT M R (B r2) -> SMT M (XOr L R) (B ((r1 && ~~ r2) || (~~r1 && r2)))
  | SMT_Equiv: forall L R r1 r2, SMT M L (B r1) -> SMT M R (B r2) -> SMT M (Equiv L R) (B (r1 == r2))
  | SMT_Implies: forall L R r1 r2, SMT M L (B r1) -> SMT M R (B r2) -> SMT M (Implies L R) (B (r1 ==> r2))
  | SMT_LT: forall L R r1 r2, SMT M L (I r1) -> SMT M R (I r2) -> SMT M (LT L R) (B (ltz r1 r2))
  | SMT_IEqual: forall L R r1 r2, SMT M L (I r1) -> SMT M R (I r2) -> SMT M (IEqual L R) (B (r1 == r2))
  | SMT_IAll: forall P x,
      (forall v, SMT (updateConstant x v M) P (B true)) -> SMT M P (B true).
End SMT.

Arguments Formula [var].
Arguments SMT [var].
Hint Constructors Result.
Hint Constructors SMT.

Section Encoding.
  Variable var: countType.
  Variable T : countType.
  Variable N: countType.

  Variable inhabitant: var.
  Variable has_type: var.
  Variable i: var.

  Fixpoint encode_pos (n: nat) : Formula :=
    iterate n (Add (IVar i)) i.

  Definition EncodeRHS (r: RHS N T): Formula :=
    let: P_App C R := r in
    foldr (fun 

      Equal (IFun inhabitant (IVar i)) (Const ((pickle C)%:Z.+1))
      (foldr 

  Definition Encode (P: {ffun N -> seq (RHS N T)}) : {ffun N -> Formula} :=
    [ffun T =>
     Equiv 
       (Equal (has_type i) (pickle T)%:Z)
       (map match P T with
        | P_Combinator C =>


                            
  

