From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

Section OperationalSemantic.
  Variable T : Type.
  Variable Combinator: finType.
  Definition Ctxt : {ffun Combinator -> T}.


  Inductive Command: Set :=
  | inhabit : seq (Ctxt * seq T)%type -> Command
  | inhabit_in_any_of: seq T -> seq Ctxt -> Command
  | inhabit_in: seq T -> Ctxt -> Command
  | recursive_targets_for_in: T -> Ctxt -> Command
  | next_targets: seq(Ctxt * seq T) -> Command
  | fail: Command.



  Definition Production : Set := T * (Combinator * seq T).

  Reserved Notation "[ < P ; cmd > ]".

  Inductive ExtCLSem: seq Production -> Command -> Prop :=
  
  

  