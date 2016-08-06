Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.Lists.Streams.

Module Type ImpLang.

Parameter int32: Set.  
Parameter uint8: Set.

Inductive NumExp (baseType : Set) : Set :=
| Const : baseType -> NumExp baseType
| Read : int32 -> NumExp baseType
| Plus : NumExp baseType -> NumExp baseType -> NumExp baseType
| Minus : NumExp baseType -> NumExp baseType -> NumExp baseType
| Mult : NumExp baseType -> NumExp baseType -> NumExp baseType
| Div : NumExp baseType -> NumExp baseType -> NumExp baseType
| Mod : NumExp baseType -> NumExp baseType -> NumExp baseType.

Definition Int32Exp := NumExp int32.
Definition UInt8Exp := NumExp uint8.                                            

Inductive BoolExp : Type :=
| ConstBool : uint8 -> BoolExp
| Nand : BoolExp -> BoolExp -> BoolExp
| LessEq8 : UInt8Exp -> UInt8Exp -> BoolExp
| GetBit8 : UInt8Exp -> UInt8Exp -> BoolExp
| LessEq32 : Int32Exp -> Int32Exp -> BoolExp
| GetBit32 : Int32Exp -> UInt8Exp -> BoolExp.

Inductive Exp : Set :=
| Logic : BoolExp -> Exp
| Arithmetic32 : Int32Exp -> Exp
| Arithmetic8 : UInt8Exp -> Exp.
                         
Inductive Stmt : Set :=
| Store : Int32Exp -> Exp -> Stmt
| PrintOut : Exp -> Stmt
| Input32 : Int32Exp -> Stmt
| Input8 : Int32Exp -> Stmt
| While : BoolExp -> list Stmt -> Stmt
| IfElse : BoolExp -> list Stmt -> list Stmt -> Stmt.

Definition ImpLang : Set := list Stmt.


Definition Memory : Set := int32 -> option uint8.
Definition StdOut : Set := list uint8.
Definition StdIn : Set := Stream (StdOut -> uint8).

Inductive RuntimeError : Type :=
| OutOfFuel : Memory -> StdIn -> StdOut -> RuntimeError
| InvalidRead : int32 -> Memory -> RuntimeError.

Fixpoint evalNatExp (e: NatExp) (memory: Memory): RuntimeError + nat :=
  match e with
  | ConstNat n => inr n
  | ReadNat p =>
    match evalNatExp p memory with
    | inr(v) =>
      match memory v with
      | Some(inl(n)) => inr(n)
      | Some(inr(_)) => inl(MemoryTypeError nat v memory)
      | None => inl(UninitializedRead v memory)
      end
    | inl(e) => inl e
    end
  | Plus x y =>
    match (evalNatExp x memory, evalNatExp y memory) with
    | (inr(x'), inr(y')) => inr(x' + y')
    | (inl(e), _) => inl(e)
    | (_, inl(e)) => inl(e)
    end
  | Minus x y =>
    match (evalNatExp x memory, evalNatExp y memory) with
    | (inr(x'), inr(y')) => inr(x' - y')
    | (inl(e), _) => inl(e)
    | (_, inl(e)) => inl(e)
    end
  | Mult x y =>
    match (evalNatExp x memory, evalNatExp y memory) with
    | (inr(x'), inr(y')) => inr(x' * y')
    | (inl(e), _) => inl(e)
    | (_, inl(e)) => inl(e)
    end
  end.

Fixpoint evalBoolExp (e: BoolExp) (memory: Memory): RuntimeError + bool :=
  match e with
  | ConstBool b => inr(b)
  | ReadBool p =>
    match evalNatExp p memory with
    | inr(v) =>
      match memory v with
      | Some(inr b) => inr(b)
      | Some(inl _) => inl(MemoryTypeError bool v memory)
      | None => inl(UninitializedRead v memory)
      end
    | inl(e) => inl(e)
    end
  | Nand x y =>
    match (evalBoolExp x memory, evalBoolExp y memory) with
    | (inr(x'), inr(y')) => inr(negb (andb x' y'))
    | (inl(e), _) => inl(e)
    | (_, inl(e)) => inl(e)
    end
  | LessEq x y =>
    match (evalNatExp x memory, evalNatExp y memory) with
    | (inr(x'), inr(y')) => inr(leb x' y')
    | (inl(e), _) => inl(e)
    | (_, inl(e)) => inl(e)
    end
  end.

Definition evalExp (e: Exp) (memory: Memory): RuntimeError + (nat + bool) :=
  match e with
  | Logic e =>
    match evalBoolExp e memory with
    | inr(b) => inr(inr b)
    | inl(e) => inl e
    end
  | Arithmetic e =>
    match evalNatExp e memory with
    | inr(n) => inr(inl n)
    | inl(e) => inl(e)
    end
  end.

Fixpoint evalImpStmt (fuel: nat)
         (stmt: Stmt)
         (memory: Memory)
         (input: StdIn)
         (output: StdOut):
  RuntimeError + (Memory * StdIn * StdOut) :=
  match fuel with
  | 0 => inl(OutOfFuel memory input output)
  | S fuel' =>
    match stmt with
    | Store x val =>
      match (evalNatExp x memory, evalExp val memory) with
      | (inr(ptr), inr(r)) =>
        inr(fun v => if eqb ptr v then Some(r) else memory v, input, output)
      | (inl(e), _) => inl(e)
      | (_, inl(e)) => inl(e)
      end
    | PrintOut val =>
      match evalExp val memory with
      | inr(r) => inr(memory, input, cons r output)
      | inl(e) => inl(e)
      end
    | InputNat x =>
      match (evalNatExp x memory) with
      | inr(ptr) =>
        inr(fun v => if eqb ptr v
                  then Some(inl( (fst(hd input)) output))
                  else memory v,
            tl input,
            output)
      | inl(e) => inl(e)
      end
    | InputBool x =>
      match (evalNatExp x memory) with
      | (inr(ptr)) =>
        inr(fun v => if eqb ptr v
                  then Some(inr( (snd(hd input)) output))
                  else memory v, tl input, output)
      | inl(e) => inl(e)
      end       
    | While cond body =>
      match evalBoolExp cond memory with
      | inr(false) => inr (memory, input, output)
      | inr(true) =>
        match eval fuel' body memory input output with
        | inr((memory', input', output')) =>
          evalImpStmt fuel' stmt memory' input' output'
        | inl(e) => inl(e)
        end
      | inl(e) => inl(e)
      end
    | IfElse cond ifBody elseBody =>
      match evalBoolExp cond memory with
      | inr(true) => eval fuel' ifBody memory input output
      | inr(false) => eval fuel' elseBody memory input output
      | inl(e) => inl(e)
      end
    end
  end
with eval (fuel: nat)
          (program: ImpLang)
          (memory: Memory)
          (input: StdIn)
          (output: StdOut):
       RuntimeError + (Memory * StdIn * StdOut) :=
       match fuel with
       | 0 => inl(OutOfFuel memory input output)
       | S fuel' =>
         match program with
         | cons stmt stmts =>
           match evalImpStmt fuel' stmt memory input output with
           | inr((memory', input', output')) =>
             eval fuel' stmts memory' input' output'
           | inl(e) => inl(e)
           end
         | nil => inr(memory, input, output)
         end
       end.

Definition InitializedMemory (p: ImpLang) : Prop :=
  forall n memory input output ptr memory',
    eval n p memory input output <> inl (UninitializedRead ptr memory').

Definition TypeSafeMemory (p: ImpLang) : Prop :=
  forall n memory input output texp ptr memory',
    eval n p memory input output <> inl (MemoryTypeError texp ptr memory').

Definition SafeMemory (p: ImpLang): Prop :=
  InitializedMemory p /\ TypeSafeMemory p.

Import ListNotations.
Definition readNatArray
           (localVarPtr: NatExp)
           (lenPtr: NatExp)
           (arrayPtr: NatExp): ImpLang :=
  [ InputNat lenPtr;
    Store localVarPtr (Arithmetic (ConstNat 0));
    While (LessEq (ReadNat localVarPtr) (Minus (ReadNat lenPtr) (ConstNat 1)))
          [ InputNat (Plus (ReadNat arrayPtr) (ReadNat localVarPtr));
            Store localVarPtr (Arithmetic (Plus (ReadNat localVarPtr) (ConstNat 1)))
          ]
  ].


