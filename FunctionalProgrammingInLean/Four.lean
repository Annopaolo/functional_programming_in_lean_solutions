/-!
# Four

Solutions to the exercises on monads, applicatives and the `Reader`/`WithLog`/`Validate` examples.
-/

namespace Four

/-
 Define a function BinTree.mapM. By analogy to mapM for lists,
 this function should apply a monadic function to each data entry in a tree,
 as a preorder traversal.
 The type signature should be:
 def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
-/
inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
| .leaf => pure leaf
| .branch left x right =>
   f x >>= fun x' =>
   BinTree.mapM f left >>= fun left' =>
   BinTree.mapM f right >>= fun right' =>
   pure (branch left' x' right')

/-
 First, write a convincing argument that the Monad instance for Option satisfies the monad contract.
 Then, consider the following instance:
  instance : Monad Option where
    pure x := some x
    bind opt next := none

  Both methods have the correct type. Why does this instance violate the monad contract?

  The monad contract is comprised of three laws:
  - bind (pure v) f = f v
  - bind v pure = v
  - bind (bind v f) g = bind v (fun x => bind (f x) g)

  The standard monad instance for Option is
  instance : Monad Option where
    pure x := some x
    bind opt next :=
      match opt with
      | none => none
      | some x => next x

  The first law is respected by executing it:
  - bind (pure v) f ==> bind (some v) f ==> f v
    Note that this breaks with the non-standard definition!
    The first step results in bind (none) instead of bind (some v)

  Running the second law:
  - bind v pure ==> none = v                  <-(case v is none)
              |===> pure x ==> some x = v     <- (case v is some x)

  For the third law, it typechecks
-/


/-
 Check the monad contract for State σ and Except ε.
-/

/-
 Adapt the reader monad example so that it can also indicate failure when the custom operator is not defined,
 rather than just returning zero. In other words, given these definitions:

    def ReaderOption (ρ : Type) (α : Type) : Type := ρ → Option α

    def ReaderExcept (ε : Type) (ρ : Type) (α : Type) : Type := ρ → Except ε α

  do the following:
  - Write suitable pure and bind functions
  - Check that these functions satisfy the Monad contract
  - Write Monad instances for ReaderOption and ReaderExcept
  - Define suitable applyPrim operators and test them with evaluateM on some example expressions
-/

def ReaderOption (ρ : Type) (α : Type) : Type := ρ → Option α

def ReaderOption.pure (x : α) : ReaderOption ρ α := fun _ => some x

def ReaderOption.bind (result : ReaderOption ρ α) (next : α -> ReaderOption ρ β) : ReaderOption ρ β :=
  fun a => match result a with
  | none => none
  | some x => next x a

#check ReaderOption.bind (ReaderOption.pure (5 : Int)) (fun x : Int => (fun _ => some x))
#check (fun x : Int => (fun _ => some x)) (5 : Int)

/-
First law:
  ReaderOption.bind (ReaderOption.pure v) f = f v
  Note that f has type α -> β -> Option α in order to typecheck and
  indeed, β -> Option α is the type of ReaderOption β α. That said, let's run a computation:

    ReaderOption.bind (fun _ => some v) (fun a' => fun b' => some a') ===>

    fun a =>
      match (fun _ => some v) a with
      | none => none
      | some x => (fun a' => fun b' => some a') x a                   ===>

    fun a => (fun a' => fun b' => some a') v a                        ===>

    fun a => some v [·]

  Now the application f v:
    (fun a' => fun b' => some a') v  ===>

    fun b' => some v
  which is exactly the same function, as a and b' respectively are unused
-/

#check ReaderOption.bind (fun x => some x) ReaderOption.pure

/-
Second law:
  ReaderOption.bind v ReaderOption.pure = v
  In order to typecheck, v must have type (ρ -> Option γ), i.e. ReaderOption ρ γ
  Let's run:

    ReaderOption.bind (fun _ => some y) ReaderOption.pure ===>

    fun a =>
      match (fun _ => some y) a with
      | none => none
      | some x => ReaderOption.pure x a                   ===>

    fun a => ReaderOption.pure y a                        ===>

    fun a => (fun _ => some y) a                          ===>

    fun a => some y [·]

  Just as before, we have that a and _ are equivalent, as they are unused.
-/

#check ReaderOption.bind (ReaderOption.bind (fun _ => some 1) (fun x => (fun _ => some x)) ) (fun x => (fun _ => some x))
#check ReaderOption.bind (fun _ => some 1) (fun x => ReaderOption.bind ((fun x' => (fun _ => some x')) x) (fun x'' => (fun _ => some x'')))

/-
Third law:
  ReaderOption.bind (ReaderOption.bind v f) g = ReaderOption.bind v (fun x => ReaderOption.bind (f x) g)
  It typechecks, so I'd say it's ok.
-/

instance : Monad (ReaderOption ρ) where
  pure := ReaderOption.pure
  bind := ReaderOption.bind


def ReaderExcept (ε : Type) (ρ : Type) (α : Type) : Type := ρ → Except ε α

def ReaderExcept.pure (x : α) : ReaderExcept ε ρ α := fun _ => Except.ok x

def ReaderExcept.bind (result : ReaderExcept ε ρ α) (next : α -> ReaderExcept ε ρ β) : ReaderExcept ε ρ β :=
  fun a => match result a with
  | Except.error e => Except.error e
  | Except.ok x => next x a

#check ReaderExcept.pure 5
#check ReaderExcept.bind (ReaderExcept.pure 5) (fun x => (fun _ => Except.ok x))
#check fun x => (fun _ => Except.ok x) 5

/-
For Monad contracts, everything typechecks so we can safely apply the same reasoning as ReaderOption.
-/

instance : Monad (ReaderExcept ρ ε) where
  pure := ReaderExcept.pure
  bind := ReaderExcept.bind

/-
  Example: Arithmetic
-/

inductive Expr (op : Type) where              -- it's parametrized by the type of operations
  | const : Int → Expr op                     -- a number
  | prim : op → Expr op → Expr op → Expr op   -- an operation

inductive Arith where
  | plus
  | minus
  | times
  | div

open Expr in
open Arith in
def fourteenDivided : Expr Arith :=           -- 14 / (45 - (9*5))
  prim div (const 14)
    (prim minus (const 45)
      (prim times (const 5)
        (const 9)))

-- In this case, return none when dividing by 0
def applyDivOption (x : Int) (y : Int) : Option Int :=
    if y == 0 then
      none
    else pure (x / y)

-- In this case, return an helpful error when dividing by 0
def applyDivExcept (x : Int) (y : Int) : Except String Int :=
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

-- The run of operations is parametrized by the monad to use for handling division (by 0)
def applyPrim' [Monad m]
    (applyDiv : Int → Int → m Int) :
    Arith → Int → Int → m Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y => applyDiv x y

-- The evaluator is parametrized by the monad to use for handling division (by 0)
-- and the function to run on binary operations
def evaluateM' [Monad m]
    (applyDiv : Int → Int → m Int) :
    Expr Arith → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM' applyDiv e1 >>= fun v1 =>
    evaluateM' applyDiv e2 >>= fun v2 =>
    applyPrim' applyDiv p v1 v2

#eval evaluateM' applyDivOption fourteenDivided
#eval evaluateM' applyDivExcept fourteenDivided

--  Now, let's add more effects!
-- Start by isolating all "special" operations (e.g. division) in a type
inductive Prim (special : Type) where
  | plus
  | minus
  | times
  | other : special → Prim special

inductive CanFail where         -- division is special in the sense that it can fail
  | div

def divOption : CanFail → Int → Int → Option Int
  | CanFail.div, x, y => if y == 0 then none else some (x / y)

def divExcept : CanFail → Int → Int → Except String Int
  | CanFail.div, x, y =>
      if y == 0 then
        Except.error s!"Tried to divide {x} by zero"
      else pure (x / y)

-- Now the apply function is also parametrized on the type of the special operations!
def applyPrim [Monad m]
    (applySpecial : special → Int → Int → m Int) :
      Prim special → Int → Int → m Int
  | Prim.plus, x, y => pure (x + y)
  | Prim.minus, x, y => pure (x - y)
  | Prim.times, x, y => pure (x * y)
  | Prim.other op, x, y => applySpecial op x y      -- There's no mention of the actual operation

-- The evaluator is now accepting expressions parametrized on the type of special operations
def evaluateM [Monad m]
    (applySpecial : special -> Int → Int → m Int) : Expr (Prim special) → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM applySpecial e1 >>= fun v1 =>
    evaluateM applySpecial e2 >>= fun v2 =>
    applyPrim applySpecial p v1 v2

-- Special effect: do nothing
def applyEmpty [Monad m] (op : Empty) (_ : Int) (_ : Int) : m Int :=
  nomatch op

open Expr Prim in
#eval evaluateM (m := Id) applyEmpty (prim plus (const 5) (const (-14)))

-- Special effect: reading the name of a primitive function (a) from an environment (r).
-- In this case, we have:
-- - constants evaluate to constant functions fun _ => c
-- - primitive operators pass down the env: e.g. e₁ + e₂ becomes fun env => e₁(env) + e₂(env)
-- - custom operators are looked up in the environment: e.g."max(e)" becomes f(e) where f is lookup("max", env)
-- To define the reader monad in Lean, the first step is to define the Reader type...
def Reader (ρ : Type) (α : Type) : Type := ρ → α
-- ...and the effect that allows users to get a hold of the env
def read : Reader ρ ρ := fun env => env

def Reader.pure (x : α) : Reader ρ α := fun _ => x

def Reader.bind  (lookup: Reader ρ α) (next: α -> Reader ρ β) : Reader ρ β :=
  fun env => next (lookup env) env

instance : Monad (Reader ρ) where
  pure := Reader.pure
  bind := Reader.bind

-- Our custom env: a list of function associated to strings
abbrev Env : Type := List (String × (Int → Int → Int))

def exampleEnv : Env := [("max", max), ("mod", (· % ·))]

-- How to use the Reader? Simply read the operator name from the environment!
def applyPrimReader (op : String) (x : Int) (y : Int) : Reader Env Int :=
read >>= fun env => match List.lookup op env with
| none => pure 0
| some f => pure (f x y)

open Expr Prim in
#eval
  evaluateM applyPrimReader
    (prim (other "max") (prim plus (const 5) (const 4))
      (prim times (const 3)
        (const 2)))
    exampleEnv

/-
 Define suitable applyPrim operators for ReaderOption and ReaderException
 and test them with evaluateM on some example expressions.
-/

def readOption : ReaderOption ρ ρ := fun env => env

#check readOption

-- In the case of ReaderOption, if none is found, we return none in the ReaderOption monad
def applyPrimReaderOption (op : String) (x : Int) (y : Int) : ReaderOption Env Int :=
-- (this is the same as readOption >>= fun..., as the >>= is just a shorthand)
ReaderOption.bind readOption fun env => match List.lookup op env with
| none => fun _ => none
| some f => pure (f x y)

open Expr Prim in
#eval
  evaluateM applyPrimReaderOption
    (prim (other "max") (prim plus (const 5) (const 4))
      (prim times (const 3)
        (const 2)))
    exampleEnv

open Expr Prim in
#eval
  evaluateM applyPrimReaderOption
    (prim (other "pippo") (prim plus (const 5) (const 4))
      (prim times (const 3)
        (const 2)))
    exampleEnv

-- This is much much easier, and it's the same thing when evaluateM'd
def applyPrimReaderOption' (op : String) (x : Int) (y : Int) : ReaderOption Env Int :=
fun env => match List.lookup op env with
| none => none
| some f => pure (f x y)

open Expr Prim in
#eval
  evaluateM applyPrimReaderOption'
    (prim (other "max") (prim plus (const 5) (const 4))
      (prim times (const 3)
        (const 2)))
    exampleEnv

open Expr Prim in
#eval
  evaluateM applyPrimReaderOption'
    (prim (other "pippo") (prim plus (const 5) (const 4))
      (prim times (const 3)
        (const 2)))
    exampleEnv

def readExcept : ReaderExcept ε ρ ρ := fun env => Except.ok env

#check readExcept

-- In the case of ReaderOption, if none is found, we return none in the ReaderOption monad
def applyPrimReaderExcept (op : String) (x : Int) (y : Int) : ReaderExcept String Env Int :=
-- (this is the same as readOption >>= fun..., as the >>= is just a shorthand)
ReaderExcept.bind readExcept fun env => match List.lookup op env with
| none => fun _ => Except.error s!"I don't know {op}!"
| some f => pure (f x y)

open Expr Prim in
#eval
  evaluateM applyPrimReaderExcept
    (prim (other "max") (prim plus (const 5) (const 4))
      (prim times (const 3)
        (const 2)))
    exampleEnv

open Expr Prim in
#eval
  evaluateM applyPrimReaderExcept
    (prim (other "pippo") (prim plus (const 5) (const 4))
      (prim times (const 3)
        (const 2)))
    exampleEnv

/-
 The WithLog type can be used with the evaluator to add optional tracing of some operations.
-/

structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α

-- In particular, the type ToTrace can serve as a signal to trace a given operator
inductive ToTrace (α : Type) : Type where
  | trace : α → ToTrace α

/-
For the tracing evaluator, expressions should have type Expr (Prim (ToTrace (Prim Empty))).
This says that the operators in the expression consist of addition, subtraction, and multiplication,
augmented with traced versions of each.
The innermost argument is Empty to signal that there are no further special operators inside of trace,
only the three basic ones.

- Implement a Monad (WithLog logged) instance

- Write an applyTraced function to apply traced operators to their arguments,
  logging both the operator and the arguments, with type
  ToTrace (Prim Empty) → Int → Int → WithLog (Prim Empty × Int × Int) Int
-/

-- Hint: values of type Prim Empty will appear in the resulting log.
-- In order to display them as a result of #eval, the following instances are required:
deriving instance Repr for WithLog
deriving instance Repr for Empty
deriving instance Repr for Prim

def WithLog.pure (data: α) : WithLog logged α :=
  {log := [], val := data}

def WithLog.bind (current: WithLog logged α) (next: α -> WithLog logged β) : WithLog logged β :=
  match next (current.val) with
  | {log := log, val := val} => {log := current.log ++ log, val := val}

instance : Monad (WithLog logged) where
  pure := WithLog.pure
  bind := WithLog.bind

-- How to use the WithLog tracer? Simply put the current expression in the `log` list!
-- IT IS BIND THE ONE THAT DOES THE ACCUMULATION OF LOGS AAAAAAAAAAAAAAAAAAAAAAAAAAAA
-- 𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸𝔸
def applyTraced (exp : ToTrace (Prim Empty)) (x : Int) (y : Int) : WithLog (Prim Empty × Int × Int) Int :=
  match exp with
  | .trace Prim.plus => {log := [(Prim.plus, x, y)], val := x + y}
  | .trace Prim.minus => {log := [(Prim.minus, x, y)], val := x - y}
  | .trace Prim.times => {log := [(Prim.times, x, y)], val := x * y}

open Expr Prim ToTrace in
#eval applyTraced (trace plus) 4 5

open Expr Prim ToTrace in
#eval evaluateM applyTraced (prim (other (trace minus)) (const 1) (const 2))

open Expr Prim ToTrace in
#eval
  evaluateM applyTraced
      (prim (other (trace plus)) (const 1)
      (prim (other (trace minus)) (const 3)
        (const 4)))

open Expr Prim ToTrace in
#eval
  evaluateM applyTraced
    (prim (other (trace times))
      (prim (other (trace plus)) (const 1)
        (const 2))
      (prim (other (trace minus)) (const 3)
        (const 4)))


/-
- Rewrite evaluateM, its helpers, and the different specific use cases using do-notation instead of explicit calls to >>=.
- Rewrite firstThirdFifthSeventh using nested actions.
-/
-- no do-notation here
def applyPrim'' [Monad m]
    (applySpecial : special → Int → Int → m Int) :
      Prim special → Int → Int → m Int
  | Prim.plus, x, y => pure (x + y)
  | Prim.minus, x, y => pure (x - y)
  | Prim.times, x, y => pure (x * y)
  | Prim.other op, x, y => applySpecial op x y      -- There's no mention of the actual operation

def evaluateM'' [Monad m]
    (applySpecial : special -> Int → Int → m Int) : Expr (Prim special) → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 => do
      let v1 <- evaluateM'' applySpecial e1
      let v2 <- evaluateM'' applySpecial e2
      applyPrim'' applySpecial p v1 v2

def applyPrimReader'' (op : String) (x : Int) (y : Int) : Reader Env Int :=
do
  let env <- read
  match List.lookup op env with
   | none => pure 0
   | some f => pure (f x y)

def applyPrimReaderExcept'' (op : String) (x : Int) (y : Int) : ReaderExcept String Env Int :=
do
  let env <- readExcept
  match List.lookup op env with
  | none => fun _ => Except.error s!"I don't know {op}!"
  | some f => pure (f x y)

def firstThirdFifthSeventh'' [Monad m] (lookup : List α → Nat → m α)
    (xs : List α) : m (α × α × α × α) := do
  pure (← lookup xs 0, ← lookup xs 2, ← lookup xs 4, ← lookup xs 6)



/-
 * Replace the `NonEmptyList` in `Validate.errors` with a bare type variable,
   and then update the definitions of the `Applicative (Validate ε)`
   and `OrElse (Validate ε α)` instances to require only that there be an `Append ε` instance available.
 * Define a function {anchorTerm misc}`Validate.mapErrors : Validate ε α → (ε → ε') → Validate ε' α` that transforms all the errors in a validation run.
-/

structure RawInput where
  name : String
  birthYear : String

structure CheckedInput (thisYear : Nat) : Type where
  name : {n : String // n ≠ ""}
  birthYear : {y : Nat // y > 1900 ∧ y ≤ thisYear}

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

deriving instance Repr for NonEmptyList

def NonEmptyList.hAppendOnTop (xs : List α) (ys: NonEmptyList α) : NonEmptyList α :=
  match xs with
  | [] => ys
  | x :: xs => {head := x, tail := xs ++ ys.head :: ys.tail}

instance : HAppend (List α) (NonEmptyList α) (NonEmptyList α) where
  hAppend := NonEmptyList.hAppendOnTop

instance : HAppend (NonEmptyList α) (NonEmptyList α) (NonEmptyList α) where
  hAppend xs ys := {head := xs.head, tail := xs.tail ++ ys.head :: ys.tail}

inductive Validate (ε α : Type) : Type where
  | ok : α → Validate ε α
  | errors : ε → Validate ε α

deriving instance Repr for Validate

instance : Functor (Validate ε) where
  map f
   | .ok x => .ok (f x)
   | .errors errs => .errors errs

instance [Append ε]: Applicative (Validate ε) where
  pure := .ok
  seq f x :=
    match f with
    | .ok g => g <$> (x ())
    | .errors errs =>
      match x () with
      | .ok _ => .errors errs
      | .errors errs' => .errors (errs ++ errs')

def Validate.orElse [Append ε]
    (a : Validate ε α)
    (b : Unit → Validate ε α) :
    Validate ε α :=
  match a with
  | .ok x => .ok x
  | .errors errs1 =>
    match b () with
    | .ok x => .ok x
    | .errors errs2 => .errors (errs1 ++ errs2)

instance[Append ε] : OrElse (Validate ε α) where
  orElse := Validate.orElse

def Validate.mapErrors (a: Validate ε α) (f: ε → ε') : Validate ε' α :=
  match a with
  | .ok x => .ok x
  | .errors errs1 => .errors (f errs1)

end Four
