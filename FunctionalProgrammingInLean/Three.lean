/-!
# Three

Solutions to the exercises on type classes, instances and `Functor`.
-/

namespace Three

--  An alternative way to represent a positive number is as the successor of some Nat.
-- Replace the definition of Pos with a structure whose constructor is named succ
-- that contains a Nat:
structure Pos where
  succ :: (pred : Nat)

-- Define instances of Add, Mul, ToString, and OfNat that allow this version of Pos
-- to be used conveniently.

def Pos.plus : Pos -> Pos -> Pos
  | Pos.succ n, Pos.succ k => Pos.succ (n + k + 1)

instance : Add Pos where
  add := Pos.plus

#eval Pos.succ 0
#eval Pos.plus {pred := 0} {pred := 0}
#eval Pos.plus {pred := 4} {pred := 5}

instance : OfNat Pos (n+1) where
  ofNat := Pos.succ n

#eval (3 : Pos)
#eval (1 : Pos)
#eval let x := 2; (x : Pos)

def Pos.mul : Pos -> Pos -> Pos
  | Pos.succ n, Pos.succ k => Pos.succ ((n+1) * (k+1) - 1)

#eval Pos.succ 0
#eval Pos.mul {pred := 0} {pred := 0}
#eval Pos.mul {pred := 4} {pred := 5}

def Pos.toNat : Pos → Nat
  | Pos.succ n => n + 1

instance : ToString Pos where
  toString p := toString (Pos.toNat p)

#eval toString (Pos.succ 0)
#eval toString (Pos.mul (5: Pos) (6 : Pos))


-- Define a datatype that represents only even numbers.
-- Define instances of Add, Mul, and ToString that allow it to be used conveniently.
inductive Even where
  | zero
  | succ : Even -> Even

def Even.add : Even -> Even -> Even
  | Even.zero, e => e
  | Even.succ n, k => Even.succ (Even.add n k)

instance : Add Even where
  add := Even.add

def Even.mul : Even -> Even -> Even
  | Even.zero, e => e
  | Even.succ n, k => k + k + (Even.mul n k)

instance : Mul Even where
  mul := Even.mul

def Even.toNat : Even → Nat
  | Even.zero => 0
  | Even.succ n => 2 + (Even.toNat n)

instance : ToString Even where
  toString n := toString (Even.toNat n)

def zero: Even := Even.zero
def two: Even := Even.succ zero
def four: Even := Even.succ two

#eval two + two
#eval four + zero
#eval four * zero

/-
An HTTP request begins with an identification of a HTTP method, such as GET or POST,
along with a URI and an HTTP version.
Define an inductive type that represents an interesting subset of the HTTP methods,
and a structure that represents HTTP responses.
Responses should have a ToString instance that makes it possible to debug them.
Use a type class to associate different IO actions with each HTTP method,
and write a test harness as an IO action that calls each method and prints the result.
-/

inductive HttpMethod where
  | post

instance : ToString HttpMethod where
  toString
  | HttpMethod.post => "POST"

structure HttpRequest where
  method : HttpMethod
  uri : String
  version : Float

instance : ToString HttpRequest where
  toString r := "[URI: " ++ r.uri ++
                ", HTTP method: " ++ (toString r.method) ++
                ", HTTP version: " ++ (toString r.version) ++ "]"

structure HttpResponse where
  request : HttpRequest
  result : Nat
  body : String

instance : ToString HttpResponse where
  toString r := "[Result: " ++ (toString r.result) ++
                ", body: " ++ r.body ++
                ", request: " ++ (toString r.request)  ++ "]"

def runRequest (req : HttpRequest) : HttpResponse :=
  match req.method with
  | HttpMethod.post => {request := req, result := 200, body := "ok"}

def runTest : IO Unit := do
  let r : HttpRequest := {method := HttpMethod.post, uri := "http://hel.lo", version := 1.1}
  IO.println (runRequest r)

#eval runTest

/-
Write an instance of OfNat for the even number datatype from the previous section's
exercises that uses recursive instance search.
-/

instance : OfNat Even 0 where
  ofNat := Even.zero

instance [OfNat Even n] : OfNat Even (n + 2) where
  -- wtf
  ofNat := Even.succ (inferInstance : OfNat Even n).ofNat

#eval (2 : Even)
-- #eval (1 : Even)

-- There is a limit to how many times the Lean compiler will attempt a recursive instance search.
-- This places a limit on the size of even number literals defined in the previous exercise.
-- Experimentally determine what the limit is.
#eval (100 : Even)
#eval (250 : Even)
#eval (254 : Even)
-- #eval (256 : Even)


/-
Define an instance of HMul (PPoint α) α (PPoint α) that multiplies both projections by the scalar.
It should work for any type α for which there is a Mul α instance.
-/

structure PPoint (α : Type) where
  x : α
  y : α

instance [Add α] : Add (PPoint α) where
  add p1 p2 := { x := p1.x + p2.x, y := p1.y + p2.y }

--@[default_instance]
-- The default_instance attribute helps class inference to build the expected type when needed.
instance [Mul α] : HMul (PPoint α) α (PPoint α) where
  hMul p n := {x := p.x * n, y := p.y * n}

#eval {x := 2.5, y := 3.7 : PPoint Float} * 2.0
-- Without default_instance, this is HMul.hMul { x := 2.5, y := 3.7 } : ?m.2 → ?m.3
-- With default_instance, it is HMul.hMul { x := 2.5, y := 3.7 } : Float → PPoint Float
#check HMul.hMul {x := 2.5, y := 3.7 : PPoint Float}

/-
 Write an instance of HAppend (List α) (NonEmptyList α) (NonEmptyList α) and test it.
 -/

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

def NonEmptyList.hAppendOnTop (xs : List α) (ys: NonEmptyList α) : NonEmptyList α :=
  match xs with
  | [] => ys
  | x :: xs => {head := x, tail := xs ++ ys.head :: ys.tail}

@[default_instance]
instance : HAppend (List α) (NonEmptyList α) (NonEmptyList α) where
  hAppend := NonEmptyList.hAppendOnTop

def idahoSpiders : NonEmptyList String := {
  head := "Banded Garden Spider",
  tail := [
    "Long-legged Sac Spider",
    "Wolf Spider",
    "Hobo Spider",
    "Cat-faced Spider"
  ]
}

#eval [1,2] ++ [3,4]
#eval ["Violin Spider"] ++ idahoSpiders
#eval [] ++ idahoSpiders


/-
 Implement a Functor instance for the binary tree datatype.
-/
inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

def BinTree.map (f : α -> β) (xs : BinTree α) : (BinTree β) :=
  match xs with
  | leaf => leaf
  | branch left x right => branch (BinTree.map f left) (f x) (BinTree.map f right)

instance : Functor BinTree where
  map := BinTree.map

end Three
