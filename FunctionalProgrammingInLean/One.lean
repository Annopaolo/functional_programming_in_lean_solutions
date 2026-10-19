/-!
# One

Solutions to the exercises on structures, polymorphism, `Option` and sums/products.
-/

namespace One

-- joinStringsWith with type String → String → String → String
-- that creates a new string by placing its first argument between
-- its second and third arguments.
-- joinStringsWith ", " "one" "and another" should evaluate to "one, and another".
def joinStringsWith (separator : String) (first: String) (second : String) : String :=
String.append first (String.append separator second)

#eval joinStringsWith ", " "one" "and another"

-- Define a function volume with type Nat → Nat → Nat → Nat that computes the volume
-- of a rectangular prism with the given height, width, and depth.
def volume' (height: Nat) (width: Nat) (depth: Nat) : Nat :=
  height * width * depth

#eval volume' 2 3 4

-- Define a structure named RectangularPrism that contains
-- the height, width, and depth of a rectangular prism, each as a Float.
structure RectangularPrism where
  height: Float
  width: Float
  depth: Float

-- Define a function named volume : RectangularPrism → Float
-- that computes the volume of a rectangular prism.
def volume (rp: RectangularPrism) : Float :=
  rp.height * rp.width * rp.depth

-- Define a structure named Segment that represents a line segment
-- by its endpoints, and define a function
-- length : Segment → Float that computes the length
-- of a line segment. Segment should have at most two fields.
structure Point2D where
  x : Float
  y : Float

structure Segment where
  start : Point2D
  finish : Point2D

def length (s: Segment)  : Float :=
  Float.sqrt ((s.start.x - s.finish.x)^2 + (s.start.y - s.finish.y)^2)

#eval length {start := {x := 0, y := 1}, finish := {x := 1, y:= 0}}

--  Write a function to find the last entry in a list. It should return an Option.
def last? {α: Type} (l : List α) : Option α :=
match l with
  | [] => none
  | x :: [] => some x
  | _ :: xs => last? xs

#eval last? [1]
#eval last? [1,2]
#eval last? ([] : List Int)

def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=
  match xs with
  |  [] => none
  | x :: xs => if predicate x then some x else (List.findFirst? xs predicate)

-- Using the analogy between types and arithmetic, write a function that
-- distributes products over sums. In other words, it should have type
-- α × (β ⊕ γ) → (α × β) ⊕ (α × γ)
def prodOverSum : α × (β ⊕ γ) → (α × β) ⊕ (α × γ)
-- wtfff
| (a, Sum.inl b) => @Sum.inl _ (α × γ) (a, b)
| (a, Sum.inr g) => @Sum.inr (α × β) _ (a, g)

def prodOverSum2 (x : α × (β ⊕ γ)) : (α × β) ⊕ (α × γ) :=
match x with
  | (a, Sum.inl b) => @Sum.inl (α × β) (α × γ) (a,b)
  | (a, Sum.inr g) => @Sum.inr (α × β) (α × γ) (a,g)

-- Using the analogy between types and arithmetic, write a function that turns multiplication by two into a sum.
-- In other words, it should have type Bool × α → α ⊕ α
def boolToSum : Bool × α → α ⊕ α
| (_, a) => @Sum.inl α α a

end One
