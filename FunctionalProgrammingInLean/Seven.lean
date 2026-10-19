/-!
# Seven

Solutions to the exercises on indexed families (`Vect`) and universe design (`Finite`).
-/

namespace Seven

inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)

def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => .nil
  | k + 1 => .cons x (replicate k x)

def Vect.zip : (n : Nat) → Vect α n → Vect β n → Vect (α × β) n
  | 0, .nil, .nil => .nil
  | k + 1, .cons x xs, .cons y ys => .cons (x, y) (zip k xs ys)

-- Define a function Vect.map with type (α → β) → Vect α n → Vect β n.
def Vect.map :(f : α -> β) -> Vect α n -> Vect β n
  | _, .nil => .nil
  | f , .cons x xs => cons (f x) (map f xs)

-- Define a function Vect.zipWith that combines the entries in a Vect one at a time with a function.
-- It should have the type (α → β → γ) → Vect α n → Vect β n → Vect γ n.
def Vect.zipWith : (f : α → β → γ) -> Vect α n → Vect β n → Vect γ n
  |  _, .nil, .nil => .nil
  | f, .cons x xs, .cons y ys => .cons (f x y) (zipWith f xs ys)

-- Define a function Vect.unzip that splits a Vect of pairs into a pair of Vects.
-- It should have the type Vect (α × β) n → Vect α n × Vect β n.
def Vect.unzip: Vect (α × β) n -> Vect α n × Vect β n
  | .nil => (.nil, .nil)
  | cons (a,b) abs =>
    match unzip abs with
    | (xs, ys) => (.cons a xs, .cons b ys)

/-
Define a function Vect.push that adds an entry to the end of a Vect.
Its type should be Vect α n → α → Vect α (n + 1) and
#eval Vect.push (.cons "snowy" .nil) "peaks" should yield Vect.cons "snowy" (Vect.cons "peaks" (Vect.nil)).
-/
def Vect.push : Vect α n -> α -> Vect α (n+1)
  | .nil, a => .cons a .nil
  | .cons x .nil, a => .cons x (.cons a .nil)
  | .cons x xs, a => .cons x (push xs a)

#eval Vect.push (.cons "snowy" .nil) "peaks"
-- Vect.cons "snowy" (Vect.cons "peaks" (Vect.nil)).

--  Define a function Vect.reverse that reverses the order of a Vect.
def Vect.reverse : Vect α n -> Vect α n
| .nil => .nil
| .cons x xs => push (reverse xs) x

#eval Vect.reverse (Vect.cons "snowy" (Vect.cons "peaks" (Vect.nil)))

/-
Define a function Vect.drop with the following type: (n : Nat) → Vect α (k + n) → Vect α k.
Verify that it works by checking that
#eval danishPeaks.drop 2 yields Vect.cons "Ejer Bavnehøj" (Vect.nil).
-/

def Vect.drop : (n : Nat) → Vect α (k + n) → Vect α k
| 0, xs => xs
| i + 1, .cons _ ys => drop i ys

-- a little helper
def Vect.fromList : (xs: List α) -> Vect α (List.length xs)
| [] => .nil
| y :: ys => .cons y (fromList ys)

def danishPeaks := Vect.fromList ["Møllehøj", "Yding Skovhøj", "Ejer Bavnehøj"]

#eval danishPeaks.drop 2
-- Vect.cons "Ejer Bavnehøj" (Vect.nil)

/-
Define a function Vect.take with type (n : Nat) → Vect α (k + n) → Vect α n
that returns the first n entries in the Vect.
Check that it works on an example.
-/

def Vect.take : (n : Nat) → Vect α (k + n) → Vect α n
| 0, _ => .nil
| i + 1, .cons y ys => .cons y (take i ys)

#eval Vect.take 1 danishPeaks
#eval Vect.take 2 danishPeaks
#eval Vect.take 3 danishPeaks
-- #eval Vect.take 4 danishPeaks -- does not typecheck, as danishPeak.length = 3!


/-
Write a function that converts any value from a type coded for by Finite into a string.
Functions should be represented as their tables.
-/

/-
- Add the empty type Empty to Finite and Finite.beq.
- Add Option to Finite and Finite.beq.
-/

inductive Finite where
  | empty : Finite
  | unit : Finite
  | bool : Finite
  | option : Finite -> Finite
  | pair : Finite → Finite → Finite
  | arr : Finite → Finite → Finite

abbrev Finite.asType : Finite → Type
  | .empty => Empty
  | .unit => Unit
  | .bool => Bool
  | .option t => Option (asType t)
  | .pair t1 t2 => asType t1 × asType t2
  | .arr dom cod => asType dom → asType cod

def List.product (xs : List α) (ys : List β) : List (α × β) := Id.run do
  let mut out : List (α × β) := []
  for x in xs do
    for y in ys do
      out := (x, y) :: out
  pure out.reverse

mutual
  def Finite.enumerate (t : Finite) : List t.asType :=
    match t with
    | .empty => []
    | .unit => [()]
    | .bool => [true, false]
    | .option t => none :: (Option.some <$> t.enumerate)
    | .pair t1 t2 => List.product t1.enumerate t2.enumerate
    | .arr dom cod => dom.functions cod.enumerate

  def Finite.functions
      (t : Finite)
      (results : List α) : List (t.asType → α) :=
    match t with
  | .empty => []
  | .unit =>
    results.map fun r =>
      fun () => r
  | .bool =>
    (List.product results results).map fun (r1, r2) =>
      fun
        | true => r1
        | false => r2
  | .option t => results.map fun x =>
    fun
    | some _ => x
    | none => x
  | .pair t1 t2 =>
    let f1s := t1.functions <| t2.functions results
    f1s.map fun f =>
      fun (x, y) =>
        f x y
  | .arr t1 t2 =>
    let args := t1.enumerate
    let base :=
      results.map fun r =>
        fun _ => r
    args.foldr
      (fun arg rest =>
        (t2.functions rest).map fun more =>
          fun f => more (f arg) f)
      base
end

def Finite.stringify {t : Finite} : (v: t.asType) -> String :=
match t with
| .empty => fun _ => ""
| .unit => fun _ => "()"
| .bool => fun b => toString b
| .option _ => fun
  | some x => "some " ++ stringify x
  | none => "none"
| .pair _ _ => fun p => "(" ++ stringify p.fst ++ ", " ++ stringify p.snd ++ ")"
| .arr dom cod => fun _ =>
    let table := List.map
      (fun p => "(" ++ stringify p.fst ++ " ->" ++ stringify p.snd ++ ")")
      (List.product dom.enumerate cod.enumerate)
  "[" ++ String.intercalate ", " table ++ "]"

#eval @Finite.stringify Finite.unit ()
#eval @Finite.stringify Finite.bool true
#eval @Finite.stringify (Finite.pair Finite.unit Finite.bool) ((), false)

def Finite.beq (t : Finite) (x y : t.asType) : Bool :=
  match t with
  -- no need for .empty, as there cannot be values of type Empty
  | .unit => true
  | .bool => x == y
  | .option t => match x, y with
    | some a, some b => beq t a b
    | _, _ => false
  | .pair t1 t2 => beq t1 x.fst y.fst && beq t2 x.snd y.snd
  | .arr dom cod =>
    dom.enumerate.all fun arg => beq cod (x arg) (y arg)

end Seven
