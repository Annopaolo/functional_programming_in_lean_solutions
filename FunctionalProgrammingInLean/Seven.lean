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

namespace TypedQueries

structure Date where
  day: Nat
  month: Nat
  year: Nat
deriving Repr, BEq

inductive DBType where
  | int | string | bool | date

abbrev DBType.asType : DBType → Type
  | .int => Int
  | .string => String
  | .bool => Bool
  | .date => Date

def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  match t with
  | .int => x == y
  | .string => x == y
  | .bool => x == y
  | .date => x == y

instance {t : DBType} : BEq t.asType where
  beq := t.beq

instance : BEq DBType where
  beq
    | .int, .int => true
    | .string, .string => true
    | .bool, .bool => true
    | .date, .date => true
    | _, _ => false

instance {t : DBType} : Repr t.asType where
  reprPrec := --reprPrec takes operator precedence into account
    match t with
    | .int => reprPrec
    | .string => reprPrec
    | .bool => reprPrec
    | .date => reprPrec

/-
 Add support for nullable columns to the query language
 by representing database types with the following structure:
-/
structure NDBType where
  underlying : DBType
  nullable : Bool

-- Defined by pattern matching rather than with `if`: an `if` does not
-- reduce during instance search, so e.g. `OfNat` and `BEq` instances
-- for non-nullable columns could not be found.
abbrev NDBType.asType : NDBType → Type
  | ⟨t, true⟩ => Option t.asType
  | ⟨t, false⟩ => t.asType

instance {t : NDBType} : BEq t.asType where
  beq :=
    match t with
    | ⟨_, true⟩ => (· == ·)
    | ⟨_, false⟩ => (· == ·)

instance {t : NDBType} : Repr t.asType where
  reprPrec :=
    match t with
    | ⟨_, true⟩ => reprPrec
    | ⟨_, false⟩ => reprPrec

-- View any value (nullable or not) as an `Option`, where `none` is NULL
def NDBType.toOption {t : NDBType} (v : t.asType) : Option t.underlying.asType :=
  match t, v with
  | ⟨_, true⟩, v => v
  | ⟨_, false⟩, v => some v

-- SQL: an operator applied to a NULL operand yields NULL
def NDBType.lift2 {u v w : DBType} (f : u.asType → v.asType → w.asType) :
    {n1 n2 : Bool} →
    NDBType.asType ⟨u, n1⟩ → NDBType.asType ⟨v, n2⟩ → NDBType.asType ⟨w, n1 || n2⟩
  | false, false, x, y => f x y
  | false, true, x, y => Option.map (f x) y
  | true, false, x, y => Option.map (f · y) x
  | true, true, x, y => Option.bind x fun x' => Option.map (f x') y

-- SQL's three-valued AND: FALSE wins over NULL
def NDBType.and3 :
    {n1 n2 : Bool} →
    NDBType.asType ⟨.bool, n1⟩ → NDBType.asType ⟨.bool, n2⟩ →
    NDBType.asType ⟨.bool, n1 || n2⟩
  | false, false, x, y => x && y
  | false, true, true, y | true, false, y, true => y
  | false, true, false, _ | true, false, _, false => some false
  | true, true, x, y =>
    match x, y with
    | some false, _ | _, some false => some false
    | some true, some true => some true
    | _, _ => none
/-
Use this type in place of DBType in Column and DBExpr,
and look up SQL's rules for NULL and comparison operators
to determine the types of DBExpr's constructors.
-/

structure Column where
  name : String
  contains : NDBType

abbrev Schema := List Column

abbrev Row : Schema → Type
  | [] => Unit
  | [col] => col.contains.asType
  | col1 :: col2 :: cols => col1.contains.asType × Row (col2::cols)

abbrev Table (s : Schema) := List (Row s)

--  For example, a diary of visits to mountain peaks can be represented with the schema peak:
abbrev peak : Schema := [
  ⟨"name", .string, false⟩,
  ⟨"location", .string, false⟩,
  ⟨"elevation", .int, false⟩,
  ⟨"lastVisited", .int, false⟩
]

def mountainDiary : Table peak := [
  ("Mount Nebo",       "USA",     (3637 : Int), (2013: Int)),
  ("Moscow Mountain",  "USA",     (1519 : Int), (2015 : Int)),
  ("Himmelbjerget",    "Denmark",  (147: Int), (2004: Int)),
  ("Mount St. Helens", "USA",     (2549 : Int), (2010: Int))
]

def Row.bEq (r1 r2 : Row s) : Bool :=
  match s with
  | [] => true
  | [_] => r1 == r2
  | _::_::_ =>
    match r1, r2 with
    | (v1, r1'), (v2, r2') =>
      v1 == v2 && bEq r1' r2'

instance : BEq (Row s) where
  beq := Row.bEq

inductive HasCol : Schema → String → NDBType → Type where
  | here : HasCol (⟨name, t⟩ :: _) name t
  | there : HasCol s name t → HasCol (_ :: s) name t

#check (HasCol.there (.there .here))

def Row.get (row : Row s) (col : HasCol s n t) : t.asType :=
  match s, col, row with
  | [_], .here, v => v
  | _::_::_, .here, (v, _) => v
  | _::_::_, .there next, (_, r) => get r next

inductive Subschema : Schema → Schema → Type where
  | nil : Subschema [] bigger
  | cons :
      HasCol bigger n t →
      Subschema smaller bigger →
      Subschema (⟨n, t⟩ :: smaller) bigger

abbrev travelDiary : Schema :=
  [⟨"name", .string, false⟩, ⟨"location", .string, false⟩, ⟨"lastVisited", .int, false⟩]

example : Subschema travelDiary peak :=
  .cons .here
    (.cons (.there .here)
      (.cons (.there (.there (.there .here))) .nil))

abbrev waterfall : Schema := [
  ⟨"name", .string, false⟩,
  ⟨"location", .string, false⟩,
  ⟨"lastVisited", .int, false⟩
]
def waterfallDiary : Table waterfall := [
  ("Multnomah Falls", "USA", (2018 : Int)),
  ("Shoshone Falls",  "USA", (2014 : Int))
]

example : Subschema [] peak := by constructor

example : Subschema [⟨"location", .string, false⟩] peak := by
  constructor
  constructor
  constructor
  constructor

-- Same, but without tactics
example : Subschema [⟨"location", .string, false⟩] peak :=
  .cons (.there .here) .nil

-- Same, but repeats the constructor tactic any needed number of times
example : Subschema [⟨"location", .string, false⟩] peak := by repeat constructor

def Subschema.addColumn :
    Subschema smaller bigger →
    Subschema smaller (c :: bigger)
  | .nil  => .nil
  | .cons col sub' => .cons (.there col) sub'.addColumn

def Subschema.reflexive : (s : Schema) → Subschema s s
  | [] => .nil
  | _ :: cs => .cons .here (reflexive cs).addColumn

def Row.project (row : Row s) : (s' : Schema) → Subschema s' s → Row s'
  | [], .nil => ()
  | [_], .cons c .nil => row.get c
  | _::_::_, .cons c cs => (row.get c, row.project _ cs)

-- Following SQL, comparing with NULL yields NULL, so the result of
-- `eq`, `lt` and `and` is nullable as soon as one of the operands is.
-- Constants are never NULL; NULL is written with its own constructor.
inductive DBExpr (s : Schema) : NDBType → Type where
  | col (n : String) (loc : HasCol s n t) : DBExpr s t
  | eq (e1 : DBExpr s ⟨t, n1⟩) (e2 : DBExpr s ⟨t, n2⟩) : DBExpr s ⟨.bool, n1 || n2⟩
  | lt (e1 : DBExpr s ⟨.int, n1⟩) (e2 : DBExpr s ⟨.int, n2⟩) : DBExpr s ⟨.bool, n1 || n2⟩
  | and (e1 : DBExpr s ⟨.bool, n1⟩) (e2 : DBExpr s ⟨.bool, n2⟩) : DBExpr s ⟨.bool, n1 || n2⟩
  | isNull (e : DBExpr s ⟨t, true⟩) : DBExpr s ⟨.bool, false⟩
  | const : t.asType → DBExpr s ⟨t, false⟩
  | null : DBExpr s ⟨t, true⟩

-- The nullability is left as `_`: Lean cannot solve `?n1 || ?n2 =?= false`,
-- so writing `false` would stop the schema `peak` from reaching the `by` blocks.
-- With `_` it is inferred from the columns (here it reduces to `false`).
def tallInDenmark :=
  (.and (.lt (.const 1000) (.col "elevation" (by repeat constructor)))
        (.eq (.col "location" (by repeat constructor)) (.const "Denmark"))
    : DBExpr peak ⟨.bool, _⟩)

macro "c!" n:term : term => `(DBExpr.col $n (by repeat constructor))

-- same as before, but shorter thanks to c! macro
def tallInDenmark' :=
  (.and (.lt (.const 1000) (c! "elevation"))
        (.eq (c! "location") (.const "Denmark"))
    : DBExpr peak ⟨.bool, _⟩)

def DBExpr.evaluate (row : Row s) : DBExpr s t → t.asType
  | .col _ loc => row.get loc
  | .eq e1 e2  => NDBType.lift2 (· == ·) (evaluate row e1) (evaluate row e2)
  | .lt e1 e2  => NDBType.lift2 (· < ·) (evaluate row e1) (evaluate row e2)
  | .and e1 e2 => NDBType.and3 (evaluate row e1) (evaluate row e2)
  | .isNull e => (evaluate row e).isNone
  | .const v => v
  | .null => none

-- SQL's WHERE keeps a row only if the condition is TRUE (not FALSE nor NULL)
def DBExpr.holds (row : Row s) (e : DBExpr s ⟨.bool, n⟩) : Bool :=
  (e.evaluate row |> NDBType.toOption) == some true

#eval tallInDenmark.evaluate ("Valby Bakke", "Denmark", 31, 2023)
#eval tallInDenmark.evaluate ("Fictional mountain", "Denmark", 1230, 2023)
#eval tallInDenmark.evaluate ("Mount Borah", "USA", 3859, 1996)

def disjoint [BEq α] (xs ys : List α) : Bool :=
  not (xs.any ys.contains || ys.any xs.contains)

def Schema.renameColumn : (s : Schema) → HasCol s n t → String → Schema
  | c :: cs, .here, n' => {c with name := n'} :: cs
  | c :: cs, .there next, n' => c :: renameColumn cs next n'

inductive Query : Schema → Type where
  | table : Table s → Query s
  | union : Query s → Query s → Query s
  | diff : Query s → Query s → Query s
  | select : Query s → DBExpr s ⟨.bool, n⟩ → Query s
  | project :
    Query s → (s' : Schema) →
    Subschema s' s →
    Query s'
  | product :
    Query s1 → Query s2 →
    disjoint (s1.map Column.name) (s2.map Column.name) →
    Query (s1 ++ s2)
  | renameColumn :
    Query s → (c : HasCol s n t) → (n' : String) →
    !((s.map Column.name).contains n') →
    Query (s.renameColumn c n')
  | prefixWith :
    (n : String) → Query s →
    Query (s.map fun c => {c with name := n ++ "." ++ c.name})

def addVal (v : c.contains.asType) (row : Row s) : Row (c :: s) :=
  match s, row with
  | [], () => v
  | c' :: cs, v' => (v, v')

def Row.append (r1 : Row s1) (r2 : Row s2) : Row (s1 ++ s2) :=
  match s1, r1 with
  | [], () => r2
  | [_], v => addVal v r2
  | _::_::_, (v, r') => (v, r'.append r2)

def Table.cartesianProduct (table1 : Table s1) (table2 : Table s2) :
    Table (s1 ++ s2) :=
  table1.flatMap fun r1 => table2.map r1.append

def List.without [BEq α] (source banned : List α) : List α :=
  source.filter fun r => !(banned.contains r)

def Row.rename (c : HasCol s n t) (row : Row s) :
    Row (s.renameColumn c n') :=
  match s, row, c with
  | [_], v, .here => v
  | _::_::_, (v, r), .here => (v, r)
  | _::_::_, (v, r), .there next => addVal v (r.rename next)

def prefixRow (row : Row s) :
    Row (s.map fun c => {c with name := n ++ "." ++ c.name}) :=
  match s, row with
  | [], _ => ()
  | [_], v => v
  | _::_::_, (v, r) => (v, prefixRow r)

def Query.exec : Query s → Table s
  | .table t => t
  | .union q1 q2 => exec q1 ++ exec q2
  | .diff q1 q2 => exec q1 |>List.without (exec q2)
  | .select q e => exec q |>.filter e.holds
  | .project q _ sub => exec q |>.map (·.project _ sub)
  | .product q1 q2 _ => exec q1 |>.cartesianProduct (exec q2)
  | .renameColumn q c _ _ => exec q |>.map (·.rename c)
  | .prefixWith _ q => exec q |>.map prefixRow

open Query in
def example2 :=
  let mountain := table mountainDiary |>.prefixWith "mountain"
  let waterfall := table waterfallDiary |>.prefixWith "waterfall"
  mountain.product waterfall (by decide)
    |>.select (.eq (c! "mountain.location") (c! "waterfall.location"))
    |>.project [⟨"mountain.name", .string, false⟩, ⟨"waterfall.name", .string, false⟩]
      (by repeat constructor)

#eval example2.exec

-- A table with a nullable column: some peaks have never been visited
abbrev wishlist : Schema := [
  ⟨"name", .string, false⟩,
  ⟨"elevation", .int, false⟩,
  ⟨"lastVisited", .int, true⟩
]

def wishlistDiary : Table wishlist := [
  ("Mount Nebo",   (3637 : Int), some (2013 : Int)),
  ("Denali",       (6190 : Int), none),
  ("Himmelbjerget", (147 : Int), some (2004 : Int))
]

open Query in
-- Rows where `lastVisited < 2010` is NULL are filtered out, as in SQL
def visitedBefore2010 :=
  table wishlistDiary
    |>.select (.lt (c! "lastVisited") (.const 2010))
    |>.project [⟨"name", .string, false⟩] (by repeat constructor)

#eval visitedBefore2010.exec
-- ["Himmelbjerget"]

open Query in
def neverVisited :=
  table wishlistDiary
    |>.select (.isNull (c! "lastVisited"))
    |>.project [⟨"name", .string, false⟩] (by repeat constructor)

#eval neverVisited.exec
-- ["Denali"]

-- NULL = NULL is NULL, and FALSE AND NULL is FALSE
#eval (DBExpr.eq (s := []) (t := .int) .null .null).evaluate ()
#eval (DBExpr.and (s := []) (.const false) (.eq (t := .int) .null (.const 1))).evaluate ()

/-
Define a structure to represent dates.
Add it to the DBType universe and update the rest of the code accordingly.
Provide the extra DBExpr constructors that seem to be necessary.
-/

end TypedQueries
