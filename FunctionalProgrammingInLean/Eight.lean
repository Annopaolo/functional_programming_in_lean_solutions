namespace Eight

/-
 Translate each of the following non-tail-recursive functions into accumulator-passing tail-recursive functions:
-/

def NonTail.length : List α → Nat
  | [] => 0
  | _ :: xs => NonTail.length xs + 1

def NonTail.factorial : Nat → Nat
  | 0 => 1
  | n + 1 => factorial n * (n + 1)

def Tail.lengthHelper (acc : Nat) : List α -> Nat
  | [] => acc
  | _ :: xs => lengthHelper (acc + 1) xs

def Tail.length (xs : List α) : Nat := Tail.lengthHelper 0 xs

#eval NonTail.length ([] : List Nat)
#eval Tail.length ([] : List Nat)
#eval NonTail.length ([1,2,3] : List Nat)
#eval Tail.length ([1,2,3] : List Nat)

def Tail.factorialHelper (acc : Nat) : Nat -> Nat
  | 0 => acc
  | n + 1 => factorialHelper (acc * (n + 1)) n

def Tail.factorial (n : Nat) : Nat := Tail.factorialHelper 1 n

#eval NonTail.factorial 0
#eval Tail.factorial 0
#eval NonTail.factorial 4
#eval Tail.factorial 4

/-
 The translation of NonTail.filter should result in a program that takes constant stack space through tail recursion,
 and time linear in the length of the input list.
 A constant factor overhead is acceptable relative to the original:
-/

def NonTail.filter (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs =>
    if p x then
      x :: filter p xs
    else
      filter p xs

def Tail.filterHelper (acc : List α) (p : α -> Bool) : List α -> List α
  | [] => acc
  | x :: xs =>
              if p x then
                filterHelper (x :: acc) p xs
              else
                filterHelper acc p xs

def Tail.filter (p : α → Bool)  (xs : List α) : List α :=
  List.reverse (Tail.filterHelper [] p xs)

#eval NonTail.filter (fun x => x % 2 == 0) []
#eval Tail.filter (fun x => x % 2 == 0) []
#eval NonTail.filter (fun x => x % 2 == 0) [1,2,3,4]
#eval Tail.filter (fun x => x % 2 == 0) [1,2,3,4]

/-
Write your own proofs for Nat.zero_add, Nat.add_assoc, and Nat.add_comm using the induction tactic.
-/

theorem MyNat.zero_add (n : Nat) : 0 + n = n := by induction n with
  | zero => rfl
  -- `show` allows to run one step in the computation: from 0 + (n + 1)
   -- we apply the Nat.succ function and get (0 + n) + 1.
   -- Essentially, we compute one step on the left handside
  | succ n n_ih => show (0 + n) + 1 = n + 1 ; rw [n_ih]

#print Nat
#print Nat.add._f

theorem MyNat.add_assoc (n m k : Nat) : n + m + k = n + (m + k) :=
  by induction k with
  | zero => rfl
  | succ k k_ih => show (n + m + k) + 1 = n + (m + k) +1 ; rw [k_ih]

theorem MyNat.add_comm_helper (m n : Nat) : (m + 1) + n = m + n + 1  := by
  induction n with
  | zero => rfl
  | succ n n_ih => show (m + 1 + n) + 1 = (m + n + 1) + 1 ; rw [n_ih]

theorem MyNat.add_comm (n m : Nat) : n + m = m + n :=
  by induction m with
  | zero => rw [MyNat.zero_add] ; rfl
  | succ m m_ih => rw [MyNat.add_comm_helper] ; show (n + m) + 1 = m + n + 1 ; rw [m_ih]

/-
Adapt the proof for sum into a proof for NonTail.reverse and Tail.reverse.
-/

def NonTail.reverse : List α → List α
  | [] => []
  | x :: xs => reverse xs ++ [x]

def Tail.reverseHelper (soFar : List α) : List α → List α
  | [] => soFar
  | x :: xs => reverseHelper (x :: soFar) xs

def Tail.reverse (xs : List α) : List α :=
  Tail.reverseHelper [] xs

theorem non_tail_reverse_eq_tail_reverse_helper (xs : List α) : (acc : List α) ->
  NonTail.reverse xs ++ acc = Tail.reverseHelper acc xs := by
  induction xs with
  | nil => intro acc; simp [NonTail.reverse, Tail.reverseHelper]
  | cons y ys tail_ih => intro acc; simp [NonTail.reverse, Tail.reverseHelper]; rw [tail_ih]

theorem non_tail_reverse_eq_tail_reverse :
    @NonTail.reverse = @Tail.reverse := by
  funext α xs
  induction xs with
  | nil => rfl
  | cons x xs xs_ih =>
    simp [NonTail.reverse, Tail.reverse, Tail.reverseHelper]
    rw [non_tail_reverse_eq_tail_reverse_helper]

/-
Prove that NonTail.factorial from the exercises in the previous section is equal to your tail-recursive solution
by finding the relationship between the accumulator and the result and proving a suitable helper theorem.
-/

theorem non_tail_factorial_eq_tail_factorial_helper (n: Nat) : (acc : Nat) ->
  NonTail.factorial n * acc = Tail.factorialHelper acc n := by
  induction n with
  | zero => intro acc; simp [NonTail.factorial, Tail.factorialHelper]
  | succ x x_ih =>
    intro acc
    simp [NonTail.factorial, Tail.factorialHelper]
    rw [Nat.mul_assoc, Nat.mul_comm acc (x + 1)]
    rw [x_ih]

theorem non_tail_factorial_eq_tail_factorial :
  @NonTail.factorial = @Tail.factorial := by
  funext x
  induction x with
  | zero => rfl
  | succ n n_ih =>
    simp [NonTail.factorial, Tail.factorial, Tail.factorialHelper]
    rw [non_tail_factorial_eq_tail_factorial_helper]

/-
Implement a ForM m (Array α) instance on arrays
using a tail-recursive accumulator-passing function and a termination_by clause.
-/
def arrayForMHelper [Monad m] (arr: Array α) (f: α -> m Unit) (i: Nat) : m Unit :=
  if proof: i < arr.size then
    f arr[i] >>= fun _ => arrayForMHelper arr f (i + 1)
  else
    pure ()
  termination_by arr.size - i


def Array.forM [Monad m] (arr: Array α) (f: α -> m Unit) : m Unit :=
  arrayForMHelper arr f 0

instance [Monad m] : ForM m (Array α) α where
  forM := Array.forM

#eval forM (Array.mk [1,2,3,4]) IO.println

/-
Reimplement Array.map, Array.find, and the ForM instance using
for ... in ... loops in the identity monad and compare the resulting code.
-/

def Array.map (f : α → β) (arr : Array α) : Array β := Id.run do
  let mut ret := Array.mk []
  for x in arr do
    ret := ret.push (f x)
  pure ret

#eval Array.map (fun x => x *2) (Array.mk [1,2,4,5])

def Array.find (arr : Array α) (p : α → Bool) : Option (Nat × α) := Id.run do
  for h : i in [0 : arr.size] do
    let x := arr[i]
    if p x then return some (i, x)
  pure none

#eval Array.find (Array.mk [1,2,4,5]) (fun x => x % 2 == 0)

def Array.forM' [Monad m] (arr: Array α) (f: α -> m Unit) : m Unit := do
  for x in arr do f x

instance [Monad m] : ForM m (Array α) α where
  forM := Array.forM'

#eval forM (Array.mk [1,2,3,4]) IO.println


-- Code does not need explicit tail-recursive helpers, and most proofs are already done by lean!

/-
Reimplement array reversal using a for ... in ... loop in the identity monad.
Compare it to the tail-recursive function.
-/

def reverseArray (arr: Array α) : Array α := Id.run do
  let mut ret := []
  for x in arr do
    ret :=  x :: ret
  pure (Array.mk ret)

#eval reverseArray (Array.mk [1,2,3,4,5])

-- ret is the accumulator! The base case is its instantiation, and the recursive case its update. Wow!
