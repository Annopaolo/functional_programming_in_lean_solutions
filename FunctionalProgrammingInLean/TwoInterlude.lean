/-!
# TwoInterlude

Solutions to the exercises on `rfl`, `decide` and safe indexing.
-/

namespace TwoInterlude

--Prove the following theorems using rfl: 2 + 3 = 5
theorem twoPlusThreeIsFive : 2 + 3 = 5 := by rfl

-- 15 - 8 = 7,
theorem fifteenMinusEightIsSeven : 15 - 8 = 7 := by rfl

-- "Hello, ".append "world" = "Hello, world".
theorem helloWorld : "Hello, ".append "world" = "Hello, world" := by rfl

-- What happens if rfl is used to prove 5 < 18? Why?
theorem failInequality : 5 < 18 := by sorry
-- Fail because  rfl can only prove equality: < is not a relation on the normal form of values

--Prove the following theorems using by decide: 2 + 3 = 5
theorem twoPlusThreeIsFive' : 2 + 3 = 5 := by decide

-- 15 - 8 = 7,
theorem fifteenMinusEightIsSeven' : 15 - 8 = 7 := by decide

-- "Hello, ".append "world" = "Hello, world".
theorem helloWorld' : "Hello, ".append "world" = "Hello, world" := by decide

-- 5 < 18
theorem failInequality' : 5 < 18 := by decide

-- Write a function that looks up the fifth entry in a list.
-- Pass the evidence that this lookup is safe as an argument to the function.
def safeFifth {α : Type} (xs : List α) (ok: List.length xs >= 5) := xs[4]

-- ok is the evidence that needs to be passed at call time
#eval safeFifth [1,2,3,4,5] (by decide)

-- this fails as the list is provably shorter
-- #eval safeFifth [1,2,3,4] (by sorry)

end TwoInterlude
