namespace SevenInterlude

def Nat.plusR : Nat → Nat → Nat
  | n, 0 => n
  | n, k + 1 => plusR n k + 1

/-
 Prove plusR_succ_left using the induction ...with tactic.
-/

theorem plusR_succ_left (n k : Nat) :
  Nat.plusR (n + 1) k = Nat.plusR n k + 1 := by
  induction k with
  | zero => rfl
  | succ k' k'_ih =>
    simp [Nat.plusR]
    exact k'_ih

/-
 Rewrite the proof of plusR_succ_left to use <;> in a single line.
-/

theorem plusR_succ_left' (n k : Nat) :
  Nat.plusR (n + 1) k = Nat.plusR n k + 1 := by
  induction k <;> simp [Nat.plusR] <;> assumption

/-
 Prove that appending lists is associative using induction on lists:
-/

theorem List.append_assoc (xs ys zs : List α) :
    xs ++ (ys ++ zs) = (xs ++ ys) ++ zs := by
    induction xs <;> simp

end SevenInterlude
