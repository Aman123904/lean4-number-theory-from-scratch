/-!
# Classical summation identities

Proved by induction with only core Lean (no Mathlib).
-/

namespace NumberTheory

/-- `sumTo f n = f 0 + f 1 + ⋯ + f (n - 1)`. -/
def sumTo (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo f n + f n

/-- **Gauss:** `2 · (0 + 1 + ⋯ + n) = n (n + 1)`. -/
theorem gauss (n : Nat) : 2 * sumTo id (n + 1) = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumTo, Nat.mul_add, ih]; simp only [id]
    grind

/-- The sum of the first `n` odd numbers is `n²`. -/
theorem sum_odds (n : Nat) : sumTo (fun i => 2 * i + 1) n = n * n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumTo, ih]; grind

/-- `1 + 2 + 4 + ⋯ + 2ⁿ⁻¹ = 2ⁿ - 1`, stated without subtraction. -/
theorem geometric_two (n : Nat) : sumTo (2 ^ ·) n + 1 = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumTo, Nat.pow_succ]; omega

/-- **Nicomachus:** `(0 + 1 + ⋯ + n)² = 0³ + 1³ + ⋯ + n³`. -/
theorem nicomachus (n : Nat) : sumTo id (n + 1) ^ 2 = sumTo (· ^ 3) (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hg := gauss n
    show (sumTo id (n + 1) + (n + 1)) ^ 2 = sumTo (· ^ 3) (n + 1) + (n + 1) ^ 3
    rw [← ih]
    generalize sumTo id (n + 1) = S at hg ⊢
    -- (S + m)² = S² + 2S·m + m², and 2S = n·m where m = n + 1
    grind

end NumberTheory
