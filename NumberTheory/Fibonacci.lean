import NumberTheory.Sums

/-!
# Fibonacci numbers
-/

namespace NumberTheory

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- A fast, linear-time implementation. -/
def fibFast (n : Nat) : Nat := (loop n).1
where
  loop : Nat → Nat × Nat
    | 0 => (0, 1)
    | n + 1 => let p := loop n; (p.2, p.1 + p.2)

theorem fibFast_loop (n : Nat) : fibFast.loop n = (fib n, fib (n + 1)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [fibFast.loop, ih, fib]

/-- The fast implementation agrees with the definition. -/
theorem fibFast_eq (n : Nat) : fibFast n = fib n := by simp [fibFast, fibFast_loop]

theorem fib_pos {n : Nat} (h : 0 < n) : 0 < fib n := by
  induction n using fib.induct with
  | case1 => contradiction
  | case2 => decide
  | case3 n _ ih => simp only [fib]; have := ih (by omega); omega

/-- `F₀ + F₁ + ⋯ + Fₙ₋₁ + 1 = Fₙ₊₁`. -/
theorem sum_fib (n : Nat) : sumTo fib n + 1 = fib (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumTo, fib]; omega

theorem fib_lt_two_pow (n : Nat) : fib n < 2 ^ n := by
  induction n using fib.induct with
  | case1 => decide
  | case2 => decide
  | case3 n ih1 ih2 => simp only [fib, Nat.pow_succ] at *; omega

/-- **Addition formula:** `F(m + n + 1) = F(m + 1) F(n + 1) + F(m) F(n)`. -/
theorem fib_add (m n : Nat) : fib (m + n + 1) = fib (m + 1) * fib (n + 1) + fib m * fib n := by
  induction n generalizing m with
  | zero => simp [fib]
  | succ n ih =>
    have h := ih (m + 1)
    rw [show m + (n + 1) + 1 = m + 1 + n + 1 by omega, h]
    simp only [fib]
    grind

/-- **Cassini-style identity** (in ℤ): `F(n+1)² - F(n) F(n+2) = (-1)ⁿ`. -/
theorem cassini (n : Nat) :
    (fib (n + 1) : Int) ^ 2 - fib n * fib (n + 2) = (-1) ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    show (fib (n + 2) : Int) ^ 2 - fib (n + 1) * fib (n + 3) = (-1) ^ (n + 1)
    have e1 : (fib (n + 2) : Int) = fib n + fib (n + 1) := by simp [fib]
    have e2 : (fib (n + 3) : Int) = fib (n + 1) + fib (n + 2) := by simp [fib]
    rw [e2, e1, show ((-1 : Int)) ^ (n + 1) = (-1) ^ n * (-1) from Int.pow_succ _ _]
    rw [e1] at ih
    generalize (-1 : Int) ^ n = s at ih ⊢
    generalize (fib n : Int) = a at ih ⊢
    generalize (fib (n + 1) : Int) = b at ih ⊢
    clear e1 e2
    grind

end NumberTheory
