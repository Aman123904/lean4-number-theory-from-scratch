/-!
# Primes from scratch: Euclid's theorem

We define primality ourselves, prove every number `≥ 2` has a prime
divisor, and derive that there are infinitely many primes.
-/

namespace NumberTheory

def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem fact_pos (n : Nat) : 0 < fact n := by
  induction n with
  | zero => decide
  | succ n ih => exact Nat.mul_pos (Nat.succ_pos n) ih

theorem dvd_fact {k n : Nat} (hk : 0 < k) (hkn : k ≤ n) : k ∣ fact n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le hkn with h | rfl
    · exact Nat.dvd_mul_left_of_dvd (ih (by omega)) _
    · exact Nat.dvd_mul_right _ _

/-- Every `n ≥ 2` has a prime divisor (strong induction). -/
theorem exists_prime_dvd : ∀ n, 2 ≤ n → ∃ p, IsPrime p ∧ p ∣ n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    by_cases hp : ∀ d, d ∣ n → d = 1 ∨ d = n
    · exact ⟨n, ⟨hn, hp⟩, Nat.dvd_refl n⟩
    · simp only [Classical.not_forall, not_or] at hp
      obtain ⟨d, hdvd, hd1, hdn⟩ := hp
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
      have hdle : d ≤ n := Nat.le_of_dvd (by omega) hdvd
      obtain ⟨p, hpp, hpd⟩ := ih d (by omega) (by omega)
      exact ⟨p, hpp, Nat.dvd_trans hpd hdvd⟩

/-- **Euclid:** for every `n` there is a prime larger than `n`. -/
theorem exists_prime_gt (n : Nat) : ∃ p, IsPrime p ∧ n < p := by
  obtain ⟨p, hp, hdvd⟩ := exists_prime_dvd (fact n + 1) (by have := fact_pos n; omega)
  refine ⟨p, hp, ?_⟩
  apply Nat.lt_of_not_le
  intro hpn
  have h1 : p ∣ fact n := dvd_fact (by have := hp.1; omega) hpn
  have h2 : p ∣ 1 := (Nat.dvd_add_right h1).mp hdvd
  have := Nat.le_of_dvd (by decide) h2
  have := hp.1
  omega

/-- There are infinitely many primes: the set of primes is not bounded. -/
theorem primes_infinite : ¬ ∃ N, ∀ p, IsPrime p → p ≤ N := by
  rintro ⟨N, hN⟩
  obtain ⟨p, hp, hlt⟩ := exists_prime_gt N
  exact absurd (hN p hp) (by omega)

end NumberTheory
