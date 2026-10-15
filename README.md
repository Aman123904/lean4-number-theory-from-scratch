# Number Theory from Scratch in Lean 4

[![Lean CI](https://github.com/Aman123904/lean4-number-theory-from-scratch/actions/workflows/ci.yml/badge.svg)](https://github.com/Aman123904/lean4-number-theory-from-scratch/actions/workflows/ci.yml)

Classical results in elementary number theory, formalized in Lean 4 using **only the core library**, with no Mathlib. Primality, factorial and Fibonacci are all defined from first principles. There is no `sorry`.

## Main theorems

**Sums** (`NumberTheory/Sums.lean`)
- `gauss`: `2·(0 + 1 + ⋯ + n) = n(n + 1)`
- `sum_odds`: the sum of the first `n` odd numbers is `n²`
- `geometric_two`: `1 + 2 + ⋯ + 2ⁿ⁻¹ + 1 = 2ⁿ`
- `nicomachus`: `(1 + ⋯ + n)² = 1³ + ⋯ + n³`

**Fibonacci** (`NumberTheory/Fibonacci.lean`)
- `fibFast_eq`: a linear-time implementation equals the definition
- `sum_fib`, `fib_lt_two_pow`, `fib_pos`
- `fib_add`: `F(m+n+1) = F(m+1)F(n+1) + F(m)F(n)`
- `cassini`: `F(n+1)² − F(n)F(n+2) = (−1)ⁿ`

**Primes** (`NumberTheory/Primes.lean`)
- `exists_prime_dvd`: every `n ≥ 2` has a prime divisor
- `exists_prime_gt`: **Euclid's theorem**, a prime larger than any `n`, via `n! + 1`
- `primes_infinite`: the primes are unbounded

## Build

```bash
lake build
```

Toolchain: `leanprover/lean4:v4.34.1`.
