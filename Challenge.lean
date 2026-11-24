module

public import Mathlib.NumberTheory.Divisors
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Palomar Challenge: Equal-Exponent Odd Perfect Numbers for Every Odd Prime `3 ≤ r ≤ 73`

An odd perfect number `N` has equal non-special exponents `r - 1` (`EqualExponents r N`)
when there exists a prime `π` such that every prime `q ∣ N` with `q ≠ π` satisfies
`N.factorization q = r - 1`.

This challenge states:
1. `notSpecial_of_prime` (Kanold's theorem): for every odd prime `r ≥ 3`, in any
   odd perfect number whose prime exponents are each odd or equal to `r - 1`, the
   prime `r` cannot have an odd exponent.
2. `no_odd_perfect_equal_exponents_all_primes_le_73`: for **every** odd prime
   `3 ≤ r ≤ 73` (all 20 odd primes, `1 ≤ β ≤ 36` where `r = 2β + 1`), there is no
   odd perfect number with `EqualExponents r N`.
3. Non-vacuity sanity checks (`perfect_six`, `equalExponents_3_2205`,
   `equalExponents_19_1937102445`).
-/

@[expose] public section

namespace OpnChallenge

/-- Every prime divisor of `N` other than one prime `π` has exponent `r - 1`. -/
def EqualExponents (r N : ℕ) : Prop :=
  ∃ π : ℕ, π.Prime ∧
    ∀ q : ℕ, q.Prime → q ∣ N → q ≠ π → N.factorization q = r - 1

/-- In an odd perfect number whose prime exponents are each odd or `r - 1`,
the prime `r` does not have an odd exponent. -/
def NotSpecial (r : ℕ) : Prop :=
  ∀ N : ℕ, Odd N → N.Perfect →
    (∀ q : ℕ, q.Prime → q ∣ N →
      Odd (N.factorization q) ∨ N.factorization q = r - 1) →
    ¬ Odd (N.factorization r)

/-- For every odd prime `r ≥ 3`, `r` cannot be the special prime. -/
theorem notSpecial_of_prime {r : ℕ} (hr : r.Prime) (hr3 : 3 ≤ r) :
    NotSpecial r := by
  sorry

/-- No odd perfect number has equal non-special exponents `r - 1` for any odd
prime `3 ≤ r ≤ 73` (all 20 odd primes through `r = 73`, i.e., `β ≤ 36`). -/
theorem no_odd_perfect_equal_exponents_all_primes_le_73
    (r : ℕ) (hr : r.Prime) (h3 : 3 ≤ r) (h73 : r ≤ 73) :
    ¬ ∃ N : ℕ, Odd N ∧ N.Perfect ∧ EqualExponents r N := by
  sorry

/-- Non-vacuity check: `6` is perfect. -/
theorem perfect_six : Nat.Perfect 6 := by
  sorry

/-- Non-vacuity check: `2205 = 3^2 * 5 * 7^2` satisfies `EqualExponents 3 2205`. -/
theorem equalExponents_3_2205 : EqualExponents 3 2205 := by
  sorry

/-- Non-vacuity check: `1937102445 = 3^18 * 5` satisfies `EqualExponents 19 1937102445`. -/
theorem equalExponents_19_1937102445 : EqualExponents 19 1937102445 := by
  sorry

end OpnChallenge
