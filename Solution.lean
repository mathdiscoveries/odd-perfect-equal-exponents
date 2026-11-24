module

public import Mathlib.NumberTheory.Divisors
public import Mathlib.Data.Nat.Factorization.Basic
public import Opn

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
    NotSpecial r :=
  Opn.notSpecial_of_prime hr hr3

private theorem no_odd_perfect_equal_exponents_71 :
    ¬ ∃ N : ℕ, Odd N ∧ N.Perfect ∧ EqualExponents 71 N :=
  Opn.sound _root_.cert71 _root_.cert71_checked rfl

/-- No odd perfect number has equal non-special exponents `r - 1` for any odd
prime `3 ≤ r ≤ 73` (all 20 odd primes through `r = 73`, i.e., `β ≤ 36`). -/
theorem no_odd_perfect_equal_exponents_all_primes_le_73
    (r : ℕ) (hr : r.Prime) (h3 : 3 ≤ r) (h73 : r ≤ 73) :
    ¬ ∃ N : ℕ, Odd N ∧ N.Perfect ∧ EqualExponents r N := by
  interval_cases r
  · exact OpnCerts.no_odd_perfect_equal_exponents_3
  · exact absurd hr (by decide)
  · exact OpnCerts.no_odd_perfect_equal_exponents_5
  · exact absurd hr (by decide)
  · exact OpnCerts.no_odd_perfect_equal_exponents_7
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact OpnCerts.no_odd_perfect_equal_exponents_11
  · exact absurd hr (by decide)
  · exact OpnCerts.no_odd_perfect_equal_exponents_13
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact OpnCerts.no_odd_perfect_equal_exponents_17
  · exact absurd hr (by decide)
  · exact OpnCerts.no_odd_perfect_equal_exponents_19
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact OpnCerts.no_odd_perfect_equal_exponents_23
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact OpnCerts.no_odd_perfect_equal_exponents_29
  · exact absurd hr (by decide)
  · exact OpnCerts.no_odd_perfect_equal_exponents_31
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact OpnCerts.no_odd_perfect_equal_exponents_37
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact OpnCerts.no_odd_perfect_equal_exponents_41
  · exact absurd hr (by decide)
  · exact OpnCerts.no_odd_perfect_equal_exponents_43
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact OpnCerts.no_odd_perfect_equal_exponents_47
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact OpnCerts.no_odd_perfect_equal_exponents_53
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact OpnCerts.no_odd_perfect_equal_exponents_59
  · exact absurd hr (by decide)
  · exact OpnCerts.no_odd_perfect_equal_exponents_61
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact OpnCerts.no_odd_perfect_equal_exponents_67
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact no_odd_perfect_equal_exponents_71
  · exact absurd hr (by decide)
  · exact OpnCerts.no_odd_perfect_equal_exponents_73

theorem perfect_six : Nat.Perfect 6 := OpnCerts.perfect_six

theorem equalExponents_3_2205 : EqualExponents 3 2205 := OpnCerts.equalExponents_3_2205

theorem equalExponents_19_1937102445 : EqualExponents 19 1937102445 :=
  OpnCerts.equalExponents_19_1937102445

end OpnChallenge
