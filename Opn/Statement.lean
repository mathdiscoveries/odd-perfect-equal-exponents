module

public import Mathlib.NumberTheory.Divisors
public import Mathlib.Data.Nat.Factorization.Basic

/-
The statement of the odd perfect library's cases, as `lean-scope-1.md`
section 2 gives it: every prime of N other than one prime π has the
exponent r - 1. Euler's congruences are not assumed.
-/


@[expose] public section

namespace Opn

/-- Every prime of N other than one prime π has exponent r - 1. -/
def EqualExponents (r N : ℕ) : Prop :=
  ∃ π : ℕ, π.Prime ∧
    ∀ q : ℕ, q.Prime → q ∣ N → q ≠ π → N.factorization q = r - 1

end Opn
