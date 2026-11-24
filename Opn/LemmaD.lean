module

public import Opn.Euler

/-
Lemma D (a) of t2-method-1.md: for an odd perfect N and a prime q of N
whose exponent is r − 1, with r odd, Φ(q) = 1 + q + ⋯ + q^(r−1) divides
N. Lemma D (b) is in `Opn/Euler.lean` (`special_prime`); part (c) is
Lemma C (a) applied to π, as Lemma R's proof uses it.
-/


@[expose] public section

namespace Opn

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- σ of the whole power of a prime in N divides σ(N). -/
theorem sigma_ordProj_dvd {N p : ℕ} (hN : N ≠ 0) (hp : p.Prime) :
    σ 1 (p ^ N.factorization p) ∣ σ 1 N := by
  have hcop : Nat.Coprime (p ^ N.factorization p) (ordCompl[p] N) :=
    (Nat.coprime_ordCompl hp hN).pow_left _
  conv_rhs => rw [← Nat.ordProj_mul_ordCompl_eq_self N p]
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop]
  exact dvd_mul_right _ _

/-- Lemma D (a): Φ(q) divides N. -/
theorem geom_dvd {N q r : ℕ} (hN : Odd N) (hperf : N.Perfect)
    (hq : q.Prime) (hqN : q ∣ N) (hr : 1 ≤ r) (hrodd : r % 2 = 1)
    (hk : N.factorization q = r - 1) :
    (∑ i ∈ range r, q ^ i) ∣ N := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp at hN
  have h1 := sigma_ordProj_dvd hN0 hq
  rw [hk, sigma_one_apply_prime_pow hq, sigma_eq_two_mul hperf,
    show r - 1 + 1 = r by omega] at h1
  have hNodd : N % 2 = 1 := Nat.odd_iff.mp hN
  have hqodd : q % 2 = 1 := by
    rcases hq.eq_two_or_odd with h2 | h2
    · subst h2
      omega
    · exact h2
  have hodd : (∑ i ∈ range r, q ^ i) % 2 = 1 := by
    rw [geom_mod_two hqodd]
    exact hrodd
  have hcop : Nat.Coprime (∑ i ∈ range r, q ^ i) 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)).symm
  rw [mul_comm] at h1
  exact hcop.dvd_of_dvd_mul_right h1

end Opn
