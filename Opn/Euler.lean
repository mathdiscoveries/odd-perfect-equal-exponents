module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Tactic.Ring
public import Opn.LemmaC

/-
Euler's form of an odd perfect number, the part the library uses
(`local certificate generator.md`, section 4, the pieces "Euler's form" and "π is the
special prime"; `t1-four-primes.md`, Lemma E; `t2-method-1.md`,
Lemma D(b)). If every prime of an odd perfect N other than π has an even
exponent, then π divides N with an odd exponent, π ≡ 1 (mod 4), and
(π + 1)/2 divides N.

`EqualExponents r N` with r odd gives the hypothesis: each prime other
than π has exponent r − 1, which is even. So the π that
`EqualExponents` names is Euler's special prime, and N is not a power
of the other primes alone (note 25-N1 of verdict 25).
-/


@[expose] public section

namespace Opn

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Pairs of terms: 1 + p + ⋯ + p^(2m−1) = (1 + p)(1 + p² + ⋯ + p^(2m−2)). -/
theorem geom_two_mul (p m : ℕ) :
    ∑ j ∈ range (2 * m), p ^ j = (1 + p) * ∑ i ∈ range m, (p ^ 2) ^ i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ,
      sum_range_succ, ih, sum_range_succ]
    ring

/-- σ(p^k) is odd for an odd prime p and an even k. -/
theorem sigma_prime_pow_odd {p k : ℕ} (hp : p.Prime) (hodd : p % 2 = 1)
    (hk : Even k) : Odd (σ 1 (p ^ k)) := by
  rw [sigma_one_apply_prime_pow hp, Nat.odd_iff, geom_mod_two hodd]
  obtain ⟨j, rfl⟩ := hk
  omega

/-- σ(M) is odd for an odd M whose every prime has an even exponent. -/
theorem sigma_odd_of_even {M : ℕ} (hM : M ≠ 0) (hodd : Odd M)
    (h : ∀ q ∈ M.primeFactors, Even (M.factorization q)) :
    Odd (σ 1 M) := by
  rw [IsMultiplicative.multiplicative_factorization (σ 1)
    isMultiplicative_sigma hM, Finsupp.prod, Nat.support_factorization]
  apply Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one
  intro q hq
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hqd := Nat.dvd_of_mem_primeFactors hq
  apply sigma_prime_pow_odd hqp _ (h q hq)
  rcases hqp.eq_two_or_odd with h2 | h2
  · subst h2
    rw [Nat.odd_iff] at hodd
    omega
  · exact h2

/-- σ(N) = 2N for a perfect N. -/
theorem sigma_eq_two_mul {N : ℕ} (h : N.Perfect) : σ 1 N = 2 * N := by
  rw [sigma_one_apply]
  exact (Nat.perfect_iff_sum_divisors_eq_two_mul h.2).mp h

/-- Euler's form, as the library uses it. -/
theorem special_prime {N π : ℕ} (hN : Odd N) (hperf : N.Perfect)
    (hπ : π.Prime)
    (h : ∀ q, q.Prime → q ∣ N → q ≠ π → Even (N.factorization q)) :
    π ∣ N ∧ Odd (N.factorization π) ∧ π % 4 = 1 ∧ (π + 1) / 2 ∣ N := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp at hN
  have hsplit : π ^ N.factorization π * (ordCompl[π] N) = N :=
    Nat.ordProj_mul_ordCompl_eq_self N π
  have hcopπ : Nat.Coprime π (ordCompl[π] N) := Nat.coprime_ordCompl hπ hN0
  have hcop : Nat.Coprime (π ^ N.factorization π) (ordCompl[π] N) :=
    hcopπ.pow_left _
  have hM0 : ordCompl[π] N ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hsplit
    exact hN0 hsplit.symm
  have hModd : Odd (ordCompl[π] N) := by
    have := hN
    rw [← hsplit] at this
    exact (Nat.odd_mul.mp this).2
  -- σ of the part prime to π is odd.
  have hσM : Odd (σ 1 (ordCompl[π] N)) := by
    apply sigma_odd_of_even hM0 hModd
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hqd := Nat.dvd_of_mem_primeFactors hq
    have hqπ : q ≠ π := by
      rintro rfl
      exact hqp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcopπ hqd)
    rw [Nat.factorization_ordCompl, Finsupp.erase_ne hqπ]
    exact h q hqp (hqd.trans (Nat.ordCompl_dvd N π)) hqπ
  -- σ(N) = σ(π^α) σ(M) = 2N.
  have hprod : σ 1 (π ^ N.factorization π) * σ 1 (ordCompl[π] N) = 2 * N := by
    rw [← isMultiplicative_sigma.map_mul_of_coprime hcop, hsplit]
    exact sigma_eq_two_mul hperf
  -- σ(π^α) is even.
  have hSeven : ¬ Odd (σ 1 (π ^ N.factorization π)) := by
    intro hS
    have h2 := Nat.odd_mul.mpr ⟨hS, hσM⟩
    rw [hprod, Nat.odd_iff] at h2
    omega
  -- So α ≥ 1, and π divides N.
  have hα : 0 < N.factorization π := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    rw [h0, pow_zero, isMultiplicative_sigma.map_one] at hSeven
    exact hSeven odd_one
  have hπN : π ∣ N := Nat.dvd_of_factorization_pos hα.ne'
  have hπodd : π % 2 = 1 := by
    rcases hπ.eq_two_or_odd with h2 | h2
    · subst h2
      rw [Nat.odd_iff] at hN
      omega
    · exact h2
  -- α is odd.
  rw [sigma_one_apply_prime_pow hπ, Nat.odd_iff, geom_mod_two hπodd] at hSeven
  have hαodd : Odd (N.factorization π) := by
    rw [Nat.odd_iff]
    omega
  -- σ(π^α) = (1 + π) T, with α + 1 = 2m.
  obtain ⟨m, hm⟩ : ∃ m, N.factorization π + 1 = 2 * m := by
    obtain ⟨k, hk⟩ := hαodd
    exact ⟨k + 1, by omega⟩
  have hfac : (1 + π) ∣ σ 1 (π ^ N.factorization π) := by
    rw [sigma_one_apply_prime_pow hπ, hm, geom_two_mul]
    exact dvd_mul_right _ _
  have h2N : (1 + π) ∣ 2 * N := by
    rw [← hprod]
    exact hfac.mul_right _
  have hNodd : N % 2 = 1 := Nat.odd_iff.mp hN
  -- π ≡ 1 (mod 4): if π ≡ 3, then 4 divides 1 + π, which divides 2N.
  have hπ4 : π % 4 = 1 := by
    by_contra hne
    have h4 : 4 ∣ 1 + π := by omega
    have := h4.trans h2N
    omega
  refine ⟨hπN, hαodd, hπ4, ?_⟩
  -- (π + 1)/2 divides N.
  have hk : 1 + π = 2 * ((π + 1) / 2) := by omega
  rw [hk] at h2N
  exact Nat.dvd_of_mul_dvd_mul_left (by omega) h2N

end Opn
