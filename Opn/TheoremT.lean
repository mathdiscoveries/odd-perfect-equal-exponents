module

public import Opn.LemmaR

/-
Theorem T of t2-method-1.md, the counting rule: if N is odd and
perfect, π is prime, r is a prime at least 3, every prime of N other
than π has exponent r − 1, and r is not π, then at most r − 1 primes of
N other than π are ≡ 1 (mod r).

The proof needs neither Lemma R nor the page's "r² ∤ Φ(q)": r^c
divides σ(N) = 2N, where c is the number of such primes, so r^c
divides N, and the exponent of r in N is r − 1 when r divides N and 0
when it does not.
-/


@[expose] public section

namespace Opn

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Theorem T. -/
theorem count_le {N π r : ℕ} (hN : Odd N) (hperf : N.Perfect)
    (hr : r.Prime) (hr3 : 3 ≤ r)
    (h : ∀ q, q.Prime → q ∣ N → q ≠ π → N.factorization q = r - 1)
    (hrπ : r ≠ π) (C : Finset ℕ)
    (hC : ∀ q ∈ C, q.Prime ∧ q ∣ N ∧ q ≠ π ∧ q % r = 1) :
    C.card ≤ r - 1 := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp at hN
  have hsplit : σ 1 N = ∏ p ∈ N.primeFactors, σ 1 (p ^ N.factorization p) := by
    rw [IsMultiplicative.multiplicative_factorization (σ 1)
      isMultiplicative_sigma hN0, Finsupp.prod, Nat.support_factorization]
  have hCsub : C ⊆ N.primeFactors := by
    intro q hq
    obtain ⟨hqp, hqN, -, -⟩ := hC q hq
    exact Nat.mem_primeFactors.mpr ⟨hqp, hqN, hN0⟩
  have h1 : (∏ q ∈ C, σ 1 (q ^ N.factorization q)) ∣ σ 1 N := by
    rw [hsplit]
    exact prod_dvd_prod_of_subset _ _ _ hCsub
  have h2 : r ^ C.card ∣ ∏ q ∈ C, σ 1 (q ^ N.factorization q) := by
    rw [← prod_const]
    apply prod_dvd_prod_of_dvd
    intro q hq
    obtain ⟨hqp, hqN, hqπ, hq1⟩ := hC q hq
    rw [h q hqp hqN hqπ, sigma_one_apply_prime_pow hqp,
      show r - 1 + 1 = r by omega]
    exact r_dvd_geom hq1
  have h3 : r ^ C.card ∣ N * 2 := by
    rw [mul_comm, ← sigma_eq_two_mul hperf]
    exact h2.trans h1
  have hr2 : Nat.Coprime r 2 :=
    (Nat.coprime_primes hr Nat.prime_two).mpr (by omega)
  have h4 : r ^ C.card ∣ N := (Nat.Coprime.pow_left _ hr2).dvd_of_dvd_mul_right h3
  by_cases hrN : r ∣ N
  · have := (hr.pow_dvd_iff_le_factorization hN0).mp h4
    rwa [h r hr hrN hrπ] at this
  · rcases Nat.eq_zero_or_pos C.card with h0 | h0
    · omega
    · exact absurd ((dvd_pow_self r h0.ne').trans h4) hrN

end Opn
