module

public import Opn.TheoremG
public import Opn.LemmaCb
public import Opn.Euler

/-
The cited fact of L2, proved for every odd prime r (`next-target-1.md`,
section 1): in an odd perfect number whose every prime has an odd
exponent or the exponent r − 1, the prime r does not have an odd
exponent. This is `NotSpecial r` of `TheoremG.lean`. Cohen and Williams
(1985, p. 71, fact (iii)) state it as "p ≠ r" for the special prime p,
citing Kanold (1941). The proof here is not Kanold's, which was not
read. It is a congruence: remove every factor r from both sides of
σ(N) = 2N. Modulo r the left side is then 1 and the right side 2.

- `ordCompl[r] x` is x with every factor r removed (Mathlib's notation).
- If q ≡ 1 (mod r) and r is odd, then Φ(q) = 1 + q + ⋯ + q^(r−1)
  ≡ r (mod r²), so Φ(q) = r·v with v ≡ 1 (mod r) (`geom_mod_sq`).
- If q ≢ 1 (mod r), then Φ(q) ≡ 1 (mod r), from Φ(q)(q − 1) = q^r − 1
  and Fermat.
-/


@[expose] public section

namespace Opn

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Removing the factors r of a number that r does not divide leaves it
as it was. -/
theorem ordCompl_of_not_dvd {r x : ℕ} (h : ¬ r ∣ x) :
    ordCompl[r] x = x := by
  rw [Nat.factorization_eq_zero_of_not_dvd h, pow_zero, Nat.div_one]

/-- Removing the factors r of r^a leaves 1. -/
theorem ordCompl_prime_pow_self {r : ℕ} (hr : r.Prime) (a : ℕ) :
    ordCompl[r] (r ^ a) = 1 := by
  rw [hr.factorization_pow, Finsupp.single_eq_same]
  exact Nat.div_self (pow_pos hr.pos a)

/-- Removing the factors r of a product, factor by factor. -/
theorem ordCompl_prod {r : ℕ} (s : Finset ℕ) (f : ℕ → ℕ) :
    ordCompl[r] (∏ i ∈ s, f i) = ∏ i ∈ s, ordCompl[r] (f i) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [prod_empty, prod_empty, Nat.factorization_one, Finsupp.coe_zero,
      Pi.zero_apply, pow_zero, Nat.div_one]
  | @insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha, Nat.ordCompl_mul, ih]

/-- (1 + x)^i = 1 + i·x when x·x = 0. -/
theorem one_add_pow_of_mul_self_eq_zero {R : Type*} [CommRing R] {x : R}
    (hx : x * x = 0) (i : ℕ) : (1 + x) ^ i = 1 + (i : R) * x := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination (i : R) * hx

/-- For r odd and q ≡ 1 (mod r): Φ(q) ≡ r (mod r²). -/
theorem geom_mod_sq {r q : ℕ} (hr : 2 ≤ r) (hrodd : r % 2 = 1)
    (h : q % r = 1) : (∑ i ∈ range r, q ^ i) % (r * r) = r := by
  obtain ⟨k, hk⟩ : ∃ k, q = 1 + k * r := by
    refine ⟨q / r, ?_⟩
    have e := Nat.div_add_mod q r
    rw [h, Nat.mul_comm] at e
    omega
  obtain ⟨m, hm⟩ : ∃ m, r = 2 * m + 1 := ⟨r / 2, by omega⟩
  have hid : ∑ i ∈ range r, i = r * m := by
    have e := Finset.sum_range_id_mul_two r
    have e2 : r * (r - 1) = r * m * 2 := by
      rw [show r - 1 = m * 2 by omega]
      ring
    rw [e2] at e
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) e
  have hrr : (r : ZMod (r * r)) * (r : ZMod (r * r)) = 0 := by
    rw [← Nat.cast_mul, ZMod.natCast_self]
  have hcast : ((∑ i ∈ range r, q ^ i : ℕ) : ZMod (r * r))
      = ((r : ℕ) : ZMod (r * r)) := by
    have hx : ((k : ZMod (r * r)) * r) * ((k : ZMod (r * r)) * r) = 0 := by
      linear_combination ((k : ZMod (r * r)) * k) * hrr
    have hq : (q : ZMod (r * r)) = 1 + (k : ZMod (r * r)) * r := by
      rw [hk]
      push_cast
      ring
    have hS : ∑ i ∈ range r, (i : ZMod (r * r))
        = ((r * m : ℕ) : ZMod (r * r)) := by
      rw [← hid, Nat.cast_sum]
    push_cast
    rw [hq]
    simp only [one_add_pow_of_mul_self_eq_zero hx]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hS, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast
    linear_combination ((m : ZMod (r * r)) * k) * hrr
  rw [ZMod.natCast_eq_natCast_iff'] at hcast
  rw [hcast]
  exact Nat.mod_eq_of_lt (by nlinarith)

/-- For r an odd prime and any q: Φ(q) with its factors r removed is
1 modulo r. -/
theorem ordCompl_geom_cast {r q : ℕ} (hr : r.Prime) (hrodd : r % 2 = 1) :
    ((ordCompl[r] (∑ i ∈ range r, q ^ i) : ℕ) : ZMod r) = 1 := by
  have : Fact r.Prime := ⟨hr⟩
  by_cases h : q % r = 1
  · -- Φ(q) = r · (r·t + 1).
    have hmod := geom_mod_sq hr.two_le hrodd h
    have hSeq : ∑ i ∈ range r, q ^ i
        = r * (r * ((∑ i ∈ range r, q ^ i) / (r * r)) + 1) := by
      have e := Nat.div_add_mod (∑ i ∈ range r, q ^ i) (r * r)
      rw [hmod] at e
      calc _ = r * r * ((∑ i ∈ range r, q ^ i) / (r * r)) + r := e.symm
        _ = _ := by ring
    have hndvd : ¬ r ∣ r * ((∑ i ∈ range r, q ^ i) / (r * r)) + 1 := by
      intro hd
      have h1 := (Nat.dvd_add_right (dvd_mul_right r _)).mp hd
      exact hr.one_lt.ne' (Nat.dvd_one.mp h1)
    have hself : ordCompl[r] r = 1 := by
      have e := ordCompl_prime_pow_self hr 1
      rwa [pow_one] at e
    rw [hSeq, Nat.ordCompl_mul, hself, one_mul, ordCompl_of_not_dvd hndvd]
    push_cast
    rw [ZMod.natCast_self, zero_mul, zero_add]
  · -- Φ(q) ≡ 1 (mod r), and r does not divide it.
    rw [ordCompl_of_not_dvd (not_r_dvd_geom hr h)]
    have hz : ((∑ i ∈ range r, q ^ i : ℕ) : ZMod r) * (q : ZMod r) + 1
        = ((∑ i ∈ range r, q ^ i : ℕ) : ZMod r) + (q : ZMod r) ^ r := by
      exact_mod_cast congrArg (Nat.cast (R := ZMod r)) (geom_mul q r)
    rw [ZMod.pow_card] at hz
    have hq1 : (q : ZMod r) - 1 ≠ 0 := by
      intro h0
      apply h
      have h1 : (q : ZMod r) = ((1 : ℕ) : ZMod r) := by
        rw [Nat.cast_one]
        exact sub_eq_zero.mp h0
      rw [ZMod.natCast_eq_natCast_iff'] at h1
      rwa [Nat.mod_eq_of_lt hr.one_lt] at h1
    have hprod : (((∑ i ∈ range r, q ^ i : ℕ) : ZMod r) - 1)
        * ((q : ZMod r) - 1) = 0 := by
      linear_combination hz
    rcases mul_eq_zero.mp hprod with h0 | h0
    · exact sub_eq_zero.mp h0
    · exact absurd h0 hq1

/-- The cited fact, proved: for an odd prime r, `NotSpecial r`. -/
theorem notSpecial_of_prime {r : ℕ} (hr : r.Prime) (hr3 : 3 ≤ r) :
    NotSpecial r := by
  intro N hN hperf hexp hα
  have : Fact r.Prime := ⟨hr⟩
  have hrodd : r % 2 = 1 := by
    rcases hr.eq_two_or_odd with h2 | h2
    · omega
    · exact h2
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp at hN
  have hNodd : N % 2 = 1 := Nat.odd_iff.mp hN
  have hαpos : 0 < N.factorization r := by
    obtain ⟨k, hk⟩ := hα
    omega
  have hrmem : r ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hr, Nat.dvd_of_factorization_pos hαpos.ne', hN0⟩
  -- σ(N) and N as products over N's primes, r's factor first.
  have hσ : σ 1 N = σ 1 (r ^ N.factorization r)
      * ∏ p ∈ N.primeFactors.erase r, σ 1 (p ^ N.factorization p) := by
    rw [IsMultiplicative.multiplicative_factorization (σ 1)
      isMultiplicative_sigma hN0, Finsupp.prod, Nat.support_factorization]
    exact (Finset.mul_prod_erase N.primeFactors
      (fun p => σ 1 (p ^ N.factorization p)) hrmem).symm
  have hNprod : N = r ^ N.factorization r
      * ∏ p ∈ N.primeFactors.erase r, p ^ N.factorization p := by
    have e := Nat.prod_factorization_pow_eq_self hN0
    rw [Finsupp.prod, Nat.support_factorization] at e
    exact e.symm.trans (Finset.mul_prod_erase N.primeFactors
      (fun p => p ^ N.factorization p) hrmem).symm
  have hperf2 := sigma_eq_two_mul hperf
  -- Only r has an odd exponent, so every other prime has r − 1.
  have hσr2 : 2 ∣ σ 1 (r ^ N.factorization r) := by
    rw [sigma_one_apply_prime_pow hr, Nat.dvd_iff_mod_eq_zero,
      geom_mod_two hrodd]
    obtain ⟨k, hk⟩ := hα
    omega
  have hexpq : ∀ p ∈ N.primeFactors.erase r, N.factorization p = r - 1 := by
    intro p hp
    have hpN := Finset.mem_of_mem_erase hp
    have hpp := Nat.prime_of_mem_primeFactors hpN
    have hpd := Nat.dvd_of_mem_primeFactors hpN
    rcases hexp p hpp hpd with hodd | heq
    · exfalso
      have hpodd : p % 2 = 1 := by
        rcases hpp.eq_two_or_odd with h2 | h2
        · subst h2
          omega
        · exact h2
      have h2p : 2 ∣ σ 1 (p ^ N.factorization p) := by
        rw [sigma_one_apply_prime_pow hpp, Nat.dvd_iff_mod_eq_zero,
          geom_mod_two hpodd]
        obtain ⟨k, hk⟩ := hodd
        omega
      have h4 : 2 * 2 ∣ σ 1 N := by
        rw [hσ]
        exact Nat.mul_dvd_mul hσr2 (h2p.trans (Finset.dvd_prod_of_mem
          (fun p => σ 1 (p ^ N.factorization p)) hp))
      rw [hperf2] at h4
      omega
    · exact heq
  -- The left side, factors r removed: 1 modulo r.
  have hL : ((ordCompl[r] (σ 1 N) : ℕ) : ZMod r) = 1 := by
    rw [hσ, Nat.ordCompl_mul, ordCompl_prod, Nat.cast_mul, Nat.cast_prod]
    have h1 : ((ordCompl[r] (σ 1 (r ^ N.factorization r)) : ℕ) : ZMod r)
        = 1 := by
      rw [sigma_one_apply_prime_pow hr]
      have hm := geom_mod_self (r := N.factorization r + 1) (q := r)
        (by omega) hr.two_le
      have hnd : ¬ r ∣ ∑ i ∈ range (N.factorization r + 1), r ^ i := by
        rw [Nat.dvd_iff_mod_eq_zero, hm]
        omega
      rw [ordCompl_of_not_dvd hnd, ← ZMod.natCast_mod, hm, Nat.cast_one]
    rw [h1, one_mul]
    apply Finset.prod_eq_one
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
    rw [hexpq p hp, sigma_one_apply_prime_pow hpp,
      show r - 1 + 1 = r by omega]
    exact ordCompl_geom_cast hr hrodd
  -- The right side, factors r removed: 2 modulo r.
  have hR : ((ordCompl[r] (2 * N) : ℕ) : ZMod r) = 2 := by
    have h2 : ¬ r ∣ 2 := by
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    have hP : ∏ p ∈ N.primeFactors.erase r,
        ((ordCompl[r] (p ^ N.factorization p) : ℕ) : ZMod r) = 1 := by
      apply Finset.prod_eq_one
      intro p hp
      have hpr : p ≠ r := Finset.ne_of_mem_erase hp
      have hpp := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
      have hnd : ¬ r ∣ p ^ N.factorization p := fun hd =>
        hpr ((Nat.prime_dvd_prime_iff_eq hr hpp).mp (hr.dvd_of_dvd_pow hd)).symm
      rw [ordCompl_of_not_dvd hnd, hexpq p hp, Nat.cast_pow]
      apply ZMod.pow_card_sub_one_eq_one
      intro h0
      have hd := (ZMod.natCast_eq_zero_iff p r).mp h0
      exact hpr ((Nat.prime_dvd_prime_iff_eq hr hpp).mp hd).symm
    rw [hNprod, Nat.ordCompl_mul, Nat.ordCompl_mul, ordCompl_of_not_dvd h2,
      ordCompl_prime_pow_self hr, ordCompl_prod, Nat.cast_mul, Nat.cast_mul,
      Nat.cast_prod, hP]
    simp
  rw [hperf2, hR] at hL
  have h0 : (1 : ZMod r) = 0 := by
    linear_combination hL
  exact one_ne_zero h0

end Opn
