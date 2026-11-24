module

public import Mathlib.NumberTheory.LucasPrimality
public import Mathlib.FieldTheory.Finite.Basic

/-
Lemma C of t2-method-1.md, parts (a) and (c), for the sum
1 + q + ... + q^(r-1) written as a sum over `Finset.range r`:
(a) a prime s dividing it is r or is 1 mod r, for r prime;
(c) it is larger than q^(r-1) for r ≥ 2, leaves 1 on division by q,
shares no factor with q, and is odd when q is odd and r is odd.
Part (b), on r itself, is not in this file.
-/


@[expose] public section

namespace Opn

/-- q · (1 + q + ... + q^(n-1)) + 1 = (1 + q + ... + q^(n-1)) + q^n. -/
theorem geom_mul (q n : ℕ) :
    (∑ i ∈ Finset.range n, q ^ i) * q + 1
      = (∑ i ∈ Finset.range n, q ^ i) + q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, pow_succ]
    omega

/-- Lemma C (a): a prime s dividing 1 + q + ... + q^(r-1), r prime,
is r or is 1 mod r. -/
theorem prime_dvd_geom {r q s : ℕ} (hr : r.Prime) (hs : s.Prime)
    (h : s ∣ ∑ i ∈ Finset.range r, q ^ i) : s = r ∨ s % r = 1 := by
  have : Fact s.Prime := ⟨hs⟩
  have hS : ((∑ i ∈ Finset.range r, q ^ i : ℕ) : ZMod s) = 0 :=
    (ZMod.natCast_eq_zero_iff _ s).mpr h
  have hz : ((∑ i ∈ Finset.range r, q ^ i : ℕ) : ZMod s) * (q : ZMod s) + 1
      = ((∑ i ∈ Finset.range r, q ^ i : ℕ) : ZMod s) + (q : ZMod s) ^ r := by
    exact_mod_cast congrArg (Nat.cast (R := ZMod s)) (geom_mul q r)
  have hx : (q : ZMod s) ^ r = 1 := by
    rw [hS, zero_mul, zero_add, zero_add] at hz
    exact hz.symm
  have hord : orderOf (q : ZMod s) ∣ r := orderOf_dvd_of_pow_eq_one hx
  rcases (Nat.dvd_prime hr).mp hord with h1 | h1
  · left
    have hq1 : (q : ZMod s) = 1 := orderOf_eq_one_iff.mp h1
    have h0 : (∑ i ∈ Finset.range r, (q : ZMod s) ^ i) = 0 := by
      have := hS
      push_cast at this
      exact this
    rw [hq1] at h0
    have h3 : (r : ZMod s) = 0 := by simpa using h0
    exact (Nat.prime_dvd_prime_iff_eq hs hr).mp
      ((ZMod.natCast_eq_zero_iff r s).mp h3)
  · right
    have hq0 : (q : ZMod s) ≠ 0 := by
      intro hzero
      rw [hzero, zero_pow hr.ne_zero] at hx
      exact zero_ne_one hx
    have h2 : orderOf (q : ZMod s) ∣ s - 1 :=
      orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hq0)
    rw [h1] at h2
    obtain ⟨k, hk⟩ := h2
    have hs2 := hs.two_le
    have e : s = r * k + 1 := by omega
    rw [e, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hr.one_lt

/-- Lemma C (c), first part: the sum is larger than its last term. -/
theorem geom_gt {r : ℕ} (hr : 2 ≤ r) (q : ℕ) :
    q ^ (r - 1) < ∑ i ∈ Finset.range r, q ^ i := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
  have e : k + 2 - 1 = k + 1 := by omega
  rw [e, Finset.sum_range_succ, Finset.sum_range_succ', pow_zero]
  omega

/-- Lemma C (c), second part: the sum leaves 1 on division by q. -/
theorem geom_mod_self {r q : ℕ} (hr : 1 ≤ r) (hq : 2 ≤ q) :
    (∑ i ∈ Finset.range r, q ^ i) % q = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  have e : ∑ i ∈ Finset.range k, q ^ (i + 1)
      = q * ∑ i ∈ Finset.range k, q ^ i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => pow_succ' q i)
  rw [Finset.sum_range_succ', pow_zero, e, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt hq

/-- Lemma C (c): the sum shares no factor with q. -/
theorem geom_coprime {r q : ℕ} (hr : 1 ≤ r) (hq : 2 ≤ q) :
    Nat.Coprime q (∑ i ∈ Finset.range r, q ^ i) := by
  show Nat.gcd q (∑ i ∈ Finset.range r, q ^ i) = 1
  rw [Nat.gcd_rec, geom_mod_self hr hq]
  exact Nat.gcd_one_left _

/-- For q odd, the sum of n powers of q has the parity of n. -/
theorem geom_mod_two {q : ℕ} (hq : q % 2 = 1) (n : ℕ) :
    (∑ i ∈ Finset.range n, q ^ i) % 2 = n % 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 : q ^ n % 2 = 1 := by
      rw [Nat.pow_mod, hq, one_pow]
      rfl
    omega

end Opn
