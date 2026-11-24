module

public import Opn.Parts
public import Opn.Roots
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Nat.Factorization.Basic

/-
A Fermat witness and "not a perfect power" give two different primes:
a number m ≥ 2 with a base a, 1 ≤ a < m, for which a^(m-1) is not 1
mod m, and which is no x^k with k ≥ 2, has two different prime
divisors. `witnessOk_two` is the same for a counted number that
`T2.witnessOk` accepts with count 2.
-/


@[expose] public section

namespace Opn

theorem two_primes_of_witness {m a : ℕ} (hm : 2 ≤ m) (ha : 1 ≤ a)
    (ham : a < m) (hw : a ^ (m - 1) % m ≠ 1)
    (hpp : T2.isPerfectPower m = false) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ m ∧ q ∣ m := by
  have hnp : ¬ m.Prime := by
    intro hp
    apply hw
    have hc : Nat.Coprime a m := by
      rw [Nat.coprime_comm]
      refine (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun hd => ?_)
      have := Nat.le_of_dvd (by omega) hd
      omega
    have h1 : a ^ m.totient ≡ 1 [MOD m] := Nat.ModEq.pow_totient hc
    rw [Nat.totient_prime hp] at h1
    have h2 : a ^ (m - 1) % m = 1 % m := h1
    rw [h2]
    exact Nat.mod_eq_of_lt (by omega)
  have hq : m.minFac.Prime := Nat.minFac_prime (by omega)
  by_contra hcon
  have hall : ∀ d : ℕ, d.Prime → d ∣ m → d = m.minFac := by
    intro d hd hdm
    by_contra hne
    exact hcon ⟨d, m.minFac, hd, hq, hne, hdm, Nat.minFac_dvd m⟩
  have he := Nat.eq_prime_pow_of_unique_prime_dvd (n := m)
    (p := m.minFac) (by omega) (fun {d} hd hdm => hall d hd hdm)
  generalize m.primeFactorsList.length = k at he
  rcases Nat.lt_or_ge k 2 with hk | hk
  · have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with e | e
    · rw [e, pow_zero] at he
      omega
    · rw [e, pow_one] at he
      rw [← he] at hq
      exact hnp hq
  · exact T2.not_pow_of_isPerfectPower_false hm hpp m.minFac k hk he.symm

/-- A counted number that `witnessOk` accepts with count 2 has two
different prime divisors. -/
theorem witnessOk_two {c : T2.Counted} (hm : 2 ≤ c.m)
    (h : T2.witnessOk c = true) (h2 : c.count = 2) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ c.m ∧ q ∣ c.m := by
  unfold T2.witnessOk at h
  have hc : (c.count == 2) = true := by simp [h2]
  rw [if_pos hc] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨ha, ham⟩, hw⟩, hpp⟩ := h
  rw [T2.powMod_eq] at hw
  exact two_primes_of_witness hm (by omega) ham hw hpp

end Opn
