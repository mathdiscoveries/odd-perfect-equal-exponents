module

public import Mathlib.NumberTheory.LucasPrimality
public import Mathlib.FieldTheory.Finite.Basic

/-
The step of Pocklington's theorem that the certificates use: for a
prime q dividing n, a Fermat witness a for the prime p of n - 1 puts
every power of p that divides n - 1 into q - 1. The hypotheses are in
the form `T2.pItemOk` checks them. (The theorem itself, over a list
of items, is not in this file yet.)
-/


@[expose] public section

namespace Opn

/-- If d divides m and not m / p, every power of p in m is in d. -/
theorem pow_dvd_of_not_dvd_div {d m p k : ℕ} (hp : p.Prime) (hd : d ∣ m)
    (hnd : ¬ d ∣ m / p) (hk : p ^ k ∣ m) : p ^ k ∣ d := by
  obtain ⟨c, rfl⟩ := hd
  have hpc : ¬ p ∣ c := by
    rintro ⟨c', rfl⟩
    apply hnd
    rw [show d * (p * c') = p * (d * c') by ring,
      Nat.mul_div_cancel_left _ hp.pos]
    exact dvd_mul_right _ _
  exact (Nat.Coprime.pow_left k
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpc)).dvd_of_dvd_mul_right hk

theorem pock_step {n q p a k : ℕ} (hn : 2 ≤ n) (hq : q.Prime) (hqn : q ∣ n)
    (hp : p.Prime) (h1 : a ^ (n - 1) % n = 1)
    (h2 : Nat.gcd ((a ^ ((n - 1) / p) % n + n - 1) % n) n = 1)
    (hk : p ^ k ∣ n - 1) : p ^ k ∣ q - 1 := by
  have : Fact q.Prime := ⟨hq⟩
  have hm1 : a ^ (n - 1) ≡ 1 [MOD q] := by
    have : a ^ (n - 1) ≡ 1 [MOD n] := by
      rw [Nat.ModEq, h1, Nat.mod_eq_of_lt (by omega)]
    exact this.of_dvd hqn
  have hx1 : (a : ZMod q) ^ (n - 1) = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hm1
    simpa using this
  have hx2 : (a : ZMod q) ^ ((n - 1) / p) ≠ 1 := by
    intro h
    have hm2 : a ^ ((n - 1) / p) ≡ 1 [MOD q] := by
      apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
      simpa using h
    have hxq : a ^ ((n - 1) / p) % n ≡ 1 [MOD q] :=
      ((Nat.mod_modEq _ n).of_dvd hqn).trans hm2
    have hn0 : n ≡ 0 [MOD q] := (Nat.modEq_zero_iff_dvd).mpr hqn
    have h3 : a ^ ((n - 1) / p) % n + n - 1 + 1 ≡ 0 + 1 [MOD q] := by
      have e : a ^ ((n - 1) / p) % n + n - 1 + 1
          = a ^ ((n - 1) / p) % n + n := by omega
      rw [e, zero_add]
      simpa using hxq.add hn0
    have h4 : q ∣ a ^ ((n - 1) / p) % n + n - 1 :=
      (Nat.modEq_zero_iff_dvd).mp (Nat.ModEq.add_right_cancel' 1 h3)
    have h5 : q ∣ (a ^ ((n - 1) / p) % n + n - 1) % n :=
      (Nat.dvd_mod_iff hqn).mpr h4
    have h6 : q ∣ 1 := h2 ▸ Nat.dvd_gcd h5 hqn
    exact hq.one_lt.ne' (Nat.dvd_one.mp h6)
  have ha0 : (a : ZMod q) ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega)] at hx1
    exact zero_ne_one hx1
  have hord : orderOf (a : ZMod q) ∣ n - 1 := orderOf_dvd_of_pow_eq_one hx1
  have hnd : ¬ orderOf (a : ZMod q) ∣ (n - 1) / p := fun h =>
    hx2 (orderOf_dvd_iff_pow_eq_one.mp h)
  have hq1 : orderOf (a : ZMod q) ∣ q - 1 :=
    orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one ha0)
  exact (pow_dvd_of_not_dvd_div hp hord hnd hk).trans hq1

end Opn
