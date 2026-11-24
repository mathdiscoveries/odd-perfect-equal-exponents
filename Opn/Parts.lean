module

public import Mathlib.NumberTheory.LucasPrimality
public import Opn.T2Check

/-
The parts of `T2.checkCert` compute what they are named for: `powMod`
is a power mod m, `phi r q` is 1 + q + ... + q^(r-1), and a number
that `trialPrime` accepts is prime. (`kthRoot` and `isPerfectPower`
are not in this file.)
-/


@[expose] public section

namespace T2

theorem powModAux_modEq (fuel b e m acc : ℕ) (he : e < 2 ^ fuel) :
    powModAux fuel b e m acc ≡ acc * b ^ e [MOD m] := by
  induction fuel generalizing b e acc with
  | zero =>
    have h0 : e = 0 := by simpa using he
    subst h0
    simp [powModAux, Nat.ModEq]
  | succ n ih =>
    have he2 : e / 2 < 2 ^ n := by
      rw [pow_succ, Nat.mul_comm] at he
      exact Nat.div_lt_of_lt_mul he
    have hb : (b * b % m) ^ (e / 2) ≡ (b * b) ^ (e / 2) [MOD m] :=
      (Nat.mod_modEq _ _).pow _
    rw [powModAux]
    split_ifs with h0 h1
    · subst h0
      simp [Nat.ModEq]
    · refine (ih _ _ _ he2).trans ?_
      have hE : b ^ e = b * (b * b) ^ (e / 2) := by
        conv_lhs => rw [← Nat.div_add_mod e 2, h1]
        rw [pow_succ, pow_mul]
        ring
      rw [hE, ← mul_assoc]
      exact (Nat.mod_modEq _ _).mul hb
    · refine (ih _ _ _ he2).trans ?_
      have h2 : e % 2 = 0 := by omega
      have hE : b ^ e = (b * b) ^ (e / 2) := by
        conv_lhs => rw [← Nat.div_add_mod e 2, h2]
        rw [Nat.add_zero, pow_mul]
        ring
      rw [hE]
      exact (Nat.ModEq.refl acc).mul hb

theorem powModAux_reduced (fuel b e m acc : ℕ) (h : acc % m = acc) :
    powModAux fuel b e m acc % m = powModAux fuel b e m acc := by
  induction fuel generalizing b e acc with
  | zero => simpa [powModAux] using h
  | succ n ih =>
    rw [powModAux]
    split_ifs with h0 h1
    · exact h
    · exact ih _ _ _ (Nat.mod_mod _ _)
    · exact ih _ _ _ h

/-- `powMod b e m` is b^e mod m. -/
theorem powMod_eq (b e m : ℕ) : powMod b e m = b ^ e % m := by
  have h := powModAux_modEq (Nat.log2 e + 1) (b % m) e m (1 % m)
    Nat.lt_log2_self
  have hr := powModAux_reduced (Nat.log2 e + 1) (b % m) e m (1 % m)
    (Nat.mod_mod _ _)
  have h2 : 1 % m * (b % m) ^ e ≡ b ^ e [MOD m] := by
    have := ((Nat.mod_modEq 1 m).mul ((Nat.mod_modEq b m).pow e))
    simpa using this
  unfold powMod
  rw [← hr]
  exact h.trans h2

theorem phiAux_eq (k q acc : ℕ) :
    phiAux k q acc = acc * q ^ k + ∑ i ∈ Finset.range k, q ^ i := by
  induction k generalizing acc with
  | zero => simp [phiAux]
  | succ n ih =>
    rw [phiAux, ih, Finset.sum_range_succ]
    ring

/-- `phi r q` is 1 + q + ... + q^(r-1). -/
theorem phi_eq {r : ℕ} (hr : 1 ≤ r) (q : ℕ) :
    phi r q = ∑ i ∈ Finset.range r, q ^ i := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  rw [phi, Nat.add_sub_cancel, phiAux_eq, Finset.sum_range_succ]
  ring

theorem trialAux_sound (fuel n d : ℕ) (h : trialAux fuel n d = true) :
    ∀ k, d ≤ k → k * k ≤ n → ¬ k ∣ n := by
  induction fuel generalizing d with
  | zero => simp [trialAux] at h
  | succ f ih =>
    rw [trialAux] at h
    split_ifs at h with h1 h2
    · intro k hk hkn
      have := Nat.mul_le_mul hk hk
      omega
    · intro k hk hkn hdiv
      rcases Nat.eq_or_lt_of_le hk with rfl | hlt
      · exact h2 (Nat.mod_eq_zero_of_dvd hdiv)
      · exact ih (d + 1) h k hlt hkn hdiv

/-- A number that trial division accepts is prime. -/
theorem trialPrime_sound {n : ℕ} (h : trialPrime n = true) : n.Prime := by
  simp only [trialPrime, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [Nat.prime_def_le_sqrt]
  exact ⟨h.1, fun m hm hms =>
    trialAux_sound _ _ _ h.2 m hm (Nat.le_sqrt.mp hms)⟩

end T2
