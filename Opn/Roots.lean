module

public import Mathlib.NumberTheory.LucasPrimality
public import Opn.T2Check

/-
Two more parts of `T2.checkCert` compute what they are named for:
`kthRoot m k` is the integer part of the k-th root of m, and a number
m ≥ 2 that `isPerfectPower` rejects is no x^k with k ≥ 2.
-/


@[expose] public section

namespace T2

/-- The bisection keeps lo^k ≤ m < (hi + 1)^k and ends with lo = hi
when the fuel covers the width. -/
theorem rootAux_spec (fuel m k lo hi : ℕ) (hlo : lo ^ k ≤ m)
    (hhi : m < (hi + 1) ^ k) (hle : lo ≤ hi) (hw : hi - lo < 2 ^ fuel) :
    rootAux fuel m k lo hi ^ k ≤ m
      ∧ m < (rootAux fuel m k lo hi + 1) ^ k := by
  induction fuel generalizing lo hi with
  | zero =>
    rw [pow_zero] at hw
    have e : hi = lo := by omega
    rw [e] at hhi
    rw [rootAux]
    exact ⟨hlo, hhi⟩
  | succ n ih =>
    rw [pow_succ] at hw
    rw [rootAux]
    split_ifs with h1 h2
    · exact ih _ _ h2 hhi (by omega) (by omega)
    · have e : (lo + hi + 1) / 2 - 1 + 1 = (lo + hi + 1) / 2 := by omega
      have h3 : m < ((lo + hi + 1) / 2 - 1 + 1) ^ k := by
        rw [e]
        exact Nat.lt_of_not_le h2
      exact ih _ _ hlo h3 (by omega) (by omega)
    · have e : hi = lo := by omega
      rw [e] at hhi
      exact ⟨hlo, hhi⟩

/-- For m ≥ 1 and k ≥ 1, `kthRoot m k` is the largest x with x^k ≤ m. -/
theorem kthRoot_spec {m k : ℕ} (hm : 1 ≤ m) (hk : k ≠ 0) :
    kthRoot m k ^ k ≤ m ∧ m < (kthRoot m k + 1) ^ k := by
  unfold kthRoot
  have h1 : m < 2 ^ (Nat.log2 m + 1) := Nat.lt_log2_self
  have h2 : Nat.log2 m + 1 < k * ((Nat.log2 m + 1) / k + 1) :=
    Nat.lt_mul_div_succ _ (Nat.pos_of_ne_zero hk)
  have h3 : 2 ^ (Nat.log2 m + 1)
      ≤ 2 ^ (k * ((Nat.log2 m + 1) / k + 1)) :=
    Nat.pow_le_pow_right (by norm_num) h2.le
  have h4 : 2 ^ (k * ((Nat.log2 m + 1) / k + 1))
      = (2 ^ ((Nat.log2 m + 1) / k + 1)) ^ k := by
    rw [Nat.mul_comm, pow_mul]
  have h5 : (2 ^ ((Nat.log2 m + 1) / k + 1)) ^ k
      ≤ (2 ^ ((Nat.log2 m + 1) / k + 1) + 1) ^ k :=
    Nat.pow_le_pow_left (Nat.le_succ _) k
  have h6 : 1 ≤ 2 ^ ((Nat.log2 m + 1) / k + 1) := Nat.one_le_two_pow
  have h7 : 2 ^ ((Nat.log2 m + 1) / k + 1)
      ≤ 2 ^ ((Nat.log2 m + 1) / k + 3) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  apply rootAux_spec
  · rw [one_pow]
    exact hm
  · omega
  · exact h6
  · omega

/-- The root of an exact power is its base. -/
theorem kthRoot_pow (x k : ℕ) (hx : 1 ≤ x) (hk : k ≠ 0) :
    kthRoot (x ^ k) k = x := by
  obtain ⟨h1, h2⟩ := kthRoot_spec (m := x ^ k) (Nat.one_le_pow _ _ hx) hk
  have a : kthRoot (x ^ k) k ≤ x := by
    by_contra hc
    have h3 : (x + 1) ^ k ≤ kthRoot (x ^ k) k ^ k :=
      Nat.pow_le_pow_left (by omega) k
    have h4 : x ^ k < (x + 1) ^ k :=
      Nat.pow_lt_pow_left (Nat.lt_succ_self x) hk
    omega
  have b : x < kthRoot (x ^ k) k + 1 := by
    by_contra hc
    have h3 : (kthRoot (x ^ k) k + 1) ^ k ≤ x ^ k :=
      Nat.pow_le_pow_left (by omega) k
    omega
  omega

theorem trialAux_of_prime (fuel n d : ℕ) (hp : n.Prime) (hd : 2 ≤ d)
    (hf : 1 ≤ fuel) (hbound : n < (d + fuel - 1) * (d + fuel - 1)) :
    trialAux fuel n d = true := by
  induction fuel generalizing d with
  | zero => omega
  | succ f ih =>
    rw [trialAux]
    split_ifs with h1 h2
    · rfl
    · exfalso
      have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero h2
      rcases hp.eq_one_or_self_of_dvd d hdvd with rfl | hdn
      · omega
      · subst hdn
        have : 2 * d ≤ d * d := Nat.mul_le_mul_right d (by omega)
        omega
    · have hf1 : 1 ≤ f := by
        by_contra hc
        have hf0 : f = 0 := by omega
        subst hf0
        simp at hbound
        omega
      exact ih (d + 1) (by omega) hf1 (by
        have : d + 1 + f - 1 = d + (f + 1) - 1 := by omega
        rw [this]; exact hbound)

theorem trialPrime_of_prime {p : ℕ} (hp : p.Prime) (hlt : p < SMALL) :
    trialPrime p = true := by
  unfold trialPrime
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hp.two_le, trialAux_of_prime 1001 p 2 hp (by omega) (by omega) ?_⟩
  unfold SMALL at hlt
  omega

theorem noDivBelow_spec (B m : ℕ) (h : noDivBelow B m = true) :
    ∀ d, 2 ≤ d → d ≤ B → ¬ d ∣ m := by
  induction B with
  | zero => intro d hd1 hd2; omega
  | succ b ih =>
    rw [noDivBelow] at h
    split_ifs at h with h1
    · intro d hd1 hd2; omega
    · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      intro d hd1 hd2 hdvd
      rcases Nat.eq_or_lt_of_le hd2 with rfl | hlt
      · exact h.1 (Nat.mod_eq_zero_of_dvd hdvd)
      · exact ih h.2 d hd1 (by omega) hdvd

theorem ppAux_false (fuel m k : ℕ) (h : ppAux fuel m k = false) (p : ℕ)
    (hp : p.Prime) (hj : k ≤ p) (hj2 : p < k + fuel) :
    kthRoot m p ^ p ≠ m := by
  induction fuel generalizing k with
  | zero => omega
  | succ n ih =>
    rw [ppAux, Bool.or_eq_false_iff] at h
    rcases Nat.eq_or_lt_of_le hj with e | hlt
    · rw [← e] at hp ⊢
      have hfilt : (k == 2 || (k % 2 == 1 && (k >= SMALL || trialPrime k))) = true := by
        rcases hp.eq_two_or_odd with rfl | hodd
        · rfl
        · simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
          right
          refine ⟨hodd, ?_⟩
          by_cases hsm : k < SMALL
          · right; exact trialPrime_of_prime hp hsm
          · left; omega
      have h1 := h.1
      rw [hfilt, Bool.true_and] at h1
      intro hc
      rw [hc] at h1
      simp at h1
    · exact ih (k + 1) h.2 (by omega) (by omega)

/-- A number m ≥ 2 that `isPerfectPower` rejects is no x^k, k ≥ 2. -/
theorem not_pow_of_isPerfectPower_false {m : ℕ} (hm : 2 ≤ m)
    (h : isPerfectPower m = false) (x k : ℕ) (hk : 2 ≤ k) :
    x ^ k ≠ m := by
  intro hx
  subst hx
  have hx1 : 2 ≤ x := by
    by_contra hc
    have hx01 : x = 0 ∨ x = 1 := by omega
    rcases hx01 with e | e
    · rw [e, zero_pow (by omega)] at hm
      omega
    · rw [e, one_pow] at hm
      omega
  set p := k.minFac with hp_def
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpdvd : p ∣ k := Nat.minFac_dvd k
  obtain ⟨q, hq⟩ := hpdvd
  set y := x ^ q
  have hy1 : 2 ≤ y := by
    have hq1 : 1 ≤ q := by
      by_contra hc
      have hq0 : q = 0 := by omega
      rw [hq0, mul_zero] at hq
      omega
    calc 2 ≤ x := hx1
      _ = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ q := Nat.pow_le_pow_right (by omega) hq1
  have hxy : y ^ p = x ^ k := by
    rw [hq, mul_comm, pow_mul]
  have hp2 : 2 ≤ p := hp.two_le
  have hkl : p ≤ Nat.log2 (x ^ k) := by
    have h1 : 2 ^ p ≤ y ^ p := Nat.pow_le_pow_left hy1 p
    rw [hxy] at h1
    by_contra hc
    have h2 : x ^ k < 2 ^ (Nat.log2 (x ^ k) + 1) := Nat.lt_log2_self
    have h3 : 2 ^ (Nat.log2 (x ^ k) + 1) ≤ 2 ^ p :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  unfold isPerfectPower at h
  dsimp only at h
  split_ifs at h with hnd
  · have hx64 : 64 ≤ x := by
      by_contra hc
      have hdvd : x ∣ x ^ k := dvd_pow_self x (by omega)
      exact noDivBelow_spec 63 (x ^ k) hnd x hx1 (by omega) hdvd
    have hy64 : 64 ≤ y := by
      have hq1 : 1 ≤ q := by
        by_contra hc
        have hq0 : q = 0 := by omega
        rw [hq0, mul_zero] at hq
        omega
      calc 64 ≤ x := hx64
        _ = x ^ 1 := (pow_one x).symm
        _ ≤ x ^ q := Nat.pow_le_pow_right (by omega) hq1
    have h6p : 6 * p ≤ Nat.log2 (x ^ k) := by
      have h1 : (2 ^ 6) ^ p ≤ y ^ p := Nat.pow_le_pow_left hy64 p
      rw [← pow_mul, hxy] at h1
      by_contra hc
      have h2 : x ^ k < 2 ^ (Nat.log2 (x ^ k) + 1) := Nat.lt_log2_self
      have h3 : 2 ^ (Nat.log2 (x ^ k) + 1) ≤ 2 ^ (6 * p) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact ppAux_false (Nat.log2 (x ^ k) / 6 + 1) (x ^ k) 2 h p hp hp2 (by omega)
      (by rw [← hxy, kthRoot_pow y p (by omega) (by omega)])
  · exact ppAux_false (Nat.log2 (x ^ k)) (x ^ k) 2 h p hp hp2 (by omega)
      (by rw [← hxy, kthRoot_pow y p (by omega) (by omega)])

end T2
