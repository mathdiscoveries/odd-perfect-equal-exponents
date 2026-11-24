module

public import Opn.LemmaC

/-
Lemma C (b) of t2-method-1.md, the two parts the library's proofs use, for
Φ(q) = 1 + q + ⋯ + q^(r−1) written as a sum over `Finset.range r`:
r divides Φ(q) when q ≡ 1 (mod r), and, for r prime, r does not divide
Φ(q) when q ≢ 1 (mod r). The page's third part, that r² does not divide
Φ(q), is not used: Theorem T counts each such q at least once, which
needs only the first part.
-/


@[expose] public section

namespace Opn

/-- Lemma C (b), first part: q ≡ 1 (mod r) gives r ∣ Φ(q). -/
theorem r_dvd_geom {r q : ℕ} (h : q % r = 1) :
    r ∣ ∑ i ∈ Finset.range r, q ^ i := by
  rw [← ZMod.natCast_eq_zero_iff]
  have hq : (q : ZMod r) = 1 := by
    rw [← ZMod.natCast_mod, h, Nat.cast_one]
  push_cast
  rw [hq]
  simp

/-- Lemma C (b), second part: for r prime, q ≢ 1 (mod r) gives r ∤ Φ(q). -/
theorem not_r_dvd_geom {r q : ℕ} (hr : r.Prime) (h : q % r ≠ 1) :
    ¬ r ∣ ∑ i ∈ Finset.range r, q ^ i := by
  intro hd
  have : Fact r.Prime := ⟨hr⟩
  have hS : ((∑ i ∈ Finset.range r, q ^ i : ℕ) : ZMod r) = 0 :=
    (ZMod.natCast_eq_zero_iff _ r).mpr hd
  have hz : ((∑ i ∈ Finset.range r, q ^ i : ℕ) : ZMod r) * (q : ZMod r) + 1
      = ((∑ i ∈ Finset.range r, q ^ i : ℕ) : ZMod r) + (q : ZMod r) ^ r := by
    exact_mod_cast congrArg (Nat.cast (R := ZMod r)) (geom_mul q r)
  rw [hS, zero_mul, zero_add, zero_add, ZMod.pow_card] at hz
  apply h
  have h1 : ((q % r : ℕ) : ZMod r) = ((1 : ℕ) : ZMod r) := by
    rw [ZMod.natCast_mod, ← hz, Nat.cast_one]
  rw [ZMod.natCast_eq_natCast_iff'] at h1
  rwa [Nat.mod_mod, Nat.mod_eq_of_lt hr.one_lt] at h1

end Opn
