module

public import Opn.TheoremS

/-
Theorem S given the cited fact, for r ≡ 1 (mod 4) (t2-method-1.md,
section 2, Corollary R′ and the paragraph after it): a certificate
that `T2.checkCert` accepts, marked as resting on the cited fact, rules
out every odd perfect N whose primes other than one prime π all have
exponent r − 1, given that fact for r.

The fact is stated as `NotSpecial r`: in an odd perfect number whose
every prime has an odd exponent or the exponent r − 1, the prime r
does not have an odd exponent. Cohen and Williams (1985, p. 71, fact
(iii)) state it as "p ≠ r" for the special prime p, citing Kanold
(1941). It is a hypothesis here, not proved. The rest of the proof is
Theorem S's (`Opn.sound`, TheoremS.lean), unchanged from the line that
builds `Hyp`.
-/


@[expose] public section

namespace Opn

open Finset

/-- The cited fact for r: r is not the prime with the odd exponent. -/
def NotSpecial (r : ℕ) : Prop :=
  ∀ N : ℕ, Odd N → N.Perfect →
    (∀ q : ℕ, q.Prime → q ∣ N →
      Odd (N.factorization q) ∨ N.factorization q = r - 1) →
    ¬ Odd (N.factorization r)

/-- Theorem S given the cited fact for c.r. -/
theorem sound_given (c : T2.Cert) (h : T2.checkCert c = true)
    (hfact : NotSpecial c.r) :
    ¬ ∃ N, Odd N ∧ N.Perfect ∧ EqualExponents c.r N := by
  rintro ⟨N, hN, hperf, π, hπ, hexp⟩
  unfold T2.checkCert at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hr3, hrodd⟩, htrial⟩, -⟩, hrest⟩ := h
  have hr := T2.trialPrime_sound htrial
  have heven : ∀ q, q.Prime → q ∣ N → q ≠ π → Even (N.factorization q) := by
    intro q hq hqN hqπ
    rw [hexp q hq hqN hqπ]
    exact ⟨(c.r - 1) / 2, by omega⟩
  obtain ⟨hπN, hπodd, hπ4, hhalf⟩ := special_prime hN hperf hπ heven
  have hrπ : c.r ≠ π := by
    intro hrπ'
    refine hfact N hN hperf (fun q hq hqN => ?_) (hrπ' ▸ hπodd)
    by_cases hqπ : q = π
    · exact Or.inl (hqπ ▸ hπodd)
    · exact Or.inr (hexp q hq hqN hqπ)
  have hrN := r_dvd hN hperf hπ hr hr3 hexp
  have H : Hyp N π c.r := ⟨hN, hperf, hπ, hr, hr3, hrodd, hexp, hrN, hrπ, hhalf⟩
  cases hp : T2.provenPrimes c.primes [] with
  | none => simp [hp] at hrest
  | some proven =>
    have hpr := provenPrimes_nil_prime hp
    simp only [hp, Bool.and_eq_true, List.all_eq_true] at hrest
    obtain ⟨⟨⟨⟨-, -⟩, -⟩, hall⟩, howed⟩ := hrest
    cases hmain : c.cases.filter (fun k => k.special.isNone) with
    | nil =>
      rw [hmain] at howed
      simp [T2.owedOk] at howed
    | cons k0 rest =>
      rw [hmain] at howed
      have hk0f : k0 ∈ c.cases.filter (fun k => k.special.isNone) := by
        rw [hmain]
        simp
      have hk0sp : k0.special = none := by
        have := (List.mem_filter.mp hk0f).2
        simpa using this
      simp only [T2.owedOk] at howed
      cases hk0 : T2.caseOk c.r proven k0 with
      | none => simp [hk0] at howed
      | some ps0 =>
        simp only [hk0, List.all_eq_true] at howed
        by_cases hπps : π ∈ ps0
        · have hw := howed π hπps
          have hπr : π ≠ c.r := fun e => hrπ e.symm
          simp [hπ4, hπr] at hw
          obtain ⟨k, hk, hks⟩ := hw
          obtain ⟨ps, hps⟩ := Option.isSome_iff_exists.mp (hall k hk)
          exact case_false H hpr hps (Or.inr hks)
        · exact case_false H hpr hk0 (Or.inl ⟨hk0sp, hπps⟩)

end Opn
