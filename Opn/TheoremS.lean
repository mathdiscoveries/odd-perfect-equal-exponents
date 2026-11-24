module

public import Opn.TheoremT
public import Opn.PocklingtonList
public import Opn.TwoPrimes
public import Opn.Statement

/-
Theorem S of t2-method-1.md: a certificate that `T2.checkCert` accepts,
not resting on the cited fact, rules out every odd perfect N whose
primes other than one prime π all have exponent r − 1.

The list parts of the function are proved here as they are used:
`stepsAux` (conditions P, S2, S3), `countedAux` (C1, W, C3), `need`
(C4) and `owedOk` (E). The checker's own conditions that the proof
does not need (one main case only, the specials odd and distinct) are
left as the checker has them.
-/


@[expose] public section

namespace Opn

open Finset

/-- The hypotheses a case of a certificate is read under. -/
structure Hyp (N π r : ℕ) : Prop where
  odd : Odd N
  perf : N.Perfect
  hπ : π.Prime
  hr : r.Prime
  hr3 : 3 ≤ r
  rodd : r % 2 = 1
  exp : ∀ q, q.Prime → q ∣ N → q ≠ π → N.factorization q = r - 1
  rN : r ∣ N
  rπ : r ≠ π
  half : (π + 1) / 2 ∣ N

/-- Φ(x) = `phi r x` divides N for a prime x ≠ π of N. -/
theorem Hyp.phi_dvd {N π r : ℕ} (H : Hyp N π r) {x : ℕ} (hx : x.Prime)
    (hxN : x ∣ N) (hxπ : x ≠ π) : T2.phi r x ∣ N := by
  rw [T2.phi_eq (by have := H.hr3; omega)]
  exact geom_dvd H.odd H.perf hx hxN (by have := H.hr3; omega) H.rodd
    (H.exp x hx hxN hxπ)

/-- `stepsAux` only adds to its list. -/
theorem stepsAux_sub (r : ℕ) (sp : Option ℕ) (proven : List ℕ) :
    ∀ (steps : List T2.Step) (acc out : List ℕ),
      T2.stepsAux r sp proven steps acc = some out → ∀ x ∈ acc, x ∈ out := by
  intro steps
  induction steps with
  | nil =>
    intro acc out h x hx
    rw [T2.stepsAux] at h
    cases h
    exact hx
  | cons s ss ih =>
    intro acc out h x hx
    rw [T2.stepsAux] at h
    split_ifs at h with hc
    exact ih _ _ h x (List.mem_append_left _ hx)

/-- In a case π = p, no parent is p (condition S3). -/
theorem stepsAux_ne (r p : ℕ) (proven : List ℕ) :
    ∀ (steps : List T2.Step) (acc out : List ℕ),
      T2.stepsAux r (some p) proven steps acc = some out →
      (∀ x ∈ acc, x ≠ p) → ∀ x ∈ out, x ≠ p := by
  intro steps
  induction steps with
  | nil =>
    intro acc out h hacc
    rw [T2.stepsAux] at h
    cases h
    exact hacc
  | cons s ss ih =>
    intro acc out h hacc
    rw [T2.stepsAux] at h
    split_ifs at h with hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨⟨⟨-, -⟩, hsp⟩, -⟩, -⟩ := hc
    apply ih _ _ h
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hacc x hx
    · rw [List.mem_singleton] at hx
      rw [hx]
      intro e
      exact hsp (by rw [e])

/-- Conditions P and S2: every parent is a prime dividing N. -/
theorem stepsAux_sound {N π r : ℕ} (H : Hyp N π r) {sp : Option ℕ}
    (hsp : ∀ p, sp = some p → p = π) {proven : List ℕ}
    (hpr : ∀ x ∈ proven, x.Prime) :
    ∀ (steps : List T2.Step) (acc out : List ℕ),
      T2.stepsAux r sp proven steps acc = some out → (∀ x ∈ out, x ≠ π) →
      (∀ x ∈ acc, x.Prime ∧ x ∣ N) → ∀ x ∈ out, x.Prime ∧ x ∣ N := by
  intro steps
  induction steps with
  | nil =>
    intro acc out h _ hacc
    rw [T2.stepsAux] at h
    cases h
    exact hacc
  | cons s ss ih =>
    intro acc out h hout hacc
    rw [T2.stepsAux] at h
    split_ifs at h with hc
    have hsub := stepsAux_sub r sp proven ss _ _ h
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨⟨⟨-, hpok⟩, -⟩, hwhy⟩, -⟩ := hc
    have hprime := primeOk_sound hpr hpok
    have hsπ : s.parent ≠ π :=
      hout _ (hsub _ (List.mem_append_right _ (List.mem_singleton_self _)))
    apply ih _ _ h hout
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hacc x hx
    · rw [List.mem_singleton] at hx
      rw [hx]
      refine ⟨hprime, ?_⟩
      cases hw : s.why with
      | r =>
        rw [hw] at hwhy
        simp only [T2.whyOk, beq_iff_eq] at hwhy
        rw [hwhy]
        exact H.rN
      | half =>
        rw [hw] at hwhy
        cases hsp' : sp with
        | none =>
          rw [hsp'] at hwhy
          simp [T2.whyOk] at hwhy
        | some p =>
          rw [hsp'] at hwhy
          simp only [T2.whyOk, beq_iff_eq] at hwhy
          rw [hsp p hsp'] at hwhy
          exact (Nat.dvd_of_mod_eq_zero hwhy).trans H.half
      | phiOf y =>
        rw [hw] at hwhy
        simp only [T2.whyOk, Bool.and_eq_true, beq_iff_eq] at hwhy
        obtain ⟨hy, hmod⟩ := hwhy
        have hyacc : y ∈ acc := by simpa using hy
        obtain ⟨hyp, hyN⟩ := hacc y hyacc
        have hyπ := hout y (hsub y (List.mem_append_left _ hyacc))
        exact (Nat.dvd_of_mod_eq_zero hmod).trans (H.phi_dvd hyp hyN hyπ)

/-- Condition C1: every prime of a counted number divides N and is
≡ 1 (mod r). -/
theorem counted_prime {N π r : ℕ} (H : Hyp N π r) {parents : List ℕ}
    (hpar : ∀ x ∈ parents, x.Prime ∧ x ∣ N ∧ x ≠ π) {c : T2.Counted}
    (hok : T2.countedOk r parents c = true) {s : ℕ} (hs : s.Prime)
    (hsd : s ∣ c.m) : s ∣ N ∧ s % r = 1 := by
  unfold T2.countedOk at hok
  split_ifs at hok with hp
  · simp only [Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨hmem, hmod⟩ := hok
    have hm : c.m ∈ parents := by simpa using hmem
    obtain ⟨hmp, hmN, -⟩ := hpar _ hm
    have e : s = c.m := (Nat.prime_dvd_prime_iff_eq hs hmp).mp hsd
    rw [e]
    exact ⟨hmN, hmod⟩
  · simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hok
    obtain ⟨⟨hmem, hmod⟩, hr0⟩ := hok
    have hof : c.of ∈ parents := by simpa using hmem
    obtain ⟨hop, hoN, hoπ⟩ := hpar _ hof
    have hΦ : c.m ∣ T2.phi r c.of := Nat.dvd_of_mod_eq_zero hmod
    have hsΦ := hsd.trans hΦ
    refine ⟨hsΦ.trans (H.phi_dvd hop hoN hoπ), ?_⟩
    rw [T2.phi_eq (by have := H.hr3; omega)] at hsΦ
    rcases prime_dvd_geom H.hr hs hsΦ with h | h
    · rw [h] at hsd
      exact absurd (Nat.mod_eq_zero_of_dvd hsd) hr0
    · exact h

/-- A counted number with count k (condition W) has a set of k primes. -/
theorem counted_set {c : T2.Counted} (hm : 2 ≤ c.m)
    (hw : T2.witnessOk c = true) :
    ∃ A : Finset ℕ, A.card = c.count ∧ ∀ s ∈ A, s.Prime ∧ s ∣ c.m := by
  by_cases h2 : c.count = 2
  · obtain ⟨p, q, hp, hq, hpq, hpd, hqd⟩ := witnessOk_two hm hw h2
    refine ⟨{p, q}, ?_, ?_⟩
    · rw [card_pair hpq, h2]
    · intro s hs
      rcases mem_insert.mp hs with e | hs
      · rw [e]
        exact ⟨hp, hpd⟩
      · rw [mem_singleton.mp hs]
        exact ⟨hq, hqd⟩
  · unfold T2.witnessOk at hw
    have hc : (c.count == 2) = false := by simp [h2]
    rw [if_neg (by simp [hc])] at hw
    have h1 : c.count = 1 := by simpa using hw
    refine ⟨{c.m.minFac}, by rw [card_singleton, h1], ?_⟩
    intro s hs
    rw [mem_singleton.mp hs]
    exact ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd _⟩

/-- Conditions C1, W, C3: the counts add up to distinct primes. -/
theorem countedAux_sound {N π r : ℕ} (H : Hyp N π r) {parents : List ℕ}
    (hpar : ∀ x ∈ parents, x.Prime ∧ x ∣ N ∧ x ≠ π) :
    ∀ (cs : List T2.Counted) (seen : List ℕ) (total : ℕ) (seen' : List ℕ)
      (total' : ℕ) (T : Finset ℕ),
      T2.countedAux r parents cs seen total = some (seen', total') →
      (∀ s ∈ T, s.Prime ∧ s ∣ N ∧ s % r = 1 ∧ ∃ m ∈ seen, s ∣ m) →
      total ≤ T.card →
      ∃ T' : Finset ℕ,
        (∀ s ∈ T', s.Prime ∧ s ∣ N ∧ s % r = 1 ∧ ∃ m ∈ seen', s ∣ m) ∧
        total' ≤ T'.card := by
  intro cs
  induction cs with
  | nil =>
    intro seen total seen' total' T h hT htot
    rw [T2.countedAux] at h
    cases h
    exact ⟨T, hT, htot⟩
  | cons c cs ih =>
    intro seen total seen' total' T h hT htot
    rw [T2.countedAux] at h
    split_ifs at h with hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      beq_iff_eq] at hc
    obtain ⟨⟨⟨hm2, hok⟩, hw⟩, hcop⟩ := hc
    obtain ⟨A, hAc, hA⟩ := counted_set hm2 hw
    have hdisj : Disjoint T A := by
      rw [Finset.disjoint_left]
      intro s hsT hsA
      obtain ⟨hsp, -, -, m, hm, hsm⟩ := hT s hsT
      obtain ⟨-, hsc⟩ := hA s hsA
      have hg := hcop m hm
      have : s ∣ Nat.gcd c.m m := Nat.dvd_gcd hsc hsm
      rw [hg] at this
      exact hsp.one_lt.ne' (Nat.dvd_one.mp this)
    apply ih (c.m :: seen) (total + c.count) seen' total' (T ∪ A) h
    · intro s hs
      rcases mem_union.mp hs with hs | hs
      · obtain ⟨h1, h2, h3, m, hm, hsm⟩ := hT s hs
        exact ⟨h1, h2, h3, m, List.mem_cons_of_mem _ hm, hsm⟩
      · obtain ⟨hsp, hsc⟩ := hA s hs
        obtain ⟨hsN, hsr⟩ := counted_prime H hpar hok hsp hsc
        exact ⟨hsp, hsN, hsr, c.m, List.mem_cons_self .., hsc⟩
    · rw [card_union_of_disjoint hdisj, hAc]
      omega

/-- A case whose assumption is true leads to a contradiction. -/
theorem case_false {N π r : ℕ} (H : Hyp N π r) {proven : List ℕ}
    (hpr : ∀ x ∈ proven, x.Prime) {k : T2.Case} {parents : List ℕ}
    (hk : T2.caseOk r proven k = some parents)
    (hass : (k.special = none ∧ π ∉ parents) ∨ k.special = some π) :
    False := by
  unfold T2.caseOk at hk
  cases hs : T2.stepsAux r k.special proven k.steps [] with
  | none => simp [hs] at hk
  | some ps =>
    simp only [hs] at hk
    cases hc : T2.countedAux r ps k.counted [] 0 with
    | none => simp [hc] at hk
    | some st =>
      obtain ⟨seen, total⟩ := st
      simp only [hc] at hk
      split_ifs at hk with hneed
      simp only [Option.some.injEq] at hk
      subst hk
      have hne : ∀ x ∈ ps, x ≠ π := by
        rcases hass with ⟨-, hπ⟩ | hsp
        · intro x hx e
          exact hπ (e ▸ hx)
        · rw [hsp] at hs
          exact stepsAux_ne r π proven k.steps [] ps hs (by simp)
      have hsp : ∀ p, k.special = some p → p = π := by
        intro p hp
        rcases hass with ⟨h0, -⟩ | h1
        · rw [h0] at hp
          cases hp
        · rw [h1] at hp
          exact (Option.some.inj hp).symm
      have hpar0 := stepsAux_sound H hsp hpr k.steps [] ps hs hne (by simp)
      have hpar : ∀ x ∈ ps, x.Prime ∧ x ∣ N ∧ x ≠ π :=
        fun x hx => ⟨(hpar0 x hx).1, (hpar0 x hx).2, hne x hx⟩
      obtain ⟨T, hT, htot⟩ := countedAux_sound H hpar k.counted [] 0 seen total
        ∅ hc (by simp) (by simp)
      -- Theorem T on the counted primes other than π.
      have hC := count_le H.odd H.perf H.hr H.hr3 H.exp H.rπ (T.erase π)
        (fun s hs => by
          rw [mem_erase] at hs
          obtain ⟨h1, h2, h3, -⟩ := hT s hs.2
          exact ⟨h1, h2, hs.1, h3⟩)
      have hle : T.card - 1 ≤ (T.erase π).card := pred_card_le_card_erase
      have hr3 := H.hr3
      rcases hass with ⟨h0, -⟩ | h1
      · rw [h0] at hneed
        simp only [T2.need] at hneed
        omega
      · rw [h1] at hneed
        simp only [T2.need] at hneed
        split_ifs at hneed with hall
        · -- every counted number is prime to π, so π is not counted
          have hπT : π ∉ T := by
            intro hπT
            obtain ⟨-, -, -, m, hm, hπm⟩ := hT π hπT
            simp only [List.all_eq_true, beq_iff_eq] at hall
            have : π ∣ Nat.gcd m π := Nat.dvd_gcd hπm (dvd_refl π)
            rw [hall m hm] at this
            exact H.hπ.one_lt.ne' (Nat.dvd_one.mp this)
          rw [erase_eq_of_notMem hπT] at hC
          omega
        · omega

/-- Theorem S. -/
theorem sound (c : T2.Cert) (h : T2.checkCert c = true)
    (hcited : c.cited = false) :
    ¬ ∃ N, Odd N ∧ N.Perfect ∧ EqualExponents c.r N := by
  rintro ⟨N, hN, hperf, π, hπ, hexp⟩
  unfold T2.checkCert at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hr3, hrodd⟩, htrial⟩, hcit⟩, hrest⟩ := h
  have hr := T2.trialPrime_sound htrial
  have hr4 : c.r % 4 ≠ 1 := by
    rw [hcited] at hcit
    simpa using hcit
  have heven : ∀ q, q.Prime → q ∣ N → q ≠ π → Even (N.factorization q) := by
    intro q hq hqN hqπ
    rw [hexp q hq hqN hqπ]
    exact ⟨(c.r - 1) / 2, by omega⟩
  obtain ⟨hπN, -, hπ4, hhalf⟩ := special_prime hN hperf hπ heven
  have hrπ : c.r ≠ π := by
    rintro rfl
    exact hr4 hπ4
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
