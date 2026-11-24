module

public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic
public import Opn.LemmaCb
public import Opn.LemmaD

/-
Lemma R of t2-method-1.md: if N is odd and perfect, π is prime, r is a
prime at least 3, and every prime of N other than π has exponent r − 1,
then r divides N.

The proof is the page's: if r ∤ N, every Φ(q) is a power of π, the
primes q other than π grow fast (q' > q^(r−1) for q < q', by the
cyclic group of units modulo a power of π), and then
σ(N)/N < 13/12 × 11/6 < 2. The bound on the product over the q is
proved here in the form ∏ q/(q − 1) ≤ (x + 1)/(x − 1) for primes at
least x with q' > q², which replaces the page's exp bound.
-/


@[expose] public section

namespace Opn

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Φ grows with q. -/
theorem geom_strictMono {r : ℕ} (hr : 2 ≤ r) {q q' : ℕ} (h : q < q') :
    ∑ i ∈ range r, q ^ i < ∑ i ∈ range r, q' ^ i := by
  apply Finset.sum_lt_sum
  · intro i _
    exact Nat.pow_le_pow_left h.le i
  · exact ⟨1, mem_range.mpr (by omega), by simpa using h⟩

/-- q ≡ 1 (mod m) gives Φ(q) ≡ r (mod m). -/
theorem geom_mod_of_one {r q m : ℕ} (h : q % m = 1 % m) :
    (∑ i ∈ range r, q ^ i) % m = r % m := by
  rw [← ZMod.natCast_eq_natCast_iff']
  have hq : (q : ZMod m) = 1 := by
    rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff']
    exact h
  push_cast
  rw [hq]
  simp

/-- Step 3 of Lemma R: if Φ(q) = π^a and π^a divides Φ(q'), with q < q'
primes and q' ≢ 1 (mod π^a), then q' > q^(r−1). -/
theorem growth {r π a q q' : ℕ} (hr : r.Prime) (hr3 : 3 ≤ r)
    (hπ : π.Prime) (hπ2 : π ≠ 2) (hq : q.Prime) (hq' : q'.Prime)
    (hqq : q < q') (hP : ∑ i ∈ range r, q ^ i = π ^ a)
    (hP' : π ^ a ∣ ∑ i ∈ range r, q' ^ i) (h1 : q' % π ^ a ≠ 1) :
    q ^ (r - 1) < q' := by
  classical
  have hq2 := hq.two_le
  have hPgt : q ^ (r - 1) < π ^ a := hP ▸ geom_gt (by omega) q
  have hqle : q ≤ q ^ (r - 1) := by
    calc q = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ (r - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hqP : q < π ^ a := lt_of_le_of_lt hqle hPgt
  have : NeZero (π ^ a) := ⟨pow_ne_zero _ hπ.ne_zero⟩
  have : Fact r.Prime := ⟨hr⟩
  have : IsCyclic (ZMod (π ^ a))ˣ := ZMod.isCyclic_units_of_prime_pow π hπ hπ2 a
  have hcopq : Nat.Coprime q (π ^ a) := by
    rw [← hP]
    exact geom_coprime (by omega) hq2
  have hcopq' : Nat.Coprime q' (π ^ a) :=
    Nat.Coprime.coprime_dvd_right hP' (geom_coprime (by omega) hq'.two_le)
  have hpow : ∀ x : ℕ, π ^ a ∣ ∑ i ∈ range r, x ^ i →
      (x : ZMod (π ^ a)) ^ r = 1 := by
    intro x hx
    have hS : ((∑ i ∈ range r, x ^ i : ℕ) : ZMod (π ^ a)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hx
    have hz : ((∑ i ∈ range r, x ^ i : ℕ) : ZMod (π ^ a)) * (x : ZMod (π ^ a))
        + 1 = ((∑ i ∈ range r, x ^ i : ℕ) : ZMod (π ^ a))
          + (x : ZMod (π ^ a)) ^ r := by
      exact_mod_cast congrArg (Nat.cast (R := ZMod (π ^ a))) (geom_mul x r)
    rw [hS, zero_mul, zero_add, zero_add] at hz
    exact hz.symm
  set u := ZMod.unitOfCoprime q hcopq with hu_def
  set v := ZMod.unitOfCoprime q' hcopq' with hv_def
  have hu : u ^ r = 1 := by
    ext
    rw [Units.val_pow_eq_pow_val, hu_def, ZMod.coe_unitOfCoprime, Units.val_one]
    exact hpow q (by rw [hP])
  have hv : v ^ r = 1 := by
    ext
    rw [Units.val_pow_eq_pow_val, hv_def, ZMod.coe_unitOfCoprime, Units.val_one]
    exact hpow q' hP'
  have hu1 : u ≠ 1 := by
    intro h
    have h' := congrArg Units.val h
    rw [hu_def, ZMod.coe_unitOfCoprime, Units.val_one, ← Nat.cast_one,
      ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hqP,
      Nat.mod_eq_of_lt (by omega : 1 < π ^ a)] at h'
    omega
  have hord : orderOf u = r := orderOf_eq_prime hu hu1
  -- The r powers of u are all the solutions of x^r = 1.
  set A := (Finset.univ : Finset (ZMod (π ^ a))ˣ).filter (fun x => x ^ r = 1)
  set B := (range r).image (fun j => u ^ j)
  have hBA : B ⊆ A := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := mem_image.mp hx
    simp only [A, mem_filter, mem_univ, true_and]
    rw [← pow_mul, mul_comm, pow_mul, hu, one_pow]
  have hBcard : B.card = r := by
    rw [card_image_of_injOn, card_range]
    intro i hi j hj hij
    have hi' : i < orderOf u := by rw [hord]; exact mem_range.mp hi
    have hj' : j < orderOf u := by rw [hord]; exact mem_range.mp hj
    exact pow_injOn_Iio_orderOf hi' hj' hij
  have hAcard : A.card ≤ r := IsCyclic.card_pow_eq_one_le hr.pos
  have hBA' : B = A := eq_of_subset_of_card_le hBA (by omega)
  have hvA : v ∈ A := by
    simp only [A, mem_filter, mem_univ, true_and]
    exact hv
  rw [← hBA'] at hvA
  obtain ⟨j, hj, hjv⟩ := mem_image.mp hvA
  have hjr : j < r := mem_range.mp hj
  have hcast : ((q ^ j : ℕ) : ZMod (π ^ a)) = ((q' : ℕ) : ZMod (π ^ a)) := by
    have := congrArg Units.val hjv
    rw [Units.val_pow_eq_pow_val, hu_def, hv_def, ZMod.coe_unitOfCoprime,
      ZMod.coe_unitOfCoprime] at this
    push_cast
    exact this
  rw [ZMod.natCast_eq_natCast_iff'] at hcast
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, Nat.mod_eq_of_lt (by omega : 1 < π ^ a)] at hcast
    exact h1 hcast.symm
  have hqj : q ^ j < π ^ a :=
    lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) (by omega)) hPgt
  rw [Nat.mod_eq_of_lt hqj] at hcast
  by_contra hlt
  push Not at hlt
  have hq'P : q' < π ^ a := lt_of_le_of_lt hlt hPgt
  rw [Nat.mod_eq_of_lt hq'P] at hcast
  have hdvd : q ∣ q' := hcast ▸ dvd_pow_self q hj0
  rcases hq'.eq_one_or_self_of_dvd q hdvd with h | h
  · omega
  · omega

/-- σ(p^k)/p^k < p/(p − 1). -/
theorem sigma_pp_lt {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ((σ 1 (p ^ k) : ℕ) : ℚ) / ((p ^ k : ℕ) : ℚ) < (p : ℚ) / (p - 1) := by
  rw [sigma_one_apply_prime_pow hp]
  have e := geom_mul p (k + 1)
  generalize ∑ i ∈ range (k + 1), p ^ i = Φ at e ⊢
  have e' : ((Φ * p + 1 : ℕ) : ℚ) = ((Φ + p ^ k * p : ℕ) : ℚ) := by
    rw [← pow_succ, e]
  push_cast at e'
  have hp2 : (2 : ℚ) ≤ p := by exact_mod_cast hp.two_le
  rw [Nat.cast_pow, div_lt_div_iff₀ (by positivity) (by linarith)]
  nlinarith

/-- σ(N)/N as a product over the primes of N. -/
theorem sigma_div_eq {N : ℕ} (hN : N ≠ 0) :
    ((σ 1 N : ℕ) : ℚ) / N = ∏ p ∈ N.primeFactors,
      ((σ 1 (p ^ N.factorization p) : ℕ) : ℚ) / ((p ^ N.factorization p : ℕ) : ℚ) := by
  have h1 : σ 1 N = ∏ p ∈ N.primeFactors, σ 1 (p ^ N.factorization p) := by
    rw [IsMultiplicative.multiplicative_factorization (σ 1)
      isMultiplicative_sigma hN, Finsupp.prod, Nat.support_factorization]
  have h2 := Nat.prod_primeFactors_pow_factorization hN
  rw [Finset.prod_div_distrib, ← Nat.cast_prod, ← Nat.cast_prod, ← h1, ← h2]

/-- For primes at least x ≥ 2, any two of which satisfy q < q' → q² < q',
∏ q/(q − 1) ≤ (x + 1)/(x − 1). -/
theorem prod_growth_le (s : Finset ℕ) : ∀ x : ℕ, 2 ≤ x → (∀ q ∈ s, x ≤ q) →
    (∀ q ∈ s, ∀ q' ∈ s, q < q' → q ^ 2 < q') →
    ∏ q ∈ s, ((q : ℚ) / (q - 1)) ≤ ((x : ℚ) + 1) / (x - 1) := by
  induction s using Finset.induction_on_min with
  | empty =>
    intro x hx _ _
    have hx' : (2 : ℚ) ≤ x := by exact_mod_cast hx
    rw [prod_empty, le_div_iff₀ (by linarith)]
    linarith
  | insert a s ha ih =>
    intro x hx hxs hg
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [prod_insert has]
    have hxa : x ≤ a := hxs a (mem_insert_self a s)
    have ih' := ih (a ^ 2 + 1) (by nlinarith)
      (fun q hq => hg a (mem_insert_self a s) q (mem_insert_of_mem hq) (ha q hq))
      (fun q hq q' hq' => hg q (mem_insert_of_mem hq) q' (mem_insert_of_mem hq'))
    push_cast at ih'
    have hX : (2 : ℚ) ≤ x := by exact_mod_cast hx
    have hA : (x : ℚ) ≤ a := by exact_mod_cast hxa
    have hA1 : (0 : ℚ) < (a : ℚ) - 1 := by linarith
    have hA0 : (0 : ℚ) < a := by linarith
    have e1 : ((a : ℚ) ^ 2 + 1 + 1) / ((a : ℚ) ^ 2 + 1 - 1)
        = ((a : ℚ) ^ 2 + 2) / (a : ℚ) ^ 2 := by ring_nf
    rw [e1] at ih'
    calc (a : ℚ) / (a - 1) * ∏ q ∈ s, ((q : ℚ) / (q - 1))
        ≤ (a : ℚ) / (a - 1) * (((a : ℚ) ^ 2 + 2) / (a : ℚ) ^ 2) :=
          mul_le_mul_of_nonneg_left ih' (by positivity)
      _ ≤ ((a : ℚ) + 1) / (a - 1) := by
          rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hA1]
          nlinarith [mul_nonneg (mul_nonneg hA0.le hA1.le)
            (show (0 : ℚ) ≤ a - 2 by linarith)]
      _ ≤ ((x : ℚ) + 1) / (x - 1) := by
          rw [div_le_div_iff₀ hA1 (by linarith)]
          nlinarith

/-- The same product is at most 11/6 for primes at least 3. -/
theorem prod_growth_le' (s : Finset ℕ) (h3 : ∀ q ∈ s, 3 ≤ q)
    (hg : ∀ q ∈ s, ∀ q' ∈ s, q < q' → q ^ 2 < q') :
    ∏ q ∈ s, ((q : ℚ) / (q - 1)) ≤ 11 / 6 := by
  induction s using Finset.induction_on_min with
  | empty => norm_num
  | insert a s ha _ =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [prod_insert has]
    have ha3 : 3 ≤ a := h3 a (mem_insert_self a s)
    have ih' := prod_growth_le s (a ^ 2 + 1) (by nlinarith)
      (fun q hq => hg a (mem_insert_self a s) q (mem_insert_of_mem hq) (ha q hq))
      (fun q hq q' hq' => hg q (mem_insert_of_mem hq) q' (mem_insert_of_mem hq'))
    push_cast at ih'
    have hA : (3 : ℚ) ≤ a := by exact_mod_cast ha3
    have hA1 : (0 : ℚ) < (a : ℚ) - 1 := by linarith
    have hA0 : (0 : ℚ) < a := by linarith
    have e1 : ((a : ℚ) ^ 2 + 1 + 1) / ((a : ℚ) ^ 2 + 1 - 1)
        = ((a : ℚ) ^ 2 + 2) / (a : ℚ) ^ 2 := by ring_nf
    rw [e1] at ih'
    calc (a : ℚ) / (a - 1) * ∏ q ∈ s, ((q : ℚ) / (q - 1))
        ≤ (a : ℚ) / (a - 1) * (((a : ℚ) ^ 2 + 2) / (a : ℚ) ^ 2) :=
          mul_le_mul_of_nonneg_left ih' (by positivity)
      _ ≤ 11 / 6 := by
          rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [mul_nonneg (mul_nonneg hA0.le (show (0 : ℚ) ≤ a - 3 by linarith))
            (show (0 : ℚ) ≤ 5 * a + 4 by linarith)]

/-- Lemma R: r divides N. -/
theorem r_dvd {N π r : ℕ} (hN : Odd N) (hperf : N.Perfect) (hπ : π.Prime)
    (hr : r.Prime) (hr3 : 3 ≤ r)
    (h : ∀ q, q.Prime → q ∣ N → q ≠ π → N.factorization q = r - 1) :
    r ∣ N := by
  by_contra hrN
  have hrodd : r % 2 = 1 := by
    rcases hr.eq_two_or_odd with h2 | h2
    · omega
    · exact h2
  have heven : ∀ q, q.Prime → q ∣ N → q ≠ π → Even (N.factorization q) := by
    intro q hq hqN hqπ
    rw [h q hq hqN hqπ]
    exact ⟨(r - 1) / 2, by omega⟩
  obtain ⟨hπN, -, hπ4, -⟩ := special_prime hN hperf hπ heven
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp at hN
  have hNodd : N % 2 = 1 := Nat.odd_iff.mp hN
  have hπ2 : π ≠ 2 := by
    rintro rfl
    omega
  have hΦdvd : ∀ q, q.Prime → q ∣ N → q ≠ π → (∑ i ∈ range r, q ^ i) ∣ N :=
    fun q hq hqN hqπ => geom_dvd hN hperf hq hqN (by omega) hrodd (h q hq hqN hqπ)
  have hnot1 : ∀ q, q.Prime → q ∣ N → q ≠ π → q % r ≠ 1 :=
    fun q hq hqN hqπ h1 => hrN ((r_dvd_geom h1).trans (hΦdvd q hq hqN hqπ))
  have honly : ∀ q, q.Prime → q ∣ N → q ≠ π → ∀ s, s.Prime →
      s ∣ ∑ i ∈ range r, q ^ i → s = π := by
    intro q hq hqN hqπ s hs hsd
    by_contra hsπ
    have hsN : s ∣ N := hsd.trans (hΦdvd q hq hqN hqπ)
    rcases prime_dvd_geom hr hs hsd with h1 | h1
    · exact hrN (h1 ▸ hsN)
    · exact hnot1 s hs hsN hsπ h1
  have hpow : ∀ q, q.Prime → q ∣ N → q ≠ π →
      ∃ a, 1 ≤ a ∧ ∑ i ∈ range r, q ^ i = π ^ a := by
    intro q hq hqN hqπ
    have hgt := geom_gt (r := r) (by omega) q
    have h1 : 1 ≤ q ^ (r - 1) := Nat.one_le_pow _ _ hq.pos
    refine ⟨_, ?_, Nat.eq_prime_pow_of_unique_prime_dvd (by omega)
      (fun hd hdd => honly q hq hqN hqπ _ hd hdd)⟩
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    have e := Nat.eq_prime_pow_of_unique_prime_dvd (n := ∑ i ∈ range r, q ^ i)
      (p := π) (by omega) (fun hd hdd => honly q hq hqN hqπ _ hd hdd)
    rw [h0, pow_zero] at e
    omega
  -- No prime q ≠ π of N has π ∣ Φ(q) with q ≡ 1 (mod π).
  have hnotπ1 : ∀ q, q.Prime → q ∣ N → q ≠ π → q % π ≠ 1 := by
    intro q hq hqN hqπ h1
    obtain ⟨a, ha1, ha⟩ := hpow q hq hqN hqπ
    have hm := geom_mod_of_one (r := r) (show q % π = 1 % π by
      rw [h1, Nat.mod_eq_of_lt hπ.one_lt])
    have hd : π ∣ ∑ i ∈ range r, q ^ i := ha ▸ dvd_pow_self π (by omega)
    rw [(Nat.dvd_iff_mod_eq_zero).mp hd] at hm
    have hπr : π ∣ r := Nat.dvd_of_mod_eq_zero hm.symm
    have := (Nat.prime_dvd_prime_iff_eq hπ hr).mp hπr
    exact hrN (this ▸ hπN)
  -- The growth of the primes other than π.
  have hgrow : ∀ q q', q.Prime → q ∣ N → q ≠ π → q'.Prime → q' ∣ N → q' ≠ π →
      q < q' → q ^ (r - 1) < q' := by
    intro q q' hq hqN hqπ hq' hq'N hq'π hqq
    obtain ⟨a, ha1, ha⟩ := hpow q hq hqN hqπ
    obtain ⟨b, hb1, hb⟩ := hpow q' hq' hq'N hq'π
    have hlt := geom_strictMono (r := r) (by omega) hqq
    rw [ha, hb] at hlt
    have hab : a ≤ b := by
      by_contra hc
      push Not at hc
      have := Nat.pow_le_pow_right hπ.pos hc.le
      omega
    have hdvd : π ^ a ∣ ∑ i ∈ range r, q' ^ i := hb ▸ pow_dvd_pow π hab
    have hne : q' % π ^ a ≠ 1 := by
      intro h1
      apply hnotπ1 q' hq' hq'N hq'π
      have := Nat.mod_mod_of_dvd q' (dvd_pow_self π (show a ≠ 0 by omega))
      rw [h1, Nat.mod_eq_of_lt hπ.one_lt] at this
      exact this.symm
    exact growth hr hr3 hπ hπ2 hq hq' hqq ha hdvd hne
  set S := N.primeFactors.erase π with hS
  have hSmem : ∀ q ∈ S, q.Prime ∧ q ∣ N ∧ q ≠ π := by
    intro q hq
    rw [hS, Finset.mem_erase, Nat.mem_primeFactors] at hq
    exact ⟨hq.2.1, hq.2.2.1, hq.1⟩
  have hS3 : ∀ q ∈ S, 3 ≤ q := by
    intro q hq
    obtain ⟨hqp, hqN, -⟩ := hSmem q hq
    rcases hqp.eq_two_or_odd with h2 | h2
    · subst h2
      omega
    · have := hqp.two_le
      omega
  have hSg : ∀ q ∈ S, ∀ q' ∈ S, q < q' → q ^ 2 < q' := by
    intro q hq q' hq' hqq
    obtain ⟨hqp, hqN, hqπ⟩ := hSmem q hq
    obtain ⟨hqp', hqN', hqπ'⟩ := hSmem q' hq'
    have := hgrow q q' hqp hqN hqπ hqp' hqN' hqπ' hqq
    have : q ^ 2 ≤ q ^ (r - 1) := Nat.pow_le_pow_right hqp.pos (by omega)
    omega
  have hprodS := prod_growth_le' S hS3 hSg
  -- σ(N)/N = 2, split at π.
  have hσ : ((σ 1 N : ℕ) : ℚ) / N = 2 := by
    rw [sigma_eq_two_mul hperf]
    push_cast
    field_simp
  rw [sigma_div_eq hN0, ← Finset.mul_prod_erase _ _
    (Nat.mem_primeFactors.mpr ⟨hπ, hπN, hN0⟩), ← hS] at hσ
  have hfπ := sigma_pp_lt hπ (N.factorization π)
  have hfS : ∏ q ∈ S, ((σ 1 (q ^ N.factorization q) : ℕ) : ℚ)
      / ((q ^ N.factorization q : ℕ) : ℚ) ≤ ∏ q ∈ S, ((q : ℚ) / (q - 1)) :=
    prod_le_prod₀ (fun _ _ => by positivity)
      (fun q hq => (sigma_pp_lt (hSmem q hq).1 _).le)
  have hfS0 : 0 ≤ ∏ q ∈ S, ((σ 1 (q ^ N.factorization q) : ℕ) : ℚ)
      / ((q ^ N.factorization q : ℕ) : ℚ) := prod_nonneg (fun _ _ => by positivity)
  have hfπ0 : 0 ≤ ((σ 1 (π ^ N.factorization π) : ℕ) : ℚ)
      / ((π ^ N.factorization π : ℕ) : ℚ) := by positivity
  rcases S.eq_empty_or_nonempty with hSe | ⟨q0, hq0⟩
  · rw [hSe, prod_empty, mul_one] at hσ
    have h5 : (5 : ℚ) ≤ π := by
      have := hπ.two_le
      exact_mod_cast (show 5 ≤ π by omega)
    have : (π : ℚ) / (π - 1) ≤ 5 / 4 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    linarith
  · -- π ≡ 1 (mod r), so π ≥ 4r + 1 ≥ 13.
    obtain ⟨hq0p, hq0N, hq0π⟩ := hSmem q0 hq0
    obtain ⟨a, ha1, ha⟩ := hpow q0 hq0p hq0N hq0π
    have hd : π ∣ ∑ i ∈ range r, q0 ^ i := ha ▸ dvd_pow_self π (by omega)
    have hπr : π % r = 1 := by
      rcases prime_dvd_geom hr hπ hd with h1 | h1
      · exact absurd (h1 ▸ hπN) hrN
      · exact h1
    have h13 : 13 ≤ π := by
      obtain ⟨k, hk⟩ : r ∣ π - 1 := by
        have := hπ.two_le
        exact (Nat.modEq_iff_dvd' (by omega)).mp
          (show 1 % r = π % r by rw [hπr, Nat.mod_eq_of_lt (by omega)])
      have h4 : 4 ∣ r * k := by
        rw [← hk]
        omega
      have h2r : Nat.Coprime 2 r := (Nat.coprime_primes Nat.prime_two hr).mpr (by omega)
      have hk4 : 2 ^ 2 ∣ k :=
        (Nat.Coprime.pow_left 2 h2r).dvd_of_dvd_mul_left (by simpa using h4)
      have hk0 : k ≠ 0 := by
        rintro rfl
        have := hπ.two_le
        omega
      have : 4 ≤ k := by
        have := Nat.le_of_dvd (by omega) hk4
        simpa using this
      have : 12 ≤ r * k := by nlinarith
      have := hπ.two_le
      omega
    have h13' : (13 : ℚ) ≤ π := by exact_mod_cast h13
    have hπb : (π : ℚ) / (π - 1) ≤ 13 / 12 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have := mul_le_mul (lt_of_lt_of_le hfπ hπb).le (hfS.trans hprodS) hfS0
      (by norm_num)
    linarith

end Opn
