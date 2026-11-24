module

public import Opn.Parts
public import Opn.Pocklington
public import Mathlib.Data.Nat.Factorization.Basic

/-
Pocklington's theorem in the certificate's form: a number that
`T2.pCertOk` accepts is prime when every number on the list of proven
primes is prime, and so every number that `T2.provenPrimes` returns
is prime.
-/


@[expose] public section

namespace Opn

/-- Pocklington: if F divides q - 1 for every prime q dividing n, and
n ≤ F², then n is prime. -/
theorem pocklington {n F : ℕ} (hn : 2 ≤ n) (hF : n ≤ F * F)
    (h : ∀ q : ℕ, q.Prime → q ∣ n → F ∣ q - 1) : n.Prime := by
  by_contra hnp
  have hq : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hq2 := hq.two_le
  have hFq : F ∣ n.minFac - 1 := h _ hq (Nat.minFac_dvd n)
  have h1 : F ≤ n.minFac - 1 := Nat.le_of_dvd (by omega) hFq
  have h2 : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
  have h3 : F < n.minFac := by omega
  have h4 : F * F < n.minFac * n.minFac := Nat.mul_lt_mul'' h3 h3
  rw [sq] at h2
  omega

/-- A prime dividing the product of the items' prime powers divides
the start value or one of the items' primes. -/
theorem prime_dvd_foldl {p : ℕ} (hp : p.Prime) (items : List T2.PItem)
    (a : ℕ)
    (h : p ∣ items.foldl (fun acc it => acc * it.p ^ it.e) a) :
    p ∣ a ∨ ∃ it ∈ items, p ∣ it.p := by
  induction items generalizing a with
  | nil => exact Or.inl h
  | cons it rest ih =>
    rw [List.foldl_cons] at h
    rcases ih _ h with h1 | ⟨it', hm, hd⟩
    · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr ⟨it, List.mem_cons.mpr (Or.inl rfl),
          hp.dvd_of_dvd_pow h2⟩
    · exact Or.inr ⟨it', List.mem_cons.mpr (Or.inr hm), hd⟩

theorem pItemOk_unpack {n : ℕ} {proven : List ℕ} {it : T2.PItem}
    (h : T2.pItemOk n proven it = true) :
    T2.primeOk proven it.p = true ∧ 1 ≤ it.e ∧ 2 ≤ it.a ∧ it.a < n
      ∧ T2.powMod it.a (n - 1) n = 1
      ∧ Nat.gcd ((T2.powMod it.a ((n - 1) / it.p) n + n - 1) % n) n
        = 1 := by
  simp only [T2.pItemOk, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- A number that `primeOk` accepts is prime, given a list of primes. -/
theorem primeOk_sound {proven : List ℕ} (hpr : ∀ x ∈ proven, x.Prime)
    {p : ℕ} (h : T2.primeOk proven p = true) : p.Prime := by
  unfold T2.primeOk at h
  split_ifs at h with hs
  · exact T2.trialPrime_sound h
  · exact hpr p (by simpa using h)

/-- A number that `pCertOk` accepts is prime, given a list of primes. -/
theorem pCertOk_prime {proven : List ℕ} (hpr : ∀ x ∈ proven, x.Prime)
    {c : T2.PCert} (h : T2.pCertOk proven c = true) : c.n.Prime := by
  simp only [T2.pCertOk, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hS, hall⟩, hdiv⟩, hle⟩ := h
  have hn : 2 ≤ c.n := by
    have : T2.SMALL = 1000000 := rfl
    omega
  have hFd := Nat.dvd_of_mod_eq_zero hdiv
  apply pocklington hn hle
  intro q hq hqn
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [hk, pow_zero]
    exact one_dvd _
  have hpF := (dvd_pow_self p hk.ne').trans hpk
  rcases prime_dvd_foldl hp _ _ hpF with h1 | ⟨it, hm, hd⟩
  · exact absurd (Nat.dvd_one.mp h1) hp.one_lt.ne'
  · obtain ⟨hpo, _, _, _, h1, h2⟩ := pItemOk_unpack (hall it hm)
    have hitp : it.p.Prime := primeOk_sound hpr hpo
    have hpe : p = it.p := (Nat.prime_dvd_prime_iff_eq hp hitp).mp hd
    rw [T2.powMod_eq] at h1 h2
    rw [hpe] at hpk ⊢
    exact pock_step hn hq hqn hitp h1 h2 (hpk.trans hFd)

/-- Every number `provenPrimes` returns is prime, given that the
numbers it starts from are. -/
theorem provenPrimes_prime (cs : List T2.PCert) (proven out : List ℕ)
    (hpr : ∀ x ∈ proven, x.Prime)
    (h : T2.provenPrimes cs proven = some out) : ∀ x ∈ out, x.Prime := by
  induction cs generalizing proven with
  | nil =>
    rw [T2.provenPrimes] at h
    cases h
    exact hpr
  | cons c cs ih =>
    rw [T2.provenPrimes] at h
    split_ifs at h with hc
    refine ih (c.n :: proven) ?_ h
    intro x hx
    rcases List.mem_cons.mp hx with e | hx
    · rw [e]
      exact pCertOk_prime hpr hc
    · exact hpr x hx

/-- Every number `provenPrimes` returns from an empty start is prime. -/
theorem provenPrimes_nil_prime {cs : List T2.PCert} {out : List ℕ}
    (h : T2.provenPrimes cs [] = some out) : ∀ x ∈ out, x.Prime :=
  provenPrimes_prime cs [] out (fun _ hx => absurd hx (by simp)) h

end Opn
