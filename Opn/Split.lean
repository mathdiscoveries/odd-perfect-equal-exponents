module

public import Opn.T2Check


/-
The split of the certificate check (local certificate generator.md): `checkCert c = true`
from its parts, each a separate `decide +kernel` theorem, so that each
part gets its own kernel check and its own memory. A part is one
Pocklington certificate, one step of a case, one counted number of a
case, the sum test of a case, or one of three small checks of the
whole. Core Lean only.
-/

@[expose] public section

namespace T2

/-- The primes proved before the i-th Pocklington certificate. -/
def provenUpTo (c : Cert) (i : Nat) : List Nat :=
  ((c.primes.take i).map (·.n)).reverse

/-- Every prime the Pocklington certificates prove. -/
def provenAll (c : Cert) : List Nat := (c.primes.map (·.n)).reverse

/-- The test `stepsAux` makes of one step. -/
def stepCond (r : Nat) (special : Option Nat) (proven parents : List Nat)
    (s : Step) : Bool :=
  decide (2 ≤ s.parent) && primeOk proven s.parent
    && special != some s.parent
    && whyOk r special parents s.parent s.why
    && !parents.contains s.parent

/-- The test `countedAux` makes of one counted number. -/
def countedCond (r : Nat) (parents seen : List Nat) (c : Counted) : Bool :=
  decide (2 ≤ c.m) && countedOk r parents c && witnessOk c
    && seen.all (fun o => Nat.gcd c.m o == 1)

/-- Part P_i: the i-th Pocklington certificate. -/
def pAt (c : Cert) (i : Nat) : Bool :=
  match c.primes[i]? with
  | some p => pCertOk (provenUpTo c i) p
  | none => false

/-- Part S_(j,i): step i of case j. -/
def sAt (c : Cert) (j i : Nat) : Bool :=
  match c.cases[j]? with
  | some k => match k.steps[i]? with
    | some s => stepCond c.r k.special (provenAll c)
        ((k.steps.take i).map (·.parent)) s
    | none => false
  | none => false

/-- Part K_(j,i): counted number i of case j. -/
def kAt (c : Cert) (j i : Nat) : Bool :=
  match c.cases[j]? with
  | some k => match k.counted[i]? with
    | some x => countedCond c.r (k.steps.map (·.parent))
        ((k.counted.take i).map (·.m)).reverse x
    | none => false
  | none => false

/-- Part N_j: the sum test of case j. -/
def nAt (c : Cert) (j : Nat) : Bool :=
  match c.cases[j]? with
  | some k => decide (need c.r k.special ((k.counted.map (·.m)).reverse)
      ≤ (k.counted.map (·.count)).sum)
  | none => false

/-- The number of steps of case j. -/
def stepsLen (c : Cert) (j : Nat) : Nat :=
  match c.cases[j]? with
  | some k => k.steps.length
  | none => 0

/-- The number of counted numbers of case j. -/
def countedLen (c : Cert) (j : Nat) : Nat :=
  match c.cases[j]? with
  | some k => k.counted.length
  | none => 0

/-- The checks of `checkCert` before its Pocklington certificates. -/
def headOk (c : Cert) : Bool :=
  decide (3 ≤ c.r) && c.r % 2 == 1 && trialPrime c.r
  && (c.r % 4 != 1 || c.cited)

/-- The checks of the cases' shape. -/
def shapeOk (c : Cert) : Bool :=
  (c.cases.filter (fun k => k.special.isNone)).length == 1
  && (c.cases.filterMap (·.special)).all
      (fun p => decide (3 ≤ p) && p % 2 == 1)
  && distinct (c.cases.filterMap (·.special))

/-- The owed condition, on the parents of the case with no special
prime as its steps list them. -/
def owedAt (c : Cert) : Bool :=
  match c.cases.filter (fun k => k.special.isNone) with
  | k :: _ => (k.steps.map (·.parent)).all (fun q =>
      !(q % 4 == 1 && q != c.r) || (c.cases.filterMap (·.special)).contains q)
  | [] => false

theorem provenPrimes_eq (ps : List PCert) (acc : List Nat)
    (h : ∀ i (hi : i < ps.length),
      pCertOk (((ps.take i).map (·.n)).reverse ++ acc) ps[i] = true) :
    provenPrimes ps acc = some ((ps.map (·.n)).reverse ++ acc) := by
  induction ps generalizing acc with
  | nil => rfl
  | cons p ps ih =>
    have h0 := h 0 (by simp)
    simp only [List.take_zero, List.map_nil, List.reverse_nil,
      List.nil_append, List.getElem_cons_zero] at h0
    simp only [provenPrimes, h0, if_true]
    rw [ih (p.n :: acc)]
    · simp
    · intro i hi
      have := h (i + 1) (by simp; omega)
      simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc]
        using this

theorem stepsAux_eq (r : Nat) (sp : Option Nat) (proven : List Nat)
    (ss : List Step) (acc : List Nat)
    (h : ∀ i (hi : i < ss.length),
      stepCond r sp proven (acc ++ (ss.take i).map (·.parent)) ss[i]
        = true) :
    stepsAux r sp proven ss acc = some (acc ++ ss.map (·.parent)) := by
  induction ss generalizing acc with
  | nil => simp [stepsAux]
  | cons s ss ih =>
    have h0 := h 0 (by simp)
    simp only [List.take_zero, List.map_nil, List.append_nil,
      List.getElem_cons_zero, stepCond] at h0
    simp only [stepsAux, h0, if_true]
    rw [ih (acc ++ [s.parent])]
    · simp
    · intro i hi
      have := h (i + 1) (by simp; omega)
      simpa [List.take_succ_cons, List.append_assoc] using this

theorem countedAux_eq (r : Nat) (parents : List Nat) (cs : List Counted)
    (seen : List Nat) (total : Nat)
    (h : ∀ i (hi : i < cs.length),
      countedCond r parents (((cs.take i).map (·.m)).reverse ++ seen) cs[i]
        = true) :
    countedAux r parents cs seen total
      = some ((cs.map (·.m)).reverse ++ seen,
          total + (cs.map (·.count)).sum) := by
  induction cs generalizing seen total with
  | nil => simp [countedAux]
  | cons x cs ih =>
    have h0 := h 0 (by simp)
    simp only [List.take_zero, List.map_nil, List.reverse_nil,
      List.nil_append, List.getElem_cons_zero, countedCond] at h0
    simp only [countedAux, h0, if_true]
    rw [ih (x.m :: seen) (total + x.count)]
    · simp [Nat.add_assoc]
    · intro i hi
      have := h (i + 1) (by simp; omega)
      simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc]
        using this

theorem caseOk_eq (c : Cert) (j : Nat) (hj : j < c.cases.length)
    (hs : ∀ i, i < c.cases[j].steps.length → sAt c j i = true)
    (hk : ∀ i, i < c.cases[j].counted.length → kAt c j i = true)
    (hn : nAt c j = true) :
    caseOk c.r (provenAll c) c.cases[j]
      = some (c.cases[j].steps.map (·.parent)) := by
  have hS := stepsAux_eq c.r c.cases[j].special (provenAll c)
    c.cases[j].steps [] (fun i hi => by
      have := hs i hi
      simp only [sAt, List.getElem?_eq_getElem hj,
        List.getElem?_eq_getElem hi] at this
      simpa using this)
  have hK := countedAux_eq c.r (c.cases[j].steps.map (·.parent))
    c.cases[j].counted [] 0 (fun i hi => by
      have := hk i hi
      simp only [kAt, List.getElem?_eq_getElem hj,
        List.getElem?_eq_getElem hi] at this
      simpa using this)
  have hN := hn
  simp only [nAt, List.getElem?_eq_getElem hj, decide_eq_true_eq] at hN
  unfold caseOk
  rw [hS]
  simp only [List.nil_append]
  rw [hK]
  simp only [List.append_nil, Nat.zero_add]
  rw [if_pos hN]

theorem checkCert_of_parts (c : Cert) (hh : headOk c = true)
    (hp : ∀ i, i < c.primes.length → pAt c i = true)
    (hs : shapeOk c = true)
    (hst : ∀ j, j < c.cases.length → ∀ i, i < stepsLen c j →
      sAt c j i = true)
    (hk : ∀ j, j < c.cases.length → ∀ i, i < countedLen c j →
      kAt c j i = true)
    (hn : ∀ j, j < c.cases.length → nAt c j = true)
    (ho : owedAt c = true) : checkCert c = true := by
  have hP : provenPrimes c.primes [] = some (provenAll c) := by
    have := provenPrimes_eq c.primes [] (fun i hi => by
      have := hp i hi
      simp only [pAt, List.getElem?_eq_getElem hi] at this
      simpa [provenUpTo] using this)
    simpa [provenAll] using this
  have hcase : ∀ k ∈ c.cases,
      caseOk c.r (provenAll c) k = some (k.steps.map (·.parent)) := by
    intro k hk'
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hk'
    have hsl : stepsLen c j = c.cases[j].steps.length := by
      simp [stepsLen, List.getElem?_eq_getElem hj]
    have hcl : countedLen c j = c.cases[j].counted.length := by
      simp [countedLen, List.getElem?_eq_getElem hj]
    exact caseOk_eq c j hj (fun i hi => hst j hj i (hsl ▸ hi))
      (fun i hi => hk j hj i (hcl ▸ hi)) (hn j hj)
  have hall : c.cases.all (fun k => (caseOk c.r (provenAll c) k).isSome)
      = true := by
    rw [List.all_eq_true]
    intro k hk'
    simp [hcase k hk']
  have howed : owedOk c.r (c.cases.filterMap (·.special)) (provenAll c)
      (c.cases.filter (fun k => k.special.isNone)) = true := by
    unfold owedAt at ho
    revert ho
    have hsub : ∀ k ∈ c.cases.filter (fun k => k.special.isNone),
        k ∈ c.cases := fun k hk' => (List.mem_filter.mp hk').1
    generalize c.cases.filter (fun k => k.special.isNone) = l at hsub ⊢
    cases l with
    | nil => simp
    | cons k ks =>
      intro ho
      simp only [owedOk, hcase k (hsub k (by simp))]
      exact ho
  unfold checkCert
  unfold headOk at hh
  unfold shapeOk at hs
  rw [hP]
  simp only [hh, hs, hall, howed, Bool.and_true]

#print axioms checkCert_of_parts

end T2
