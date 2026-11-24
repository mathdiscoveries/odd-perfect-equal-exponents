module


/-
A size probe for the odd perfect library's Lean scope page: the conditions
of `t2_cert.py` (Theorem S of t2-method-1.md) as one function to Bool,
in core Lean 4 with no library beyond it, written so that Lean's
kernel can evaluate it (`decide +kernel`). Every recursion is on a
list or on a counter given beforehand.

This file proves nothing about odd perfect numbers. It has no proof
that `checkCert c = true` implies the statement; that proof is the
work the scope page sizes.
-/

@[expose] public section

namespace T2

def SMALL : Nat := 1000000

/-- b^e mod m by repeated squaring; `fuel` bounds the steps. -/
def powModAux : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _, acc => acc
  | fuel + 1, b, e, m, acc =>
    if e = 0 then acc
    else powModAux fuel (b * b % m) (e / 2) m
      (if e % 2 = 1 then acc * b % m else acc)

def powMod (b e m : Nat) : Nat :=
  powModAux (Nat.log2 e + 1) (b % m) e m (1 % m)

def phiAux : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | k + 1, q, acc => phiAux k q (acc * q + 1)

/-- 1 + q + ... + q^(r-1). -/
def phi (r q : Nat) : Nat := phiAux (r - 1) q 1

def trialAux : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, n, d =>
    if d * d > n then true
    else if n % d = 0 then false
    else trialAux fuel n (d + 1)

/-- Trial division; decides primality for n below SMALL. -/
def trialPrime (n : Nat) : Bool := decide (2 ≤ n) && trialAux 1001 n 2

def rootAux : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, lo, _ => lo
  | fuel + 1, m, k, lo, hi =>
    if lo < hi then
      if ((lo + hi + 1) / 2) ^ k ≤ m then rootAux fuel m k ((lo + hi + 1) / 2) hi
      else rootAux fuel m k lo ((lo + hi + 1) / 2 - 1)
    else lo

/-- The integer part of the k-th root of m. -/
def kthRoot (m k : Nat) : Nat :=
  rootAux ((Nat.log2 m + 1) / k + 3) m k 1 (2 ^ ((Nat.log2 m + 1) / k + 1))

def noDivBelow : Nat → Nat → Bool
  | 0, _ => true
  | d + 1, m => if d + 1 < 2 then true else m % (d + 1) != 0 && noDivBelow d m

def ppAux : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, m, k =>
    ((k == 2 || (k % 2 == 1 && (k >= SMALL || trialPrime k)))
      && (kthRoot m k) ^ k == m)
    || ppAux fuel m (k + 1)

/-- m = x^k for some k from 2 to the bit length of m (prime exponents suffice,
and when m has no divisor in 2..63 then x ≥ 64 = 2^6 so k ≤ log2(m)/6). -/
def isPerfectPower (m : Nat) : Bool :=
  let lim := if noDivBelow 63 m then Nat.log2 m / 6 + 1 else Nat.log2 m
  ppAux lim m 2

inductive Why where
  | r
  | half
  | phiOf (x : Nat)

structure Step where
  parent : Nat
  why : Why

structure Counted where
  m : Nat
  ofParent : Bool
  of : Nat
  count : Nat
  witness : Nat

structure Case where
  special : Option Nat
  steps : List Step
  counted : List Counted

structure PItem where
  p : Nat
  e : Nat
  a : Nat

/-- A Pocklington certificate for n: the factored part of n - 1. -/
structure PCert where
  n : Nat
  items : List PItem

structure Cert where
  r : Nat
  cited : Bool
  cases : List Case
  /-- every Pocklington certificate, those that others rest on first -/
  primes : List PCert

def primeOk (proven : List Nat) (p : Nat) : Bool :=
  if p < SMALL then trialPrime p else proven.contains p

def pItemOk (n : Nat) (proven : List Nat) (it : PItem) : Bool :=
  primeOk proven it.p && decide (1 ≤ it.e) && decide (2 ≤ it.a)
  && decide (it.a < n) && powMod it.a (n - 1) n == 1
  && Nat.gcd ((powMod it.a ((n - 1) / it.p) n + n - 1) % n) n == 1

def pCertOk (proven : List Nat) (c : PCert) : Bool :=
  decide (SMALL ≤ c.n) && c.items.all (pItemOk c.n proven)
  && (c.n - 1) % (c.items.foldl (fun acc it => acc * it.p ^ it.e) 1) == 0
  && decide (c.n ≤ (c.items.foldl (fun acc it => acc * it.p ^ it.e) 1)
      * (c.items.foldl (fun acc it => acc * it.p ^ it.e) 1))

/-- Condition P for the large primes: each certificate in turn. -/
def provenPrimes : List PCert → List Nat → Option (List Nat)
  | [], proven => some proven
  | c :: cs, proven =>
    if pCertOk proven c then provenPrimes cs (c.n :: proven) else none

def whyOk (r : Nat) (special : Option Nat) (parents : List Nat) (q : Nat) :
    Why → Bool
  | .r => q == r
  | .half => match special with
    | some p => ((p + 1) / 2) % q == 0
    | none => false
  | .phiOf x => parents.contains x && phi r x % q == 0

/-- Conditions P, S2, S3: the parents of a case, in order. -/
def stepsAux (r : Nat) (special : Option Nat) (proven : List Nat) :
    List Step → List Nat → Option (List Nat)
  | [], parents => some parents
  | s :: ss, parents =>
    if decide (2 ≤ s.parent) && primeOk proven s.parent
        && special != some s.parent
        && whyOk r special parents s.parent s.why
        && !parents.contains s.parent
    then stepsAux r special proven ss (parents ++ [s.parent]) else none

def witnessOk (c : Counted) : Bool :=
  if c.count == 2 then
    decide (2 ≤ c.witness) && decide (c.witness < c.m)
    && powMod c.witness (c.m - 1) c.m != 1 && !isPerfectPower c.m
  else c.count == 1

def countedOk (r : Nat) (parents : List Nat) (c : Counted) : Bool :=
  if c.ofParent then parents.contains c.m && c.m % r == 1
  else parents.contains c.of && phi r c.of % c.m == 0 && c.m % r != 0

/-- Conditions C1, W, C3: the counted numbers and the sum of counts. -/
def countedAux (r : Nat) (parents : List Nat) :
    List Counted → List Nat → Nat → Option (List Nat × Nat)
  | [], seen, total => some (seen, total)
  | c :: cs, seen, total =>
    if decide (2 ≤ c.m) && countedOk r parents c && witnessOk c
        && seen.all (fun o => Nat.gcd c.m o == 1)
    then countedAux r parents cs (c.m :: seen) (total + c.count) else none

def need (r : Nat) (special : Option Nat) (seen : List Nat) : Nat :=
  match special with
  | some p => if seen.all (fun m => Nat.gcd m p == 1) then r else r + 1
  | none => r + 1

/-- One case: its parents when every condition of the case holds. -/
def caseOk (r : Nat) (proven : List Nat) (c : Case) : Option (List Nat) :=
  match stepsAux r c.special proven c.steps [] with
  | none => none
  | some parents =>
    match countedAux r parents c.counted [] 0 with
    | none => none
    | some (seen, total) =>
      if need r c.special seen ≤ total then some parents else none

def distinct : List Nat → Bool
  | [] => true
  | x :: xs => !xs.contains x && distinct xs

def owedOk (r : Nat) (specials : List Nat) (proven : List Nat) :
    List Case → Bool
  | [] => false
  | k :: _ => match caseOk r proven k with
    | some parents =>
      parents.all (fun q => !(q % 4 == 1 && q != r) || specials.contains q)
    | none => false

/-- Conditions R to E of Theorem S on a whole certificate. -/
def checkCert (c : Cert) : Bool :=
  decide (3 ≤ c.r) && c.r % 2 == 1 && trialPrime c.r
  && (c.r % 4 != 1 || c.cited)
  && match provenPrimes c.primes [] with
    | none => false
    | some proven =>
      (c.cases.filter (fun k => k.special.isNone)).length == 1
      && (c.cases.filterMap (·.special)).all
          (fun p => decide (3 ≤ p) && p % 2 == 1)
      && distinct (c.cases.filterMap (·.special))
      && c.cases.all (fun k => (caseOk c.r proven k).isSome)
      && owedOk c.r (c.cases.filterMap (·.special)) proven
          (c.cases.filter (fun k => k.special.isNone))

end T2
