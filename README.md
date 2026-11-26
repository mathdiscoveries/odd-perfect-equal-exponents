# Odd Perfect Numbers: Equal Non-Special Exponents for All Odd Primes `3 ≤ r ≤ 73`

Unconditional Lean 4 (`v4.35.0`) + Mathlib formalization ruling out odd perfect
numbers $N = \pi^\alpha q_1^{r-1} \cdots q_t^{r-1}$ with equal non-special
exponents $r - 1$ (`2β = r - 1`) for **every odd prime $3 \le r \le 73$**
(all 20 odd primes, $1 \le \beta \le 36$), together with Theorem 1 of the
companion paper, implied by Kanold's 1941 congruence, that $r$ cannot be the
special prime (`notSpecial_of_prime`) for every odd prime $r \ge 3$.

This covers all 9 prime cases through $r = 73$ excluded in earlier work
(Steuerwald 1937, Kanold 1941, McDaniel 1970, Hagis-McDaniel 1972,
McDaniel-Hagis 1975, Cohen-Williams 1985), proved again here, and the 11
other prime cases in this range, among them all five cases
$\beta \in \{9, 15, 20, 21, 23\}$ ($r \in \{19, 31, 41, 43, 47\}$) that
Cohen and Williams (1985) attempted without success, as well as
$r \in \{53, 59, 61, 67, 71, 73\}$. This package formalizes the companion
paper's proof (its Theorems 1 and 2). Larger
cases ($79 \le r \le 167$) are documented separately at
https://mathdiscoveries.org/results/odd-perfect-equal-exponents.

## Build & Verify

```bash
lake build Challenge Solution Opn
lake env lean Opn/Verify.lean
lake comparator --paranoid --inadvisably-no-sandbox
```

## Disclosure & License

Generated and checked by AI research agents built and directed by **Tyler B. Hughes**. No human mathematician has yet refereed the proof. Licensed under Apache-2.0.
