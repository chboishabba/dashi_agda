# BSD K1: selected E real / Q₂ pointwise filters — 14 November 2026

Selected ORIGINAL E: y²=x(x−1)(x+1), with original Kummer
coordinates [x],[x−1] on the nonexceptional locus and original
torsion conventions for O,(0,0),(1,0),(-1,0).
Attribution: classical complete two-descent (e.g. Silverman,
*Arithmetic of Elliptic Curves*, Chapter X); same-object Agda owners
EllipticRationalKummerOpenExact and
EllipticRationalTwoTorsionKummerExact. Do not replace the original
square-class setoid by Boolean codes.

## Actual elementary local arithmetic, not a general H¹ theorem

Let K be R or a local nonarchimedean field Q_p, and let P=(x,y)
be an actual point of E(K), excluding y=0 and infinity.

**Real place.** Because y²=x(x−1)(x+1)>0, x lies in
(-1,0) or (1,infinity). On either interval, x and x−1 have
identical signs; hence firstNegative=secondNegative for the
literal [x],[x−1] Kummer pair. The O, zero, one, minus-one
cases are separately calibrated by the ORIGINAL torsion table:
(1,1), (-1,-1), (1,2), (-1,-2). No x>0-only inference.

**Finite place p (stronger than the requested dyadic case).**
For nonzero x,y in Q_p let vx=v_p(x), vy=v_p(y).

- If vx>0, both x−1 and x+1 are units by the ultrametric
  inequality. Taking valuations of the curve factorization gives
  2vy=vx, so vx is even.
- If vx<0, write x±1=x(1±1/x); 1/x has positive valuation,
  so both parentheses are units. Thus v_p(x±1)=vx and
  2vy=3vx, hence vx=2(vy−vx), so vx is even.
- If vx=0, parity is immediate.
- For y=0 or O use the original rational torsion Kummer
  dictionary; its first coordinate is always 1 or −1, with
  even valuation, also at p=2.

Consequently, **for every actual local point** its first
Kummer coordinate has even p-valuation for each finite p,
including the selected actual dyadic prime 2.
The second coordinate can have odd v₂ (the torsion pair
(1,2) confirms this), so do NOT promote a false symmetric
two-coordinate parity constraint.

## New source implementation

DASHI/Mathematics/Arithmetic/EllipticCubicValuationParityExact.agda
uses the existing integer ring solver to prove:

- positiveValuationBalanceEven: 2vy=vx -> EvenValuation vx;
- negativeValuationBalanceEven: 2vy=3vx -> EvenValuation vx,
  with explicit witness vy-vx;
- originalCubicValuationRegimeEven: exhaust the three
  **valuation equations** into an even-valuation witness.

This is real algebra on Agda integers, but its local-field
producers remain open. The source was committed on #1500 and
registered in scripts/check_bsd_agda_k1_k5_local_maxcut.sh.
Kernel acceptance remains pending; no postulates or holes
were intentionally added.

## Exact missing same-object K1 lemmas

1. Build actual Q₂ and R local point + valuation/sign carriers in
   Agda (or proof-preserving admissions from exact owners).
2. For every actual E(Q₂) non-torsion P, prove the three
   valuation regimes from the existing curveFactorization
   and ultrametric unit laws; include the torsion exceptions.
3. For every actual E(R) P, prove the ordered-field interval
   alternative and identical signs, including exceptions.
4. Build actual H¹(Q_v,E[2]) and the same-object local Kummer
   realization; prove all members of each local Kummer image
   inherit the pointwise constraints.
5. Build global H¹ supported square-class map, good-prime
   unramifiedness and faithful transport, and instantiate
   EllipticRationalPlaceTwoDescentProducerExact.
6. Do NOT infer classical Sha[2], full Sha, rank=0 or BSD
   solely from these pointwise necessary conditions.

**Status:** pointwise mathematical arguments derived,
integer parity algebra source-written, Q₂/R and H¹
same-object welds OPEN, Agda 2.9 kernel receipt OPEN.

## 14 Nov second-coordinate odd-prime source and Q2 negative control

`DASHI/Mathematics/Arithmetic/EllipticOddPrimeSecondValuationParityExact.agda`
now source-writes the second original Kummer coordinate v_p(x-1) parity
for ODD primes, using the already-existing integer parity theorems.
For v_p(x-1)>0 and p odd, x and x+1 are units because x=1 modulo p
and x+1=2 modulo p. Thus 2v_p(y)=v_p(x-1). If v_p(x-1)<0,
the three factors x,x-1,x+1 have identical valuation and
2v_p(y)=3v_p(x-1), again forcing even parity.
This establishes the same mathematical odd-prime support condition
used by the more advanced Lean source owner
`Synthesis/MillenniumBSDCMOddPrimeLocalSecondParityExact.lean` on
`chboishabba/dashi_lean4` PR #107. Cross-kernel Agda↔Lean proof
transport and local Qp H1 still require independent validation.

**Important actual Q2 negative control:** x=39 on the original
curve gives y²=39*38*40=59280=2^4*3705, with 3705 congruent 1 mod 8.
Therefore 59280 is an actual Q2 square, by the standard 2-adic
square criterion; a non-torsion E(Q2) point has x=39.
Yet v2(x-1)=v2(38)=1 is ODD. Thus the second-coordinate parity
claim must be restricted to ODD p; asserting the same at p=2
would be false even for actual local points, not merely for
an abstract square-class code.

Independent deterministic arithmetic check:
`python3 scripts/check_bsd_k1_local_squareclass_parity.py`.
Checks rational x whose original cubic RHS is a Qp square at
2,3,5,7,11,13 and enforces first-coordinate all-p parity and
second-coordinate odd-prime parity, plus the x=39 negative control.
Enumeration is NON-kernel evidence and cannot replace the
nonarchimedean valuation theorem or Galois-H1 same-object weld.
