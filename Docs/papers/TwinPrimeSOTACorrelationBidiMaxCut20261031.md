# Twin-prime SOTA ↔ exact-correlation max-cut (31 October 2026)

## Scope and attribution

Bidirectional comparison of published bounded-prime-gap benchmarks with the exact shifted-prime problem. Mathematical roots: Brun/Chen (sieve), Hardy–Littlewood (prime-pair conjecture), Goldston–Pintz–Yıldırım, Yitang Zhang, Maynard–Tao, Polymath8b. PrimeGapsLib (Axiom Math) and OpenAI PrimeGaps186 (2026) own their independent Lean work; reported 186 Lean result depends on explicit external analytic and numerical assumptions. DASHI implementation owners remain `TwinPrimeSOTABoundedGapBidiExact`, `TwinPrimeMangoldtNonzeroPrimeSumWitnessExact`, the classified finite Mangoldt split, and the certified Nat prime enumerator. None of these imports or proves twin-prime infinitude.

## SOTA fact vs exact-shift residual

- Established Polymath8b: H1 <= 246. This means infinitely many **consecutive** primes have gap at most 246, not necessarily 2.
- 2026 reported result: H1 <= 186, independent peer review and full kernel discharge of its external assumptions not established here.
- Chen's theorem: infinitely many p with p+2 either prime or a product of at most two primes. It does not certify the second endpoint prime.
- `TwinPrimeSOTABoundedGapBidiExact` already proves the conditional equivalence for a bounded pair whose **actual shift is retained as 2**. General bounded-gap witnesses lose this residual.

## Exact real-valued correlation and a necessary-and-sufficient target

For X >= 4, set
`P(X) = sum_{p <= X-2, p and p+2 prime} (log p)(log(p+2))`.
Let `S(X) = sum_{n+2 <= X} Lambda(n)Lambda(n+2)` for the classical real von Mangoldt Lambda, and `E(X) = S(X)-P(X)`. Then:

1. `S(X)=P(X)+E(X)` by the nine classified support cases: prime/prime contributes to P, all other nonzero cases require at least one proper prime-power endpoint. All terms are nonnegative.
2. **BIDI:** infinitely many twin-prime pairs iff `P(X)` is unbounded above as X grows. In the forward direction every prime pair contributes at least `log(3)log(5)>0`; in reverse, finitely many pairs imply eventual constancy of `P`.
3. Therefore the equivalent analytic max-cut is `sup_X [S(X)-E(X)] = +infinity`; **not** necessarily `S(X) >= cX`.
4. The stronger cofinal lower bound `S(X)>=cX` with fixed c>0 combined with `E(X)=o(X)` suffices. Hardy–Littlewood predicts an asymptotic of linear order, but is unproved.
5. An alternative sufficient criterion is: for every N there is a finite interval beginning >=N on which the **actual prime-only sum** is nonzero. This is precisely the conditional direction implemented by `TwinPrimeMangoldtNonzeroPrimeSumWitnessExact`.

The inverse direction from a twin witness to a *nonzero weighted* term requires actual real log positivity and faithful embedding of the prime-one weight; abstract `WeilTestSpace.Scalar` alone does **not** guarantee it. Do not silently claim that the generic abstract scalar implementation supplies the real-valued equivalence.

## Corrected proper-prime-power counting scale

For integer X >=4, every proper prime power m<=X has an exponent k>=2. Its number is bounded by
`Q(X) <= floor(sqrt X) + sum_{k=3}^{floor(log_2 X)} floor(X^(1/k))`
`<= floor(sqrt X) + floor(log_2 X)*floor(X^(1/3))`.
The estimate intentionally overcounts composite bases and duplicates; this is safe. For each such value m, it can occur as the **left endpoint of at most one** n,n+2 pair and the **right endpoint of at most one** pair. With `0<=Lambda(t)<=log X` for `2<=t<=X`, union bound gives
`0 <= E(X) <= 2 Q(X) (log X)^2 = O(sqrt(X) (log X)^2 + X^(1/3) (log X)^3) = o(X)`.
This is asymptotically substantially sharper than the earlier O(X log² X) count, which **does not itself imply o(X)**. The bound is elementary, not a research record. A useful proof-friendly bound avoids log_2 via at most floor(log_2 X) possible exponents and elementary floor/root inequalities.

## Discriminator / remaining unproved cut

Retaining a CRT residue, wave phase, finite FRACTRAN trace, C3 orbit sum, average, 27-state observer, or Monster character is not a substitute for proving an unbounded positive **actual** prime-pair correlation. At fixed finite sieve resolution arbitrarily large double-composite survivors persist. The missing result is one of:
(A) unconditional `forall M exists X, P(X)>M` in classical ordered real scalars;
(B) cofinally nonzero actual prime-only intervals with sound prime-log interpretation;
(C) another unconditional construction of arbitrarily large certified prime p with p+2 prime.

Forward import obligations: (i) explicit theorem provenance/assumptions; (ii) map published prime predicate to Nat primality; (iii) preserve *actual* shift and consecutive-pair distinction; (iv) only transport verified inequalities; (v) never present an assumed lower bound as a proved theorem.

Backward obligations: actual weight nonnegativity and prime-one positivity; exhaustive nine-case split; proper-power support count; real-Lambda interpretation of abstract scalar; exact unboundedness principle. Existing source-written Agda is not automatically kernel-verified.

## Public benchmarking sources

- Maynard, *Small gaps between primes*, Annals of Mathematics 181 (2015), https://annals.math.princeton.edu/2015/181-1/p07
- Axiom Math formalisation blueprint https://primegaps.axiommath.ai/paper/
- Tao's bounded-gap constant ledger https://teorth.github.io/optimizationproblems/constants/88a.html
- 2026 reported 186 and qualifications https://mathworld.wolfram.com/BoundedGapsBetweenPrimes.html

**Status:** Documentation/proof specification, not a new unconditional twin-prime theorem. All prior author and repository proof ownership retained. No ESD surfaces touched.


## Two genuine attempts, same max-cut (31 Oct continuation)

**Strong attempt (linear-order):** Seek `c>0`, `X0`, such that for all `X>=X0`, `S(X)>=cX`. Given the classical real `E(X)=o(X)`, choose `X1` with `E(X)<=cX/2`. Then `P(X)>=cX/2` for every `X>=max(X0,X1)`, yielding unbounded P and true twin-prime infinitude. This is a valid conditional deduction, **not** a derivation of the missing strong hypothesis.

**Intermediate attempt (cofinal linear subsequence):** It suffices to prove `limsup_{X→∞}S(X)/X>0`. Select `c>0` and unbounded `X_j` with `S(X_j)>=cX_j`, then subtract `E(X_j)=o(X_j)`. This relaxes eventual uniformity of the strong bound, but still requires genuinely new positive prime-correlation information.

**Weak attempt (exact necessary-and-sufficient target):** `P(X)=S(X)-E(X)` unbounded. Since every twin contributes `log p log(p+2)>=log 3 log 5>0`, infinitely many pairs force unbounded P. Conversely finitely many twin pairs make P eventually constant. This does not imply `S(X)>=cX`: the abstract nonnegative toy model `P(X)=sqrt(X), E(X)=0` is unbounded but sublinear. It is **not** a model of the primes, only a logical non-implication witness.

**Dyadic localization:** Infinitely many twins iff infinitely many dyadic slabs `[2^k,2^{k+1})` contain a twin starting point. Under strictly positive real prime-one weights, equivalently infinitely many dyadic increments of P (with careful consistent endpoint convention) are nonzero. A proof of a single dyadic block, or infinitely many sieve survivors, is insufficient.

**Highest-impact discriminator:** Current polynomial/CRT finite sieve labels and weighted bounded gaps do not distinguish genuine prime-one pairs from parity-matched composite survivors at arbitrarily high moduli. Neither route currently produces a new source of positive signed prime-specific correlation. A candidate lemma must directly discriminate the true prime ownership after every refinement rather than assume it in a record.

**Executed finite numerical probe:** `python /mnt/data/check_twin_routes.py` evaluated the classical von Mangoldt weights by prime-power enumeration in the local session, with floating-point logs (not interval-certified): 
`(X, proper-powers, S, P, E, P/X, S/X)`
- `100: (10,112.8880,79.9745,32.9135,0.79975,1.12888)`
- `1,000: (25,1135.4628,1028.3687,107.0940,1.02837,1.13546)`
- `10,000: (51,13302.9243,12950.5862,352.3382,1.29506,1.33029)`
- `100,000: (108,131522.9125,130224.4190,1298.4935,1.30224,1.31523)`
- `300,000: (155,393317.3863,391321.3631,1996.0232,1.30440,1.31106)`

These finite observations are consistent with the Hardy–Littlewood prediction but do not prove either max-cut. This doc and its related Agda module are source-written; no Agda executable was available in this tool session, so they are **not kernel-verified**. No ESD surface changed.

## 31 Oct max-cut continuation and executable check

**Two attempted cuts:**
- **Strong**: prove a positive linear lower bound on the true classical Mangoldt total, or at least a positive limsup after scaling by X. The already derived `E=o(X)` would then yield a positive linear prime-only subsequence. Neither lower bound follows from available finite sieves or the public bounded-gap formalisation.
- **Weak**: prove unbounded real `P(X)=S(X)-E(X)`; by strictly positive prime-one logarithmic weights, this is equivalent to twin-prime infinitude. An abstract cofinal finite-window witness is constructively bidirectional with `TwinPrimesInfinitelyOften`, and is source-written in `TwinPrimeStrongWeakMaxCutBidiExact.agda`. This is an equivalence, not a solution of its premise.

**Verified independently in local Python this turn:** `scripts/check_twin_prime_strong_weak_maxcut.py` computes distinct actual proper prime powers, actual Mangoldt correlation, prime-only contribution, and all remaining support contributions. It checks numerical splitting and the overcounted proper-power support bound. Output columns `N, twin-count, proper-prime-powers, S/N, P/N, E/N`:

```text
100 8 10 1.128880 0.799745 0.329135
1000 35 25 1.135463 1.028369 0.107094
10000 205 51 1.330292 1.295059 0.035234
100000 1224 108 1.315229 1.302244 0.012985
300000 2994 155 1.311058 1.304405 0.006653
```

Logarithms are Python floating-point, so the numerical test is not an interval-certified real proof. The exact count of 1224 twins in the evaluated range `n+2 <= 100000` is subject to that endpoint convention (earlier scripts with a different start range can differ). 

**New source-written owner:** `DASHI/Arithmetic/TwinPrimeStrongWeakMaxCutBidiExact.agda`, with a helper-based lower-bound transitivity readout; Agda compiler was not available in the container, therefore it has **not** been kernel-checked. It imports the established certified Nat twin and finite interval owners and does not change protected ESD paths.

**Source verification:** Public [Axiom Math PrimeGapsLib](https://primegaps.axiommath.ai/paper/) explicitly takes Bombieri–Vinogradov as an analytic input for H1<=246. [OpenAI PrimeGaps186](https://github.com/openai/PrimeGaps186) explicitly assumes three inputs: rank-three hyper-Kloosterman bound, rank-two Kloosterman correlation bound, and a collection of physical-integral/cap numerical bounds. Its conditional Lean theorem is not gap 2. No existing source proves the needed unconditional prime-only correlation lower bound.

**Max-cut decision:** further manipulation of the exact finite `S=P+E` identity or bounded-gap hypotheses alone does not yield a positive contribution. A new theorem must establish either positive actual prime-one correlation on an unbounded sequence or its dyadic nonvanishing, without smuggling prime ownership/density into an axiom.

## Steelman upgrade, 31 October 2026

The research target is now tiered rather than moved: [TwinPrimeSteelmanAsymptoticBidiTarget20261031.md](TwinPrimeSteelmanAsymptoticBidiTarget20261031.md). T0 is exact twin-prime infinitude ↔ unbounded real prime-only correlation; T1 positive limsup S(X)/X, T2 positive liminf, T3 Hardy–Littlewood S(X)~2C2 X, and T4 the counting asymptotic pi2(X)~2C2 Li2(X). Neither existing bounded-gap results nor source-written Agda establish T0–T4. Read the separate document for explicit assumption and weight-transport boundaries.
