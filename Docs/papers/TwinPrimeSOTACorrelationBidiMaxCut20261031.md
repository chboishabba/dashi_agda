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
