# Four non-RH/YM Clay lanes — geometry-FORWARD, STEELMAN, BIDI, reverse-solve
23 November 2026 · Addendum to [four-lane maximum-cut](ClayNonYMRHFourLaneGeometricMaxCut20261123.md). Source-first; proof promotion FAIL-CLOSED.

## 0. Source readback and a genuine error repair

**Karp previous claim corrected.** The previous PR #1541 note claimed `m(2m-1)` address equality checks. That counted the new endpoints as if they were inserted separately. In the ACTUAL `Karp21FinFreeRawSparseWordVerifierExact.rawSparseScore` constructor, the new pair `(u,a),(v,b)` joins history **only after both checks**. At edge j there are 2j earlier endpoint observations and two new queries, yielding `4j` potential address equality tests. Therefore

```
Cmax(m) = sum_{j=0}^{m-1} 4j = 2m(m-1).
```

This is already source-written in `Karp21FinFreePairwiseQuadraticCountExact.maxAddressComparisonsClosed` and implemented in `scripts/karp21_binary_native_sparse_verifier.py` (including the separate `m(m-1)` outer loop-iteration count). On malformed/rejected inputs, and with short-circuiting, counts can be smaller; **Cmax** is a full-scan upper count, not a universal exact runtime. At m=1 the native history comparison count is 0. The old `m(2m-1)` is incorrect for that geometry. Do not create a replacement Agda source owner.

## 1. Navier–Stokes: recover which recenterings are actually legal

### Reuse original mathematics before physical promotion

Original source owners:
- `NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact`: signed `S=-sum_{i<j}(r_i-r_j)(w_i-w_j)`, with physical `r_i=rho_p+rho_q`, `w_i=2 Re<M,A_i>`, `M=sum_i A_i`.
- `NSTriadKNFiniteBipartiteCovarianceExact`: exact division-free bipartite finite sum.
- `NSTriadKNFixedOutputInputLaplacianCriticalRegionPairBlocksExact`: per-incidence R236 region classifier AFTER the original pair term is formed; retain six unordered region blocks and all zero-work incidences.
- #1539 physical R734/R735 auxiliary W2 and R850/R853 unrestricted payment negative controls: do NOT resurrect a refuted positive assumption.

For a partition into occupied regions a with population n_a and rate sum R_a, shifting **work**, not rate, by `w_i'=w_i-c_a` on region a changes its cross-region signed block by

```
D_ab = (c_a-c_b)(n_b R_a-n_a R_b),  a != b.
```

This gives a *reverse* characterization, not just a forward identity:
1. **Every individual signed block preserved** iff `(c_a-c_b)(n_b R_a-n_a R_b)=0` for every pair. Construct graph G_rate on occupied regions with edge ab precisely when `n_b R_a != n_a R_b`; all-block-preserving shifts are exactly constants on each connected component of G_rate. For three occupied groups, if at least two region-average rates differ, G_rate is connected and therefore only common shifts preserve all six blocks. If all means agree, each cross-block aggregate survives arbitrary regional shifts even though individual pair terms may change.
2. **Only the global signed sum preserved** iff
```
  sum_a c_a (N R_a-n_a R_total)=0,
  N=sum n_a,  R_total=sum R_a.
```
   This is one linear condition and can hold when individual blocks change. Negative control: one incidence in each of three regions, rates (1,2,3), shifts (1,0,1): total defect is 0 but two cross-block defects are -1 and +1. Do NOT infer B1–B4 from a cancelled total.
3. **Same coherent physical output** is a separate constraint. In the unconstrained finite complex/Hilbert amplitude construction, `sum_i w_i=2||M||²`. Thus a fixed `M` requires `sum_a n_a c_a=0`. For `M!=0`, this is sufficient **in the free ambient amplitude model**: choose
```
  A_i' = A_i - (c_region(i)/(2||M||²)) M.
```
   Then `sum_i A_i'=M` and `2 Re<M,A_i'>=w_i-c_region(i)`. For `M=0`, every work value is 0; any claimed nonzero work shift is impossible with the same zero M. The free ambient construction does NOT establish that the altered A_i remain original mixed-helicity, divergence-free or physical Galerkin triad products. A physical source lift must pay those exact constructor images separately.
4. Hence the **formal linear reverse problem** for preserving fixed M and only the global sum is `n dot c=0` and `(NR-nR_total) dot c=0`; for preserving *all* original blocks impose every G_rate edge equality too. These conditions are mathematically explicit, not a new proof of an NSE signed estimate.

Keep original sign, zero branch, fixed physical time, and source R236 `criticalRegionTag`. A finite invariant is a necessary constraint on any proposed physical transformation, not permission to substitute a transformed work family in the PDE.

### Executed exact controls

A separate local Fraction regression checked 2,400 randomized three-region exact-rational reverse examples (block defects, total defects, kernel-component equivalence), 600 finite Hilbert-amplitude lift trials (nonzero output), the three-region total-but-not-block negative control, and the zero-output obstruction. These are mathematical finite checks, not original Galerkin helical source or Agda kernel acceptance.

## 2. Karp-21 / P != NP: incidence geometry and endpoint reconstruction

Use the SAME canonical signed weighted simple graph word (gamma n,m,u,v,zigzag weights, positive threshold; strict u<v<n and ordered distinct edges), the existing 2m-bit local occurrence labels and original `rawSparseScore`. No `Fin n`, full vertex vector or n-entry array belongs on the executable sparse path.

Let `U` be the set of k distinct endpoint vertex IDs present in the actual m edges, and let b be the number of connected components of the graph **on U** (excluding the n-k isolated unused vertices). The endpoint-occurrence equivalence relation identifying equal vertex IDs has exactly k classes. A 2m-bit occurrence-label word is consistent iff every such class has one Boolean label. Thus:
- exactly `2^k` consistent occurrence-label words exist before score/threshold filtering; each has exactly `2^(n-k)` full n-vertex label extensions, with ignored isolated vertices freely chosen. The full extension is a PROOF object, not runtime memory.
- project to signed-edge **cut parities** `y_e=x_u xor x_v`, of length m. Not all `2^m` parity words are possible: `y` is in the incidence coboundary image exactly when XOR around every graph cycle is zero. A spanning-forest parity propagation supplies a constructive inverse on U if and only if every encountered cycle closes.
- the incidence map over F2 has kernel of dimension b (one free flip on each connected component of U) and image dimension k-b. Hence `2^(k-b)` feasible parity words, each with `2^b` support-label lifts and `2^(b+n-k)` complete original vertex-label lifts.
- The original signed objective is retained exactly: `score(y)=sum_e w_e y_e`; negative and zero weights are not discarded. The original positive-threshold comparison is also retained. Reconstructing original endpoint labels from parities requires the **b component-orientation bits** (plus the isolated n-k free bits if a full proof vector is demanded). Binary parity alone forgets these signs; it is a quotient, not a bijective codec.
- A triangle with parity (1,0,0) is a negative control: its cycle XOR is 1 and no global vertex labels exist. A forest has no cycle constraint. For a graph with n=2^k but m=1, only two support vertices are represented by the executable verifier; the n-k full-vector extension must stay *off* the runtime.

**BIDI:** original consistent 2m occurrence labels -> incidence parities satisfying all cycles; cycle-consistent parity + one chosen flip for each support connected component -> unique support labels -> the exact original 2m occurrence word. This is source-faithful *finite graph geometry*. The unproven glue to original executable all-word parser semantics, physical F1 tape instructions, F2 heap, F3 transition simulation, F4 bit-clock, G2/G3/G4 typed original NP receipts, and independent universal SATNotInP remain OPEN. No graph quotient lower bound implies P!=NP.

### Executed exact controls

A separate local Python exact exhaustive regression checked 5,024 graph/parity configurations (n=2..5, up to 4 canonical edges), comparing constructive BFS parity reconstruction against all 2^n full assignments, the predicted 2^(b+n-k) lift count, signed score agreement, exact 2^k consistent 2m-bit occurrence words and the corrected 2m(m-1) original scan count. This is not a source-native Agda proof or physical bit-machine benchmark.

## 3. BSD: reverse-read the original odd finite-field symmetry

For **E32**, f(x)=x³-x is odd. For any p=3 mod 4, the involution x->-x has Legendre sign -1, so the original complete sum vanishes and `a_p(E32)=0` by classical finite-field arithmetic. Reverse caution: vanishing at a finite set of primes does NOT prove inertness, identify the full CM L-function, or construct the E32 eta/Mellin bridge. The same pairing extends to odd cubic `x³-d²x` at good primes p not dividing 2d, but those are DIFFERENT twisted curves: do not collapse their original source identities into E32. An independent exact finite sample checked 127 (prime, nonzero d) pairs below 301, plus the E32 split-prime p=5 negative control. The user-selected E32 K4 same-object and S6 all-curves rank remain OPEN.

## 4. Hodge: reverse the complementary intersection geometry

On the selected literal `X_r=(CP¹)^r` only, define `h_I=product_{i in I} h_i`, `h_i²=0`. Its complementary rational intersection pairing is the exact permutation matrix

```
  int_X(h_I h_J) = 1 iff J=I^c, else 0, for |J|=r-|I|.
```

Given an actual rational Hodge class `alpha=sum_{|I|=p} a_I h_I`, reverse-solve every coefficient by `a_I=int_X(alpha h_{I^c})`, then output the **actual algebraic** coordinate-cycle combination `Z_alpha=sum_I a_I [coordinate point cycle_I]`. Forward evaluation of its established classical cycle-class gives alpha; backward coefficient extraction recovers the input. Every complement pairing has determinant +1 or -1 and no rational kernel. Tests cover 900 random rational class reconstructions at r=0..8. This is classical product-family geometry and a geometric explanation of its non-descent beyond that family, not a new all-varieties Hodge theorem. Generic original Hodge comparison owner fields, all-X cycle preimages and native exact-head Agda kernel remain OPEN.

## Outcome and next actual source-specific gates

1. NS: attempt the fixed-output *physical helical* lift into original `A_i` and signed B1–B4 coherent-work inequality, refusing any independent region work recenter that changes the source.
2. Karp: BIDI the original `rawSparseScore` and canonical graph-word semantics with a source-native cycle test or the existing 2m-occurrence grammar, then **physical** F1/F3/F4 tape and signed score clock. Reuse original `Karp21FinFreePairwiseQuadraticCountExact`, no duplicate arithmetic theorem.
3. BSD: actual SAME E32 eta/modularity/Mellin identification before counting any selected coefficient as universal.
4. Hodge: literal generic singular/de Rham comparison and algebraic cycle-class inhabitant for genuinely new varieties, not another P¹ product toy.

No RH or YM theorem/roadmap modification. No Clay promotion; no CI or Agda/Lean kernel invocation. Preserve original authors Karp, Künneth, algebraic Hodge/CM, and prior repo mathematical owners.
