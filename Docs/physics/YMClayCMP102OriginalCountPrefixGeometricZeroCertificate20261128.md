# CMP102 original Bishop finite-prefix geometric-zero certificate (Section 26)

28 November 2026; native Agda source/body to be elaborated. This proof
derivation is in the **original CMP102/CMP109 coefficient and finite-prefix
convention**, not a substitute Taylor model, and must be transported into the
original Bishop `Real`/`Sequence` constructive order through already written
finite Cauchy and factorial estimates. This document is a mathematical proof
plan/certificate, **not** a native Agda proof of the final inequality.

## Critical source indexing reconciliation

The original `DASHI/Foundations/BishopFinSumSeriesBridgeExact.agda`
proves `finSumIsSeriesOf`; `Seq.SeriesOf terms count` sums terms
indexed **0 through count-1**. Accordingly, write
`A_c(X)=sum_{j=0}^{c-1} X^j/(2j+2)!`,
`B_c(X)=sum_{j=0}^{c-1} X^j/(2j+3)!`.
These are exactly `YMClayCMP102OriginalGFiniteLimitTransportExact.aPrefix`
and `bPrefix` once original coefficient identity and finite-sum bridge
are consumed; at c=0 both are zero.

The actual source expression is
`G_c(X)=1-2A_c-X A_c^2+2X B_c+X^2 B_c^2`.
Do not shift to an inclusive N partial sum: that would change the
claimed power of the geometric rate by one.

## Unbounded original all-degree cancellation

Let formal even/odd factorial series
`C(z)=sum_{j>=0} z^(2j)/(2j)!`,
`S(z)=sum_{j>=0} z^(2j+1)/(2j+1)!`.
At every integer k>=1, the coefficient of z^(2k) in `C²-S²`
is exactly
`1/(2k)! (sum_{i even} binom(2k,i)-sum_{i odd} binom(2k,i))=0`.
The degree-zero coefficient is one. This follows from the finite
binomial parity identity `(1-1)^(2k)=0`, not an unproved analytic
interchange. The original all-degree signed Cauchy endpoint parity
is ALREADY SOURCE-WRITTEN in
`YMClayCMP102OriginalEndpointCauchyShiftExact.agda`
(`originalSignedEvenRowIsNativeAPart`,
`originalSignedOddRowIsNegativeNativeBPart`,
`shiftedNativeBracketCoefficientZero`). No second Cauchy algebra
should be introduced.

Since `C(z)=1+z² A(z²)` and
`S(z)=z(1+z² B(z²))`, the coefficient identity reduces exactly to
`1-2A-X A²+2X B+X² B²=0`.
By the original finite Cauchy split, the coefficient of X^k in G_c
depends only on A_j (j<=k) and B_j (j<k). Therefore for all k<c:
`[X^k] G_c=0`.
For c>=1, the first nonzero coefficient is exactly
`[X^c] G_c=2/(2c+2)!`, because the ONLY omitted term affecting
that degree is `-2 A_c`'s next factorial coefficient.
This coefficient is positive, hence *finite* G_c is generally NOT
identically zero; it converges to zero at the specified rate.

## Uniform absolute polynomial majorant (all c, all |X|<=1/4)

For j>=0, original factorial ratio gives
`a_(j+1)/a_j=1/((2j+4)(2j+3))<=1/12`,
`b_(j+1)/b_j=1/((2j+5)(2j+4))<=1/20`.
The full nonnegative coefficient sums at X=1 obey
`A_c(1)<= (1/2)/(1-1/12)=6/11<3/5`,
`B_c(1)<= (1/6)/(1-1/20)=10/57<1/5`.

Let `||p||_1` be the sum of absolute rational coefficients.
The original finite `G_c` has
`||G_c||_1 <= 1+2A_c(1)+A_c(1)^2+2B_c(1)+B_c(1)^2 <= 3`
(the right equality at A=3/5,B=1/5 is exactly 3).
As all coefficients of degrees k<c vanish, the uniform estimate is
`|G_c(X)| <= |X|^c ||G_c||_1 <= 3*(1/4)^c`
for every c>=0 and every real `|X|<=1/4`.

This is the **same 3*4^-count rate** noted but left as an independent
certificate in the original G finite-limit transport owner, with the
original SeriesOf indexing now explicit. It gives constructive
convergence of the original prefixes to zero when expressed through
existing Bishop factorial monotonicity, finite sum/triangle inequality,
and `Seq` geometric convergence. Combined with the already written
`originalGPrefixConvergesToOriginalG` and
`originalGZeroFromOriginalPrefixConvergence`, it proves original
`G(X) ~= 0` on the Bishop quarter disk **only after** those native
inequalities and convergence lemmas are written and kernel accepted.

## Native Agda endpoint weld (remaining, precise)

1. Reuse `finSumIsSeriesOf` for exactly c summands; identify the
   existing `aPrefix,bPrefix` terms with original CMP102 coefficients.
2. Consume the already-written original signed all-degree Cauchy
   coefficient identity. Prove a native low-degree zero coefficient
   lemma `k<c -> coeff(G_c,k) ~= 0` with the finite Cauchy sum.
3. Apply original embedded factorial ratio order and finite triangle
   inequalities to prove `abs(originalGPrefix X c)<=3*4^-c` for
   every c and `|X|<=1/4`; no assumption of `G=0`.
4. Consume the existing `Seq` geometric convergence theorem to supply
   `Seq._ConvergesTo_ (originalGPrefix X) R.0ℝ` in the ORIGINAL
   Bishop represented real, then pass it to the existing
   `originalGZeroFromOriginalPrefixConvergence`.
5. Run Agda 2.9 native typecheck, no GitHub CI; inspect transitive
   source and axioms before any proof promotion.

## Finite exact arithmetic receipt

`scripts/check_ym_cmp102_original_count_prefix_geometric_bound_20261128.py`
checks the ACTUAL rational coefficients at counts 0..40:
all 820 low-degree zero coefficient cases, 40 exact leading
coefficients, 123 rational coefficient-majorant inequalities and
205 quarter-disk rational endpoint/interior evaluations:
**1188/1188** exact assertions PASS on locally reconstructed code.
The script is committed; the exact committed bytes have not been
independently rerun in a native checkout.

Important firewall: this scalar CMP102 identity is not an absolute
CMP116 cluster expansion, a continuum physical Wilson measure,
Osterwalder–Schrader reconstruction or a Yang–Mills mass gap.
Preserve the original two-pair nonfactorizing shared plaquette and
the original Wilson/Bałaban physical provenance.
