# Constructive π fast-evaluation max-cut — 18 November 2026

## Scope and provenance
This lane retains the original Bishop real `bishopMachinPi` in
`DASHI/Foundations/BishopMachinArctanConstructionExact.agda`.
Original arctangent series, Bishop completeness, and alternating interlacing
belong to the cited Murray/Csimma, Bishop/Bridges, Machin, and existing DASHI
owners. The new Python script is a **finite rational reference implementation**,
not an Agda proof, not a new geometric π, and not a proof of the four-term
identity in the Bishop real setoid.

## Current implementation
`scripts/check_bishop_fast_pi_binary_split.py` implements a balanced
integer-only P/Q/T evaluator for
`atan(1/q) = sum (-1)^k / ((2k+1)q^(2k+1))`.

Define `p_0=1, q_0=q` and, for `k>0`,
`p_k=-(2k-1), q_k=(2k+1)q²`. The k-th arctangent term is
`product_{j=0}^k p_j/q_j`.

For a segment [a,b), let P/Q be the product of its ratios and T/Q their
relative prefix sum. The exact merge is

```
P = P_L P_R
Q = Q_L Q_R
T = T_L Q_R + P_L T_R
```

The script tests finite prefix and arbitrary subsegment identities against
independent exact `Fraction` sums. It uses alternating parity to produce
rational lower/upper bounds and per-argument integer precision schedules.

Two formulas are evaluated:
- Machin: `16 atan(1/5) - 4 atan(1/239)`.
- Four-term: `176 atan(1/57)+28 atan(1/239)-48 atan(1/682)+96 atan(1/12943)`.
  Both formulas yield rational intervals for their own series-defined values.
  Their overlap at finitely many precisions is **not** a theorem of equality
  of their Bishop limits.

## Independent offline verification performed before push
- The equivalent local reference script passed direct rational sum parity
  and binary splitting tests for multiple denominators, prefixes and ranges.
- SymPy exact Gaussian-integer calculation established
  `Re(z)=Im(z)>0` for
  `z=(57+i)^44 (239+i)^7 (12943+i)^24/(682+i)^12`.
  This proves only the finite formal angular identity modulo 2π;
  the same-source Bishop arctangent addition/branch identification is open.
- Locally measured median exact **enclosure-evaluation** wall times on
  18 November 2026 (Python 3, seven runs, not Agda):
  
| Decimal places | Direct Machin Fraction | Binary-split Machin | Four-term binary split |
|---:|---:|---:|---:|
| 100 | 0.217 ms | 0.073 ms | 0.100 ms |
| 1,000 | 23.160 ms | 1.398 ms | 1.939 ms |
| 3,000 | 431.917 ms | 7.861 ms | 11.748 ms |
| 10,000 | not timed | 63.829 ms | 98.783 ms |

The four-term formula uses fewer series terms but currently loses on actual
wall time (more large-number arithmetic). These numbers exclude scheduling,
Agda elaboration, and full transitive proof validation. Re-run locally before
using as performance claims on another machine.

## Complexity and description-length accounting
- Direct `Fraction` accumulation performs N gcd/normalization operations
  on generally growing integers, with an unfavorable quadratic aggregate
  operand-size/work pattern.
- Balanced integer binary splitting has logarithmic recursion depth,
  O(N) arithmetic nodes, and a quasi-linear-in-output-size path under fast
  multiplication for suitable hypergeometric recurrences. Exact bit
  complexity depends on multiplication algorithm, cancellation, and output
  representation; no universal O(N log N) **bit** bound is asserted.
- Kolmogorov complexity K(x) is not computable. As reproducible proxies,
  record uncompressed source bytes, DEFLATE-compressed source bytes, and
  rational certificate bytes at fixed precision. These are engineering
  description-length metrics, **not** measurements of true K(π).
- The integer term recurrence avoids repeatedly storing full powers
  `q^(2k+1)` in split leaves; the per-argument precision schedule must
  also maintain powers incrementally rather than recomputing them.

## Remaining named Agda proof cut
P0. Real.agda representation-level dyadic rational enclosure,
setoid preservation and exact width (mind the factor-of-two shift).
P1. Structural split recursion, positive denominator, exact leaf/merge,
arbitrary-range invariant, and equality to original finite arctangent sums.
P2. Reuse existing alternating brackets; build independent per-argument
precision schedule and certified `bishopMachinPi` interval.
P3. Formal rational Gaussian product, branch bounds, source sine/cosine
addition for arbitrary half-ball arctangent arguments, and identity of the
four-term Bishop real with the original Machin real.
P4. A canonical interval→Bishop Cauchy adaptor and overlap/uniqueness
transport on the literal vendored carrier.
TRIG. Discharge six fields in `MachinQuarterAnalyticInputs` with actual
original Bishop sine/cosine series proofs; no fake period field.
C3. Exact cube-root interval producer, Halley soundness/termination,
genuine cubic modular equation and same-real identification.
CH. Chudnovsky hypergeometric splitting, tail/root certificates, genuine
modular proof identifying its limit with original π.
YM.REAL. Rational Haar Cauchy and group invariance, original finite RG
weld, and --safe transitive acceptance (independent of π).

## Acceptance boundary
The exact Agda compiler is unavailable in the current execution environment.
No Agda declaration has been typechecked by this change, and no original
YM.REAL gate or period theorem is claimed closed. Future proof promotion
requires a pinned toolchain, `agda --safe` over the complete import graph,
and explicit source provenance and kernel receipts.
