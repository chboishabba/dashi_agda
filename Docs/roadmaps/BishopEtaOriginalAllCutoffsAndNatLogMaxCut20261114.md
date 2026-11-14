# Bishop/eta: original all-cutoff constructive maximum cut (14 Nov 2026)

Owner Agda PR #1478; original previous donor #1408. All references
below are literal original Murray/Bishop real setoid /
`RiemannBishopComplexAnalyticCarrierExact.BishopComplex`.
This documents a **mathematical bound** and exact finite checks;
there is **no current Agda 2.9 kernel proof** for the decisive
source `originalRound11EtaCompactUniformConvergence`.

## 1. Original Nat indexing is not optional

`BishopRiemannDirichletExponentialTermExact.agda` uses
`NatLogCandidate = Nat → R.ℝ` and

`bishopDirichletExponentialTerm T logNat s j
  = expC(-s*logNat j)`.

The intended canonical source law is
`logNat j ≃ log(j+1)`, so `a_s(j)` represents
`(j+1)^(-s)`. Its log producer comes from the **original
negative-log power series** `-log(1-x)`, not from an already
identified real integral.

The exact pre-existing Agda type in
`BishopOriginalEtaDyadicSourceLawReductionExact.agda` is

`OriginalDyadicNatLogLaw logNat = (k:Nat) →
    logNat(suc(twice k)) ≃ logNat(suc zero)+logNat k`.

Equivalently it compares source indices `2k+1`, `1`, `k`:
the represented *positive integers* are `2(k+1)`, `2`,
`k+1`. Thus the physical identity is
`log(2(k+1))=log 2 + log(k+1)`, not a shift-free
`logNat(2k)=logNat 2+logNat k`.

To inhabit `originalCanonicalNatLogDyadicAddition`,
prove the actual convergent negative-log source agrees with
its positive-real logarithm and prove multiplicativity in the
original real setoid; a substitution using a different
`∫1^n dt/t` source does not meet this interface.

## 2. Real sine/cosine addition: exact remaining source leaves

`BishopOriginalNativeComplexExpAdditionFromTrigExact.agda`
already contains the correct `OriginalCosineAddition T` and
`OriginalSineAddition T` premise types and a native expC addition
compiler. `BishopComplexExpFactEqualsNativeExpExact.agda`
separately supplies the factorial-complex-exp-to-native-exp
convergence route.

Reuse the true coefficient construction and finite rectangle
/ triangular Cauchy-product majorant. The two selected trig
identities require a *limit equality in the Murray setoid*
for all original `x,y`, not merely the abstract textbook
binomial identity or finite coefficients.

Mathematical coefficient identity:
`cos(x+y)=cos x cos y-sin x sin y`,
`sin(x+y)=sin x cos y+cos x sin y`.
Kernel facing tasks:
`originalBishopCosineAddition`, `originalBishopSineAddition`;
then reuse
`originalBishopAnalyticExpAddFromNativeRealExpAndTrig`.
Do not infer these from the existence of a convergence record.

## 3. Distinguish the two derivatives

For each positive real `u`, fixed complex `s`:
`d/du u^(-s)=-s u^(-s-1)`, hence
`u_N^(-s)-u_(N+1)^(-s)=s∫_N^(N+1)u^(-s-1)du`.

For each *fixed integer* `n` and varying complex `s`:
`d/ds n^(-s)=-log(n)n^(-s)`.
These are different derivative theorems. The **real-variable**
one is needed for the Abel/pair tail magnitude; the complex
parameter derivative is used in analyticity, and neither
is established on the selected native Bishop term by naming
the other.

Exact original-source producers to add:
`originalBishopNatLogAgreesWithRealLog`,
`originalBishopComplexPositiveRealDerivative`,
`originalRound11DirichletTermFundamentalTheorem`,
and the original norm/order/FTC transport.

## 4. Complete pairs vs arbitrary cutoffs

Define the source `a_s(j)=expC(-s*L(j))`. The original repo's
`originalEtaPrefix term n` is the **2n-term** prefix
`Σ_(j=0)^(n-1)(a_s(2j)-a_s(2j+1))`.
Existing original owners:
`BishopOriginalDirichletEtaFinitePairingExact.agda`,
`BishopOriginalEtaPairBlockTelescopingExact.agda`,
`BishopOriginalEtaFiniteAbelSourceExact.agda`.

For complete pairs and conventional integer index `n`,
`w_k(s)=(2k-1)^(-s)-(2k)^(-s)
 =s∫_(2k-1)^(2k)u^(-s-1)du`.

For `M<N`, `Re s=σ>0`:
`|Σ_(k=M+1)^N w_k(s)|
 <= |s|/σ*(2M)^(-σ)`.
This is the pair-only bound from the attachment (given the
true original real-variable FTC). It **does not** directly
bound an arbitrary odd raw prefix: include the final unmatched
term, or use finite Abel summation.

For any integer `1≤N≤M` and `Re(s)≥δ>0`, `|s|≤R`:

`|Σ_(n=N)^M (-1)^(n-1)*n^(-s)|
 ≤ (1+R/δ)*N^(-δ).`           (A)

Finite proof: local alternating partial coefficients
`A_j=Σ_(n=N)^j(-1)^(n-1)` take values `0,+1,-1`,
hence `|A_j|≤1`. Summation by parts gives a last-term
bound `M^(-σ)` plus `Σ_(j=N)^(M-1)
|j^(-s)-(j+1)^(-s)|`; the latter is bounded by the
real-axis FTC `|s|/σ*(N^(-σ)-M^(-σ))`.
Thus a safe all-endpoints bound is `(1+|s|/σ)N^(-σ)`,
and then (A), valid for `N≥1`.

On a compact `K` with `Re s≥δ` and `|s|≤R`,
`C_K=1+R/δ`. A fully **rational**, constructive
modulus works whenever the lower bound `δ=p/q>0`
and `C_K,eps` are rational: choose an integer `N`
such that
`N^p * eps^q ≥ C_K^q`.
Choose `eps/2` in that inequality for a strict
`<eps` bound. This uses integer power arithmetic,
not a floating exponent or an unproved Bishop real
`ceil` operation.

Example: `δ=1/2,C_K=9,eps=1/10` yields `N=8100`
for `≤eps`, and `N=32400` for `≤eps/2<eps`.
The formal Agda proof must transport such a modulus
through the original `SeriesOf` limit and the genuine
source complex absolute-value/order structure.

## 5. Executed diagnostics / reproduction

Run:
`python3 scripts/check_bishop_eta_abel_uniform_tail.py`
`python3 scripts/check_bishop_eta_all_cutoffs_maxcut_20261114.py`.

The second checker has independent cases: **21,845** exact rational
finite Abel identities, **1,972** exact real arbitrary-endpoint tails,
**576** exact complete-pair tails, and **245** complex numerical
arbitrary-endpoint diagnostics. Exact positive-rational modulus
computed by integer powers. These are **not** Agda kernel
acceptance for the actual Bishop source.

## 6. Original A/B acceptance gates, preserved verbatim

A: `originalBishopCosineAddition`,
`originalBishopSineAddition`,
`originalCanonicalNatLogDyadicAddition` on the existing T/L,
reusing native exp and shifted-pair compilers.

B: `originalRound11DirichletTermAnalyticDerivative`
(holomorphy in s), `originalRound11DirichletTermFundamentalTheorem`
(real-axis u derivative/FTC separately),
`originalRound11EtaAbelPairTailBound`, then
`originalRound11EtaCompactUniformCauchy` and
`originalRound11EtaCompactUniformConvergence` with
all raw odd/even cutoffs and a Bishop-setoid modulus.

Analyticity of the limit requires original complex derivative
or an accepted locally-uniform holomorphic-limit theorem.
The finite factor identity and eta convergence do NOT alone
justify global zeta division; `1-2^(1-s)=0` on
`s=1+2πik/log2`, requiring a separate divisor/
removable-singularity analysis.

**Gate status: all selected A/B analytic leaves still OPEN.
Nothing in the attached argument or the diagnostic script is
a new kernel receipt or an RH conclusion.**
