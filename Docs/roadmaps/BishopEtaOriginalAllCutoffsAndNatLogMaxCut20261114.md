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

## 1b. New finite negative-log remainder directly on the true source

Instead of postulating an equality with the reciprocal integral, set
`ell_N(x)=sum_(j=1)^N x^j/j`, the literal original
negative-log finite polynomial, and let `z=x+(1-x)y`.
An EXACT rational polynomial differentiation gives

`d/dt[ell_N(x+(1-x)t)-ell_N(t)-ell_N(x)]
   = (t^N-(x+(1-x)t)^N)/(1-t)
   = -x*sum_(j=0)^(N-1)(x+(1-x)t)^(N-1-j)t^j`.

The quotient is a polynomial, so there is **no pole** at t=1
after cancellation. For `0≤x,y<1`, integrating only
finite polynomials and using monotonicity gives

`0≤ell_N(x)+ell_N(y)-ell_N(x+(1-x)y)
  ≤ y/(1-y)*(x+(1-x)y)^N`.

For the exact original dyadic positive integers `2,m,2m`,
choose `x=1/2`, `y=(m-1)/m`,
`z=(2m-1)/(2m)`, obtaining

`0≤L_N(2)+L_N(m)-L_N(2m)
    ≤ (m-1)*((2m-1)/(2m))^N`.

The right side has a **constructive per-m geometric modulus**.
At m=1 it is identically 0. This directly targets the selected
`OriginalDyadicNatLogLaw` with its true source indexing, and is
strictly more faithful than changing L to an integral-defined log.
To discharge it in Agda, reuse the original negative-log coefficient
family and the existing
`AbelBishopComplexPowerDifferenceExact.originalComplexPowerDifferenceFactorisation`
for finite power differences; prove the finite polynomial integration
/order bound and transport the vanishing remainder to the selected
Bishop series limits. **That carrier-level setoid transport has not
yet been constructed.**

New exact regression:
`python3 scripts/check_bishop_original_natlog_dyadic_remainder_20261114.py`.
It passes **180** polynomial derivative identities, **200**
exact rational polynomial integral identities, **400** finite
dyadic remainder bounds, and produces rational-power epsilon cutoffs
without floating-point evaluation.

## 1c. New higher-alpha path: two-sided original Nat-log increments, no real FTC

For `m≥1`, the **actual** negative-log polynomial at the physical
positive integer m is
`L_N(m)=ell_N((m-1)/m)`. Let
`a=(m-1)/m`, `b=m/(m+1)`. The exact finite power difference
`b^j-a^j=(b-a)Σ_(r<j)b^(j-1-r)a^r` yields the two-sided bound

`(1-a^N)/(m+1) ≤ L_N(m+1)-L_N(m) ≤ (1-b^N)/m`. (D1)

For each *fixed* m, 0≤a,b<1. Transporting the limit `N→∞`
in the **original Bishop real order/setoid** therefore gives

`1/(m+1) ≤ L(m+1)-L(m) ≤ 1/m`. (D2)

This provides both monotonicity and a uniform-in-n finite increment
bound. Summing the lower bound for m≤n<2m gives
`L(2m)-L(m)≥1/2` and induction from L(1)=0 yields
`L(2^k)≥k/2`. For any positive integer
`2^k≤n<2^(k+1)`, monotonicity yields `L(n)≥k/2`.

For compact `Re(s)≥delta>0`, `|s|≤R`,
define `q=exp_B(-delta/2)` (so 0<q<1). The original
term is `a_s(n)=expC(-s L(n))`, indexed by n≥1.
Using the native complex exponential addition/norm and its
finite complex Taylor estimate,

`|a_s(n)|≤q^k` on dyadic block k,

`|a_s(n+1)-a_s(n)| ≤ R exp_B(R) q^k / n`
for 2^k≤n<2^(k+1), since D2 bounds `ΔL_n≤1/n`.

There are 2^k integers in that block and each 1/n≤2^-k,
so its *total* variation is at most `R exp_B(R) q^k`.
The original finite Abel identity, plus the unmatched last
raw term, therefore produces an all-cutoffs estimate

`|Σ_(n=N)^M (-1)^(n-1)a_s(n)|
  ≤ [1+R exp_B(R)/(1-q)] q^K`
for all 2^K≤N≤M. (D3)

This yields a **geometric constructive Cauchy modulus** on any
compact K, *conditional on* original-setoid transport of D1→D2,
native complex exp norm/difference, the original signed finite
Abel source, and true Bishop completeness. It does **NOT**
require first proving either `OriginalDyadicNatLogLaw` or the
continuous real-variable FTC for u↦u^-s; the latter remain
important separate targets for finite eta/zeta factorization and
holomorphy but are not prerequisites for this B convergence route.

Exact regression:
`scripts/check_bishop_natlog_two_sided_dyadic_20261114.py`
tests 3,150 exact two-sided finite increments, 64 rational shell
lower bounds, 15 exact dyadic lower comparisons, and 252 separate
complex numerical geometric-tail examples. **No Agda kernel
receipt** for D2/D3 yet.

**New first maximum-cut theorem:**
`originalCanonicalNatLogSuccessorIncrementSandwich`, then
`originalCanonicalNatLogDyadicLowerBound`, then
`originalRound11EtaDyadicGeometricVariation`, then
`originalRound11EtaCompactUniformConvergence`.

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
New source-written finite carrier: `DASHI/Analysis/BishopOriginalEtaRawAllCutoffPrefixExact.agda`
defines `originalAlternatingRawTerm` and proves the proposed
`originalRawEvenPrefixEqualsSelectedPairs` and
`originalRawOddPrefixEqualsSelectedPairsPlusOne`, without any
new analytic premise. Pinned Agda kernel acceptance is pending.

The formal Agda proof must transport such a modulus
through the original `SeriesOf` limit and the genuine
source complex absolute-value/order structure.

## 5. Executed diagnostics / reproduction

Run:
`python3 scripts/check_bishop_eta_abel_uniform_tail.py`
`python3 scripts/check_bishop_eta_all_cutoffs_maxcut_20261114.py`
`python3 scripts/check_bishop_original_natlog_dyadic_remainder_20261114.py`.

The second checker has independent cases: **21,845** exact rational
finite Abel identities, **1,972** exact real arbitrary-endpoint tails,
**576** exact complete-pair tails, **167,481** exact original raw odd/even-prefix parity cases, and **245** complex numerical
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
