# 2026-11-14 — Bishop/eta + RH A2/G3 exact maximum cut

Owners: Agda #1478 and Agda #1499; Lean #50 and #108.
**Classification:** exact-rational diagnostics + a source-written Lean
negative-control candidate; NO newly admitted Agda 2.9 / Lean 4.28
kernel theorem. These files are not a proof of RH or A2 method failure.

## Bishop A1 — two original trigonometric addition laws

The actual carrier is the configured Murray/Bishop
`BishopPowerSeriesElementaryBridgeExact.BishopElementaryPowerSeriesData`
and the original Round11 `BishopSetoidComplexTranscendentals`.
`BishopOriginalNativeComplexExpAdditionFromTrigExact` already
compiles `OriginalCosineAddition T` and
`OriginalSineAddition T` into literal expC addition.

The attachment's coefficient manipulations are algebraically sound:
`cosCos[n] - sinSin[n] = (-1)^n (x+y)^(2n)/(2n)!`,
`sinCos[n] + cosSin[n] = (-1)^n (x+y)^(2n+1)/(2n+1)!`.
The necessary majorant for the EVEN factorial absolute tail is
`A^(2N)/(2N)! / (1-A²/((2N+1)(2N+2)))` whenever its denominator
is positive. This must be transported to the original
`Sequence.SeriesOf` and `Real._≃_` limits; a finite binomial
coefficient identity does not provide that transport definitionally.

New test: `scripts/check_bishop_trig_cauchy_coefficients_20261114.py`.
Exact `Fraction` checks: 936 coefficient identities and 1300
absolute even factorial tail envelopes. No native Agda proof admitted.

Remaining exact constructor:
`originalBishopTrigCauchyConfiguredCoefficientIdentification` →
`originalBishopTrigRectangleTriangleCommonLimit` →
`originalBishopCosineAddition` and
`originalBishopSineAddition` on the source `T`, then use
`originalBishopAnalyticExpAddFromNativeRealExpAndTrig`.

## Bishop A2 — canonical Nat-log

`BishopRiemannDirichletExponentialTermExact.sourceCanonicalNatLogCandidate`
uses `sourceNegativeLogValue (natLogArgument n)`, where
`natLogArgument n=(n+1)/(n+2)`; index `n` represents positive
integer `n+1`. It is NOT defined as a reciprocal integral.

The finite original negative-log polynomial
`ell_N(z)=Σ_(j=1)^N z^j/j` has a rational identity, for
`x=1/2, y=(m-1)/m, z=(2m-1)/(2m)`:

`0 ≤ ell_N(x)+ell_N(y)-ell_N(z) ≤ (m-1) z^N`.

The existing exact script
`check_bishop_original_natlog_dyadic_remainder_20261114.py`
verifies the polynomial derivative, finite integration and
geometric bound (180+200+400 cases). Its analytic limit belongs in
`OriginalDyadicNatLogLaw sourceCanonicalNatLogCandidate` at
indices `(2k+1), 1, k`: `L(2(k+1))=L(2)+L(k+1)`.
Do not replace this with a new integral-defined `L`.
Remaining: finite coefficient equality to the original
`NativeLog.sourceNegativeLogTerm`, `Real` order of the geometric
remainder, convergence-to-zero, limit sum/addition uniqueness.

## Bishop B1 — the TWO different FTCs

(1) Complex parameter derivative for fixed integer `n`:
`∂_s expC(-sL(n))=-L(n)expC(-sL(n))`.

(2) Real variable derivative for fixed complex `s`:
`d/du u^(-s)=-s*u^(-s-1)`.
The second derivative and the real interval FTC
`n^(-s)-(n+1)^(-s)=s ∫_n^(n+1)u^(-s-1)du`
are what drive the alternating Abel tail. The attachment's
straight-line complex-parameter FTC is not a proof of the real-axis
lemma. Instantiate both in the original `BishopComplex` plus
canonical negative-log source, not a synthetic complex exponential.

## Bishop B2 — all raw cutoffs, original complex norm

Existing actual source
`BishopOriginalEtaRawAllCutoffPrefixExact.agda` supplies the
source-written raw even and odd prefix decomposition;
`BishopOriginalEtaFiniteAbelSourceExact.agda` supplies the finite
Abel telescope. For all `1≤N≤M`, `Re(s)≥δ>0`, `|s|≤R`,
the classical analytic result is

`|Σ_(n=N)^M (-1)^(n-1)n^(-s)| ≤ (1+R/δ)N^(-δ)`.

The irrational/rational Cauchy modulus is standard; the prior
rational `δ=p/q` exact-power method is particularly convenient:
choose `N^p*eps^q ≥ (1+R/δ)^q`.
Remaining type-specific proof: original `NatLog` and exp
identification, real FTC and original complex absolute norm,
actual Bishop uniform Cauchy on each compact K and
`SeriesOf` completeness. Neither existing exact-regression
nor finite prefix alignment closes that analytic source theorem.
The special points where `1-2^(1-s)=0` also need independent
divisor/removable-singularity handling for a zeta quotient claim.

## RH A2 — source-selected witness is NOT the attachment's bump

The actual Lean #50 source is
`QuarticFourSignedPolePair t`, with source-owned `W.targetStrength`.
**Previously paid G1 progress:** the donor
`RiemannProjectiveQuarticFourWindowSignedPoleQuantitativeBand.lean`
defines `W.fourthLipschitz =
compactCoshFourthLipschitzConstant (quarticFourSignedPoleCombinedProfile
W.R W.muHalf W.muTwo t)`, where the compact-cosh constant is the
**actual fifth absolute moment**
`∫ |P(u)| cosh(|u|) |u|^5 du`.
It already proves
`W.fourthLipschitz_le_explicitK0` for t≥200,
`quarticSignedPoleExplicitK0_lt_four_billion`, and
`quarticSignedPoleThresholdBelowPlattTrudgian_proved`, compiling
a quantitative G1 strip band above the PT cutoff. **Do not erase
these original G1 results or treat K as entirely unconstructed.**
They are source-written existing theorems and still require the
relevant exact-head kernel receipts before formal acceptance.

The next A2 task is a MUCH SHARPER same-witness K estimate, not merely
a finite coarse K. The already proved
leading local comparison is exactly

`W.postSixthTerminalLeadingAllowance < W.targetStrength
 ↔ W.fourthLipschitz
      < W.postSixthTerminalFourthLipschitzThreshold`.

At the strength floor the sufficient ceiling is approximately
737.365. The separately asserted bound `28416/25=1136.64`
is for a different bump, is a `sup |W''''|` claim rather than
the required `Lip(W'''')`, and is not a source certificate
for the current selected W. This number is also *larger*
than the floor sufficient ceiling; even treating it as the
same quantity would not discharge the sufficient inequality.
The previously paid coarse G1 bound `K0<4e9` also does NOT
satisfy the A2 sufficient ceiling ~737.365. Sharpen the
*constructed selected* profile estimate (possibly its fifth
absolute moment) or restore signed eighth-order cancellation.

The exact source `FarExact` is the signed
`FarBaseExact + FarHorizontalExact` split with an explicit
zero count and the still-unproduced
`HorizontalFarCurvatureBound CH`. It is not by definition
`Σ Re((s-rho)^(-2))*W(t)` or a single universal
positive `log(t/2π)` debt.

The attachment's local pole pointwise positivity is false:
for horizontal displacement a=1/4, vertical separation b=1/2,
both within its putative local window,
`(a²-b²)/(a²+b²)²=-48/25`, not ≥1.
For `|b|≥1,|a|≤1/2`, that same bare kernel is
strictly negative, but it has not been shown to equal the original
physical FarExact with the sign and compensating subtractions.
Neither `CompensationTarget≤0` nor a height-independent actual
`LocalMuGain` is supplied for the selected witness.
The numerical 14.1347 illustration is not a source-certified
bound on all four terms of the decision inequality.

### Correct horizontal real-part Taylor parity

If W is **real and even**, for
`F(z)=∫ W(x) exp(zx)dx`,

`Re F(iγ+a)=∫ W(x) cosh(ax) cos(γx)dx`.

Odd powers of the **real part** do vanish by parity even
for a single translated argument; the earlier broad suggestion
that a symmetric a,-a pairing was necessary was too strong.
The correct estimate under compact support is

`Re(F(iγ+a)-F(iγ))
  = (a²/2)Re F''(iγ) + R4`,

`|R4|≤|a|⁴/24 ∫ |x|⁴|W(x)| exp(|a||x|) dx`.

This is an analytic same-symmetry bridge, NOT a proof that the
original selected quartic signed-pole kernel equals this F.

### Fourier curvature no-go has narrower quantifiers

For real, even, nonnegative smooth compact W, nonzero away
from zero, `G(γ)=Re F''(iγ)` is rapidly decreasing,
`G(0)>0` and `∫G=0`; thus G is negative somewhere.
This defeats an **all-real-frequency** positive-curvature
shortcut, not the source's *selected actual zeta zeros* or the
complete inequality including FarExact, LocalMuGain, and
CompensationTarget. The missing theorem is still
`originalSelectedA2StrictSignedCompensation` OR an actual
`originalSelectedA2CompensationNoGo` on the selected
cofinal zero carrier. No method no-go is proved here.

## RH Route B — actual source vs signed spectral surrogate

Lean #50's actual identity (read from
`RiemannSelectedSignedFifthCorrelationGapAudit.lean`) is

`W.signedFifthCorrelationGapAt rho EV eps n
 = W.signedFifthPhysicalCapInteriorAt n
    + W.outerVerticalAbsoluteBudget rho EV -3*eps`

for source-owned sufficiently large cutoffs. The three real
remaining producers in
`signedFifthAnalyticInput_of_three_producers` are
eventual upper-boundary decay, direct same-cap signed gap
nonnegativity, and outer-terminal limit convergence.

The attachment substitutes a *different* heat spectral model
`Σ μ(k)(γ_k^5-E_t[γ²]γ_k^3)e^(-2γ_k²t)`.
Even that model's positive-leading-pair computation has the
wrong sign if its written μ is the Möbius function:
`μ(1)=+1, μ(2)=-1`.
For two positive heat weights `a,b` at `0≤x<y`,
with `mean=(a*x²+b*y²)/(a+b)`, the EXACT identity is

`a(x⁵-mean*x³)-b(y⁵-mean*y³)
  = -(a*b/(a+b))*(y²-x²)*(x³+y³)<0`.

If both numerator signs are positive, the corresponding
two-mode expression is positive:
`(a*b/(a+b))*(y²-x²)*(y³-x³)>0`.
Thus the spectral sign is sensitive to the selected weights and
cannot be transported silently to the actual physical cap.
No conclusion about the full infinite signed sum follows
without uniform tail control; no original Route-B theorem is
discharged by a two-mode calculation.

The attachment also estimates spectral tails by replacing the
actual zero ordinates γ_k with the index k; this needs a proved
zero-enumeration/growth comparison and may not be used as written.

## Regressions and local proof candidates

- `scripts/check_rh_a2_g3_attachment_maxcut_20261114.py`
  (exact rational local-pole and positive-weight/signed two-mode checks);
- Lean #108:
  `Synthesis/RiemannA2G3PoleAndSignedHeatNegativeControls.lean`
  (source-written theorem candidates, kernel not run);
- `scripts/check_bishop_trig_cauchy_coefficients_20261114.py`;
- previously written original-indexing and Nat-log exact checkers
  on #1478.

## Highest-alpha next source acceptance

A1: `originalBishopTrigRectangleTriangleCommonLimit` on the
configured series; produce the two real sine/cosine laws.

A2: `originalCanonicalNatLogDyadicAddition` by finishing the
finite -log geometric remainder → original Bishop limit transport.

B1: `originalRound11DirichletTermFundamentalTheorem`
on positive-real argument, and independent holomorphic
parameter derivative.

B2: `originalRound11EtaAbelPairTailBound`,
`originalRound11EtaCompactUniformCauchy`, and
`originalRound11EtaCompactUniformConvergence` on
all original raw cutoffs.

RH B: `selectedOriginalWitnessFourthLipschitzBound`
**on actual selected W**, `selectedOriginalHorizontalFarCurvatureBound`,
`originalA2FarExactZeroShellBound`, original completed
compensation lower bound on the canonical cofinal zeros.

RH C: decide actual `originalSelectedA2StrictSignedCompensation`
versus a logically valid same-source no-go; Route B separately
requires the THREE original `SignedFifthAnalyticInput`
producers, not a spectral substitute.

**NO A/B endpoint and NO RH A2/G3 C gate promoted this round;
the diagnostics prove discrete finite identities and falsify
incorrect auxiliary claims.**
