# Six-frontier original-source maximum cut — implementation round 9
**Date:** 14 November 2026
**Owner:** dashi_agda #1499 canonical tracker; owner PR branches below.
**Trust:** every linked source-written Agda/Lean candidate is **NOT**
kernel-accepted in this round; local exact-rational regressions PASS.
No Clay problem or NP-completeness consequence is claimed solved.

## Execution contract

Combined fail-closed runner:
`scripts/check_clay_sixfrontier_physical_local_20261114.sh`

Set six explicit worktree env vars:
`DASHI_YM_WORKTREE` (#1503), `DASHI_KARP_WORKTREE` (#1502),
`DASHI_NS_WORKTREE` (#1501), `DASHI_BISHOP_WORKTREE` (#1478),
`DASHI_BSD_LEAN_WORKTREE` (dashi_lean4 #107),
`DASHI_RH_LEAN_WORKTREE` (dashi_lean4 #108).
`CLAY_SIX_SOURCE_ONLY=1` runs only exact finite regression tests.
The default runner demands pinned Agda/Nix and Lean/Lake and stops
on missing roots, kernel errors and unadmitted sources; a green run
would accept only the named *auxiliary source roots*, **not**
the original six terminal theorems.

The native source still owns its declared blame and attribution:
separate proofs for direct finite arithmetic, original-carrier
identification, analytic estimates, physical dynamics and kernel trust.
A theorem candidate, a synthetic sample and an unproved source
inequality never become one another through naming or a Boolean flag.

## Yang–Mills — PR #1503

**Already owned:** F19/P0 original Wilson finite cylinder,
normalized Haar and polymer/relative-density source, R445 exact
finite TV obstruction, covariance compiler, conditional mixture
inference; new exterior influence bound script
`scripts/check_ym_r445_weighted_exterior_influence.py`.

**Round 9:** `check_ym_r445_interacting_transfer_contraction_20261114.py`
uses the genuinely correlated two-state transfer matrix
`[[3/4,1/4],[1/4,3/4]]`. It computes
`D_k=(1/2)^k` at 41 exact rational distances and the summable
geometric tails at 30 cutoffs. The actual physical Yang–Mills
Wilson conditional law has not been identified with this
auxiliary model.

**Original max-cut leaves:**
`originalWilsonConditionalSameOutside`,
`originalWilsonExteriorInfluenceBound`,
`originalWilsonLocalizedDkBound` with cutoff-uniform
summable k, original uniform RG moment/covariance decay,
E1 interacting continuum, D1 continuum physical decay,
D2 same-E1 OS gap. Do not infer E1/D1 from a finite
transfer matrix or from local TV alone.

## Karp-21 — PR #1502

**Already owned:** literal 3-state finite gamma table,
`physicalAllLengthGammaRunSameOriginalPositive` for
positive gamma payloads, original raw first-enabled rule,
bit-native to raw first-enabled nonterminal correspondence,
source graph termination ≤edges+1 and signed ledger word bound.

**Round 9:** `Karp21NativeGammaPhysicalAcceptanceObservationExact.agda`
distinguishes halted-and-accepted work-head Blank from
halted-and-rejected Mark and instantiates exact positive gamma
payloads plus malformed empty/lone-zero input. Independently,
`check_karp21_literal_gamma_allwords_20261114.py`
replays all 32,767 words of 0..14 bits against the original
source gamma first-field parser and suffix.
`check_karp21_allwords_physical_local.sh` owns all six Agda
finite gamma roots.

**Original max-cut leaves:**
`physicalGammaAllInputsMatchesOriginalParser`
(no per-word exhaustive test substitutes for this universal theorem);
`nativeN21PhysicalFieldStreamSameOriginal`;
`originalBitTapeStepSimulatesN21Rule` on all phases,
including terminal observation quotient;
`nativeN21CompleteLiveHeapPolynomial` with input,
history, ledger, threshold, scratch/copies/heads;
`karpFractranBitMachineClockPolynomial`,
`karpFractranDecodePreservesAcceptance`,
`originalN21InNP` and original F3/F4 polynomial bit clock.
The token-only gamma fuel bound is not the whole verifier clock.

## BSD K1–K5 — dashi_lean4 PR #107

**Original curve:** `E : y²=x³−x`; field `ℚ_[2]`.
Existing `cmQ2SquareRoot3705` Hensel candidate consumes
the actual unit 3705≡1 mod8 for x=39.

**Round 9:** true Q₂ Hensel **source candidates**:
`cmQ2SquareRootOfOneModEight` (integer units 1 mod8),
`cmActualCurveQ2PointAt39`, and
`MillenniumBSDCMQ2EightLocalPointWitnessesExact.lean` for

| x | c with x³−x = c²u | u ≡ 1 (mod 8) |
|---|---|---|
| 28 | 2 | 5481 |
| 31 | 8 | 465 |
| 33 | 8 | 561 |
| 39 | 4 | 3705 |
| 41 | 4 | 4305 |
| 112 | 4 | 87801 |
| 1/4 | 1/8 | −15 |
| 1/16 | 1/64 | −255 |

The exact Fraction implementation of the eight actual
`(squareclass(x−1),squareclass(x),squareclass(x+1))`
triples uses `(v₂ mod 2,odd unit mod 8)` and proves all
eight **pairwise distinct**. It checks 2,732 locally compatible
integer x between −16,384 and 16,384, producing only six
triples on the integer slice; the two rational x above add
the missing two. Finite exact arithmetic is PASS. The
generalized Hensel Q₂ point and eight-point Lean sources
have no pinned kernel receipt.

**Original open leaves:** kernel acceptance of Hensel source,
reified `E(Q₂)` and true Kummer map to
`H¹(G_{Q₂},E[2])`; rigorous eight-class *exhaustion*,
real Kummer source, continuous restricted localization,
Selmer² and `Sha(E)[2]` LES, faithful MW finite generation
and rank, K4 eta/Mellin/same-object positivity, odd-primary
Sha/full BSD K5. Eight distinct image witnesses alone
do **not** establish full H¹ or the Kummer image upper bound.

## Navier–Stokes — PR #1501

**Already owned:** R71 exact physical finite cutoff RHS,
transverse/reality source, degree-two polynomial representation,
R74 finite rational coordinate chart, R853 same-packet
selected normal form
`r=6(12*C-P+(2ν−δ)*D)`, R829 initial arithmetic
`r₀=−28273644/125`, and R854/R855 exact conditional
negative affine-integral scalar arithmetic.

**Round 9:** rational sparse-polynomial
`check_ns_r853_quadratic_lie_derivative_20261114.py`
derives `L_F r=Σ ∂_i r F_i` exactly for a supplied
`F=quadratic` and selected `C,P,D`, with a
coefficient sup-box bound checked against the R854/R855
constant budget. Two exact arithmetic controls PASS;
they are **synthetic** until the actual R71 chart and
R853 same-observable source identities are produced.
It cannot replace real C¹ Picard or a negative true rate.

**Original open leaves:**
`originalR71R74PhysicalRHSIsRealQuadraticField`,
`originalR71RealGalerkinLocalSolution` on original R830
fixed horizon, `originalR853SignedRateAlongGalerkinSolution`,
`originalR828R854RateLipschitzAlongSolution`
(or R855 relaxed proven source bound), and
`nsR854OriginalRealRateIntegralStrictlyNegative`.
The original R823 reserve counterexample is also open.

## Bishop/eta — PR #1478

**Already owned:** selected original negative-log power
series `sourceCanonicalNatLogCandidate`; P1 complex
factorial-exp native source-weld; original finite Abel source;
original paired eta prefix and odd/even raw cutoff
decomposition; exact finite negative-log dyadic and
discrete incremental regression; 936 trig Cauchy coefficient
checks and 1,300 factorial tail cases.

**Round 9:** source-written
`BishopOriginalEtaRawSeriesOfSameSourceExact.agda`
identifies both coordinates of the original raw partial sum
with literal Murray `Sequence.SeriesOf`, instantiated with
actual selected `OriginalRound11DirichletEta.sourceTerms`.
It is now target 16 in
`scripts/check_bishop_eta_native_exp_cross_pr_local.sh`,
not a kernel receipt.

**Highest-alpha alternative:** prove
`originalCanonicalNatLogSuccessorIncrementSandwich` on
original Bishop setoid via the exact finite -log polynomial:
`1/(m+1)≤L(m+1)−L(m)≤1/m`.
This gives `L(2^k)≥k/2` and an original dyadic
geometric Abel modulus for every raw odd/even cutoff,
without first requiring continuous real FTC or exact
dyadic Nat-log equality *for eta convergence*.
Remaining: original expC addition/modulus/difference,
`originalRound11EtaDyadicGeometricVariation`,
`originalRound11EtaCompactUniformConvergence`,
trig addition, independent canonical log identity,
parameter derivative/real-variable FTC and analytic
holomorphic-limit transport. The original analytic
convergence and any RH consequence are OPEN.

## RH A2/G3 / Route B — dashi_lean4 PR #108, Agda #1499

**Already owned:** A2 exact four-coordinate scalar
`LocalPositiveDebt + literalFarExactAt <
compensationTargetThreshold + LocalMuGain`,
G1 constructed witness with an explicit coarse
uniform `fourthLipschitz < 4e9` and quantitative
strip compiler; A2 leading positive eighth-cap requires
a MUCH sharper same-witness threshold ~737.365
or a signed eighth treatment; original
`signedFifthCorrelationGapAt =
signedFifthPhysicalCapInteriorAt +
outerVerticalAbsoluteBudget −3eps`.

**Round 9:** `RiemannA2ActualSelectedIntervalDecisionExact.lean`
on the actual W, rho, EV, n has exact conditional
interval PASS, pointwise interval NO-GO and
eventual cofinal NO-GO compilers without absolute-value
replacement of FarExact. The rational interval regression
checks 4 exact synthetic cases and explicitly tags
source inputs as UNVERIFIED. No selected-zero curvature
nor completed compensation bound has been produced.

**Original open leaves:** selected
`fourthLipschitz` sharp enough on the ACTUAL W;
`HorizontalFarCurvatureBound CH`; original zero-shell
bound and completed N-mu compensation;
`originalSelectedA2StrictSignedCompensation`
OR a genuine same-zero-carrier cofinal inverse no-go.
Route B separately requires true eventual signed physical
cap gap, upper-boundary decay, outer-terminal convergence.
A substitute Möbius heat spectrum, negative bare-pole
sample or all-frequency Fourier sign-change cannot settle
these exact zeta-zero propositions.

## Zero-promotion ledger

| Lane | New source candidate | Finite diagnostics | Pinned kernel | Original endpoint |
|---|---|---|---|---|
| YM | finite interacting inference benchmark | PASS | not applicable | OPEN |
| Karp | gamma acceptance observation | PASS | PENDING | F2/F3/F4/NP OPEN |
| BSD | generic Q₂ Hensel + eight real curve points | PASS | PENDING | H¹/Kummer/Sha² OPEN |
| NS | polynomial R853 Lie compiler | PASS | not applicable | real flow/rate OPEN |
| Bishop | literal raw SeriesOf carrier | PASS | PENDING | eta uniform OPEN |
| RH | actual A2 signed interval decisions | PASS | PENDING | selected-zero sign OPEN |

**Next proof acceptance priority:**
BSD generic Q₂ Hensel and eight point source; Karp
F1 universal parser observation; Bishop raw SeriesOf
and finite Abel on pinned Agda; RH original
interval compiler; then invest in BSD Q₂
H¹ image upper bound and Bishop original
Nat-log incremental source transport.
All source-owned comments must retain known methods/authorities
(Bishop/Murray; Karp/Elias/Conway; Hensel/Kummer/Selmer;
Wilson/Bałaban; Navier–Stokes/Galerkin; Weil/Riemann)
and declare which gates were paid versus merely reduced.
