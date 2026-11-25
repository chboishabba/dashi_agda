# GRH P0 — literal local sixth/eighth phase and tenth-order source remainder
26 November 2026. Continuation of GRHSignedPhaseTransverseConsumerRecovery20261126.
Paper 9 #1546 supplies two-slice residual chart; classical Taylor/series algebra
is background; DASHI work is the original-source transport and estimate.

## Original owner audit

Agda #1533 entry 119c91399ddc8b43f8b82c606f37becc9f6630fc.
Lean #116 entry 4a53411c799d2850b623bf714405b36afe4feb7a and Lean main
both have identical LocalRemainderBounds.lean blob
4c900e06125cdd76993ce86349cfc2680696b64e. That source owns
signedProfileMomentSix, completeJointSixthHarmonic, literalCompleteJointSixthHarmonic,
literalLocalSignedSixthHarmonicAt, literalLocalBeyondSixthRemainderAt,
complex_cos_sub_sixth_abs_le_eighth, signedProfileAbsMomentSix_le_fourthLipschitz.
Existing baseQuarticJetRemainder_eq_sixthCosineRemainder explicitly consumes
quarticFourSignedPoleCombinedProfile_zeroth_zero, _second_zero, _fourth
to get M0=M2=0 and M4=-4*targetStrength. JointHorizontalJet
(blob 4d0437ffb058c7e8b6961521a611608b1494ba3f) supplies
signedNormalizedPairKernel_eq_combinedIntegral and complete quartic jet.
ConeDecomposition owns local guard |q|<=eta and SameOrd exclusion.
FourierTerminal blob fece9d70499d6e324a849ba4bf7c62870ed3d82b
already owns literalLocalExactAt_eq_canonical use and the strict
completed-plus-local-slack endpoint. Do not rebuild these.

## Actual local signed coefficient weld

On the original zeta W, set r=t/16>0, a=heightOf rho,
d=Im rho-t, alpha=a/r, q=d/r, m=original zero multiplicity.
M_k=int P_W(u)u^k du, P_W the original signed combined profile.
The original pointwise sixth is m*M6*P6(a,d)/(720*r^8).
The new eighth is m*M8*P8(a,d)/(40320*r^10).
Both phases are homogeneous, even in a and d individually, so the
actual horizontal reflection a->-a does NOT annihilate either
mixed mode. Exchange of squared coordinates is not this symmetry.

Define L(F) as the original finite sum over centeredZeroFinset t n
with the unchanged |q|<=eta and off-SameOrd guards, of m*F(a,d).
The exact local signed harmonic contributions are
M6/(720*r^8) [L(a^6-d^6)-15 L(a²d²(a²-d²))]
and
M8/(40320*r^10) [L((a^4-d^4)^2)+16 L(a^4d^4)-28 L(a²d²(a²-d²)^2)].
Actual nonnegative multiplicities mean the eighth mixed moment is >=0,
and strictly positive if one included off-axis/off-diagonal point has
positive multiplicity. Sixth is signed. Equal horizontal partners
reinforce, not cancel, both mixed values; no sign assertion for M8.
These sums retain the original finite source, not an extrapolation to
global raw polynomial sums.

Lean #116 updated existing LocalRemainderBounds source (no new framework):
fdc7d1eafb6798c4e0ead9d1bba6e797bc3fb5d6, blob
5e2b8b0448a0b2ed30aff0133503b2eba7ae9ad9.
Adds actual eighth moment/harmonic, physical scaling identities,
horizontal reflection, literal local eighth and beyond-eighth definitions,
exact split of original local remainder into sixth+eighth+beyond,
and literalLocalPhysicalPhaseAt with finite mixed phase identities.
These are source-written UNCOMPILED. No kernel acceptance claimed.

## Local tenth-order analytic bound (mathematical)

For original kernel int P_W cosh(alpha*u)cos(q*u),
write z=(alpha+i*q)u. Since support |u|<=L=pi+1 and
canonical local |alpha|,|q|<=1/L, |z|²<=2.
For all k>=5, the ratio of successive absolute even Taylor terms is
|z|²/((2k+1)(2k+2))<=1/66.
Hence |Re cosh z - sum_(j=0..4) Re z^(2j)/(2j)!|
<= (66/(65*10!))*|z|^10.
All terms are integrable on compact support. Integrate the absolute
bound using the exact original M0/M2/M4 identities and the sixth/eighth
moments. Literal beyond-eighth remainder obeys
|R10(rho)| <= (66/(65*10!))*m*M10abs*(a²+d²)^5/r^12.
M10abs <= L^4 M6abs <= L^4 W.fourthLipschitz by support and existing G1 lemma.
Thus no new independently controlled moment required. Sum with the same
local guard; triangle inequality gives the finite local remainder bound
factor*M10abs/r^12 * L((a²+d²)^5).
For fixed t,eta, the local strip band contains finitely many zeros
(counting multiplicity). Once integer n>r*eta the original half-open
centeredZeroFinset exhausts it; all these local moments stabilize.
No unjustified infinite Taylor sum: far source remains exact; raw
P6/P8 on an unbounded zero set are not a summable substitute.
Physical local radius r*eta grows with t, so r^-12 alone is not a
uniform asymptotic estimate of the complete local sum.
This mathematical remainder bound and common-support finite stabilization
have NOT been formalized in the Lean kernel here.

## Executed regression and actual remaining gates

scripts/check_grh_literal_phase_weld.py matches locally executed blob
151117ba9ac2c70c6145c9d8ca039393e14d0b84. Python compile PASS and
timeout90 local SymPy/Fraction execution PASS: 2 phase charts, 4 physical
scale/reflection identities, 5 Taylor coefficients, 95 tail ratio
controls, 5 exact truncated tail controls, 2 guarded mixed-moment sums
and horizontal reflection non-cancellation. The rows are synthetic
tagged fixtures, not actual zeros. The mathematical geometric series
proof is separate from the finite checks. No CI.

G1 original zeta sixth already owned; eighth coefficient and guarded
local sum now source-written. G2 actual local mixed moments retained,
no exchange-cancellation assumption. G3 fixed-window zeta local
stabilization mathematical; native proof of bound/stabilization still
open. All-character G1-G3 still need actual per-character kernel,
zero multiplicity and local cutoff attachment; no automorphic promotion.
E2 global exact signed far and quantitative bounds, E3 independent strict
completed source inequality still open. Existing admission route remains
primary; Lean #113 merged, parser fix #121 open at 5d5c479dc52b,
pinned local kernel and native Agda all-character correspondence not run.
External theorem status not newly verified here.
