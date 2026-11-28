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


## 26 Nov continuation — original post-sixth compiler recovered, sharpened debt and strict BIDI

Audited actual Agda master 41b222417983d85f7e42cce4971351b51b6527cb,
#1533 entry f05b528f89f5f1d5ea0a994d33517853e3cced4e, portfolio #1551
aa357f9f72866271b6a0ef9d08cc1e0958f12667; portfolio copy predates the
local phase continuation and is not a separate governing plan.
Lean main 9ba8f00cf2941850268bc927c0e1a6112996f4d8 and #116 entry
fdc7d1eafb6798c4e0ead9d1bba6e797bc3fb5d6 have byte-identical
EighthRemainder d636892f60c60f51968440f6016a00d46f9e88ce,
PostSixthAbsorb 1219c304badf9f25326493bf894f33554cc4b2b4,
FourierTerminal fece9d70499d6e324a849ba4bf7c62870ed3d82b.
Already source-owned: mixedDegreeSix_referenceIntegral,
completeJointBeyondSixthRemainder_eq_integral,
completeJointBeyondSixthRemainder_abs_le_eighth, M8abs<=L²*K(W),
literalLocalEighthDebtAt_le_G1_expandedWindowN, original negative M6
witness and terminal cap, literalLocalExactAt_stable/eq_canonical,
canonicalLocalExactTerm_tsum_eq, canonicalFarExactTerm_summable,
globalSignedLiteralPairSource_eq_canonicalLocal_add_far,
literalFarExactAt_eq_base_add_horizontal, and
exists_canonicalLiteralFarPairSource_linearCutoff_bound_of_horizontalCurvature.
Thus local finite support and the canonical far representation are NOT
missing. Original FarPaid/Abel/outer paired compilers already exist.

### Two rigorous local envelope improvements

Let x=alpha²,y=q², L=pi+1 and E_old=x^4/30000+y^4/17000+
(x³y+x²y²+xy³)/300. On the scalar unit square use the original
cos/cosh degree-six remainder bounds 1/35840. The truncated cosh
polynomial is <=1+1/2+1/24+1/720<8/5. Exact mixed polynomial
tail has coefficients bounded by 1/1440 on each outer mixed term
and 1/576+2/17280+1/518400<1/500 on the middle term,
since x,y<=1. Hence the tightened scalar envelope
x^4/35840+y^4/22400+(x³y+x²y²+xy³)/500
is coefficientwise <=(375/448)*E_old. This factor is the maximum
coefficient ratio for THIS scalar majorant, not the optimal analytic
constant. Native source reuses the original scalar lemmas and original
finite-source G1 compiler, without a new complex-series dependency.

Sharper mathematical route: P_(2m)=R^m T_m((x-y)/R), R=x+y>0,
origin separately zero for m>0. Therefore |P8|<=R^4. Using
C10=66/(65*10!), the original scalar cosh series gives
|beyond6|<=R^4/8!+C10 R^5<= (997/39312000) R^4
on the scalar unit square R<=2. This radial polynomial is
coefficientwise <=(4/5)*E_old (axis limiting ratio about .76084;
mixed ratios .03043/.04565/.03043). Alternatively retain the
actual signed M8 and tenth remainder. M10abs<=L² M8abs<=L^4 K(W)
is same-object; no independent moment norm. Native tenth reference
integral, support norm and conditional scalar-to-profile compiler
source-written. The precise remaining native analytic lemma is
QuarticSignedPoleTenthTaylorBound; its mathematical proof is above,
not a kernel receipt. No all-order raw polynomial far summation.

### Actual local debt and reverse terminal

For n=original canonical exhaustion index let J4,J6,J8 be literal
signed guarded sums. D8_literal is original eighth absolute debt;
D8_G1 is its existing expanded-window upper bound.
B_k=J4+J6+k D8_literal. For the native scalar route k=375/448,
B_k >= exact local L0. Under original selected-witness hypotheses,
B_k <= B_old-(1-k)D8_G1 by existing corrected fourth scalar,
signed sixth cap, and eighth G1 estimate. For the signed route
B_signed=J4+J6+J8+C10 M10abs/r^12 * literalLocalPhysicalPhaseAt
(a²+d²)^5; B_signed>=L0 using the mathematical tenth bound.
min(B_k,B_signed) is sufficient; native signed candidate conditional
on the exact scalar lemma. Source-written three existing Lean #116
modules: EighthRemainder (commits b3bec25b,3572b11d),
PostSixthAbsorb (29233e4c,2e0d1bf4), FourierTerminal (1a2ca00e).
No new witness or altered far normalization.

Let F=canonicalLiteralFarPairSource, I=exact original mu integral,
D=completedSignedResidual, d=target defect, H=L0+F, D=(H-I)/2.
For any valid local budget B>=L0 the revised cut is exactly
F < 4d+I-B iff D+(B-L0)/2<2d.
Far allowance increases by B_old-B, at least (73/448)D8_G1 for
the native tight route; mathematical radial 4/5 gives at least D8_G1/5
when the same aggregate compiler is instantiated. However even B=L0
cannot manufacture a negative global margin: hypothetical off-line
pair forces D>=2d. Independent strict completed-source inequality
still required, not a consequence of reduction in local slack.

### Local execution and remaining min-cut

New scripts/check_rh_scaled_local_budget.py, commit 63de2521, Git
blob 5e8e460a86af0d509c7566dd30aa89d25b96da43 matches executed local
bytes. Python compile and timeout90 exact SymPy/Fraction PASS:
2 phase/radial identities, 15 coefficient comparisons, 1089 exact
rational series interval stress points, 2 terminal identities and
9 negative controls. The interval grid is synthetic, not actual zeros;
universal inequalities proved separately by coefficient/series algebra.
No CI, Lean, Agda executable present or kernel acceptance.

Exact remaining local native gate: prove QuarticSignedPoleTenthTaylorBound
and instantiate 4/5 native scalar compiler; elaborate all new terms.
Far representation/summability already owned. Quantitative E2:
instantiate actual selected-W uniform HorizontalFarCurvatureBound and
signedOrdinateCurvature envelope (or stronger original Schwartz route);
retain normalized complete far compensation and mu/prime/pole accounting.
The absolute shell bound alone is not the strict scale/signed estimate.
E3: independent F-I<4d-B for every original hypothetical target, or
equivalently completed residual plus slack; not implied by exact
explicit-formula rewriting. For prime-port route E0 inhabited actual
extended selected test, E1 kernel source receipt and E2/E3 signed
enlarged tails and log/near-double resonance remain separate.
All-character G1-G3: same-source Dirichlet character/conductor,
multiplicity/reflection and actual L/zero predicate, with genuine
per-character profile/explicit formula; zeta-only local proof does
not construct these. Primary direct admission already on merged Lean
#113: main RHAdmission.lean blob 43a3f106e09a013fada4d1868f3bf9b0ba7dbf87
imports original Main and exact five theorem types. #121 parser fix
still open at 5d5c479dc52b; pinned v4.33.1 local kernel and compatible
native cross-prover handoff remain distinct. External verification not
newly established here. No GRH/RH promotion. Classical Taylor,
Chebyshev and triangle inequalities are background; DASHI contribution
is original source-specific coefficient budget and terminal weld,
Paper 9 donor provenance retained.
