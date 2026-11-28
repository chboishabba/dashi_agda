# GRH — signed transverse phase recovery and consumer-specific descent

26 November 2026. Paper 9 donor PR #1546 at 2b8bff03,
Docs/proofs/Paper9CofinalCrossGRHPhasePNPSelector20261126.md
(blob 26885bcb7f590a61fe8f1eebdd378ef554a1a6d6).
Original GRH #1533 entry a5e9bf045428438d11d64b1746af3c604e531089.
Classical symmetric polynomial algebra and interpolation credited as background;
Paper 9 supplies the signed two-slice kernel. DASHI contribution here is
the explicit phase-coordinate recovery/consumer weld. No GRH proof promotion.

## Existing owners / exact scope

Reopened #1533 controlling roadmap (entry blob da2606a96874a819a3d76bbcb650b071436c5a1c),
GRHNative27ConsumerDescentExact (e9bd9653), RHFourWindowAngularC3C4SufficientConsumerExact
(74842d94), QueryFactorisationSufficiency (98c59223),
ObserverFactorizedRefinementExact (4ed03017), ConsumerDescentMinimalObserverExact,
and original completed-source RHGRHBilateralCompletedLogPolePairQuarticAdverseMass.
The original per-character EveryCharacter/Mellin compiler remains the authority.
Do not identify horizontal/ordinate exchange with an actual analytic source symmetry.
Do not duplicate the existing observer framework.

## Exact BIDI (squared variables x=a^2, y=delta^2)

Every homogeneous antisymmetric cubic is
F6=A(x^3-y^3)+Cxy(x-y). Its axis is A, diagonal zero, transverse
T=F6(1,2)=-7A-2C; inverse C=-(T+7A)/2.
Every homogeneous symmetric quartic is
F8=A(x^2-y^2)^2+B x^2 y^2+Cxy(x-y)^2. Axis A, diagonal B,
T=F8(1,2)=9A+4B+2C; inverse C=(T-9A-4B)/2.
The original Re(a+i delta)^6 and ^8 have chart coefficients (1,-15)
and (1,16,-28), respectively. In each old fibre C is arbitrary, hence
one transverse independent linear scalar is necessary and sufficient
for full recovery. At (1,2) the invisible basis values are -2,+2.

Native source GRHSignedPhaseTransverseRecoveryExact.agda:
observe6/8, recover6/8, both round trips, literal axis/diagonal/transverse
evaluation lemmas, sixthFactors/eighthFactors using the existing
Consumer.FactorsThrough/Factorized.factorizedRefinement, and explicit
old-observer lost-mixed witnesses. old6LinearSuffices/Requires and
old8LinearSuffices/Requires are the two directions of the linear
consumer condition below. Source-written; Agda kernel NOT RUN.

## All-order extension

For squared degree m>=1 put k=floor(m/2), s=x+y, p=xy and u=p/s^2
when s!=0. Symmetric homogeneous polynomials of degree m even are
s^m H(u); antisymmetric ones of m odd are (x-y)s^(m-1) H(u).
Indeed antisymmetry implies divisibility by x-y, leaving a symmetric
homogeneous polynomial; the fundamental theorem of symmetric polynomials
then gives the monomial basis s^(m-(m mod 2)-2j)p^j, j=0..k.
The homogeneous polynomial interpretation extends to s=0 without
division. The physical nonnegative squared-coordinate origin has value
zero for m>=1. For a ray (1,t), divide its value by
(1-t)^(m mod 2)(1+t)^(m-(m mod 2)).
The resulting observation is H(t/(1+t)^2). Choose k+1 distinct
projective coordinates; exclude t=1 for odd m, and do not count
t and 1/t independently. E.g. even ratios 0,1,...,k and odd ratios
0,2,...,k+1. The scaled Vandermonde is invertible, so the k+1
observations give full recovery, and fewer linear scalar observations
cannot be injective. The two-slice rank is 2 for even m>=2 and 1
for odd m; additional dimensions are k-1 and k respectively.
The general proof is mathematical; general native Agda interpolation
proof not supplied here. The exact executable recover_projective
implements it for rational observations.

## Actual selected consumer boundary

For a declared finite weighted linear evaluation L(F)=sum_i w_i F(x_i,y_i),
old-sixth slice descent iff L(xy(x-y))=0; old-eighth slice descent iff
L(xy(x-y)^2)=0. Proof: difference of two old-fibre points is exactly
deltaC times the displayed basis. Necessity from deltaC=1; sufficiency
by omitting that coordinate. Native source proves the linear-coefficient
criterion, not an actual infinite Dirichlet source identity. For an
absolutely convergent infinite sum the same conclusion needs legitimate
linear passage through the sum. For non-linear consumers use the original
fibre-constancy theorem, not this linear criterion.
Equal signed weights at exchanged points cancel sixth but not eighth;
opposite signed weights cancel eighth but not sixth. At (1,2),(2,1)
the equal-weight obstruction pair is (0,4), opposite-weight (-4,0).
Nonnegative weights with any positive off-axis/off-diagonal eighth
contribution cannot annihilate the eighth basis. This is a conditional
no-go on that weight class, not an assertion of actual GRH weights.

## Receipt and next exact cut

scripts/check_grh_signed_phase_recovery.py blob bd7430b58a65fd7e0467f886319c6b22f24d5c97
matches locally executed bytes, timeout90, Python compile PASS.
Sixth/eighth inverses, original phase identities, parity and invisible
modes PASS; all 32 squared degrees (physical 2..64), 288 single-row
deletion nullspaces, exact projective reconstruction, equal/opposite
weight controls and three invalid observation negative controls PASS.
No CI, Lean, Agda or actual global zero-sum execution.

For each actual character/scale/zero-multiplicity indexed consumer:
1. identify the original local polynomial term and its actual signed
   coefficients, without replacing the completed source by a polynomial;
2. either preserve its transverse evaluation or prove the actual
   mixed-coefficient cancellation (and justified sum/limit passage);
3. retain character, conjugation, zero/ordinate, multiplicity, sign,
   prime, pole, Gamma, time/scale, and original normalization metadata;
4. use the existing complete-source compiler, independently bound
   all E2 post-sixth/FarExact tails and E3 strict signed global inequality
   if pursuing the independent proof.

The external all-character admission route is independent: pinned original
Lean proof, compatible kernel and actual Agda character/L-function/zero
transport remain the primary GRH gate. No external proof acceptance is
newly verified by this change. No new generic Mellin or quotient machinery.
