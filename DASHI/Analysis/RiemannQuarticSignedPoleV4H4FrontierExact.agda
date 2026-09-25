module DASHI.Analysis.RiemannQuarticSignedPoleV4H4FrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- RH CLAY-FACING V4 / H4 RECUT OWNER
--
-- This module supersedes the older reading in
--
--   RiemannQuarticSignedPoleBidiMarkedFourthExact
--
-- that treated a localized target-centred Montgomery producer as the
-- mandatory next analytic theorem.
--
-- The newer Lean tranche splits the literal centred fourth-angular statistic
-- into
--
--   A4_local = V4 + H4,
--
-- with
--
--   V4
--     = sum m_rho (gamma_rho-t)^4
--         - integral (x-t)^4 mu(x) dx,
--
--   H4
--     = sum m_rho a_rho^2
--         (a_rho^2 - 6 (gamma_rho-t)^2).
--
-- V4 is source-written in Lean by specializing the already-owned literal
-- N-mu Abel identity to phi_t(x)=(x-t)^4 and combining it with the existing
-- arbitrary-endpoint RvM discrepancy theorem.
--
-- The source-written generic compiler is
--
--   |V4(t,r)| <= 9 r^4 E
--
-- whenever the cumulative N-mu discrepancy from the left endpoint is bounded
-- by E throughout the symmetric window.
--
-- H4 now has a sharper signed recut.  Define the adverse cone by
--
--   6 delta^2 < a^2.
--
-- Outside this cone the exact H4 summand is nonpositive.  Inside it,
--
--   a^2(a^2-6 delta^2) <= a^4.
--
-- The adverse cone is a subset of the already-owned broader local cone, where
-- the zeta strip theorem gives |a|<=1/2.  Therefore each adverse envelope is
-- at most 1/16 times multiplicity, and the existing fixed-window local zero
-- count supplies an unconditional O(log t) finite H4 upper bound.
--
-- IMPORTANT TRUST BOUNDARY
--
-- These V4/H4 quantitative facts are Lean source-written donors.  This Agda
-- module records the authoritative programme state and does NOT claim that
-- those analytic proofs have been independently replayed by the Agda kernel.
--
-- Montgomery / marked-pair machinery remains a retained optional alternative,
-- not a Clay-facing required premise.
------------------------------------------------------------------------

data V4H4Coordinate : Set where
  exactVerticalHorizontalFourthSplit : V4H4Coordinate
  verticalFourthLiteralNMuAbelSpecialization : V4H4Coordinate
  verticalFourthNineR4ECompiler : V4H4Coordinate
  verticalFourthArbitraryEndpointRvMProducer : V4H4Coordinate

  horizontalExactPolynomial : V4H4Coordinate
  horizontalAdverseConeSignSplit : V4H4Coordinate
  horizontalAdverseConeFourthEnvelope : V4H4Coordinate
  horizontalAdverseConeSubsetExistingLocalCone : V4H4Coordinate
  horizontalFiniteLocalCountBound : V4H4Coordinate

  localizedMontgomeryProducer : V4H4Coordinate
  finiteV4CarrierWeld : V4H4Coordinate
  explicitLeftEndpointAtom : V4H4Coordinate
  explicitV4H4AbsorbBudgetSurface : V4H4Coordinate
  fourthAngularToG3OrientationFirewall : V4H4Coordinate
  v4h4BudgetToLiteralG3Weld : V4H4Coordinate
  finalSignedAbsorption : V4H4Coordinate
  terminalG3Compiler : V4H4Coordinate

data V4H4Status : Set where
  theoremOwned : V4H4Status
  leanSourceWrittenDonor : V4H4Status
  optionalAlternative : V4H4Status
  openAssembly : V4H4Status
  openAnalyticObstruction : V4H4Status
  compilerOwned : V4H4Status

v4h4Status : V4H4Coordinate -> V4H4Status
v4h4Status exactVerticalHorizontalFourthSplit = theoremOwned

v4h4Status verticalFourthLiteralNMuAbelSpecialization =
  leanSourceWrittenDonor
v4h4Status verticalFourthNineR4ECompiler =
  leanSourceWrittenDonor
v4h4Status verticalFourthArbitraryEndpointRvMProducer =
  leanSourceWrittenDonor

v4h4Status horizontalExactPolynomial = theoremOwned
v4h4Status horizontalAdverseConeSignSplit =
  leanSourceWrittenDonor
v4h4Status horizontalAdverseConeFourthEnvelope =
  leanSourceWrittenDonor
v4h4Status horizontalAdverseConeSubsetExistingLocalCone =
  leanSourceWrittenDonor
v4h4Status horizontalFiniteLocalCountBound =
  leanSourceWrittenDonor

v4h4Status localizedMontgomeryProducer = optionalAlternative
v4h4Status finiteV4CarrierWeld = leanSourceWrittenDonor
v4h4Status explicitLeftEndpointAtom = leanSourceWrittenDonor
v4h4Status explicitV4H4AbsorbBudgetSurface = leanSourceWrittenDonor
v4h4Status fourthAngularToG3OrientationFirewall = leanSourceWrittenDonor
v4h4Status v4h4BudgetToLiteralG3Weld = leanSourceWrittenDonor
v4h4Status finalSignedAbsorption = openAnalyticObstruction
v4h4Status terminalG3Compiler = compilerOwned

record V4H4Boundary : Set where
  constructor v4-h4-boundary
  field
    exactVerticalHorizontalFourthSplitPaid : Bool

    verticalFourthLiteralNMuAbelSourceWritten : Bool
    verticalFourthNineR4ECompilerSourceWritten : Bool
    verticalFourthArbitraryEndpointRvMSourceWritten : Bool

    horizontalExactPolynomialPaid : Bool
    horizontalAdverseConeSignSplitSourceWritten : Bool
    horizontalAdverseConeFourthEnvelopeSourceWritten : Bool
    horizontalAdverseConeSubsetExistingConeSourceWritten : Bool
    horizontalFiniteLocalCountBoundSourceWritten : Bool

    localizedMontgomeryRequired : Bool
    finiteV4CarrierWeldSourceWritten : Bool
    explicitLeftEndpointAtomSourceWritten : Bool
    explicitV4H4AbsorbBudgetSurfaceSourceWritten : Bool
    fourthAngularToG3OrientationFirewallSourceWritten : Bool
    v4h4BudgetToLiteralG3WeldSourceWritten : Bool
    finalSignedAbsorptionPaid : Bool
    terminalG3CompilerPaid : Bool

    exactVerticalHorizontalFourthSplitPaidIsTrue :
      exactVerticalHorizontalFourthSplitPaid ≡ true

    verticalFourthLiteralNMuAbelSourceWrittenIsTrue :
      verticalFourthLiteralNMuAbelSourceWritten ≡ true
    verticalFourthNineR4ECompilerSourceWrittenIsTrue :
      verticalFourthNineR4ECompilerSourceWritten ≡ true
    verticalFourthArbitraryEndpointRvMSourceWrittenIsTrue :
      verticalFourthArbitraryEndpointRvMSourceWritten ≡ true

    horizontalExactPolynomialPaidIsTrue :
      horizontalExactPolynomialPaid ≡ true
    horizontalAdverseConeSignSplitSourceWrittenIsTrue :
      horizontalAdverseConeSignSplitSourceWritten ≡ true
    horizontalAdverseConeFourthEnvelopeSourceWrittenIsTrue :
      horizontalAdverseConeFourthEnvelopeSourceWritten ≡ true
    horizontalAdverseConeSubsetExistingConeSourceWrittenIsTrue :
      horizontalAdverseConeSubsetExistingConeSourceWritten ≡ true
    horizontalFiniteLocalCountBoundSourceWrittenIsTrue :
      horizontalFiniteLocalCountBoundSourceWritten ≡ true

    localizedMontgomeryRequiredIsFalse :
      localizedMontgomeryRequired ≡ false
    finiteV4CarrierWeldSourceWrittenIsTrue :
      finiteV4CarrierWeldSourceWritten ≡ true
    explicitLeftEndpointAtomSourceWrittenIsTrue :
      explicitLeftEndpointAtomSourceWritten ≡ true
    explicitV4H4AbsorbBudgetSurfaceSourceWrittenIsTrue :
      explicitV4H4AbsorbBudgetSurfaceSourceWritten ≡ true
    fourthAngularToG3OrientationFirewallSourceWrittenIsTrue :
      fourthAngularToG3OrientationFirewallSourceWritten ≡ true
    v4h4BudgetToLiteralG3WeldSourceWrittenIsTrue :
      v4h4BudgetToLiteralG3WeldSourceWritten ≡ true
    finalSignedAbsorptionPaidIsFalse :
      finalSignedAbsorptionPaid ≡ false
    terminalG3CompilerPaidIsTrue :
      terminalG3CompilerPaid ≡ true

    interpretation : String
    nextResearchCut : String
    trustBoundary : String

canonicalV4H4Boundary : V4H4Boundary
canonicalV4H4Boundary =
  v4-h4-boundary
    true
    true true true
    true true true true true
    false
    true true true true
    true false true
    refl
    refl refl refl refl
    refl refl refl refl refl
    refl
    refl refl refl refl
    refl refl refl
    "The preferred Clay-facing local fourth-angular route is V4 plus H4, not a mandatory localized Montgomery theorem. V4 is an ordinary literal N-mu/RvM Abel specialization with a source-written 9*r^4*E compiler. H4 preserves sign: only 6*delta^2<a^2 can contribute positively, and that adverse cone is paid above by an a^4 envelope plus the existing fixed-window local zero-count theorem. Lean now also source-writes the exact finite carrier convention weld: the closed local vertical fourth carrier equals the literal half-open Zeta23 V4 carrier plus one explicit left-endpoint atom; SameOrd(t) contributes zero because the fourth weight vanishes there. The endpoint atom is bounded by the literal one-unit zero count rather than a generic-position choice. A new orientation firewall proves P_G3(rho)=m*S/(6*r^6)*(a^4-fourthAngular(rho)); therefore an upper bound on V4+H4 naturally gives a lower bound on the leading G3 quartic polynomial. Lean then pays the correct polarity instead: |V4| supplies a lower V4 bound, H4 has the unconditional lower envelope H4>=-(3/2)r^2 times local multiplicity, the local a^4 mass is at most 1/16 times that multiplicity, and the multiplicity is theorem-welded to the literal expanded Zeta23 count N(t-r-1,t+r]. This yields a source-written upper bound for literalOffOrdExactAt with the smooth mu fourth moment and FarExact still signed. The old marked 0/2/4 producer remains an optional alternative."
    "The orientation problem is now paid source-written by the lower-fourth-angular route. The remaining Clay-facing analytic task is the literal strict scalar absorption inequality for the corrected budget: targetStrength/(6*(t/16)^6) times [EV + (1/16 + (3/2)r^2)*N(t-r-1,t+r] - localMuFourth] plus local remainder debt plus signed FarExact must lie below compensationTargetThreshold by a positive margin. Lean has additionally exposed the concrete Zeta23 Stirling density floor mu(x) >= (2*pi)^(-1) log(T/(2*pi)) - (20/(2*pi))/T^2 for x>=T>=1 and now source-writes its exact quartic integration on the literal local carrier: localMuFourth >= (2/5)*r^5*muLowerEnvelope(t-r). That floor is substituted into the corrected literal G3 upper budget, so there is no remaining mu-integration representation seam. The Clay-facing task is now the strict scalar ABSORB inequality itself. Inspect and sharpen the dominating paid term if that inequality fails; do not introduce a new abstract hypothesis or absolute-value FarExact."
    "V4, H4, the endpoint carrier weld, the orientation firewall, the corrected budget-to-literal-G3 upper weld, the explicit pointwise mu Stirling floor, and its integrated quartic local-moment floor are Lean source-written donors only. The strict scalar absorption inequality remains unpaid. This owner is an Agda programme/status theorem and does not claim independent Agda-kernel replay or an exact-head Lean kernel receipt for those source tranches."

montgomeryProducerIsOptional :
  v4h4Status localizedMontgomeryProducer ≡ optionalAlternative
montgomeryProducerIsOptional = refl

v4SourceWrittenNotAgdaNative :
  v4h4Status verticalFourthNineR4ECompiler ≡ leanSourceWrittenDonor
v4SourceWrittenNotAgdaNative = refl

h4SourceWrittenNotAgdaNative :
  v4h4Status horizontalFiniteLocalCountBound ≡ leanSourceWrittenDonor
h4SourceWrittenNotAgdaNative = refl

finiteVerticalCarrierWeldIsSourceWritten :
  v4h4Status finiteV4CarrierWeld ≡ leanSourceWrittenDonor
finiteVerticalCarrierWeldIsSourceWritten = refl

leftEndpointAtomIsExplicit :
  v4h4Status explicitLeftEndpointAtom ≡ leanSourceWrittenDonor
leftEndpointAtomIsExplicit = refl

fourthAngularOrientationFirewallIsSourceWritten :
  v4h4Status fourthAngularToG3OrientationFirewall ≡ leanSourceWrittenDonor
fourthAngularOrientationFirewallIsSourceWritten = refl

budgetToLiteralG3WeldIsSourceWritten :
  v4h4Status v4h4BudgetToLiteralG3Weld ≡ leanSourceWrittenDonor
budgetToLiteralG3WeldIsSourceWritten = refl

absorptionRemainsTheAnalyticCut :
  v4h4Status finalSignedAbsorption ≡ openAnalyticObstruction
absorptionRemainsTheAnalyticCut = refl


------------------------------------------------------------------------
-- POST-WELD SCALARIZATION STATUS
--
-- Lean commit 523cfb0b556594ad89970cdeb05305d55a68e525 pushes the
-- explicit pointwise Stirling floor through the literal quartic weight:
--
--   integral_[t-r,t+r] (x-t)^4 mu(x) dx
--     >= (2/5) r^5 * muLowerEnvelope(t-r).
--
-- The corrected literal G3 source bound is then rewritten with this scalar
-- floor substituted for the smooth-mu fourth moment.  This is a Lean donor
-- status only; no Agda-native analytic replay is claimed here.
------------------------------------------------------------------------

data V4H4ScalarizationCoordinate : Set where
  pointwiseMuStirlingFloor : V4H4ScalarizationCoordinate
  exactQuarticWeightIntegral : V4H4ScalarizationCoordinate
  integratedMuFourthFloor : V4H4ScalarizationCoordinate
  correctedMuEnvelopeBudget : V4H4ScalarizationCoordinate
  strictScalarAbsorb : V4H4ScalarizationCoordinate

v4h4ScalarizationStatus :
  V4H4ScalarizationCoordinate -> V4H4Status
v4h4ScalarizationStatus pointwiseMuStirlingFloor =
  leanSourceWrittenDonor
v4h4ScalarizationStatus exactQuarticWeightIntegral =
  leanSourceWrittenDonor
v4h4ScalarizationStatus integratedMuFourthFloor =
  leanSourceWrittenDonor
v4h4ScalarizationStatus correctedMuEnvelopeBudget =
  leanSourceWrittenDonor
v4h4ScalarizationStatus strictScalarAbsorb =
  openAnalyticObstruction

integratedMuFourthFloorIsSourceWritten :
  v4h4ScalarizationStatus integratedMuFourthFloor
    ≡ leanSourceWrittenDonor
integratedMuFourthFloorIsSourceWritten = refl

correctedMuEnvelopeBudgetIsSourceWritten :
  v4h4ScalarizationStatus correctedMuEnvelopeBudget
    ≡ leanSourceWrittenDonor
correctedMuEnvelopeBudgetIsSourceWritten = refl

strictScalarAbsorbRemainsOpen :
  v4h4ScalarizationStatus strictScalarAbsorb
    ≡ openAnalyticObstruction
strictScalarAbsorbRemainsOpen = refl


------------------------------------------------------------------------
-- SELECTED-WITNESS SIXTH-ORDER SHARPENING DONOR
--
-- Lean PR #22 now cross-welds the complete-jet sixth absolute moment to the
-- same selected-witness G1 constant already used by the quantitative target
-- band:
--
--   M6_abs(W)
--     = integral |P_W(u)| |u|^6 du
--     <= integral |P_W(u)| cosh(|u|) |u|^5 du
--     = K(W).
--
-- This removes M6_abs as an independent witness invariant.  The old explicit
-- G1 K0 is still deliberately coarse and is NOT claimed to close terminal
-- ABSORB.
--
-- Lean also exposes the signed sixth moment
--
--   M6_signed(W) = integral P_W(u) u^6 du
--
-- and the sixth angular harmonic
--
--   M6_signed(W)/720
--     * (alpha^6 - 15 alpha^4 q^2 + 15 alpha^2 q^4 - q^6)
--   = M6_signed(W)/720 * Re((alpha + i q)^6).
--
-- The kernel is algebraically recut as
--
--   complete quartic + signed sixth harmonic + beyond-sixth residual.
--
-- IMPORTANT: the beyond-sixth residual has not yet been proved O(8) here or
-- in the Lean donor.  That analytic estimate/sign exploitation is the new
-- preferred sharpening frontier.  No Agda-native replay is claimed.
------------------------------------------------------------------------

data SixthSharpeningCoordinate : Set where
  absoluteSixthMomentToG1Lipschitz : SixthSharpeningCoordinate
  terminalBudgetToG1Lipschitz : SixthSharpeningCoordinate
  signedSixthMomentCarrier : SixthSharpeningCoordinate
  signedSixthHarmonicCarrier : SixthSharpeningCoordinate
  quarticPlusSixthAlgebraicRecut : SixthSharpeningCoordinate
  beyondSixthOrderEightEstimate : SixthSharpeningCoordinate
  strictScalarAbsorbAfterSixthSharpening : SixthSharpeningCoordinate

sixthSharpeningStatus :
  SixthSharpeningCoordinate -> V4H4Status
sixthSharpeningStatus absoluteSixthMomentToG1Lipschitz =
  leanSourceWrittenDonor
sixthSharpeningStatus terminalBudgetToG1Lipschitz =
  leanSourceWrittenDonor
sixthSharpeningStatus signedSixthMomentCarrier =
  leanSourceWrittenDonor
sixthSharpeningStatus signedSixthHarmonicCarrier =
  leanSourceWrittenDonor
sixthSharpeningStatus quarticPlusSixthAlgebraicRecut =
  leanSourceWrittenDonor
sixthSharpeningStatus beyondSixthOrderEightEstimate =
  leanSourceWrittenDonor
sixthSharpeningStatus strictScalarAbsorbAfterSixthSharpening =
  openAnalyticObstruction

absoluteSixthMomentToG1LipschitzIsSourceWritten :
  sixthSharpeningStatus absoluteSixthMomentToG1Lipschitz
    ≡ leanSourceWrittenDonor
absoluteSixthMomentToG1LipschitzIsSourceWritten = refl

signedSixthHarmonicCarrierIsSourceWritten :
  sixthSharpeningStatus signedSixthHarmonicCarrier
    ≡ leanSourceWrittenDonor
signedSixthHarmonicCarrierIsSourceWritten = refl

beyondSixthOrderEightEstimateIsSourceWritten :
  sixthSharpeningStatus beyondSixthOrderEightEstimate
    ≡ leanSourceWrittenDonor
beyondSixthOrderEightEstimateIsSourceWritten = refl

sixthSharpeningLeanDonorHead : String
sixthSharpeningLeanDonorHead =
  "9e9efb151febe48144e889fb7571f20c93027d2c"

sixthSharpeningTransportedIntoAgdaKernelHere : Bool
sixthSharpeningTransportedIntoAgdaKernelHere = false

coarseExplicitG1K0CertifiedTerminalAbsorbHere : Bool
coarseExplicitG1K0CertifiedTerminalAbsorbHere = false

sixthSharpeningInterpretation : String
sixthSharpeningInterpretation =
  "The generic M6 support/L1 cap is no longer the preferred sixth-order interface. Lean source-writes M6_abs(W)<=K(W), exposes the signed sixth harmonic M6_signed(W)/720 * Re((alpha+i*q)^6), proves a mixed total-degree-eight majorant for the post-sixth residual from separate real cos/cosh unit-ball Taylor theorems, and cross-welds M8_abs(W)<=(pi+1)^2*K(W). The literal physical residual is transported at r^-10 and summed on the same finite local carrier. The existing explicit G1 K0 remains too coarse to declare terminal ABSORB closed; the remaining preferred cut is the signed-sixth scalar contribution plus the now count-paid eighth debt and signed FarExact. Montgomery remains irrelevant to this cut."


------------------------------------------------------------------------
-- LITERAL FINITE SIGNED-SIXTH TRANSPORT
--
-- Lean now transports the normalized signed sixth harmonic through the exact
-- physical r^-2 normalization and literal zero multiplicity, then sums it on
-- the same finite local centeredZeroFinset carrier:
--
--   localCompleteRemainder_n
--     = localSignedSixthHarmonic_n
--       + localBeyondSixthRemainder_n.
--
-- This is an exact finite same-object decomposition.  It is not an O(8)
-- theorem and does not itself pay strict scalar ABSORB.
------------------------------------------------------------------------

data LiteralSixthTransportCoordinate : Set where
  perZeroSignedSixthPhysicalTransport : LiteralSixthTransportCoordinate
  perZeroBeyondSixthPhysicalTransport : LiteralSixthTransportCoordinate
  finiteLocalSignedSixthSplit : LiteralSixthTransportCoordinate
  finiteLocalBeyondSixthBound : LiteralSixthTransportCoordinate

literalSixthTransportStatus :
  LiteralSixthTransportCoordinate -> V4H4Status
literalSixthTransportStatus perZeroSignedSixthPhysicalTransport =
  leanSourceWrittenDonor
literalSixthTransportStatus perZeroBeyondSixthPhysicalTransport =
  leanSourceWrittenDonor
literalSixthTransportStatus finiteLocalSignedSixthSplit =
  leanSourceWrittenDonor
literalSixthTransportStatus finiteLocalBeyondSixthBound =
  leanSourceWrittenDonor

finiteLocalSignedSixthSplitIsSourceWritten :
  literalSixthTransportStatus finiteLocalSignedSixthSplit
    ≡ leanSourceWrittenDonor
finiteLocalSignedSixthSplitIsSourceWritten = refl

finiteLocalBeyondSixthBoundIsSourceWritten :
  literalSixthTransportStatus finiteLocalBeyondSixthBound
    ≡ leanSourceWrittenDonor
finiteLocalBeyondSixthBoundIsSourceWritten = refl


------------------------------------------------------------------------
-- MIXED EIGHTH-ORDER / POST-SIXTH TERMINAL DONOR
--
-- Lean PR #22 now pays the two items that were previously left open after
-- the scalar degree-six Taylor facts:
--
--  * a mixed real-product theorem for cosh(alpha*u) cos(q*u), retaining the
--    complete total-degree-six Taylor polynomial and majorizing only degree
--    eight and above;
--  * literal physical and finite transport of that beyond-sixth residual at
--    r^-10.
--
-- The mixed proof deliberately does NOT apply the unit-ball complex
-- exponential theorem to (q+i*alpha)u.  It combines the separately-certified
-- real cos/cosh unit-ball remainders.
--
-- The selected-profile eighth absolute moment is not a new witness invariant:
--
--   M8_abs(W) <= (pi+1)^2 M6_abs(W) <= (pi+1)^2 K(W).
--
-- A downstream source compiler now has the form
--
--   quartic corrected main
--     + localSignedSixthHarmonic
--     + localEighthDebt
--     + FarExact,
--
-- and the eighth debt is bounded by the same expanded literal zero count.
-- The signed sixth harmonic and FarExact remain signed.
--
-- Strict scalar ABSORB itself is still open.  These are Lean source-written
-- donors only; no Agda-native analytic replay is claimed.
------------------------------------------------------------------------

data PostSixthCoordinate : Set where
  mixedCoshCosDegreeEightMajorant : PostSixthCoordinate
  selectedM8ToM6ToG1Weld : PostSixthCoordinate
  normalizedBeyondSixthIntegralIdentity : PostSixthCoordinate
  normalizedBeyondSixthM8Bound : PostSixthCoordinate
  literalPhysicalRMinusTenTransport : PostSixthCoordinate
  finiteLocalEighthDebt : PostSixthCoordinate
  finiteLocalEighthCountPayment : PostSixthCoordinate
  signedSixthEighthFarTerminalBudget : PostSixthCoordinate
  strictPostSixthScalarAbsorb : PostSixthCoordinate

postSixthStatus : PostSixthCoordinate -> V4H4Status
postSixthStatus mixedCoshCosDegreeEightMajorant =
  leanSourceWrittenDonor
postSixthStatus selectedM8ToM6ToG1Weld =
  leanSourceWrittenDonor
postSixthStatus normalizedBeyondSixthIntegralIdentity =
  leanSourceWrittenDonor
postSixthStatus normalizedBeyondSixthM8Bound =
  leanSourceWrittenDonor
postSixthStatus literalPhysicalRMinusTenTransport =
  leanSourceWrittenDonor
postSixthStatus finiteLocalEighthDebt =
  leanSourceWrittenDonor
postSixthStatus finiteLocalEighthCountPayment =
  leanSourceWrittenDonor
postSixthStatus signedSixthEighthFarTerminalBudget =
  leanSourceWrittenDonor
postSixthStatus strictPostSixthScalarAbsorb =
  openAnalyticObstruction

mixedEighthMajorantIsSourceWritten :
  postSixthStatus mixedCoshCosDegreeEightMajorant
    ≡ leanSourceWrittenDonor
mixedEighthMajorantIsSourceWritten = refl

literalRMinusTenTransportIsSourceWritten :
  postSixthStatus literalPhysicalRMinusTenTransport
    ≡ leanSourceWrittenDonor
literalRMinusTenTransportIsSourceWritten = refl

strictPostSixthScalarAbsorbRemainsOpen :
  postSixthStatus strictPostSixthScalarAbsorb
    ≡ openAnalyticObstruction
strictPostSixthScalarAbsorbRemainsOpen = refl

postSixthLeanDonorHead : String
postSixthLeanDonorHead =
  "9e9efb151febe48144e889fb7571f20c93027d2c"

postSixthTransportedIntoAgdaKernelHere : Bool
postSixthTransportedIntoAgdaKernelHere = false

postSixthInterpretation : String
postSixthInterpretation =
  "The absolute M6 bottleneck is no longer present on the preferred terminal source surface. Lean retains the signed sixth harmonic, proves and transports only the beyond-sixth residual with a total-degree-eight envelope, pays its finite local multiplicity through the existing expanded Zeta23 count, and bounds M8 through the same selected-witness G1 constant K(W). The remaining Clay-facing analytic test is the strict scalar inequality for quartic main + signed sixth + eighth debt + signed FarExact against the literal target threshold."


------------------------------------------------------------------------
-- SIGNED-SIXTH OUTER-CONE REDUCTION DONOR
--
-- Lean PR #22 now factors the literal physical sixth angular carrier exactly:
--
--   a^6 - 15 a^4 d^2 + 15 a^2 d^4 - d^6
--     = (a^2 - d^2) (a^4 - 14 a^2 d^2 + d^4).
--
-- On the outer cone
--
--   16 a^2 <= d^2,
--
-- the physical phase is nonpositive.  Therefore, under the explicit remaining
-- witness-sign hypothesis
--
--   0 <= M6_signed(W),
--
-- the entire outer-cone finite signed-sixth sum is nonpositive and can be
-- discarded in an upper source bound without taking absolute values.
--
-- The complementary potentially adverse carrier satisfies
--
--   d^2 < 16 a^2.
--
-- Since every literal zeta zero on this carrier has |a| <= 1/2, Lean further
-- proves
--
--   d^2 < 4.
--
-- Thus the preferred sixth-order payment is reduced from the full canonical
-- local window to a fixed physical strip |d| < 2, conditional only on the sign
-- of the selected signed sixth moment.  The sign of M6_signed(W) itself has
-- NOT been proved by this donor and remains the immediate analytic/witness
-- frontier.  No Agda-native replay is claimed here.
------------------------------------------------------------------------

data SignedSixthConeCoordinate : Set where
  physicalSixthFactorization : SignedSixthConeCoordinate
  outerConePhaseNonpositive : SignedSixthConeCoordinate
  exactPhysicalSixthTransport : SignedSixthConeCoordinate
  finiteOuterCentralSixthSplit : SignedSixthConeCoordinate
  outerSixthNonpositiveOfM6Nonnegative : SignedSixthConeCoordinate
  centralSixthFixedStrip : SignedSixthConeCoordinate
  selectedSignedM6Nonnegative : SignedSixthConeCoordinate
  fixedStripSixthCountPayment : SignedSixthConeCoordinate

signedSixthConeStatus :
  SignedSixthConeCoordinate -> V4H4Status
signedSixthConeStatus physicalSixthFactorization =
  leanSourceWrittenDonor
signedSixthConeStatus outerConePhaseNonpositive =
  leanSourceWrittenDonor
signedSixthConeStatus exactPhysicalSixthTransport =
  leanSourceWrittenDonor
signedSixthConeStatus finiteOuterCentralSixthSplit =
  leanSourceWrittenDonor
signedSixthConeStatus outerSixthNonpositiveOfM6Nonnegative =
  leanSourceWrittenDonor
signedSixthConeStatus centralSixthFixedStrip =
  leanSourceWrittenDonor
signedSixthConeStatus selectedSignedM6Nonnegative =
  openAnalyticObstruction
signedSixthConeStatus fixedStripSixthCountPayment =
  openAnalyticObstruction

outerSixthConeReductionIsSourceWritten :
  signedSixthConeStatus outerSixthNonpositiveOfM6Nonnegative
    ≡ leanSourceWrittenDonor
outerSixthConeReductionIsSourceWritten = refl

centralSixthFixedStripIsSourceWritten :
  signedSixthConeStatus centralSixthFixedStrip
    ≡ leanSourceWrittenDonor
centralSixthFixedStripIsSourceWritten = refl

selectedSignedM6SignRemainsOpen :
  signedSixthConeStatus selectedSignedM6Nonnegative
    ≡ openAnalyticObstruction
selectedSignedM6SignRemainsOpen = refl

signedSixthConeLeanDonorHead : String
signedSixthConeLeanDonorHead =
  "bb33220b76eb563d781cff573b8dc7102676e1fe"

signedSixthConeTransportedIntoAgdaKernelHere : Bool
signedSixthConeTransportedIntoAgdaKernelHere = false

signedSixthConeInterpretation : String
signedSixthConeInterpretation =
  "The signed sixth harmonic no longer needs to be treated on the full canonical local carrier.  Lean factors its literal physical phase and proves that, if the selected signed profile sixth moment is nonnegative, the outer cone 16*a^2<=d^2 contributes nonpositively.  The complementary potentially adverse terms lie in the fixed strip d^2<4.  The next preferred cut is therefore to prove/evaluate the selected witness sign M6_signed(W)>=0 and then pay only the fixed-width central strip, while retaining FarExact signed."


------------------------------------------------------------------------
-- SELECTED-WITNESS SIXTH-SIGN CORRECTION
--
-- The previous outer-cone section is a valid conditional donor, but its
-- hypothesis M6_signed(W) >= 0 is NOT the selected-witness sign.
--
-- Lean has now reduced the selected signed sixth moment to the literal
-- four-window endpoint determinant
--
--   M6_signed(W)
--     = 4 * (poleTwo * J6_half - poleHalf * J6_two).
--
-- The exact atomic J2-null endpoint values are
--
--   J6_half
--     = -(2245/101088) * pi^6 < 0,
--
--   J6_twoThirds
--     =  (35/8748) * pi^6 > 0.
--
-- Corridor margins plus the existing arbitrary-k smooth/atomic convergence
-- preserve these endpoint signs for sufficiently narrow smooth windows.
-- Existing smooth-pole convergence preserves positivity of both endpoint pole
-- residuals.  Recutting the witness radius through these additional donors
-- therefore constructs a floor-certified witness with
--
--   M6_signed(W) < 0.
--
-- Consequently the earlier M6>=0 fixed-strip route remains only a conditional
-- side lemma.  The preferred selected-witness route must exploit/bound the
-- actual negative sixth coefficient.  Strict terminal ABSORB remains open.
------------------------------------------------------------------------

data SelectedSixthSignCoordinate : Set where
  signedM6EndpointDeterminant : SelectedSixthSignCoordinate
  genericProjectiveMomentBridge : SelectedSixthSignCoordinate
  signedM6FourWindowJ6Determinant : SelectedSixthSignCoordinate
  atomicJ6Formula : SelectedSixthSignCoordinate
  atomicJ6EndpointSigns : SelectedSixthSignCoordinate
  smoothJ6EndpointSignPersistence : SelectedSixthSignCoordinate
  smoothEndpointPolePositivity : SelectedSixthSignCoordinate
  floorWitnessWithNegativeSignedM6 : SelectedSixthSignCoordinate
  negativeSignedM6TerminalPayment : SelectedSixthSignCoordinate

selectedSixthSignStatus :
  SelectedSixthSignCoordinate -> V4H4Status
selectedSixthSignStatus signedM6EndpointDeterminant =
  leanSourceWrittenDonor
selectedSixthSignStatus genericProjectiveMomentBridge =
  leanSourceWrittenDonor
selectedSixthSignStatus signedM6FourWindowJ6Determinant =
  leanSourceWrittenDonor
selectedSixthSignStatus atomicJ6Formula =
  leanSourceWrittenDonor
selectedSixthSignStatus atomicJ6EndpointSigns =
  leanSourceWrittenDonor
selectedSixthSignStatus smoothJ6EndpointSignPersistence =
  leanSourceWrittenDonor
selectedSixthSignStatus smoothEndpointPolePositivity =
  leanSourceWrittenDonor
selectedSixthSignStatus floorWitnessWithNegativeSignedM6 =
  leanSourceWrittenDonor
selectedSixthSignStatus negativeSignedM6TerminalPayment =
  leanSourceWrittenDonor

selectedWitnessNegativeSignedM6IsSourceWritten :
  selectedSixthSignStatus floorWitnessWithNegativeSignedM6
    ≡ leanSourceWrittenDonor
selectedWitnessNegativeSignedM6IsSourceWritten = refl

negativeSignedM6TerminalPaymentIsSourceWritten :
  selectedSixthSignStatus negativeSignedM6TerminalPayment
    ≡ leanSourceWrittenDonor
negativeSignedM6TerminalPaymentIsSourceWritten = refl

selectedSixthSignLeanDonorHead : String
selectedSixthSignLeanDonorHead =
  "e4afb5da3ad4cf4a821cd5a7fbb8e17ff0da0e72"

selectedSixthSignTransportedIntoAgdaKernelHere : Bool
selectedSixthSignTransportedIntoAgdaKernelHere = false

selectedSixthSignInterpretation : String
selectedSixthSignInterpretation =
  "The selected floor-certified smooth witness can now be chosen with a terminal-strength signed sixth certificate: -(3/20)*pi^6 <= M6_signed(W) < 0. Lean obtains this by tightening the actual endpoint pole residuals, proving terminal endpoint J6 magnitude bounds, and recutting the same strength-floor witness. The cap is proved strong enough for the dominant sixth-vs-quartic coefficient at the canonical radius and is substituted directly into the literal finite post-sixth source. A direct post-sixth strict-scalar compiler now runs that source through the existing cofinal tsum and completed-residual weld to G3. The selected M6 payment is therefore no longer the Clay-facing obstruction. FarExact remains signed and presently has no theorem-bearing quantitative payment on this carrier; together with the final strict scalar comparison, that is the preferred remaining cut."


------------------------------------------------------------------------
-- CLAY MIN-CUT AFTER TERMINAL SELECTED-M6 PAYMENT
--
-- PDF-guided pruning: the manuscript treats formalization as an audit trail,
-- not a reason to continue developing every available moment/cone lemma.  The
-- selected sixth lane is now quantitatively strong enough to enter the literal
-- terminal source:
--
--   strengthFloor <= S(W)
--   -(3/20)*pi^6 <= M6_signed(W) < 0.
--
-- Lean proves the cap beats the dominant sixth-vs-quartic coefficient at the
-- canonical radius, substitutes it into the same literal expanded zero count,
-- keeps the eighth debt on the already-owned G1 K(W) cross-weld, and compiles
-- eventual strict terminal ABSORB directly to G3.
--
-- Inspection of the live preferred source found no theorem-bearing upper
-- payment for literalFarExactAt.  The cone stack only preserves it through the
-- signed compensation coordinate
--
--   goodGain - FarExact.
--
-- Therefore the next Clay-facing mathematical cut is NOT more selected-M6 or
-- generic J_k machinery.  It is a same-object quantitative FarExact /
-- signed-compensation theorem strong enough to close the literal strict scalar
-- inequality.
--
-- These facts remain Lean source-written donors only.  No Agda-native replay
-- or exact-head Lean kernel receipt is claimed here.
------------------------------------------------------------------------

data ClayPostM6Coordinate : Set where
  terminalSelectedM6Cap : ClayPostM6Coordinate
  terminalSelectedM6DominantBalance : ClayPostM6Coordinate
  terminalSelectedM6LiteralSourcePayment : ClayPostM6Coordinate
  terminalSelectedM6DirectG3Compiler : ClayPostM6Coordinate
  literalFarExactQuantitativePayment : ClayPostM6Coordinate
  finalPostM6StrictScalarAbsorb : ClayPostM6Coordinate

clayPostM6Status : ClayPostM6Coordinate -> V4H4Status
clayPostM6Status terminalSelectedM6Cap =
  leanSourceWrittenDonor
clayPostM6Status terminalSelectedM6DominantBalance =
  leanSourceWrittenDonor
clayPostM6Status terminalSelectedM6LiteralSourcePayment =
  leanSourceWrittenDonor
clayPostM6Status terminalSelectedM6DirectG3Compiler =
  leanSourceWrittenDonor
clayPostM6Status literalFarExactQuantitativePayment =
  openAnalyticObstruction
clayPostM6Status finalPostM6StrictScalarAbsorb =
  openAnalyticObstruction

terminalSelectedM6CapIsSourceWritten :
  clayPostM6Status terminalSelectedM6Cap
    ≡ leanSourceWrittenDonor
terminalSelectedM6CapIsSourceWritten = refl

farExactPaymentIsNowThePreferredOpenCut :
  clayPostM6Status literalFarExactQuantitativePayment
    ≡ openAnalyticObstruction
farExactPaymentIsNowThePreferredOpenCut = refl

finalPostM6StrictScalarAbsorbRemainsOpen :
  clayPostM6Status finalPostM6StrictScalarAbsorb
    ≡ openAnalyticObstruction
finalPostM6StrictScalarAbsorbRemainsOpen = refl

clayPostM6LeanDonorHead : String
clayPostM6LeanDonorHead =
  "e4afb5da3ad4cf4a821cd5a7fbb8e17ff0da0e72"

clayPostM6TransportedIntoAgdaKernelHere : Bool
clayPostM6TransportedIntoAgdaKernelHere = false


------------------------------------------------------------------------
-- FAR-EXACT RECUT TO ONE HORIZONTAL CURVATURE COORDINATE
--
-- Lean has now removed literalFarExactAt as an opaque terminal coordinate.
-- On the identical centered zero carrier it splits exactly into
--
--   FarExact = FarBase + FarHorizontal.
--
-- FarBase is the existing signed zero/N-mu ordinate test and is paid by the
-- imported literal inverse-square zero shell:
--
--   |FarBase_n|
--     <= C_Psi(W) *
--        (18 A log(|t|+4)/J + 72 A/sqrt(J)).
--
-- For the canonical far boundary Lean chooses
--
--   J(t) = floor(t/2000),
--
-- valid for t >= 2000, so the base term is an explicit
-- O(log(t)/t) + O(t^(-1/2)) source uniformly in the finite exhaustion n.
--
-- FarHorizontal is then identified exactly with the already-existing signed
-- endpoint-linear horizontal source.  The normalized horizontal kernel is the
-- cosine transform of
--
--   P_W(u) * (cosh(alpha*u)-1),
--
-- and the existing two-integration-by-parts theorem yields
--
--   |H_W(alpha,q)| <= C_H(W,alpha)/q^2.
--
-- Physical rescaling cancels the outer r^-2 against q^-2, giving literally
--
--   |horizontalSource_rho|
--     <= m_rho * C_H(W,alpha_rho) / (Im rho - t)^2.
--
-- Lean exposes the one remaining uniformity coordinate
--
--   HorizontalFarCurvatureBound W CH
--
-- asserting C_H(W,alpha_rho) <= CH on the literal zero carrier.  Under this
-- single scalar hypothesis the WHOLE FarExact finite source satisfies
--
--   |FarExact_n|
--     <= (C_Psi(W)+CH) *
--        (18 A log(|t|+4)/J + 72 A/sqrt(J)),
--
-- uniformly in n, and a far-paid terminal scalar budget compiles directly
-- through the existing selected-M6/cofinal/completed-residual stack to G3.
--
-- Therefore FarExact itself is no longer the semantic/carrier obstruction.
-- The preferred remaining analytic min-cut is:
--
--   (1) a selected-witness quantitative bound CH for the exact horizontal
--       curvature coordinate, strong enough on the Clay-high range; and
--   (2) the final far-paid strict scalar inequality.
--
-- The existing uniform K(W) theorem is NOT silently reused for CH: it is an
-- L1-type profile bound and does not by itself control C2 curvature or impose
-- a uniform positive lower bound on the selected smoothing radius R.
--
-- All entries below are Lean source-written donors only.  No Agda-native
-- analytic replay is claimed here.
------------------------------------------------------------------------

data FarExactRecutCoordinate : Set where
  farExactBaseHorizontalExactSplit : FarExactRecutCoordinate
  farBaseLiteralShellPayment : FarExactRecutCoordinate
  farBaseCanonicalLinearCutoff : FarExactRecutCoordinate
  farHorizontalExistingSourceIdentification : FarExactRecutCoordinate
  farHorizontalNormalizedInverseSquareDecay : FarExactRecutCoordinate
  farHorizontalPhysicalGapSquareTransport : FarExactRecutCoordinate
  wholeFarExactShellCompilerGivenCH : FarExactRecutCoordinate
  farPaidScalarDirectG3Compiler : FarExactRecutCoordinate
  selectedWitnessHorizontalCurvatureBound : FarExactRecutCoordinate
  finalFarPaidStrictScalarAbsorb : FarExactRecutCoordinate

farExactRecutStatus :
  FarExactRecutCoordinate -> V4H4Status
farExactRecutStatus farExactBaseHorizontalExactSplit =
  leanSourceWrittenDonor
farExactRecutStatus farBaseLiteralShellPayment =
  leanSourceWrittenDonor
farExactRecutStatus farBaseCanonicalLinearCutoff =
  leanSourceWrittenDonor
farExactRecutStatus farHorizontalExistingSourceIdentification =
  leanSourceWrittenDonor
farExactRecutStatus farHorizontalNormalizedInverseSquareDecay =
  leanSourceWrittenDonor
farExactRecutStatus farHorizontalPhysicalGapSquareTransport =
  leanSourceWrittenDonor
farExactRecutStatus wholeFarExactShellCompilerGivenCH =
  leanSourceWrittenDonor
farExactRecutStatus farPaidScalarDirectG3Compiler =
  leanSourceWrittenDonor
farExactRecutStatus selectedWitnessHorizontalCurvatureBound =
  openAnalyticObstruction
farExactRecutStatus finalFarPaidStrictScalarAbsorb =
  openAnalyticObstruction

farExactCarrierPaymentIsSourceWritten :
  farExactRecutStatus wholeFarExactShellCompilerGivenCH
    ≡ leanSourceWrittenDonor
farExactCarrierPaymentIsSourceWritten = refl

horizontalCurvatureIsPreferredOpenCut :
  farExactRecutStatus selectedWitnessHorizontalCurvatureBound
    ≡ openAnalyticObstruction
horizontalCurvatureIsPreferredOpenCut = refl

farPaidStrictScalarRemainsOpen :
  farExactRecutStatus finalFarPaidStrictScalarAbsorb
    ≡ openAnalyticObstruction
farPaidStrictScalarRemainsOpen = refl

farExactRecutLeanDonorHead : String
farExactRecutLeanDonorHead =
  "b034c2f6ba2b8559015488b590aa6448d7155af1"

farExactRecutTransportedIntoAgdaKernelHere : Bool
farExactRecutTransportedIntoAgdaKernelHere = false

farExactRecutInterpretation : String
farExactRecutInterpretation =
  "FarExact is no longer an opaque Clay-facing carrier. Lean splits it exactly into the existing base N-mu zero source and existing horizontal source, pays the base by the literal inverse-square zero shell with canonical cutoff floor(t/2000), proves inverse-square decay for the exact signed horizontal normalized kernel, transports that decay with exact physical scaling, and compiles the whole far source to the same shell under one explicit HorizontalFarCurvatureBound CH. The far-paid scalar budget already compiles directly to G3. The preferred remaining analytic cut is therefore a quantitative selected-witness CH theorem plus the final far-paid strict scalar inequality. Existing K(W) is not treated as C2 control."


------------------------------------------------------------------------
-- FAR-PAID ROUTE SUPERSEDED BY LITERAL NORMALIZED COMPENSATION CUT
--
-- The previous FarExact/CH section remains a valid absolute-value audit route,
-- but it is NOT the preferred Clay-facing min-cut.
--
-- New Lean source analysis exposes why.  At the canonical physical boundary
--
--   h = (t/16) * eta0,     eta0 = 1/(pi+1),
--
-- the normalized frequency is exactly q = +/- eta0.  It is fixed as t grows.
-- Consequently improving remote Fourier decay from q^-2 to q^-6 or q^-8 does
-- not create the missing t^-4 gain at this boundary.  The generic compensated
-- N-mu source carries an unavoidable outer (t/16)^-2 scale, whereas the target
-- quartic signal is on the (t/16)^-6 scale.
--
-- The required extra four inverse powers must therefore come from the exact
-- signed/cancelled compensated high-ordinate functional itself, not from an
-- absolute far-shell estimate.
--
-- Lean now performs the following exact recut on the same source family:
--
--   1. FarExact = FarBase + FarHorizontal on the identical finite carrier.
--   2. FarHorizontal is exactly the existing G3 horizontal source.
--   3. The base zero tail is paired with the matching mu/Gamma channel before
--      estimation, yielding a canonical compensated N-mu tail.
--   4. The selected-M6 terminal source cancels FarExact algebraically and gives
--      an upper bound for the exact local pair source alone.
--   5. For one finite cut n, define
--
--        F_n = completedResidual - (1/2) * localExact_n.
--
--      Lean proves the literal identity
--
--        F_n
--          = (1/2) *
--            ( global exact off-ordinate pair tsum
--              - local exact pair sum_n
--              - integral Psi_W * mu ).
--
--   6. The normalized carrier
--
--        (t/16)^2 * F_n
--
--      is placed directly on quartic scale.  The single remaining high
--      inequality is exposed as PostSixthLiteralCompensationCut.
--
--   7. That one inequality compiles through the already-paid selected-M6 local
--      budget and the existing completed-residual theorem all the way to
--      contradiction.
--
-- Lean additionally welds the terminal-M6 witness to the already-paid G1
-- quantitative target band on the SAME witness using the universal explicit
-- K0 bound, and absorbs the V4 producer threshold into one fixed global high
-- cutoff.
--
-- Therefore the preferred Clay-facing statement is now:
--
--   above one fixed high threshold,
--   hypothetical off-line zero
--   + selected literal compensated high cut
--   -> False.
--
-- No independent FarExact theorem, horizontal-curvature theorem, final scalar
-- ABSORB theorem, second witness, or taper-regularity programme remains on the
-- preferred interface.
--
-- This is still a Lean source-written donor only.  The literal compensation
-- high cut itself is the genuine open analytic theorem.  No Agda-native replay
-- is claimed.
------------------------------------------------------------------------

data LiteralCompensationMinCutCoordinate : Set where
  farExactExactBaseHorizontalSplit : LiteralCompensationMinCutCoordinate
  farHorizontalExistingG3Identification : LiteralCompensationMinCutCoordinate
  canonicalNMuCompensationRecut : LiteralCompensationMinCutCoordinate
  canonicalNormalizedBoundaryIdentity : LiteralCompensationMinCutCoordinate
  quarticScaleNormalizationDiagnosis : LiteralCompensationMinCutCoordinate
  selectedLocalBudgetFarCancellation : LiteralCompensationMinCutCoordinate
  finiteCutCompensatedFarIdentity : LiteralCompensationMinCutCoordinate
  literalCompensationCutNormalizedEquivalence : LiteralCompensationMinCutCoordinate
  literalCompensationCutToContradiction : LiteralCompensationMinCutCoordinate
  sameWitnessTerminalM6AndTargetBand : LiteralCompensationMinCutCoordinate
  fixedHighV4Compiler : LiteralCompensationMinCutCoordinate
  selectedLiteralCompensationHighCut : LiteralCompensationMinCutCoordinate

literalCompensationMinCutStatus :
  LiteralCompensationMinCutCoordinate -> V4H4Status
literalCompensationMinCutStatus farExactExactBaseHorizontalSplit =
  leanSourceWrittenDonor
literalCompensationMinCutStatus farHorizontalExistingG3Identification =
  leanSourceWrittenDonor
literalCompensationMinCutStatus canonicalNMuCompensationRecut =
  leanSourceWrittenDonor
literalCompensationMinCutStatus canonicalNormalizedBoundaryIdentity =
  leanSourceWrittenDonor
literalCompensationMinCutStatus quarticScaleNormalizationDiagnosis =
  leanSourceWrittenDonor
literalCompensationMinCutStatus selectedLocalBudgetFarCancellation =
  leanSourceWrittenDonor
literalCompensationMinCutStatus finiteCutCompensatedFarIdentity =
  leanSourceWrittenDonor
literalCompensationMinCutStatus literalCompensationCutNormalizedEquivalence =
  leanSourceWrittenDonor
literalCompensationMinCutStatus literalCompensationCutToContradiction =
  leanSourceWrittenDonor
literalCompensationMinCutStatus sameWitnessTerminalM6AndTargetBand =
  leanSourceWrittenDonor
literalCompensationMinCutStatus fixedHighV4Compiler =
  leanSourceWrittenDonor
literalCompensationMinCutStatus selectedLiteralCompensationHighCut =
  openAnalyticObstruction

literalCompensationCutIsOnlyPreferredOpenCoordinate :
  literalCompensationMinCutStatus selectedLiteralCompensationHighCut
    ≡ openAnalyticObstruction
literalCompensationCutIsOnlyPreferredOpenCoordinate = refl

farPaidCHRouteIsNotPreferredMinCut : Bool
farPaidCHRouteIsNotPreferredMinCut = true

literalCompensationLeanDonorHead : String
literalCompensationLeanDonorHead =
  "0addb974ca43b76659360fe5822f1617a54e1cc8"

literalCompensationTransportedIntoAgdaKernelHere : Bool
literalCompensationTransportedIntoAgdaKernelHere = false

literalCompensationMinCutInterpretation : String
literalCompensationMinCutInterpretation =
  "The preferred RH Clay-facing route has been collapsed to one exact high-ordinate statement on the literal four-window source. FarExact is split and then recombined with the matching mu/Gamma compensation; the selected local source budget cancels FarExact algebraically; the remaining finite-cut compensated functional is normalized on the exact quartic scale and expanded as global pair source minus local pair source minus the full mu integral. That literal compensation cut compiles directly to the existing completed-residual contradiction. The same selected witness simultaneously carries the terminal M6 certificate and quantitative target band, and the V4 producer threshold is absorbed into one fixed high cutoff. The older absolute FarPaid/HorizontalFarCurvatureBound lane remains a valid audit fallback but is not the preferred min-cut."


------------------------------------------------------------------------
-- QUARTIC-SCALE LITERAL COMPENSATION WALL
--
-- Lean has now sharpened the preferred literal high cut one final time.
-- Write r=t/16 and
--
--   E4_W(q) = r^4 * centeredZetaMuDiscrepancy t (t+r*q).
--
-- The exact centered Abel integrand satisfies
--
--   r^7 * centeredAbelIntegrand (t+r*q)
--     = normalizedOrdinateCosineD1(q) * E4_W(q).
--
-- This proves at theorem level that the four inverse powers missing between
-- the generic r^-2 centered N-mu scale and the quartic r^-6 target scale must
-- come from cancellation/sign in the centered discrepancy coordinate itself.
-- They cannot be manufactured by improving remote Fourier decay at the fixed
-- canonical q-boundary.
--
-- Lean also defines
--
--   quarticScaleFiniteCutCompensatedFar n = r^6 * F_n
--
-- and proves this is exactly
--
--   r^4 * normalizedFiniteCutCompensatedFar n.
--
-- Consequently the old PostSixthLiteralCompensationCut is equivalent to the
-- dimensionless quartic-scale inequality
--
--   |r^6 F_n| < r^6 * terminalResidualMargin.
--
-- The selected-literal high predicate is equivalent to a
-- selected-quartic-scale high predicate carrying this inequality, and above
-- one fixed high threshold that single predicate compiles directly to
-- contradiction.
--
-- All exhaustion/cofinality plumbing is already theorem-bearing: symmetric
-- centered Abel partials converge to -signedNMuPair, and the finite centered
-- completed residual converges to completedSignedResidual.  Thus no separate
-- exhaustion theorem remains on the preferred cut.
--
-- The ONLY preferred open analytic coordinate is the actual quartic-scale
-- compensated high inequality itself.  No pointwise r^-4 discrepancy bound is
-- claimed; the required theorem may be genuinely integrated/signed.
------------------------------------------------------------------------

data QuarticScaleCompensationCoordinate : Set where
  quarticScaleCenteredDiscrepancyCoordinate :
    QuarticScaleCompensationCoordinate
  centeredAbelIntegrandQuarticScaleIdentity :
    QuarticScaleCompensationCoordinate
  quarticScaleFiniteCutIdentity :
    QuarticScaleCompensationCoordinate
  literalCutQuarticScaleEquivalence :
    QuarticScaleCompensationCoordinate
  selectedQuarticScaleHighCutEquivalence :
    QuarticScaleCompensationCoordinate
  fixedHighQuarticScaleCutToContradiction :
    QuarticScaleCompensationCoordinate
  symmetricCenteredAbelExhaustion :
    QuarticScaleCompensationCoordinate
  quarticScaleCompensatedHighInequality :
    QuarticScaleCompensationCoordinate

quarticScaleCompensationStatus :
  QuarticScaleCompensationCoordinate -> V4H4Status
quarticScaleCompensationStatus quarticScaleCenteredDiscrepancyCoordinate =
  leanSourceWrittenDonor
quarticScaleCompensationStatus centeredAbelIntegrandQuarticScaleIdentity =
  leanSourceWrittenDonor
quarticScaleCompensationStatus quarticScaleFiniteCutIdentity =
  leanSourceWrittenDonor
quarticScaleCompensationStatus literalCutQuarticScaleEquivalence =
  leanSourceWrittenDonor
quarticScaleCompensationStatus selectedQuarticScaleHighCutEquivalence =
  leanSourceWrittenDonor
quarticScaleCompensationStatus fixedHighQuarticScaleCutToContradiction =
  leanSourceWrittenDonor
quarticScaleCompensationStatus symmetricCenteredAbelExhaustion =
  leanSourceWrittenDonor
quarticScaleCompensationStatus quarticScaleCompensatedHighInequality =
  openAnalyticObstruction

quarticScaleCompensatedHighInequalityIsOnlyPreferredOpenCoordinate :
  quarticScaleCompensationStatus quarticScaleCompensatedHighInequality
    ≡ openAnalyticObstruction
quarticScaleCompensatedHighInequalityIsOnlyPreferredOpenCoordinate = refl

quarticScaleCompensationLeanDonorHead : String
quarticScaleCompensationLeanDonorHead =
  "802a9b530899f2ab514ebc83bcfc73b2f3aa0733"

quarticScaleCompensationTransportedIntoAgdaKernelHere : Bool
quarticScaleCompensationTransportedIntoAgdaKernelHere = false

quarticScaleCompensationInterpretation : String
quarticScaleCompensationInterpretation =
  "The preferred RH min-cut is now dimensionless and literal. With r=t/16, Lean proves r^7 times the exact centered Abel integrand at t+r*q equals the normalized cosine derivative times r^4 times the centered N-mu discrepancy. It also proves the finite compensated remainder satisfies r^6*F_n = r^4*normalizedF_n, rewrites the literal high cut equivalently on this quartic scale, and compiles the selected quartic-scale high cut above one fixed threshold directly to contradiction. Symmetric centered-Abel exhaustion and convergence to the completed residual are already paid. The only preferred open analytic theorem is therefore the quartic-scale compensated high inequality itself; no pointwise r^-4 discrepancy estimate is asserted."


------------------------------------------------------------------------
-- ODD-PAIRING / LOCAL-V4 FAIL-FAST RECUT
--
-- Lean tested the highest-alpha structural idea suggested by the selected
-- quartic jet.
--
-- Exact facts now exposed:
--
--   C'_W(-q) = - C'_W(q).
--
-- With M2(W)=0 and M4(W)=-4*S(W),
--
--   C'_W(q)
--     = -(2/3) * S(W) * q^3 + R5_W(q),
--
-- where on |q| <= eta0
--
--   |R5_W(q)|
--     <= (1/100) * |q|^5 * M6_abs(W).
--
-- Note the sign: the cubic coefficient is NEGATIVE for q>0 because M4<0.
--
-- The quartic-scale centered discrepancy satisfies, for q>=0,
--
--   E4_W(q)-E4_W(-q)
--     = r^4 * D(t-rq,t+rq),
--
-- so odd pairing really sees one symmetric literal N-mu window.
--
-- The leading cubic pairing was then reduced exactly to the already-owned V4
-- coordinate.  For physical half-width h,
--
--   V4(t,h)
--     = h^4 * D(t-h,t+h)
--       - integral_{t-h}^{t+h} 4(x-t)^3 E_t(x) dx.
--
-- Therefore the cubic-leading selected correlation is precisely a scalar
-- multiple of
--
--   h^4 D(t-h,t+h) - V4(t,h).
--
-- This is a useful FAIL-FAST result: the cubic Taylor theorem is certified
-- only on |q|<=eta0, exactly the canonical local interval already removed by
-- finiteCutCompensatedFar.  It therefore sharpens the PAID local V4 lane, but
-- does not pay the remaining high complement.
--
-- Lean also pairs the full symmetric centered-Abel exhaustion globally:
--
--   leftAbel_n + rightAbel_n
--     = integral_0^n
--         Psi'_t(t+s) * D(t-s,t+s) ds.
--
-- Splitting at the canonical physical half-width gives exact local + outer
-- paired coordinates.  The finite centered G3 functional is
--
--   centeredCompletedResidualAt_n
--     = -(1/2) * localPaired
--       + ( -(1/2) * outerPaired_n + signedHorizontalRemainder ).
--
-- Hence the genuine remaining paired analytic object is
--
--   -(1/2) * outer paired symmetric N-mu correlation
--     + signed horizontal remainder.
--
-- No bound for that object is claimed.  The local cubic/V4 recut has been
-- tested and should not be expanded into a second proof programme.
------------------------------------------------------------------------

data OddPairedQuarticCoordinate : Set where
  normalizedD1Odd : OddPairedQuarticCoordinate
  normalizedD1CubicJet : OddPairedQuarticCoordinate
  normalizedD1QuinticBound : OddPairedQuarticCoordinate
  antisymmetricDiscrepancySymmetricWindow : OddPairedQuarticCoordinate
  centeredV4ExactRecut : OddPairedQuarticCoordinate
  cubicLeadingCorrelationV4Boundary : OddPairedQuarticCoordinate
  globalSymmetricAbelPairing : OddPairedQuarticCoordinate
  canonicalLocalOuterPairSplit : OddPairedQuarticCoordinate
  outerPairedHorizontalHighObject : OddPairedQuarticCoordinate
  outerPairedHorizontalHighEstimate : OddPairedQuarticCoordinate

oddPairedQuarticStatus :
  OddPairedQuarticCoordinate -> V4H4Status
oddPairedQuarticStatus normalizedD1Odd =
  leanSourceWrittenDonor
oddPairedQuarticStatus normalizedD1CubicJet =
  leanSourceWrittenDonor
oddPairedQuarticStatus normalizedD1QuinticBound =
  leanSourceWrittenDonor
oddPairedQuarticStatus antisymmetricDiscrepancySymmetricWindow =
  leanSourceWrittenDonor
oddPairedQuarticStatus centeredV4ExactRecut =
  leanSourceWrittenDonor
oddPairedQuarticStatus cubicLeadingCorrelationV4Boundary =
  leanSourceWrittenDonor
oddPairedQuarticStatus globalSymmetricAbelPairing =
  leanSourceWrittenDonor
oddPairedQuarticStatus canonicalLocalOuterPairSplit =
  leanSourceWrittenDonor
oddPairedQuarticStatus outerPairedHorizontalHighObject =
  leanSourceWrittenDonor
oddPairedQuarticStatus outerPairedHorizontalHighEstimate =
  openAnalyticObstruction

oddPairingLocalV4IsPaid :
  oddPairedQuarticStatus cubicLeadingCorrelationV4Boundary
    ≡ leanSourceWrittenDonor
oddPairingLocalV4IsPaid = refl

outerPairedHorizontalEstimateIsActualOpenWall :
  oddPairedQuarticStatus outerPairedHorizontalHighEstimate
    ≡ openAnalyticObstruction
outerPairedHorizontalEstimateIsActualOpenWall = refl

oddPairedQuarticLeanDonorHead : String
oddPairedQuarticLeanDonorHead =
  "da229d43def6891951c1ece4a5b009a6243789d0"

oddPairedQuarticTransportedIntoAgdaKernelHere : Bool
oddPairedQuarticTransportedIntoAgdaKernelHere = false

oddPairedQuarticInterpretation : String
oddPairedQuarticInterpretation =
  "Lean confirms the selected normalized cosine derivative is odd and has cubic jet -(2/3)S q^3 with a certified O(q^5 M6_abs) remainder on the canonical local interval. The antisymmetric quartic-scale centered discrepancy is exactly one symmetric N-mu window, and the leading cubic correlation reduces exactly to the existing V4 boundary-minus-moment coordinate. This is a fail-fast result rather than a closure: the Taylor regime is exactly the already-paid local interval. Globally, the symmetric Abel exhaustion pairs to Psi'_t(t+s) times D(t-s,t+s), which splits at the canonical radius into local plus outer pieces. The remaining analytic wall is the exact outer paired symmetric N-mu correlation combined with the same signed horizontal remainder."


------------------------------------------------------------------------
-- OUTER-PAIRED ASYMPTOTIC RECUT
--
-- Lean now recuts the finite outer paired+horizontal presentation onto the
-- already-owned manuscript far completed carrier.
--
-- For one centered-Abel exhaustion E, define the limiting outer object
--
--   OuterLimit(E)
--     = 1/2 * (-E.leftLimit - E.rightLimit
--              + canonicalLocalLeftAbel
--              + canonicalLocalRightAbel)
--       + signedHorizontalRemainder.
--
-- Lean proves exactly
--
--   OuterLimit(E)
--     = canonicalFarCompletedCompensation
--       + 1/2 * (canonicalLocalLeftBoundary
--                + canonicalLocalRightBoundary).
--
-- The selected ordinate test is even about t, so the boundary pair further
-- collapses to one symmetric literal N-mu window:
--
--   canonicalLocalLeftBoundary + canonicalLocalRightBoundary
--     =
--   signedOrdinateTest(t+h0)
--     * D(t-h0,t+h0).
--
-- Hence the asymptotic outer-paired object is not a second analytic invariant:
-- it is the manuscript far completed compensation plus one explicit symmetric
-- canonical boundary coordinate.
--
-- No sign or quantitative bound for that combined object is claimed.  A quick
-- audit of the existing cutset found no theorem making the full off-ordinate
-- outer pair kernel nonpositive.  The localized bidi prime positivity lane
-- also remains firewalled from this same-object outer carrier and is not
-- reopened.
------------------------------------------------------------------------

data OuterPairedAsymptoticCoordinate : Set where
  outerPairedLimitCarrier : OuterPairedAsymptoticCoordinate
  outerLimitToCanonicalFarBoundary : OuterPairedAsymptoticCoordinate
  canonicalBoundaryPairSymmetricWindow : OuterPairedAsymptoticCoordinate
  outerLimitFarPlusSymmetricBoundary : OuterPairedAsymptoticCoordinate
  outerFarBoundaryHighEstimate : OuterPairedAsymptoticCoordinate

outerPairedAsymptoticStatus :
  OuterPairedAsymptoticCoordinate -> V4H4Status
outerPairedAsymptoticStatus outerPairedLimitCarrier =
  leanSourceWrittenDonor
outerPairedAsymptoticStatus outerLimitToCanonicalFarBoundary =
  leanSourceWrittenDonor
outerPairedAsymptoticStatus canonicalBoundaryPairSymmetricWindow =
  leanSourceWrittenDonor
outerPairedAsymptoticStatus outerLimitFarPlusSymmetricBoundary =
  leanSourceWrittenDonor
outerPairedAsymptoticStatus outerFarBoundaryHighEstimate =
  openAnalyticObstruction

outerLimitFarBoundaryRecutIsSourceWritten :
  outerPairedAsymptoticStatus outerLimitFarPlusSymmetricBoundary
    ≡ leanSourceWrittenDonor
outerLimitFarBoundaryRecutIsSourceWritten = refl

outerFarBoundaryHighEstimateRemainsOpen :
  outerPairedAsymptoticStatus outerFarBoundaryHighEstimate
    ≡ openAnalyticObstruction
outerFarBoundaryHighEstimateRemainsOpen = refl

outerPairedAsymptoticLeanDonorHead : String
outerPairedAsymptoticLeanDonorHead =
  "9edf85124ba69024b9f7637245cd3317a49bfaf9"

outerPairedAsymptoticTransportedIntoAgdaKernelHere : Bool
outerPairedAsymptoticTransportedIntoAgdaKernelHere = false

outerPairedAsymptoticInterpretation : String
outerPairedAsymptoticInterpretation =
  "The global odd-paired high carrier has now been recut back onto the manuscript same-object far coordinate. Lean source-writes that the exhausted outer paired symmetric N-mu correlation plus signed horizontal remainder equals canonicalFarCompletedCompensation plus one half of the two canonical Abel boundary terms, and then collapses those two boundaries to signedOrdinateTest(t+h0) times the single symmetric discrepancy D(t-h0,t+h0). Thus there is no second outer analytic invariant and no remaining representation seam here. The preferred open theorem is a signed quantitative estimate for this exact far-plus-symmetric-boundary object strong enough to close the quartic-scale terminal margin. No global outer pair-kernel sign and no same-object prime identification is currently claimed."


------------------------------------------------------------------------
-- FIXED COUPLED SIGNED HIGH SCALAR
--
-- Lean has now removed two accidental strengthenings from the preferred
-- high-ordinate cut.
--
-- (1) The terminal G3 compiler needs only the ONE-SIDED inequality
--
--       F_n < terminalResidualMargin,
--
--     not
--
--       |F_n| < terminalResidualMargin.
--
--     The older absolute-value predicate remains a valid sufficient condition
--     but is no longer the Clay-facing min-cut.
--
-- (2) The finite local literal source is exactly stable once the centered
--     exhaustion radius n exceeds the canonical physical local half-width h0.
--     This is proved directly from
--
--       rho in centeredZeroFinset(t,n)
--         iff t-n < Im(rho) <= t+n
--
--     and the CLOSED local predicate |q| <= eta0.  A possible zero exactly at
--     t-h0 is therefore retained; no generic-position or endpoint deletion is
--     used.
--
-- The previously exposed asymptotic coupled carrier
--
--   C_far =
--     canonicalFarCompletedCompensation
--       + 1/2 * Psi_t(t+h0) * D(t-h0,t+h0)
--
-- is exhaustion-independent and satisfies
--
--   C_far
--     = completedSignedResidual - canonicalLocalPairedContribution.
--
-- Lean exposes the exact local bookkeeping correction
--
--   Lcorr_n =
--     1/2 * literalLocalExactAt(eta0,n)
--       - canonicalLocalPairedContribution,
--
-- so
--
--   finiteCutCompensatedFar(n) = C_far - Lcorr_n.
--
-- It further expands
--
--   Lcorr_n
--     = 1/2 *
--       ( literalLocalPairMinusBaseAt(n)
--         + canonicalLocalMuPair
--         + Psi_t(t+h0) * D(t-h0,t+h0) ).
--
-- Because literalLocalExactAt stabilizes for n>h0, Lcorr_n also stabilizes.
-- Lean packages that unique stable value as
--
--   canonicalLiteralVsPairedLocalCorrection.
--
-- Therefore the preferred terminal high hypothesis is now ONE FIXED SIGNED
-- SCALAR inequality:
--
--   C_far - canonicalLiteralVsPairedLocalCorrection
--     < terminalResidualMargin.
--
-- No existential exhaustion index and no absolute value remain.
--
-- The selected fixed-coupled high predicate compiles, above one fixed high
-- threshold, directly to contradiction through the already-paid V4 and
-- selected-M6 stack.
--
-- This is still only a representation/min-cut sharpening.  Lean does NOT prove
-- the fixed signed scalar inequality itself.
------------------------------------------------------------------------

data FixedCoupledSignedHighCoordinate : Set where
  oneSidedFiniteCompensationCut :
    FixedCoupledSignedHighCoordinate
  oneSidedCutToG3 :
    FixedCoupledSignedHighCoordinate
  farBoundaryCoupledCarrier :
    FixedCoupledSignedHighCoordinate
  farBoundaryCarrierExhaustionIndependent :
    FixedCoupledSignedHighCoordinate
  farNMuZeroMinusMuComplement :
    FixedCoupledSignedHighCoordinate
  pairedVsLiteralLocalCorrection :
    FixedCoupledSignedHighCoordinate
  closedLocalFiniteStabilization :
    FixedCoupledSignedHighCoordinate
  fixedCanonicalLocalCorrection :
    FixedCoupledSignedHighCoordinate
  fixedCoupledCutEquivalence :
    FixedCoupledSignedHighCoordinate
  selectedFixedCoupledCutToContradiction :
    FixedCoupledSignedHighCoordinate
  fixedCoupledSignedHighInequality :
    FixedCoupledSignedHighCoordinate

fixedCoupledSignedHighStatus :
  FixedCoupledSignedHighCoordinate -> V4H4Status
fixedCoupledSignedHighStatus oneSidedFiniteCompensationCut =
  leanSourceWrittenDonor
fixedCoupledSignedHighStatus oneSidedCutToG3 =
  leanSourceWrittenDonor
fixedCoupledSignedHighStatus farBoundaryCoupledCarrier =
  leanSourceWrittenDonor
fixedCoupledSignedHighStatus farBoundaryCarrierExhaustionIndependent =
  leanSourceWrittenDonor
fixedCoupledSignedHighStatus farNMuZeroMinusMuComplement =
  leanSourceWrittenDonor
fixedCoupledSignedHighStatus pairedVsLiteralLocalCorrection =
  leanSourceWrittenDonor
fixedCoupledSignedHighStatus closedLocalFiniteStabilization =
  leanSourceWrittenDonor
fixedCoupledSignedHighStatus fixedCanonicalLocalCorrection =
  leanSourceWrittenDonor
fixedCoupledSignedHighStatus fixedCoupledCutEquivalence =
  leanSourceWrittenDonor
fixedCoupledSignedHighStatus selectedFixedCoupledCutToContradiction =
  leanSourceWrittenDonor
fixedCoupledSignedHighStatus fixedCoupledSignedHighInequality =
  openAnalyticObstruction

absoluteValueTaxRemoved :
  fixedCoupledSignedHighStatus oneSidedFiniteCompensationCut
    ≡ leanSourceWrittenDonor
absoluteValueTaxRemoved = refl

fixedCoupledHighInequalityRemainsOpen :
  fixedCoupledSignedHighStatus fixedCoupledSignedHighInequality
    ≡ openAnalyticObstruction
fixedCoupledHighInequalityRemainsOpen = refl

fixedCoupledSignedHighLeanDonorHead : String
fixedCoupledSignedHighLeanDonorHead =
  "4ca0b32c20304301e9a4c7cb00dac990f00bed06"

fixedCoupledSignedHighTransportedIntoAgdaKernelHere : Bool
fixedCoupledSignedHighTransportedIntoAgdaKernelHere = false

fixedCoupledSignedHighInterpretation : String
fixedCoupledSignedHighInterpretation =
  "The preferred RH high cut is now one fixed signed scalar inequality. Lean removes the unnecessary absolute value from the finite compensation predicate, proves the closed canonical local literal source stabilizes exactly for every centered exhaustion radius n>h0 including the possible left-endpoint atom, exposes the exact correction between the paired-Abel local subtraction and the literal local pair subtraction, and collapses the resulting fixed carrier to the canonical literal scalar H_W = one half times [global off-ordinate signed literal pair-source tsum minus canonical stabilized local literal source minus the full theorem-bearing mu/Gamma ordinate integral]. Thus no exhaustion index, Abel boundary, far surrogate, or absolute value remains in the preferred theorem interface. The selected canonical signed high predicate compiles directly to contradiction. The only new mathematics still open is the one-sided quantitative bound H_W < terminalResidualMargin; no Agda-native replay is claimed."


------------------------------------------------------------------------
-- CANONICAL LITERAL FAR TSUM RECUT
--
-- Lean removes the last global-minus-local bookkeeping subtraction from the
-- preferred fixed high scalar.
--
-- The canonical local indicator is finitely supported inside the canonical
-- centered exhaustion finset.  The global off-ordinate source is already
-- summable.  Hence the exact pointwise partition
--
--   literalOffOrdSource
--     = canonicalLocalExactTerm + canonicalFarExactTerm
--
-- sums to
--
--   global off-ordinate pair source
--     = canonicalLiteralLocalExact
--       + canonicalLiteralFarPairSource.
--
-- Substituting this into the fixed scalar cancels the stabilized local term
-- exactly and gives
--
--   H_W
--     = 1/2 *
--       ( canonicalLiteralFarPairSource
--         - integral Psi_t(x) mu(x) dx ).
--
-- Thus the preferred analytic theorem is now literally a one-sided estimate
-- for the signed canonical-far zero source against the exact theorem-bearing
-- mu/Gamma pairing.  There is no exhaustion variable, no Abel boundary term,
-- no global-minus-local subtraction, and no absolute value in the interface.
--
-- Reapplying the short-support explicit formula does not close this theorem:
-- the no-prime and signed-pole-cancellation facts are already consumed in the
-- identity completedSignedResidual = combinedCluster.  Using that identity
-- again only cycles back to the target cluster inequality.
------------------------------------------------------------------------

data CanonicalLiteralFarTsumCoordinate : Set where
  canonicalLocalIndicatorSummable :
    CanonicalLiteralFarTsumCoordinate
  canonicalLocalIndicatorTsumStable :
    CanonicalLiteralFarTsumCoordinate
  canonicalFarIndicatorSummable :
    CanonicalLiteralFarTsumCoordinate
  globalOffOrdLocalFarTsumSplit :
    CanonicalLiteralFarTsumCoordinate
  signedPairSourceLocalFarTsumSplit :
    CanonicalLiteralFarTsumCoordinate
  fixedHighResidualLiteralFarNormalForm :
    CanonicalLiteralFarTsumCoordinate
  literalFarHighCutEquivalence :
    CanonicalLiteralFarTsumCoordinate
  literalFarSignedHighEstimate :
    CanonicalLiteralFarTsumCoordinate

canonicalLiteralFarTsumStatus :
  CanonicalLiteralFarTsumCoordinate -> V4H4Status
canonicalLiteralFarTsumStatus canonicalLocalIndicatorSummable =
  leanSourceWrittenDonor
canonicalLiteralFarTsumStatus canonicalLocalIndicatorTsumStable =
  leanSourceWrittenDonor
canonicalLiteralFarTsumStatus canonicalFarIndicatorSummable =
  leanSourceWrittenDonor
canonicalLiteralFarTsumStatus globalOffOrdLocalFarTsumSplit =
  leanSourceWrittenDonor
canonicalLiteralFarTsumStatus signedPairSourceLocalFarTsumSplit =
  leanSourceWrittenDonor
canonicalLiteralFarTsumStatus fixedHighResidualLiteralFarNormalForm =
  leanSourceWrittenDonor
canonicalLiteralFarTsumStatus literalFarHighCutEquivalence =
  leanSourceWrittenDonor
canonicalLiteralFarTsumStatus literalFarSignedHighEstimate =
  openAnalyticObstruction

canonicalLiteralFarNormalFormIsSourceWritten :
  canonicalLiteralFarTsumStatus fixedHighResidualLiteralFarNormalForm
    ≡ leanSourceWrittenDonor
canonicalLiteralFarNormalFormIsSourceWritten = refl

literalFarSignedHighEstimateRemainsOpen :
  canonicalLiteralFarTsumStatus literalFarSignedHighEstimate
    ≡ openAnalyticObstruction
literalFarSignedHighEstimateRemainsOpen = refl

canonicalLiteralFarTsumLeanDonorHead : String
canonicalLiteralFarTsumLeanDonorHead =
  "7bd411fd598177d075fefdc45be1abaecf6cc020"

canonicalLiteralFarTsumTransportedIntoAgdaKernelHere : Bool
canonicalLiteralFarTsumTransportedIntoAgdaKernelHere = false

canonicalLiteralFarTsumInterpretation : String
canonicalLiteralFarTsumInterpretation =
  "Lean source-writes the exact summable partition of the global off-ordinate literal pair source into the stabilized canonical local term plus one canonical far indicator tsum, then cancels the local term from the preferred fixed high scalar. The Clay-facing high coordinate is therefore H_W = (1/2)*(canonicalLiteralFarPairSource - integral Psi_t*mu). This is a signed one-sided theorem on the literal far zero carrier itself: no finite exhaustion index, Abel boundary, global-minus-local syntax, or absolute value remains. The short-support/no-prime and pole-cancellation explicit-formula identities are already consumed downstream and do not independently prove this strict estimate."


------------------------------------------------------------------------
-- CANONICAL FAR TSUM / ABSOLUTE-SHELL SCALE AUDIT
--
-- Lean now closes the finite-to-global seam for the literal canonical far
-- carrier:
--
--   literalFarExactAt(eta0,n)
--     -> canonicalLiteralFarPairSource
--
-- under centered exhaustion, by summability of the exact canonical-far
-- indicator.
--
-- Consequently the already-existing finite shell estimate transports to the
-- SAME global carrier:
--
--   |canonicalLiteralFarPairSource|
--     <= (signedOrdinateCurvature + CH)
--          * farShellBound(A,|t|,floor(t/2000))
--
-- whenever the existing horizontal-curvature hypothesis CH is supplied.
--
-- This is deliberately NOT promoted as the preferred high proof.  The shell
-- majorant itself contains the nonnegative term
--
--   72*A / sqrt(J),
--
-- so at the canonical linear cutoff J~t it carries only a t^(-1/2)-scale
-- component before witness curvature factors.  This is an audit of the
-- available absolute envelope, not a lower bound on the true signed far
-- source.  It confirms that constant optimization inside the absolute shell
-- route cannot manufacture the quartic t^(-6) cancellation required by the
-- terminal high inequality.
--
-- The preferred open object therefore remains the SIGNED scalar
--
--   (1/2) *
--   ( canonicalLiteralFarPairSource
--     - integral Psi_t * mu ),
--
-- with the two terms kept coupled.
------------------------------------------------------------------------

data CanonicalFarShellAuditCoordinate : Set where
  canonicalFarFiniteToTsum :
    CanonicalFarShellAuditCoordinate
  canonicalFarGlobalAbsoluteShellBound :
    CanonicalFarShellAuditCoordinate
  absoluteShellSqrtTermAudit :
    CanonicalFarShellAuditCoordinate
  signedFarMinusMuCancellation :
    CanonicalFarShellAuditCoordinate

canonicalFarShellAuditStatus :
  CanonicalFarShellAuditCoordinate -> V4H4Status
canonicalFarShellAuditStatus canonicalFarFiniteToTsum =
  leanSourceWrittenDonor
canonicalFarShellAuditStatus canonicalFarGlobalAbsoluteShellBound =
  leanSourceWrittenDonor
canonicalFarShellAuditStatus absoluteShellSqrtTermAudit =
  leanSourceWrittenDonor
canonicalFarShellAuditStatus signedFarMinusMuCancellation =
  openAnalyticObstruction

absoluteShellRouteIsAuditedNotPreferred :
  canonicalFarShellAuditStatus absoluteShellSqrtTermAudit
    ≡ leanSourceWrittenDonor
absoluteShellRouteIsAuditedNotPreferred = refl

signedFarMinusMuCancellationRemainsOpen :
  canonicalFarShellAuditStatus signedFarMinusMuCancellation
    ≡ openAnalyticObstruction
signedFarMinusMuCancellationRemainsOpen = refl

canonicalFarShellAuditLeanDonorHead : String
canonicalFarShellAuditLeanDonorHead =
  "42c7455acafb166802435c8ad20c94dee6b0832d"

canonicalFarShellAuditTransportedIntoAgdaKernelHere : Bool
canonicalFarShellAuditTransportedIntoAgdaKernelHere = false

canonicalFarShellAuditInterpretation : String
canonicalFarShellAuditInterpretation =
  "Lean transports the existing finite literal-far shell estimates to the exact global canonicalLiteralFarPairSource tsum and audits the scale of that absolute envelope. The shell majorant contains 72*A/sqrt(J); at the canonical linear cutoff this is only a t^(-1/2)-scale envelope component, so the absolute shell route is retained only as a fail-fast audit. The preferred theorem remains the one-sided signed cancellation between the canonical far pair-source tsum and the full theorem-bearing mu/Gamma ordinate integral."


------------------------------------------------------------------------
-- LITERAL FAR-MINUS-MU IS THE FINAL HIGH-ZERO THEOREM
--
-- Lean now states the remaining analytic obligation directly, without any
-- internal compensation alias:
--
--   (1/2) *
--   ( canonicalLiteralFarPairSource
--     - integral Psi_t(x) * mu(x) dx )
--     < postSixthTerminalResidualMargin.
--
-- It also proves that, under the already-paid selected witness conditions
-- (target-strength floor, signed M6 window, positive quantitative target band,
-- and the canonical V4 error coordinate), this literal inequality is
-- equivalent to the selected canonical signed high cut consumed by the
-- contradiction compiler.
--
-- Therefore a uniform proof of this signed cancellation for every hypothetical
-- off-line zero above the fixed high cutoff eliminates the remaining high-zero
-- case.  This is not a representation lemma still waiting to be unfolded; it
-- is the actual open RH analytic theorem on this route.
------------------------------------------------------------------------

data LiteralFarMinusMuFinalHighCoordinate : Set where
  literalFarMinusMuSelectedCut :
    LiteralFarMinusMuFinalHighCoordinate
  literalFarMinusMuSelectedCutIffCanonical :
    LiteralFarMinusMuFinalHighCoordinate
  literalFarMinusMuCompilesHighContradiction :
    LiteralFarMinusMuFinalHighCoordinate
  literalFarMinusMuUniformEstimate :
    LiteralFarMinusMuFinalHighCoordinate

literalFarMinusMuFinalHighStatus :
  LiteralFarMinusMuFinalHighCoordinate -> V4H4Status
literalFarMinusMuFinalHighStatus literalFarMinusMuSelectedCut =
  leanSourceWrittenDonor
literalFarMinusMuFinalHighStatus literalFarMinusMuSelectedCutIffCanonical =
  leanSourceWrittenDonor
literalFarMinusMuFinalHighStatus literalFarMinusMuCompilesHighContradiction =
  leanSourceWrittenDonor
literalFarMinusMuFinalHighStatus literalFarMinusMuUniformEstimate =
  openAnalyticObstruction

literalFarMinusMuCompilerIsSourceWritten :
  literalFarMinusMuFinalHighStatus literalFarMinusMuCompilesHighContradiction
    ≡ leanSourceWrittenDonor
literalFarMinusMuCompilerIsSourceWritten = refl

literalFarMinusMuUniformEstimateRemainsOpen :
  literalFarMinusMuFinalHighStatus literalFarMinusMuUniformEstimate
    ≡ openAnalyticObstruction
literalFarMinusMuUniformEstimateRemainsOpen = refl

literalFarMinusMuFinalHighLeanDonorHead : String
literalFarMinusMuFinalHighLeanDonorHead =
  "a59dceb90cdc47748a86ab119b9ce22bb2f103b8"

literalFarMinusMuFinalHighTransportedIntoAgdaKernelHere : Bool
literalFarMinusMuFinalHighTransportedIntoAgdaKernelHere = false

literalFarMinusMuFinalHighInterpretation : String
literalFarMinusMuFinalHighInterpretation =
  "The RH min-cut is now exact. Lean defines the selected literal far-minus-mu high cut using only the canonical far literal pair-source tsum, the full theorem-bearing signed ordinate mu integral, and the terminal residual margin. It source-proves this selected literal statement equivalent to the previously compiled canonical signed high cut and proves that the selected literal statement excludes every hypothetical off-line zero above the fixed high cutoff. Thus the remaining task is not further bookkeeping: it is a uniform one-sided signed cancellation theorem for (1/2)*(Far_W - integral Psi_t*mu). No proof of that new analytic theorem is claimed here."


------------------------------------------------------------------------
-- UNIFORM LITERAL FAR-MINUS-MU HIGH THEOREM
--
-- Lean now packages the remaining analytic obligation at its natural global
-- quantifier level:
--
--   LiteralFarMinusMuUniformHighEstimate(CV,T)
--
-- meaning that for every t>T and every hypothetical off-line zero rho at
-- height t, there exists the already-certified selected witness W satisfying
-- the strength/M6/target-band package and
--
--   (1/2) *
--   ( canonicalLiteralFarPairSource(W)
--     - integral Psi_t * mu )
--     < terminalResidualMargin(W,rho,CV,t).
--
-- Source-written consequences:
--
-- 1. Uniform estimate -> no off-line zero above T.
--
-- 2. Any actual high off-line zero -> failure of the uniform estimate.
--
-- 3. More sharply, combining selected-witness existence with the contradiction
--    compiler gives a counterexample rigidity inequality: every hypothetical
--    high off-line zero carries a concrete selected W for which
--
--      terminalResidualMargin
--        <= (1/2) * (canonical far source - integral Psi_t*mu).
--
-- No positivity of terminalResidualMargin is claimed independently; that
-- margin subtracts the entire local V4/M6/M8 budget and its sign is part of
-- the genuine terminal analysis.
--
-- This is the correct final RH-facing theorem interface.  The uniform signed
-- estimate itself remains open.
------------------------------------------------------------------------

data UniformLiteralFarMinusMuCoordinate : Set where
  counterexampleForcesFarMinusMuLowerBound :
    UniformLiteralFarMinusMuCoordinate
  uniformLiteralFarMinusMuEstimate :
    UniformLiteralFarMinusMuCoordinate
  uniformEstimateExcludesHighOffLine :
    UniformLiteralFarMinusMuCoordinate
  highOffLineForcesUniformEstimateFailure :
    UniformLiteralFarMinusMuCoordinate

uniformLiteralFarMinusMuStatus :
  UniformLiteralFarMinusMuCoordinate -> V4H4Status
uniformLiteralFarMinusMuStatus counterexampleForcesFarMinusMuLowerBound =
  leanSourceWrittenDonor
uniformLiteralFarMinusMuStatus uniformLiteralFarMinusMuEstimate =
  openAnalyticObstruction
uniformLiteralFarMinusMuStatus uniformEstimateExcludesHighOffLine =
  leanSourceWrittenDonor
uniformLiteralFarMinusMuStatus highOffLineForcesUniformEstimateFailure =
  leanSourceWrittenDonor

counterexampleRigidityIsSourceWritten :
  uniformLiteralFarMinusMuStatus counterexampleForcesFarMinusMuLowerBound
    ≡ leanSourceWrittenDonor
counterexampleRigidityIsSourceWritten = refl

uniformLiteralFarMinusMuEstimateRemainsOpen :
  uniformLiteralFarMinusMuStatus uniformLiteralFarMinusMuEstimate
    ≡ openAnalyticObstruction
uniformLiteralFarMinusMuEstimateRemainsOpen = refl

uniformLiteralFarMinusMuLeanDonorHead : String
uniformLiteralFarMinusMuLeanDonorHead =
  "99cfb2a23720d28874ea1b01cc106a64940d5089"

uniformLiteralFarMinusMuTransportedIntoAgdaKernelHere : Bool
uniformLiteralFarMinusMuTransportedIntoAgdaKernelHere = false

uniformLiteralFarMinusMuInterpretation : String
uniformLiteralFarMinusMuInterpretation =
  "Lean now packages the final high-ordinate RH obligation as one uniform selected-witness theorem: above one fixed cutoff, every hypothetical off-line zero must admit a selected four-window witness whose signed canonical far literal pair-source tsum minus the full theorem-bearing mu integral lies strictly below the terminal residual margin. Lean source-proves that this uniform estimate excludes all high off-line zeros, and conversely any such zero forces failure of the estimate. It also proves a counterexample rigidity lower bound: a hypothetical off-line zero forces the same selected witness scalar to be at least the terminal margin. No independent positivity of that margin is asserted. The uniform signed far-minus-mu estimate itself remains the open analytic theorem."


------------------------------------------------------------------------
-- DE-VACUIFIED AMBIENT HIGH THEOREM + EXACT PT THRESHOLD CLOSURE
--
-- The zero-specific terminal margin depends on rho only through:
--
--   a = heightOf rho
--   m = mult rho
--
-- via
--
--   combinedZeroHeightDefect(rho)
--     = m * physicalCombinedHeightDefect(a).
--
-- Lean now exposes the ambient margin
--
--   ambientMargin(W,m,a,EV)
--     = 2*m*physicalCombinedHeightDefect_W(a)
--       - (1/2)*postSixthTerminalLocalM6Budget_W(EV).
--
-- On the selected target band, for
--
--   0 < |a| <= 1/2,
--
-- the physical combined height defect is strictly positive, hence the ambient
-- margin is monotone increasing in m.  Therefore multiplicity one is the
-- hardest ambient case.
--
-- Preferred independent analytic target:
--
--   for every t above the final low/high cutoff and every real strip
--   displacement 0<|a|<=1/2, construct the selected W with
--
--     (1/2)*(canonicalLiteralFarPairSource(W) - integral Psi_t*mu)
--       < ambientMargin(W,1,a,CV,t).
--
-- This theorem is genuinely de-vacuified: its parameter domain exists
-- independently of whether an off-line zero exists.  Lean source-proves that
-- it implies the previous zero-quantified uniform high estimate.
--
-- PT seam:
--
-- The arbitrary-endpoint RvM proof previously consumed existential
-- backlund_horizontal, introducing an opaque threshold TB.  The imported
-- Zeta23 source already has explicit backlund_horizontal_at valid from T>=4.
-- Lean now consumes that explicit theorem, exposing:
--
--   arbitrary endpoint discrepancy cutoff A >= 5
--   V4 discrepancy left-end cutoff t-r >= 5.
--
-- Since the canonical local radius satisfies r<t/16, every
--
--   t > quarticPlattTrudgianCutoff
--
-- has t-r > 5.  The final literal far-minus-mu contradiction compiler is now
-- source-written with EXACT high threshold quarticPlattTrudgianCutoff.
-- There is no finite PT<t<=T middle band left in this route.
------------------------------------------------------------------------

data AmbientFarMinusMuCoordinate : Set where
  ambientMarginExactCoordinate :
    AmbientFarMinusMuCoordinate
  ambientHeightDefectPositiveOnStrip :
    AmbientFarMinusMuCoordinate
  ambientMarginMonotoneMultiplicity :
    AmbientFarMinusMuCoordinate
  ambientSimpleMultiplicityEstimate :
    AmbientFarMinusMuCoordinate
  ambientSimpleEstimateImpliesZeroUniform :
    AmbientFarMinusMuCoordinate
  explicitBacklundCutoffFour :
    AmbientFarMinusMuCoordinate
  arbitraryEndpointRvMCutoffFive :
    AmbientFarMinusMuCoordinate
  quarticV4CutoffFive :
    AmbientFarMinusMuCoordinate
  PTExactlyCompilesLiteralFarMinusMu :
    AmbientFarMinusMuCoordinate
  PTAmbientEstimateExcludesOffLine :
    AmbientFarMinusMuCoordinate

ambientFarMinusMuStatus :
  AmbientFarMinusMuCoordinate -> V4H4Status
ambientFarMinusMuStatus ambientMarginExactCoordinate =
  leanSourceWrittenDonor
ambientFarMinusMuStatus ambientHeightDefectPositiveOnStrip =
  leanSourceWrittenDonor
ambientFarMinusMuStatus ambientMarginMonotoneMultiplicity =
  leanSourceWrittenDonor
ambientFarMinusMuStatus ambientSimpleMultiplicityEstimate =
  openAnalyticObstruction
ambientFarMinusMuStatus ambientSimpleEstimateImpliesZeroUniform =
  leanSourceWrittenDonor
ambientFarMinusMuStatus explicitBacklundCutoffFour =
  leanSourceWrittenDonor
ambientFarMinusMuStatus arbitraryEndpointRvMCutoffFive =
  leanSourceWrittenDonor
ambientFarMinusMuStatus quarticV4CutoffFive =
  leanSourceWrittenDonor
ambientFarMinusMuStatus PTExactlyCompilesLiteralFarMinusMu =
  leanSourceWrittenDonor
ambientFarMinusMuStatus PTAmbientEstimateExcludesOffLine =
  leanSourceWrittenDonor

ambientSimpleMultiplicityEstimateIsPreferredOpenTheorem :
  ambientFarMinusMuStatus ambientSimpleMultiplicityEstimate
    ≡ openAnalyticObstruction
ambientSimpleMultiplicityEstimateIsPreferredOpenTheorem = refl

PTMiddleBandIsClosed :
  ambientFarMinusMuStatus PTExactlyCompilesLiteralFarMinusMu
    ≡ leanSourceWrittenDonor
PTMiddleBandIsClosed = refl

ambientFarMinusMuLeanDonorHead : String
ambientFarMinusMuLeanDonorHead =
  "014363d094d6f53e8c936ed1c89d88642d6aac79"

ambientFarMinusMuTransportedIntoAgdaKernelHere : Bool
ambientFarMinusMuTransportedIntoAgdaKernelHere = false

ambientFarMinusMuInterpretation : String
ambientFarMinusMuInterpretation =
  "The preferred RH analytic frontier is now de-vacuified. Lean factors the terminal margin through ambient horizontal displacement a and multiplicity m, proves the selected physical height defect positive on 0<|a|<=1/2, and proves the margin monotone in m, reducing the hardest ambient theorem to multiplicity one. A uniform ambient theorem over all real strip displacements would imply the earlier zero-quantified far-minus-mu estimate and hence exclude off-line zeros. Separately, Lean replaces the opaque existential Backlund threshold by the imported explicit Backlund theorem valid from 4, derives arbitrary-endpoint RvM and quartic V4 cutoffs at 5, and proves the literal far-minus-mu contradiction compiler starts exactly above the Platt-Trudgian cutoff. The PT-to-final-T middle-band seam is therefore closed. The ambient multiplicity-one signed far-minus-mu estimate remains open."
