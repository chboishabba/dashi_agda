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
