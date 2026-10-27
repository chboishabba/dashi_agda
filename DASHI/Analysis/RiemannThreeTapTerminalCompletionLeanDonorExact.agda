module DASHI.Analysis.RiemannThreeTapTerminalCompletionLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannQuarticSignedPoleFourierTerminalLeanDonorExact as Terminal
import DASHI.Analysis.RiemannThreeTapCurrentLeanFrontierExact as Current

------------------------------------------------------------------------
-- RH THREE-TAP TERMINAL COMPLETION DONOR
--
-- Lean companion branch:
--   chboishabba/dashi_lean4
--   agent/rh-marked-cluster-target-reflection
--
-- New source-written owners:
--
--   RiemannSelectedPrimeSensitiveThreeTapTerminalTest.lean
--   RiemannSelectedPrimeSensitiveThreeTapTargetMoment.lean
--   RiemannSelectedPrimeSensitiveSymmetricShiftMoments.lean
--
-- The terminal scalar is now explicit:
--
--   M = 2*target - completedExternal - 1/2*localSlack.
--
-- The transformed same-ordinate height defect is exactly quadratic in the
-- tap strength epsilon.  The physical three-tap deformation also has an
-- exact normalized-profile representation:
--
--   T_{eps,L}(G(r*u))
--     = (T_{eps,rL} G)(r*u).
--
-- Hence the fixed physical arithmetic shift L=log 2 becomes the normalized
-- displacement
--
--   B(t) = (t/16)*log 2.
--
-- Lean proves that for t>=200,
--
--   pi+1 < B(t).
--
-- Therefore the original selected profile support bound |v|<pi+1, and the
-- M6/M8 Taylor constants derived from it, cannot simply be reused after the
-- deformation.  A new transformed local budget is mathematically required.
--
-- Agda records the exact cross-language cutset.  It does not manufacture the
-- missing real-analysis estimate or claim RH.
------------------------------------------------------------------------

record ThreeTapTerminalCompletionReceipt : Set where
  constructor three-tap-terminal-completion-receipt
  field
    repository : String
    branch : String

    terminalPath : String
    targetPath : String
    momentsPath : String

    terminalFormattingFixCommit : String
    targetPolynomialCommit : String
    momentTransportCommit : String
    normalizedWeldCommit : String
    supportAndTargetWeldCommit : String
    transformedLocalBudgetCommit : String
    terminalizedCommit : String
    signedFifthBridgeCommit : String
    nearLineCoordinateCommit : String
    normalizedProjectiveCommit : String
    adaptiveRemainderCommit : String
    j2PolynomialCommit : String
    adaptiveMixedCommit : String
    j2PhaseCommit : String
    j2NormalizedCommit : String
    adaptiveJetCommit : String
    adaptiveLocalDebtCommit : String
    adaptiveOffOrdWeldCommit : String
    adaptiveTerminalCommit : String
    adaptiveGlobalCommit : String
    workflowCommit : String

open ThreeTapTerminalCompletionReceipt public

currentThreeTapTerminalCompletionReceipt :
  ThreeTapTerminalCompletionReceipt
currentThreeTapTerminalCompletionReceipt =
  three-tap-terminal-completion-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-marked-cluster-target-reflection"

    "Synthesis/RiemannSelectedPrimeSensitiveThreeTapTerminalTest.lean"
    "Synthesis/RiemannSelectedPrimeSensitiveThreeTapTargetMoment.lean"
    "Synthesis/RiemannSelectedPrimeSensitiveSymmetricShiftMoments.lean"

    "bad786d931da51de582400732d0ddeca8c800795"
    "9d6a021a67781d5bf0b7c4a0f24617c0f6f82637"
    "bdd6faebaa8d5a45e5e39e8c69694cb7978b2c2d"
    "a2a5a0cac5f88f8320247c6cb11c2e0c33b46a4d"
    "55fc6436fd750820a2e12c16f3247be627760657"
    "a027fa0f0a6c40f242e1a927416bc65ec4d66236"
    "423150cc363d74aa695af18b11958f3f7b6a5741"
    "29169957eadb1c6d77f027c3f03926c6a29b0152"
    "6edfed016c24ce1296e00950d052b0a09e9036ec"
    "5138969d1f7385ce3c1ea4fbdb51957c81655b6d"
    "93d7b8e50c18e13976c0739c840e31d923ea8b64"
    "8fb6c46dfb650a5765aa83632aeea96c8459d413"
    "18e7dcc3af7bd8dd8c9852fa1854bb8c898b1b03"
    "1e860f3f4588fea7d740e6569c95f475345dc46a"
    "65ade7a857a2523a8cd4bd73a55ae7178f7ebe03"
    "adf01fa75f7997caa745b0567d084792abe94f9b"
    "9c6ffd83f988b18056c5c030b019f85066ebe1e8"
    "440aab000cfe718b1014fe36c59a3a37ef0e362f"
    "a31c6567f496dcebec3a451dca9c31529a3f97af"
    "1254da6de2c7f4563fc9ea1b09c0f79f0c52530c"
    "cdc3de715dadf2697071a0f77d519ada777c7a22"

record ThreeTapTerminalCompletionBoundary : Set where
  constructor three-tap-terminal-completion-boundary
  field
    canonicalTerminalMarginSourceWritten : Bool
    terminalMarginEquivalentToCanonicalHighCutSourceWritten : Bool

    transformedCompletedCarrierSourceWritten : Bool
    resonanceSpecializationSourceWritten : Bool
    zeroHeightTargetObstructionSourceWritten : Bool

    transformedHeightDefectQuadraticSourceWritten : Bool
    normalizedPhysicalShiftWeldSourceWritten : Bool
    symmetricShiftMomentsThroughEightSourceWritten : Bool
    transformedSelectedZeroTargetWeldedSourceWritten : Bool
    transformedAdaptiveSupportRadiusSourceWritten : Bool
    transformedProjectiveAbsMomentObjectsSourceWritten : Bool
    transformedProjectiveM6M8TransportPaid : Bool
    transformedNormalizedProjectiveRescaleSourceWritten : Bool
    transformedAdaptiveEighthRemainderSourceWritten : Bool
    transformedPhysicalM6M8RescaleSourceWritten : Bool
    transformedAdaptiveMixedRemainderSourceWritten : Bool
    transformedJ2PhaseNormalFormSourceWritten : Bool
    transformedJ2ExceptionalStrengthClassificationSourceWritten : Bool
    transformedAdaptiveDegreeSixJetSourceWritten : Bool
    transformedFiniteAdaptiveLocalDebtSourceWritten : Bool
    transformedOffOrdCarrierWeldSourceWritten : Bool
    transformedCutoffFreeLocalSlackSourceWritten : Bool
    transformedCutoffFreeTerminalScalarSourceWritten : Bool
    transformedJ2PolynomialSourceWritten : Bool
    signedFifthRouteTargetsCanonicalMarginSourceWritten : Bool
    transformedNearLineJ2J4CoordinatesSourceWritten : Bool

    fixedPhysicalShiftBecomesHeightGrowingNormalizedShiftSourceWritten : Bool
    normalizedLogTwoShiftOutsideCanonicalSupportAtHighTSourceWritten : Bool

    originalLocalM6M8BudgetReusableWithoutNewProof : Bool
    transformedAbsoluteM6M8EnvelopePaid : Bool
    transformedTerminalStrictSignPaid : Bool
    resonanceStrictSignPaid : Bool
    nearLineLeadingCoefficientStrictlyPositivePaid : Bool

    leanExactHeadKernelReceiptOwnedHere : Bool
    agdaIndependentlyProvesRealAnalysisHere : Bool
    rhDerivedHere : Bool

    terminalObjectPaid :
      canonicalTerminalMarginSourceWritten ≡ true
    targetPolynomialPaid :
      transformedHeightDefectQuadraticSourceWritten ≡ true
    normalizedWeldPaid :
      normalizedPhysicalShiftWeldSourceWritten ≡ true
    momentTransportPaid :
      symmetricShiftMomentsThroughEightSourceWritten ≡ true
    selectedTargetWeldPaid :
      transformedSelectedZeroTargetWeldedSourceWritten ≡ true
    adaptiveSupportPaid :
      transformedAdaptiveSupportRadiusSourceWritten ≡ true
    projectiveMomentObjectsPaid :
      transformedProjectiveAbsMomentObjectsSourceWritten ≡ true
    normalizedProjectiveRescalePaid :
      transformedNormalizedProjectiveRescaleSourceWritten ≡ true
    adaptiveEighthRemainderPaid :
      transformedAdaptiveEighthRemainderSourceWritten ≡ true
    physicalM6M8RescalePaid :
      transformedPhysicalM6M8RescaleSourceWritten ≡ true
    adaptiveMixedRemainderPaid :
      transformedAdaptiveMixedRemainderSourceWritten ≡ true
    j2PhaseNormalFormPaid :
      transformedJ2PhaseNormalFormSourceWritten ≡ true
    j2ExceptionalStrengthClassificationPaid :
      transformedJ2ExceptionalStrengthClassificationSourceWritten ≡ true
    adaptiveDegreeSixJetPaid :
      transformedAdaptiveDegreeSixJetSourceWritten ≡ true
    finiteAdaptiveLocalDebtPaid :
      transformedFiniteAdaptiveLocalDebtSourceWritten ≡ true
    offOrdCarrierWeldPaid :
      transformedOffOrdCarrierWeldSourceWritten ≡ true
    cutoffFreeLocalSlackPaid :
      transformedCutoffFreeLocalSlackSourceWritten ≡ true
    cutoffFreeTerminalScalarPaid :
      transformedCutoffFreeTerminalScalarSourceWritten ≡ true
    j2PolynomialPaid :
      transformedJ2PolynomialSourceWritten ≡ true
    signedFifthCommonConsumerPaid :
      signedFifthRouteTargetsCanonicalMarginSourceWritten ≡ true
    nearLineCoordinatesPaid :
      transformedNearLineJ2J4CoordinatesSourceWritten ≡ true
    supportFirewallPaid :
      normalizedLogTwoShiftOutsideCanonicalSupportAtHighTSourceWritten ≡ true

    oldBudgetReuseRejected :
      originalLocalM6M8BudgetReusableWithoutNewProof ≡ false
    projectiveM6M8TransportStillOpen :
      transformedProjectiveM6M8TransportPaid ≡ false
    transformedAbsoluteBudgetPaid :
      transformedAbsoluteM6M8EnvelopePaid ≡ true
    strictTerminalSignStillOpen :
      transformedTerminalStrictSignPaid ≡ false
    resonanceSignStillOpen :
      resonanceStrictSignPaid ≡ false
    nearLineCoefficientStillOpen :
      nearLineLeadingCoefficientStrictlyPositivePaid ≡ false

    kernelReceiptNotClaimed :
      leanExactHeadKernelReceiptOwnedHere ≡ false
    agdaDoesNotInventAnalyticProof :
      agdaIndependentlyProvesRealAnalysisHere ≡ false
    rhStillNotDerived :
      rhDerivedHere ≡ false

    exactRemainingWall : String
    normalizationWarning : String
    twoScaleReuseRule : String
    signedFifthParallelRule : String

open ThreeTapTerminalCompletionBoundary public

canonicalThreeTapTerminalCompletionBoundary :
  ThreeTapTerminalCompletionBoundary
canonicalThreeTapTerminalCompletionBoundary =
  three-tap-terminal-completion-boundary
    true true
    true true true
    true true true
    true true true false true true true true true true true true true true true true true true
    true true
    false true false false false
    false false false

    refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl
    refl refl refl refl refl refl
    refl refl refl

    "Current Lean frontier: A1 finite O(log t/t), q^-2 pair decay, literal inverse-square window machinery, dyadic numerical series, boundary-safe complement geometry, and the conditional carrier-to-tail compiler are source-written. A2 correct-polarity fourth-angular control, the selected negative M6 certificate, dominant-coefficient payment, debt-minus-smooth-mu normal form, and positive canonical smooth-mu gain are source-written. Route B has the exact gap and direct physical-cap normal form. Remaining mathematics: A1 countable chart-to-shell carrier summation, fixed-width witness or compact-alpha uniform curvature, and translated gamma+pole gain versus local slack; A2 the final strict lower-order/far/compensation scalar; Route B eventual gap nonnegativity. Mid-strip stays downstream of a real near-line PASS. RH remains unpromoted."
    "The physical shift log 2 is not O(1) in the normalized quartic variable: it is B(t)=(t/16)log2 and already exceeds pi+1 for t>=200. Reusing the original support/M6/M8 constants would be a same-object error. Also, projectiveProfile(T_eps g) must not be identified with T_eps(projectiveProfile g) without a theorem; Lean now records that commutation only as an unpaid proposition."
    "If one-scale three-tap fails, reuse the same normalized-shift and moment-transport interfaces for the log2/log3 two-scale operator; do not create a parallel budget formalism."
    "Keep the signed fifth-cap/RvM correlation route independent.  It targets the same canonical high cut and remains a separate analytic producer."

terminalScalarIsTheOnlyMainlineConsumer :
  ThreeTapTerminalCompletionBoundary.canonicalTerminalMarginSourceWritten
    canonicalThreeTapTerminalCompletionBoundary ≡ true
terminalScalarIsTheOnlyMainlineConsumer = refl

oldLocalBudgetCannotBeReused :
  ThreeTapTerminalCompletionBoundary.originalLocalM6M8BudgetReusableWithoutNewProof
    canonicalThreeTapTerminalCompletionBoundary ≡ false
oldLocalBudgetCannotBeReused = refl

transformedAbsoluteBudgetIsPaid :
  ThreeTapTerminalCompletionBoundary.transformedAbsoluteM6M8EnvelopePaid
    canonicalThreeTapTerminalCompletionBoundary ≡ true
transformedAbsoluteBudgetIsPaid = refl

rhStillOpen :
  ThreeTapTerminalCompletionBoundary.rhDerivedHere
    canonicalThreeTapTerminalCompletionBoundary ≡ false
rhStillOpen = refl


------------------------------------------------------------------------
-- Current Lean frontier projection.
-- This updates status only. Lean remains the real-analysis theorem owner.
------------------------------------------------------------------------

currentLeanFrontierMirror : Current.ThreeTapCurrentLeanFrontier
currentLeanFrontierMirror = Current.currentThreeTapCurrentLeanFrontier

currentA1FiniteAndDecayPaid :
  Current.a1FiniteAndDecaySourceWritten Current.currentThreeTapCurrentLeanFrontier ≡ true
currentA1FiniteAndDecayPaid = Current.a1FiniteAndDecayPaid

currentA1InverseSquareWindowsPaid :
  Current.a1LiteralWindowMachinerySourceWritten Current.currentThreeTapCurrentLeanFrontier ≡ true
currentA1InverseSquareWindowsPaid = Current.a1LiteralWindowsPaid

currentA1DyadicSeriesPaid :
  Current.a1DyadicSeriesSourceWritten Current.currentThreeTapCurrentLeanFrontier ≡ true
currentA1DyadicSeriesPaid = Current.a1SeriesPaid

currentA1TailCompilerPaid :
  Current.a1CarrierToTailCompilerSourceWritten Current.currentThreeTapCurrentLeanFrontier ≡ true
currentA1TailCompilerPaid = Current.a1ConditionalTailCompilerPaid

currentA1CarrierSummationStillOpen :
  Current.a1CarrierSummationPaid Current.currentThreeTapCurrentLeanFrontier ≡ false
currentA1CarrierSummationStillOpen = Current.a1CarrierIsStillOpen

currentA1UniformCurvatureStillOpen :
  Current.a1UniformCurvaturePaid Current.currentThreeTapCurrentLeanFrontier ≡ false
currentA1UniformCurvatureStillOpen = Current.a1UniformCurvatureIsStillOpen

currentA1CompensationStillOpen :
  Current.a1CompensationPaid Current.currentThreeTapCurrentLeanFrontier ≡ false
currentA1CompensationStillOpen = Current.a1CompensationIsStillOpen

currentA2StrictScalarStillOpen :
  Current.a2StrictScalarPaid Current.currentThreeTapCurrentLeanFrontier ≡ false
currentA2StrictScalarStillOpen = Current.a2ScalarIsStillOpen

currentRouteBEventualGapStillOpen :
  Current.routeBEventualGapPaid Current.currentThreeTapCurrentLeanFrontier ≡ false
currentRouteBEventualGapStillOpen = Current.routeBIsStillOpen

currentFrontierDoesNotPromoteRH :
  Current.rhDerivedHere Current.currentThreeTapCurrentLeanFrontier ≡ false
currentFrontierDoesNotPromoteRH = Current.rhNotClaimedByAgdaStatusMirror
