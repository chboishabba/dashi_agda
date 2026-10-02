module DASHI.Analysis.RiemannThreeTapTerminalCompletionLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannQuarticSignedPoleFourierTerminalLeanDonorExact as Terminal

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
    "4e9abc06b987e0e1299de10d952cbb126141d520"
    "423150cc363d74aa695af18b11958f3f7b6a5741"
    "29169957eadb1c6d77f027c3f03926c6a29b0152"
    "fcf58344f83a03cb812b32effe5a2ff913de84bf"

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
    transformedRawM6M8SourceWritten : Bool
    signedFifthRouteTargetsCanonicalMarginSourceWritten : Bool

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
    rawM6M8Paid :
      transformedRawM6M8SourceWritten ≡ true
    signedFifthCommonConsumerPaid :
      signedFifthRouteTargetsCanonicalMarginSourceWritten ≡ true
    supportFirewallPaid :
      normalizedLogTwoShiftOutsideCanonicalSupportAtHighTSourceWritten ≡ true

    oldBudgetReuseRejected :
      originalLocalM6M8BudgetReusableWithoutNewProof ≡ false
    transformedAbsoluteBudgetStillOpen :
      transformedAbsoluteM6M8EnvelopePaid ≡ false
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
    true true true true
    true true
    false false false false false
    false false false

    refl refl refl refl refl refl refl refl refl
    refl refl refl refl refl
    refl refl refl

    "The exact transformed selected-zero target, adaptive normalized support radius, and raw M6/M8 objects are now source-written. Construct the transformed ABSOLUTE sixth/eighth-and-higher remainder envelope / localSlack on that same shifted profile, then prove or refute strict terminal positivity at resonance and in the first nonzero a->0 order."
    "The physical shift log 2 is not O(1) in the normalized quartic variable: it is B(t)=(t/16)log2 and already exceeds pi+1 for t>=200.  Reusing the original support/M6/M8 constants would be a same-object error."
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

transformedAbsoluteBudgetRemainsOpen :
  ThreeTapTerminalCompletionBoundary.transformedAbsoluteM6M8EnvelopePaid
    canonicalThreeTapTerminalCompletionBoundary ≡ false
transformedAbsoluteBudgetRemainsOpen = refl

rhStillOpen :
  ThreeTapTerminalCompletionBoundary.rhDerivedHere
    canonicalThreeTapTerminalCompletionBoundary ≡ false
rhStillOpen = refl
