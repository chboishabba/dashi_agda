module DASHI.Physics.Closure.NSNonCircularObstructionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSThetaTailToBKMBridgeReceipt as TailBKM
import DASHI.Physics.Closure.NSDangerShellMaximumPrincipleReceipt as Danger
import DASHI.Physics.Closure.NSDangerShellMaxPrincipleConditionalProofReceipt
  as Conditional
import DASHI.Physics.Closure.NSNegativeSobolevDangerShellReceipt as NegSob
import DASHI.Physics.Closure.ParaproductDecompositionReceipt as Paraproduct

------------------------------------------------------------------------
-- Non-circular K-star drift obstruction.
--
-- This receipt records the current NS Clay obstruction as a structural
-- obstruction, not as an open lemma pretending to be nearly proved.  The
-- high-high paraproduct term must be controlled at the danger shell without
-- assuming H^{1/2}, Serrin, BKM, or stronger regularity.  The admissible
-- replacement target is now a negative-Sobolev nonlinear-defect estimate in
-- H^{-1/2}, paired against the tail in H^{1/2}.

data NSNonCircularObstructionStatus : Set where
  highHighParaproductCircularityRecorded :
    NSNonCircularObstructionStatus

data NSObstructionType : Set where
  highHighParaproductCircularity :
    NSObstructionType

data NSCircularAttemptStep : Set where
  assumeTailFluxDominatedByDissipation :
    NSCircularAttemptStep

  deriveHighHighSobolevHalfControl :
    NSCircularAttemptStep

  consumeSerrinOrBKMRegularity :
    NSCircularAttemptStep

  concludeAttemptIsCircular :
    NSCircularAttemptStep

canonicalNSCircularAttemptSteps :
  List NSCircularAttemptStep
canonicalNSCircularAttemptSteps =
  assumeTailFluxDominatedByDissipation
  ∷ deriveHighHighSobolevHalfControl
  ∷ consumeSerrinOrBKMRegularity
  ∷ concludeAttemptIsCircular
  ∷ []

data NSPublishableComparisonClaim : Set where
  thetaLessThanOneIsComputableSeamCriterion :
    NSPublishableComparisonClaim

  thetaPreservationEqualsHighHighControlTarget :
    NSPublishableComparisonClaim

  highHighControlIsClayLevelStep :
    NSPublishableComparisonClaim

canonicalNSPublishableComparisonClaims :
  List NSPublishableComparisonClaim
canonicalNSPublishableComparisonClaims =
  thetaLessThanOneIsComputableSeamCriterion
  ∷ thetaPreservationEqualsHighHighControlTarget
  ∷ highHighControlIsClayLevelStep
  ∷ []

data NSOpenObligation : Set where
  proveNonCircularKStarDriftBound :
    NSOpenObligation

  proveHighHighParaproductDominanceWithoutSerrin :
    NSOpenObligation

  proveHMinusHalfNonlinearDefectBound :
    NSOpenObligation

  preserveThetaLessThanOneUnderSmoothNSFlow :
    NSOpenObligation

canonicalNSOpenObligations :
  List NSOpenObligation
canonicalNSOpenObligations =
  proveNonCircularKStarDriftBound
  ∷ proveHighHighParaproductDominanceWithoutSerrin
  ∷ proveHMinusHalfNonlinearDefectBound
  ∷ preserveThetaLessThanOneUnderSmoothNSFlow
  ∷ []

data NSNonCircularPromotion : Set where

nsNonCircularPromotionImpossibleHere :
  NSNonCircularPromotion →
  ⊥
nsNonCircularPromotionImpossibleHere ()

obstructionStatement :
  String
obstructionStatement =
  "NonCircularKStarDriftBound is obstructed by the high-high paraproduct term: the admissible route is to prove an H^{-1/2} nonlinear-defect estimate for P_{>K*}(u.grad u), while not assuming H^{1/2} velocity control, Serrin, BKM, or stronger regularity."

comparisonStatement :
  String
comparisonStatement =
  "Theta<1 is recorded as a computable seam criterion and danger-shell locator.  Preserving Theta<1 reduces to non-circular high-high control; that control is the Clay-level NS step."

promotionBoundary :
  String
promotionBoundary =
  "This receipt records the obstruction and comparison target only. It does not prove KStar drift containment, the danger-shell maximum principle, BKM/Serrin continuation, global regularity, or Clay Navier-Stokes."

record NSNonCircularObstructionReceipt : Setω where
  field
    status :
      NSNonCircularObstructionStatus

    statusIsCanonical :
      status ≡ highHighParaproductCircularityRecorded

    obstructionType :
      NSObstructionType

    obstructionTypeIsHighHigh :
      obstructionType ≡ highHighParaproductCircularity

    tailToBKMReceipt :
      TailBKM.NSThetaTailToBKMBridgeReceipt zero

    tailToBKMStillConditional :
      TailBKM.bkmCriterionDischarged tailToBKMReceipt ≡ false

    dangerShellReceipt :
      Danger.NSDangerShellMaximumPrincipleReceipt

    dangerShellStillOpen :
      Danger.dangerShellMaxPrincipleProved dangerShellReceipt ≡ false

    conditionalMaxReceipt :
      Conditional.NSDangerShellMaxPrincipleConditionalProofReceipt zero

    nonCircularWeakeningStillOpen :
      Conditional.nonCircularWeakeningProved conditionalMaxReceipt ≡ false

    negativeSobolevReceipt :
      NegSob.NSNegativeSobolevDangerShellReceipt zero

    negativeSobolevTargetRecorded :
      NegSob.nonlinearDefectSpaceTargetRecorded negativeSobolevReceipt
      ≡
      true

    negativeSobolevEstimateStillOpen :
      NegSob.highHighDefectBoundProvedHere negativeSobolevReceipt
      ≡
      false

    negativeSobolevNoRegularityShortcut :
      NegSob.hOneHalfVelocityRegularityAssumed negativeSobolevReceipt
      ≡
      false

    negativeSobolevNoClay :
      NegSob.clayNavierStokesPromoted negativeSobolevReceipt ≡ false

    paraproductReceipt :
      Paraproduct.ParaproductDecompositionReceipt

    circularAttemptSteps :
      List NSCircularAttemptStep

    circularAttemptStepsAreCanonical :
      circularAttemptSteps ≡ canonicalNSCircularAttemptSteps

    publishableClaims :
      List NSPublishableComparisonClaim

    publishableClaimsAreCanonical :
      publishableClaims ≡ canonicalNSPublishableComparisonClaims

    openObligations :
      List NSOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalNSOpenObligations

    highHighControlProvedHere :
      Bool

    highHighControlProvedHereIsFalse :
      highHighControlProvedHere ≡ false

    thetaPreservationProvedHere :
      Bool

    thetaPreservationProvedHereIsFalse :
      thetaPreservationProvedHere ≡ false

    serrinOrBKMAssumedByAllowedProof :
      Bool

    serrinOrBKMAssumedByAllowedProofIsFalse :
      serrinOrBKMAssumedByAllowedProof ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotions :
      List NSNonCircularPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      NSNonCircularPromotion →
      ⊥

    obstruction :
      String

    obstructionIsCanonical :
      obstruction ≡ obstructionStatement

    comparison :
      String

    comparisonIsCanonical :
      comparison ≡ comparisonStatement

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ promotionBoundary

open NSNonCircularObstructionReceipt public

canonicalNSNonCircularObstructionReceipt :
  NSNonCircularObstructionReceipt
canonicalNSNonCircularObstructionReceipt =
  record
    { status =
        highHighParaproductCircularityRecorded
    ; statusIsCanonical =
        refl
    ; obstructionType =
        highHighParaproductCircularity
    ; obstructionTypeIsHighHigh =
        refl
    ; tailToBKMReceipt =
        TailBKM.canonicalNSThetaTailToBKMBridgeReceipt
    ; tailToBKMStillConditional =
        refl
    ; dangerShellReceipt =
        Danger.canonicalNSDangerShellMaximumPrincipleReceipt
    ; dangerShellStillOpen =
        refl
    ; conditionalMaxReceipt =
        Conditional.canonicalNSDangerShellMaxPrincipleConditionalProofReceipt
    ; nonCircularWeakeningStillOpen =
        refl
    ; negativeSobolevReceipt =
        NegSob.canonicalNSNegativeSobolevDangerShellReceipt
    ; negativeSobolevTargetRecorded =
        refl
    ; negativeSobolevEstimateStillOpen =
        refl
    ; negativeSobolevNoRegularityShortcut =
        refl
    ; negativeSobolevNoClay =
        refl
    ; paraproductReceipt =
        Paraproduct.canonicalParaproductDecompositionReceipt
    ; circularAttemptSteps =
        canonicalNSCircularAttemptSteps
    ; circularAttemptStepsAreCanonical =
        refl
    ; publishableClaims =
        canonicalNSPublishableComparisonClaims
    ; publishableClaimsAreCanonical =
        refl
    ; openObligations =
        canonicalNSOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; highHighControlProvedHere =
        false
    ; highHighControlProvedHereIsFalse =
        refl
    ; thetaPreservationProvedHere =
        false
    ; thetaPreservationProvedHereIsFalse =
        refl
    ; serrinOrBKMAssumedByAllowedProof =
        false
    ; serrinOrBKMAssumedByAllowedProofIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        nsNonCircularPromotionImpossibleHere
    ; obstruction =
        obstructionStatement
    ; obstructionIsCanonical =
        refl
    ; comparison =
        comparisonStatement
    ; comparisonIsCanonical =
        refl
    ; boundary =
        promotionBoundary
    ; boundaryIsCanonical =
        refl
    }

canonicalNSNonCircularHighHighStillOpen :
  highHighControlProvedHere canonicalNSNonCircularObstructionReceipt ≡ false
canonicalNSNonCircularHighHighStillOpen =
  refl

canonicalNSNonCircularNoClayPromotion :
  clayNavierStokesPromoted canonicalNSNonCircularObstructionReceipt ≡ false
canonicalNSNonCircularNoClayPromotion =
  refl
