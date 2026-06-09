module DASHI.Physics.Closure.NSThetaPressureMarginCorrectionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSNonCircularObstructionReceipt as Obstruction
import DASHI.Physics.Closure.NSNonCircularKStarDriftBoundTargetReceipt
  as Target
import DASHI.Physics.Closure.ParaproductDecompositionReceipt as Paraproduct

------------------------------------------------------------------------
-- NS theta pressure-margin correction.
--
-- This receipt records the latest correction to the NS comparison language.
-- The earlier phrase "H^{11/8} is weaker than Serrin/H^{1/2}" is retracted:
-- as a spatial Sobolev exponent, 11/8 is stronger than 1/2.  The safe claim
-- is different: theta<1 gives conditional, tail-localized L2 pressure-margin
-- decay above K*, not global Serrin/BKM control.  The high-high paraproduct
-- remains the honest wall, because standard HH control imports H^{1/2}-type
-- input and therefore regularity-class information.

data NSThetaPressureMarginCorrectionStatus : Set where
  thetaTailLocalizedCriterion_recorded_H118ComparisonCorrected :
    NSThetaPressureMarginCorrectionStatus

data NSCorrectedComparisonClaim : Set where
  hElevenEighthsSpatiallyStrongerThanHOneHalf :
    NSCorrectedComparisonClaim

  staleWeakerThanSerrinClaimRetracted :
    NSCorrectedComparisonClaim

  thetaLessThanOneIsTailLocalizedPressureMargin :
    NSCorrectedComparisonClaim

  tailDecayDoesNotByItselfGiveGlobalSerrinOrBKM :
    NSCorrectedComparisonClaim

  highHighControlWithoutRegularityInputIsWall :
    NSCorrectedComparisonClaim

canonicalNSCorrectedComparisonClaims :
  List NSCorrectedComparisonClaim
canonicalNSCorrectedComparisonClaims =
  hElevenEighthsSpatiallyStrongerThanHOneHalf
  ∷ staleWeakerThanSerrinClaimRetracted
  ∷ thetaLessThanOneIsTailLocalizedPressureMargin
  ∷ tailDecayDoesNotByItselfGiveGlobalSerrinOrBKM
  ∷ highHighControlWithoutRegularityInputIsWall
  ∷ []

data NSParaproductWallClause : Set where
  lowHighControlledByBernsteinAndLowFrequencyGradient :
    NSParaproductWallClause

  highHighRequiresSobolevL3OrHOneHalfRoute :
    NSParaproductWallClause

  hOneHalfRouteIsRegularityInput :
    NSParaproductWallClause

  nonCircularHHBoundStillOpen :
    NSParaproductWallClause

canonicalNSParaproductWallClauses :
  List NSParaproductWallClause
canonicalNSParaproductWallClauses =
  lowHighControlledByBernsteinAndLowFrequencyGradient
  ∷ highHighRequiresSobolevL3OrHOneHalfRoute
  ∷ hOneHalfRouteIsRegularityInput
  ∷ nonCircularHHBoundStillOpen
  ∷ []

data NSThetaPressureMarginPromotion : Set where

nsThetaPressureMarginPromotionImpossibleHere :
  NSThetaPressureMarginPromotion →
  ⊥
nsThetaPressureMarginPromotionImpossibleHere ()

correctionStatement :
  String
correctionStatement =
  "Correction: H^{11/8} is spatially stronger than H^{1/2}; the safe NS claim is only that theta<1 gives conditional tail-localized L2 pressure-margin decay above K*, not global Serrin/BKM control."

wallStatement :
  String
wallStatement =
  "The honest wall is the high-high paraproduct: standard estimates require L3/H^{1/2}-type input, so a Clay-level DASHI proof must control HH without importing regularity."

promotionBoundary :
  String
promotionBoundary =
  "This receipt corrects the comparison language.  It does not prove theta preservation, NonCircularKStarDriftBound, Serrin/BKM continuation, global regularity, or Clay Navier-Stokes."

record NSThetaPressureMarginCorrectionReceipt : Setω where
  field
    status :
      NSThetaPressureMarginCorrectionStatus

    statusIsCanonical :
      status
      ≡
      thetaTailLocalizedCriterion_recorded_H118ComparisonCorrected

    obstructionReceipt :
      Obstruction.NSNonCircularObstructionReceipt

    obstructionHighHighStillOpen :
      Obstruction.highHighControlProvedHere obstructionReceipt ≡ false

    obstructionNoClay :
      Obstruction.clayNavierStokesPromoted obstructionReceipt ≡ false

    targetReceipt :
      Target.NSNonCircularKStarDriftBoundTargetReceipt

    targetThetaPreservationStillOpen :
      Target.thetaPreservationProvedHere targetReceipt ≡ false

    targetNoHHalfSerrinBKMAssumed :
      Target.hHalfSerrinBKMAssumed targetReceipt ≡ false

    targetNoClay :
      Target.clayNavierStokesPromoted targetReceipt ≡ false

    paraproductReceipt :
      Paraproduct.ParaproductDecompositionReceipt

    paraproductDecomposed :
      Paraproduct.paraproductDecomposed paraproductReceipt ≡ true

    paraproductNoGlobalRegularity :
      Paraproduct.fullGlobalRegularityEstimate paraproductReceipt ≡ false

    correctedClaims :
      List NSCorrectedComparisonClaim

    correctedClaimsAreCanonical :
      correctedClaims ≡ canonicalNSCorrectedComparisonClaims

    wallClauses :
      List NSParaproductWallClause

    wallClausesAreCanonical :
      wallClauses ≡ canonicalNSParaproductWallClauses

    staleH118WeakerThanHHalfClaimAccepted :
      Bool

    staleH118WeakerThanHHalfClaimAcceptedIsFalse :
      staleH118WeakerThanHHalfClaimAccepted ≡ false

    h118SpatiallyStrongerThanHHalfRecorded :
      Bool

    h118SpatiallyStrongerThanHHalfRecordedIsTrue :
      h118SpatiallyStrongerThanHHalfRecorded ≡ true

    thetaTailLocalizedDecayOnly :
      Bool

    thetaTailLocalizedDecayOnlyIsTrue :
      thetaTailLocalizedDecayOnly ≡ true

    globalSerrinOrBKMProvedHere :
      Bool

    globalSerrinOrBKMProvedHereIsFalse :
      globalSerrinOrBKMProvedHere ≡ false

    nonCircularHHControlProvedHere :
      Bool

    nonCircularHHControlProvedHereIsFalse :
      nonCircularHHControlProvedHere ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotions :
      List NSThetaPressureMarginPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      NSThetaPressureMarginPromotion →
      ⊥

    correctionText :
      String

    correctionTextIsCanonical :
      correctionText ≡ correctionStatement

    wallText :
      String

    wallTextIsCanonical :
      wallText ≡ wallStatement

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ promotionBoundary

open NSThetaPressureMarginCorrectionReceipt public

canonicalNSThetaPressureMarginCorrectionReceipt :
  NSThetaPressureMarginCorrectionReceipt
canonicalNSThetaPressureMarginCorrectionReceipt =
  record
    { status =
        thetaTailLocalizedCriterion_recorded_H118ComparisonCorrected
    ; statusIsCanonical =
        refl
    ; obstructionReceipt =
        Obstruction.canonicalNSNonCircularObstructionReceipt
    ; obstructionHighHighStillOpen =
        refl
    ; obstructionNoClay =
        refl
    ; targetReceipt =
        Target.canonicalNSNonCircularKStarDriftBoundTargetReceipt
    ; targetThetaPreservationStillOpen =
        refl
    ; targetNoHHalfSerrinBKMAssumed =
        refl
    ; targetNoClay =
        refl
    ; paraproductReceipt =
        Paraproduct.canonicalParaproductDecompositionReceipt
    ; paraproductDecomposed =
        refl
    ; paraproductNoGlobalRegularity =
        refl
    ; correctedClaims =
        canonicalNSCorrectedComparisonClaims
    ; correctedClaimsAreCanonical =
        refl
    ; wallClauses =
        canonicalNSParaproductWallClauses
    ; wallClausesAreCanonical =
        refl
    ; staleH118WeakerThanHHalfClaimAccepted =
        false
    ; staleH118WeakerThanHHalfClaimAcceptedIsFalse =
        refl
    ; h118SpatiallyStrongerThanHHalfRecorded =
        true
    ; h118SpatiallyStrongerThanHHalfRecordedIsTrue =
        refl
    ; thetaTailLocalizedDecayOnly =
        true
    ; thetaTailLocalizedDecayOnlyIsTrue =
        refl
    ; globalSerrinOrBKMProvedHere =
        false
    ; globalSerrinOrBKMProvedHereIsFalse =
        refl
    ; nonCircularHHControlProvedHere =
        false
    ; nonCircularHHControlProvedHereIsFalse =
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
        nsThetaPressureMarginPromotionImpossibleHere
    ; correctionText =
        correctionStatement
    ; correctionTextIsCanonical =
        refl
    ; wallText =
        wallStatement
    ; wallTextIsCanonical =
        refl
    ; boundary =
        promotionBoundary
    ; boundaryIsCanonical =
        refl
    }

canonicalNSThetaCorrectionRetractsStaleComparison :
  staleH118WeakerThanHHalfClaimAccepted
    canonicalNSThetaPressureMarginCorrectionReceipt
  ≡
  false
canonicalNSThetaCorrectionRetractsStaleComparison =
  refl

canonicalNSThetaCorrectionNoClay :
  clayNavierStokesPromoted canonicalNSThetaPressureMarginCorrectionReceipt
  ≡
  false
canonicalNSThetaCorrectionNoClay =
  refl
