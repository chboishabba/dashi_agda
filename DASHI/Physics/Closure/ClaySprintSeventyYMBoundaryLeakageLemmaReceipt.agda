module DASHI.Physics.Closure.ClaySprintSeventyYMBoundaryLeakageLemmaReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClaySprintSeventyClayRoadmapLemmaStackReceipt
  as Sprint70Roadmap

------------------------------------------------------------------------
-- Sprint 70 YM boundary leakage lemma receipt.
--
-- This receipt records the plaquette-level boundary audit and the corrected
-- transfer-matrix bookkeeping.  It is deliberately fail-closed: mixed
-- temporal plaquettes are recorded as transfer-matrix face action rather than
-- residual correction, while temporal measure factorization and Clay/YM remain
-- open.

Scalar : Set
Scalar = String

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data Sprint70BoundaryLeakageRouteDecision : Set where
  mixedPlaquettesAreTransferMatrixNotCorrection :
    Sprint70BoundaryLeakageRouteDecision
  noTemporalSpanningCounterexample :
    Sprint70BoundaryLeakageRouteDecision
  bookkeepingLambdaOne :
    Sprint70BoundaryLeakageRouteDecision
  legacyCorrectionBucketWasBookkeepingError :
    Sprint70BoundaryLeakageRouteDecision
  noYangMillsPromotion :
    Sprint70BoundaryLeakageRouteDecision

canonicalSprint70BoundaryLeakageRouteDecisions :
  List Sprint70BoundaryLeakageRouteDecision
canonicalSprint70BoundaryLeakageRouteDecisions =
  mixedPlaquettesAreTransferMatrixNotCorrection
  ∷ noTemporalSpanningCounterexample
  ∷ bookkeepingLambdaOne
  ∷ legacyCorrectionBucketWasBookkeepingError
  ∷ noYangMillsPromotion
  ∷ []

data Sprint70BoundaryLeakageOpenGate : Set where
  gateWilsonActionSlabDecomposition :
    Sprint70BoundaryLeakageOpenGate
  gateNoSupportSpanningCorrection :
    Sprint70BoundaryLeakageOpenGate
  gateLinkVariableDisjointnessFormalized :
    Sprint70BoundaryLeakageOpenGate
  gateTemporalMeasureFactorizationWithLeakage :
    Sprint70BoundaryLeakageOpenGate
  gateAnisotropicBalabanPartitionIdentity :
    Sprint70BoundaryLeakageOpenGate
  gateAllDiameterWeightedKP :
    Sprint70BoundaryLeakageOpenGate

canonicalSprint70BoundaryLeakageOpenGates :
  List Sprint70BoundaryLeakageOpenGate
canonicalSprint70BoundaryLeakageOpenGates =
  gateWilsonActionSlabDecomposition
  ∷ gateNoSupportSpanningCorrection
  ∷ gateLinkVariableDisjointnessFormalized
  ∷ gateTemporalMeasureFactorizationWithLeakage
  ∷ gateAnisotropicBalabanPartitionIdentity
  ∷ gateAllDiameterWeightedKP
  ∷ []

data Sprint70BoundaryLeakagePromotion : Set where

sprint70BoundaryLeakagePromotionImpossibleHere :
  Sprint70BoundaryLeakagePromotion →
  ⊥
sprint70BoundaryLeakagePromotionImpossibleHere ()

sprint70BoundaryLeakageArithmetic : String
sprint70BoundaryLeakageArithmetic =
  "Safe arithmetic: q=0.23178189475262734, 4q=0.9271275790105094, (1.025)^3=1.076890625, and (1.025)^3 * 4q = 0.9984149980153639 < 1 with margin 0.0015850019846360697."

sprint70BoundaryLeakageDefaultAudit : String
sprint70BoundaryLeakageDefaultAudit =
  "Default corrected audit command: python scripts/ym_sprint70_boundary_correction_audit.py --L 2 --dimension 4 --q 0.23178189475262734 --per-face-leakage-bound 0.025 --out-dir outputs/sprint70_ym_boundary_correction. Result: mixed plaquettes are transfer-matrix face action, residual_correction_action_total=0.0, bookkeeping_lambda=1.0, total_leakage_times_4q=0.9271275790105094, route_decision=MIXED_PLAQUETTES_ABSORBED_INTO_TRANSFER_MATRIX. The legacy correction bucket still records total_leakage_times_4q=1.7130035863183526 as the old bookkeeping error."

sprint70BoundaryLeakageManualControl : String
sprint70BoundaryLeakageManualControl =
  "Manual control with mixed-coupling suppression 0.02 is now a legacy diagnostic only. Under corrected transfer-matrix bookkeeping, total_leakage_factor=1.0 and total_leakage_times_4q=0.9271275790105094 regardless of that suppression parameter."

sprint70BoundaryLeakageBoundary : String
sprint70BoundaryLeakageBoundary =
  "Sprint 70 corrects the boundary bookkeeping fork. Mixed spatial-temporal plaquettes touching a temporal face are transfer-matrix face action, not residual correction, so the action-bookkeeping multiplier is 1.0. This does not prove exact temporal measure factorization: link-variable disjointness, TemporalMeasureFactorizationWithLeakage, AnisotropicBalabanPartitionIdentity, all-diameter KP, mass gap, continuum transfer, and Clay/YM promotion remain open/false."

record ClaySprintSeventyYMBoundaryLeakageLemmaReceipt : Set₁ where
  field
    sprint70RoadmapNoPromotion :
      Sprint70Roadmap.clayYangMillsPromoted ≡ false

    threeFaceLeakageSafeArithmetic :
      Bool
    threeFaceLeakageSafeArithmeticIsTrue :
      threeFaceLeakageSafeArithmetic ≡ true

    qCurrent :
      Scalar
    qCurrentIsCanonical :
      qCurrent ≡ "0.23178189475262734"

    fourQ :
      Scalar
    fourQIsCanonical :
      fourQ ≡ "0.9271275790105094"

    safeThreeFaceLeakageFactor :
      Scalar
    safeThreeFaceLeakageFactorIsCanonical :
      safeThreeFaceLeakageFactor ≡ "1.076890625"

    safeThreeFaceTimesFourQ :
      Scalar
    safeThreeFaceTimesFourQIsCanonical :
      safeThreeFaceTimesFourQ ≡ "0.9984149980153639"

    safeThreeFaceMargin :
      Scalar
    safeThreeFaceMarginIsCanonical :
      safeThreeFaceMargin ≡ "0.0015850019846360697"

    temporalSpanningCounterexample :
      Bool
    temporalSpanningCounterexampleIsFalse :
      temporalSpanningCounterexample ≡ false

    defaultMaxTopCorrectionRatio :
      Scalar
    defaultMaxTopCorrectionRatioIsCanonical :
      defaultMaxTopCorrectionRatio ≡ "0.0"

    defaultMaxBottomCorrectionRatio :
      Scalar
    defaultMaxBottomCorrectionRatioIsCanonical :
      defaultMaxBottomCorrectionRatio ≡ "0.0"

    defaultMaxSpatialCorrectionRatio :
      Scalar
    defaultMaxSpatialCorrectionRatioIsCanonical :
      defaultMaxSpatialCorrectionRatio ≡ "0.0"

    defaultTotalLeakageFactor :
      Scalar
    defaultTotalLeakageFactorIsCanonical :
      defaultTotalLeakageFactor ≡ "1.0"

    defaultTotalLeakageTimesFourQ :
      Scalar
    defaultTotalLeakageTimesFourQIsCanonical :
      defaultTotalLeakageTimesFourQ ≡ "0.9271275790105094"

    defaultBoundaryCorrectionSmall :
      Bool
    defaultBoundaryCorrectionSmallIsTrue :
      defaultBoundaryCorrectionSmall ≡ true

    mixedPlaquettesAreTransferMatrixNotCorrectionRecorded :
      Bool
    mixedPlaquettesAreTransferMatrixNotCorrectionRecordedIsTrue :
      mixedPlaquettesAreTransferMatrixNotCorrectionRecorded ≡ true

    linkVariableDisjointnessFormalized :
      Bool
    linkVariableDisjointnessFormalizedIsFalse :
      linkVariableDisjointnessFormalized ≡ false

    temporalMeasureFactorizationWithLeakageProved :
      Bool
    temporalMeasureFactorizationWithLeakageProvedIsFalse :
      temporalMeasureFactorizationWithLeakageProved ≡ false

    routeDecisions :
      List Sprint70BoundaryLeakageRouteDecision
    routeDecisionsAreCanonical :
      routeDecisions ≡ canonicalSprint70BoundaryLeakageRouteDecisions

    openGates :
      List Sprint70BoundaryLeakageOpenGate
    openGatesAreCanonical :
      openGates ≡ canonicalSprint70BoundaryLeakageOpenGates

    arithmetic :
      String
    arithmeticIsCanonical :
      arithmetic ≡ sprint70BoundaryLeakageArithmetic

    defaultAudit :
      String
    defaultAuditIsCanonical :
      defaultAudit ≡ sprint70BoundaryLeakageDefaultAudit

    manualControl :
      String
    manualControlIsCanonical :
      manualControl ≡ sprint70BoundaryLeakageManualControl

    boundary :
      String
    boundaryIsCanonical :
      boundary ≡ sprint70BoundaryLeakageBoundary

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    promotions :
      List Sprint70BoundaryLeakagePromotion
    promotionsAreEmpty :
      promotions ≡ []
    noPromotionPossibleHere :
      Sprint70BoundaryLeakagePromotion → ⊥

canonicalSprint70YMBoundaryLeakageLemmaReceipt :
  ClaySprintSeventyYMBoundaryLeakageLemmaReceipt
canonicalSprint70YMBoundaryLeakageLemmaReceipt =
  record
    { sprint70RoadmapNoPromotion = refl
    ; threeFaceLeakageSafeArithmetic = true
    ; threeFaceLeakageSafeArithmeticIsTrue = refl
    ; qCurrent = "0.23178189475262734"
    ; qCurrentIsCanonical = refl
    ; fourQ = "0.9271275790105094"
    ; fourQIsCanonical = refl
    ; safeThreeFaceLeakageFactor = "1.076890625"
    ; safeThreeFaceLeakageFactorIsCanonical = refl
    ; safeThreeFaceTimesFourQ = "0.9984149980153639"
    ; safeThreeFaceTimesFourQIsCanonical = refl
    ; safeThreeFaceMargin = "0.0015850019846360697"
    ; safeThreeFaceMarginIsCanonical = refl
    ; temporalSpanningCounterexample = false
    ; temporalSpanningCounterexampleIsFalse = refl
    ; defaultMaxTopCorrectionRatio = "0.0"
    ; defaultMaxTopCorrectionRatioIsCanonical = refl
    ; defaultMaxBottomCorrectionRatio = "0.0"
    ; defaultMaxBottomCorrectionRatioIsCanonical = refl
    ; defaultMaxSpatialCorrectionRatio = "0.0"
    ; defaultMaxSpatialCorrectionRatioIsCanonical = refl
    ; defaultTotalLeakageFactor = "1.0"
    ; defaultTotalLeakageFactorIsCanonical = refl
    ; defaultTotalLeakageTimesFourQ = "0.9271275790105094"
    ; defaultTotalLeakageTimesFourQIsCanonical = refl
    ; defaultBoundaryCorrectionSmall = true
    ; defaultBoundaryCorrectionSmallIsTrue = refl
    ; mixedPlaquettesAreTransferMatrixNotCorrectionRecorded = true
    ; mixedPlaquettesAreTransferMatrixNotCorrectionRecordedIsTrue = refl
    ; linkVariableDisjointnessFormalized = false
    ; linkVariableDisjointnessFormalizedIsFalse = refl
    ; temporalMeasureFactorizationWithLeakageProved = false
    ; temporalMeasureFactorizationWithLeakageProvedIsFalse = refl
    ; routeDecisions = canonicalSprint70BoundaryLeakageRouteDecisions
    ; routeDecisionsAreCanonical = refl
    ; openGates = canonicalSprint70BoundaryLeakageOpenGates
    ; openGatesAreCanonical = refl
    ; arithmetic = sprint70BoundaryLeakageArithmetic
    ; arithmeticIsCanonical = refl
    ; defaultAudit = sprint70BoundaryLeakageDefaultAudit
    ; defaultAuditIsCanonical = refl
    ; manualControl = sprint70BoundaryLeakageManualControl
    ; manualControlIsCanonical = refl
    ; boundary = sprint70BoundaryLeakageBoundary
    ; boundaryIsCanonical = refl
    ; clayYangMillsPromotedIsFalse = refl
    ; promotions = []
    ; promotionsAreEmpty = refl
    ; noPromotionPossibleHere =
        sprint70BoundaryLeakagePromotionImpossibleHere
    }
