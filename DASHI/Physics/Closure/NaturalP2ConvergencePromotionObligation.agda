module DASHI.Physics.Closure.NaturalP2ConvergencePromotionObligation where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Arithmetic.NormalizeAddSumPreservation as NASP
import DASHI.Physics.Closure.CanonicalDynamicsLawTheorem as CDT
import DASHI.Physics.Closure.CanonicalP2OfflineL2ObstructionCertificate as CPOL2
import DASHI.Physics.Closure.CanonicalP2KeyScheduleBridgeObstruction as CPKSO
import DASHI.Physics.Closure.CanonicalScheduleIndependentNaturalChargeNextIngredientGap as CSING
import DASHI.Physics.Closure.P0BlockadeProofObligations as P0
import DASHI.Physics.PressureGradientFlowShiftInstance as PGFSI

------------------------------------------------------------------------
-- W2d natural / p2 / convergence promotion obligation.
--
-- CanonicalDynamicsLawTheorem now carries finite shift-flow convergence,
-- pointed metric convergence, and a realization-indexed metric family.  Those
-- are deliberately still shift-flow-carrier receipts.  This module records the
-- remaining fields needed before the broader natural / p2 lane can be
-- promoted.  It does not claim naturality, p2 closure, or carrier-independent
-- convergence beyond the landed shift-flow carrier.

data NaturalP2ConvergencePromotionAuthorityToken : Set where

------------------------------------------------------------------------
-- Non-promoting positive invariant.
--
-- `NormalizeAddSumPreservation` records the current repo-native invariant
-- that `normalizeAdd` preserves `lhs + rhs` definitionally, hence preserves
-- the p-adic valuation of that sum for every tracked prime.  This corrects
-- the earlier carry-field obstruction target without importing the heavy
-- shift-contract/profile stack here.

naturalP2NormalizeAddSumInvariant :
  NASP.NormalizeAddSumPreservationReceipt
naturalP2NormalizeAddSumInvariant =
  NASP.canonicalNormalizeAddSumPreservationReceipt

record NaturalP2BridgeOrObstructionReceipt : Setω where
  field
    Source Target : Set
    Candidate : (Source → Target) → Set

    bridgeOrObstruction :
      P0.P2BridgeOrObstruction Candidate

    naturalityCarrier : Set
    singleStepCarrier : Set
    doubleStepCarrier : Set

    naturalityLaw :
      naturalityCarrier → Set

    p2CoherenceLaw :
      singleStepCarrier →
      doubleStepCarrier →
      Set

record CarrierGeneralConvergenceRateReceipt : Setω where
  field
    State : Set

    convergenceBound :
      P0.ConvergenceBound {State}

    carrierTransport : Set
    realizationIndex : Set

    transportPreservesConvergence :
      carrierTransport → Set

    realizationUniformityLaw :
      realizationIndex → Set

    beyondShiftFlowBoundary :
      String

record NaturalP2ConvergencePromotionReceipt : Setω where
  field
    promotionAuthority :
      NaturalP2ConvergencePromotionAuthorityToken

    canonicalDynamicsLaw :
      CDT.CanonicalDynamicsLawTheorem

    p2Receipt :
      NaturalP2BridgeOrObstructionReceipt

    carrierGeneralConvergence :
      CarrierGeneralConvergenceRateReceipt

    shiftConvergenceReceipt :
      P0.ConvergenceBound {PGFSI.ShiftFlowState}

    realizedMetricFamilyReceipt :
      CDT.RealizationIndexedPointedMetricConvergenceTarget

naturalP2ConvergencePromotionAuthorityUnavailable :
  NaturalP2ConvergencePromotionAuthorityToken → ⊥
naturalP2ConvergencePromotionAuthorityUnavailable ()

naturalP2ConvergencePromotionReceiptImpossible :
  NaturalP2ConvergencePromotionReceipt → ⊥
naturalP2ConvergencePromotionReceiptImpossible receipt =
  naturalP2ConvergencePromotionAuthorityUnavailable
    (NaturalP2ConvergencePromotionReceipt.promotionAuthority receipt)

------------------------------------------------------------------------
-- Current non-promoting status.

data NaturalP2ConvergenceMissingField : Set where
  missingPromotionAuthorityToken :
    NaturalP2ConvergenceMissingField
  missingNaturalBridgeOrObstruction :
    NaturalP2ConvergenceMissingField
  missingNaturalityCarrier :
    NaturalP2ConvergenceMissingField
  missingP2SingleStepCarrier :
    NaturalP2ConvergenceMissingField
  missingP2DoubleStepCarrier :
    NaturalP2ConvergenceMissingField
  missingP2NaturalityLaw :
    NaturalP2ConvergenceMissingField
  missingP2CoherenceLaw :
    NaturalP2ConvergenceMissingField
  missingCarrierTransportLaw :
    NaturalP2ConvergenceMissingField
  missingTransportPreservesConvergenceLaw :
    NaturalP2ConvergenceMissingField
  missingCarrierGeneralConvergenceRate :
    NaturalP2ConvergenceMissingField
  missingRealizationUniformityLaw :
    NaturalP2ConvergenceMissingField
  missingUniformRealizationRateBeyondShiftFlow :
    NaturalP2ConvergenceMissingField
  missingOfflineL2ToCarrierRateLift :
    NaturalP2ConvergenceMissingField

record NaturalP2ConvergencePromotionImpossibilityDiagnostic : Setω where
  field
    authorityUnavailable :
      NaturalP2ConvergencePromotionAuthorityToken → ⊥

    receiptImpossible :
      NaturalP2ConvergencePromotionReceipt → ⊥

    typedMissingFields :
      List NaturalP2ConvergenceMissingField

    obstructionSummary :
      String

data StrongerNaturalP2ConvergenceIngredient : Set where
  canonicalP2KeyScheduleBridgeNeeded :
    StrongerNaturalP2ConvergenceIngredient
  carrierTransportPreservesRateNeeded :
    StrongerNaturalP2ConvergenceIngredient
  uniformRealizationRateBeyondShiftFlowNeeded :
    StrongerNaturalP2ConvergenceIngredient
  offlineL2ToCarrierGeneralRateLiftNeeded :
    StrongerNaturalP2ConvergenceIngredient

data OfflineL2ConvergenceRateLiftMissingField : Set where
  missingBelowδToCarrierTransport :
    OfflineL2ConvergenceRateLiftMissingField
  missingOfflineL2PreservesPointedRate :
    OfflineL2ConvergenceRateLiftMissingField
  missingOfflineL2UniformRealizationLaw :
    OfflineL2ConvergenceRateLiftMissingField
  missingPositiveP2KeyScheduleBridge :
    OfflineL2ConvergenceRateLiftMissingField

record OfflineL2InsufficientForConvergenceRate : Setω where
  field
    offlineL2Certificate :
      CPOL2.CanonicalP2OfflineL2ObstructionCertificate

    allBelowδCandidatesImpossible :
      CPOL2.OfflineL2P2BridgeCandidate
        CPOL2.normalizedShadowBelowδ_p2 →
      ⊥

    landedShiftConvergence :
      P0.ConvergenceBound {PGFSI.ShiftFlowState}

    landedRealizationMetricFamily :
      CDT.RealizationIndexedPointedMetricConvergenceTarget

    missingLiftFields :
      List OfflineL2ConvergenceRateLiftMissingField

    stillMissingPromotionFields :
      List NaturalP2ConvergenceMissingField

    resultBoundary :
      String

canonicalOfflineL2InsufficientForConvergenceRate :
  OfflineL2InsufficientForConvergenceRate
canonicalOfflineL2InsufficientForConvergenceRate =
  record
    { offlineL2Certificate =
        CPOL2.canonicalP2OfflineL2ObstructionCertificate
    ; allBelowδCandidatesImpossible =
        CPOL2.CanonicalP2OfflineL2ObstructionCertificate.allBelowδCandidatesImpossible
          CPOL2.canonicalP2OfflineL2ObstructionCertificate
    ; landedShiftConvergence =
        CDT.CanonicalDynamicsLawTheorem.boundedConvergenceRate
          CDT.canonicalDynamicsLawTheorem
    ; landedRealizationMetricFamily =
        CDT.CanonicalDynamicsLawTheorem.realizationMetricConvergenceFamily
          CDT.canonicalDynamicsLawTheorem
    ; missingLiftFields =
        missingBelowδToCarrierTransport
        ∷ missingOfflineL2PreservesPointedRate
        ∷ missingOfflineL2UniformRealizationLaw
        ∷ missingPositiveP2KeyScheduleBridge
        ∷ []
    ; stillMissingPromotionFields =
        missingCarrierTransportLaw
        ∷ missingTransportPreservesConvergenceLaw
        ∷ missingCarrierGeneralConvergenceRate
        ∷ missingRealizationUniformityLaw
        ∷ missingUniformRealizationRateBeyondShiftFlow
        ∷ missingOfflineL2ToCarrierRateLift
        ∷ []
    ; resultBoundary =
        "Path B non-promotion: the OfflineL2 certificate is an obstruction to below-delta normalized-shadow candidates forcing the p2 key; it does not supply carrier transport, rate preservation, or uniform realization evidence for a carrier-general convergence bound"
    }

record NaturalP2BridgeCarrierGeneralConvergenceObstruction : Setω where
  field
    canonicalDynamicsLaw :
      CDT.CanonicalDynamicsLawTheorem

    normalizeAddSumInvariant :
      NASP.NormalizeAddSumPreservationReceipt

    p2ScheduleBridgeObstruction :
      CPKSO.CanonicalP2KeyScheduleBridgeObstruction

    p2NextIngredientGap :
      CSING.CanonicalScheduleIndependentNaturalChargeNextIngredientGap

    landedShiftConvergence :
      P0.ConvergenceBound {PGFSI.ShiftFlowState}

    landedRealizationMetricFamily :
      CDT.RealizationIndexedPointedMetricConvergenceTarget

    pathBOfflineL2Result :
      OfflineL2InsufficientForConvergenceRate

    strongerIngredients :
      List StrongerNaturalP2ConvergenceIngredient

    noPromotionAuthority :
      NaturalP2ConvergencePromotionAuthorityToken → ⊥

    receiptStillImpossible :
      NaturalP2ConvergencePromotionReceipt → ⊥

    obstructionSummary :
      String

canonicalNaturalP2BridgeCarrierGeneralConvergenceObstruction :
  NaturalP2BridgeCarrierGeneralConvergenceObstruction
canonicalNaturalP2BridgeCarrierGeneralConvergenceObstruction =
  record
    { canonicalDynamicsLaw =
        CDT.canonicalDynamicsLawTheorem
    ; normalizeAddSumInvariant =
        naturalP2NormalizeAddSumInvariant
    ; p2ScheduleBridgeObstruction =
        CPKSO.canonicalP2KeyScheduleBridgeObstruction
    ; p2NextIngredientGap =
        CSING.canonicalScheduleIndependentNaturalChargeNextIngredientGap
    ; landedShiftConvergence =
        CDT.CanonicalDynamicsLawTheorem.boundedConvergenceRate
          CDT.canonicalDynamicsLawTheorem
    ; landedRealizationMetricFamily =
        CDT.CanonicalDynamicsLawTheorem.realizationMetricConvergenceFamily
          CDT.canonicalDynamicsLawTheorem
    ; pathBOfflineL2Result =
        canonicalOfflineL2InsufficientForConvergenceRate
    ; strongerIngredients =
        canonicalP2KeyScheduleBridgeNeeded
        ∷ carrierTransportPreservesRateNeeded
        ∷ uniformRealizationRateBeyondShiftFlowNeeded
        ∷ offlineL2ToCarrierGeneralRateLiftNeeded
        ∷ []
    ; noPromotionAuthority =
        naturalP2ConvergencePromotionAuthorityUnavailable
    ; receiptStillImpossible =
        naturalP2ConvergencePromotionReceiptImpossible
    ; obstructionSummary =
        "Sharper W2 status: normalizeAdd preserves lhs+rhs and all p-adic valuations of that sum definitionally, so the carry-field obstruction is not the right invariant target; promotion still needs carrier transport preserving the pointed rate plus uniform realization-rate evidence beyond the shift-flow carrier and the constructorless authority token"
    }

record NaturalP2ConvergencePromotionCurrentStatus : Setω where
  field
    canonicalDynamicsLaw :
      CDT.CanonicalDynamicsLawTheorem

    landedShiftConvergence :
      P0.ConvergenceBound {PGFSI.ShiftFlowState}

    landedConcreteShiftTarget :
      CDT.ShiftConvergenceRateTarget

    landedPointedMetricTarget :
      CDT.PointedMetricHorizonConvergenceTarget
        PGFSI.ShiftFlowState

    landedRealizationMetricFamily :
      CDT.RealizationIndexedPointedMetricConvergenceTarget

    impossibilityDiagnostic :
      NaturalP2ConvergencePromotionImpossibilityDiagnostic

    sharperTypedObstruction :
      NaturalP2BridgeCarrierGeneralConvergenceObstruction

    pathBOfflineL2Result :
      OfflineL2InsufficientForConvergenceRate

    normalizeAddSumInvariant :
      NASP.NormalizeAddSumPreservationReceipt

    missingFields :
      List NaturalP2ConvergenceMissingField

    requiredNextReceipt :
      String

    landedBoundary :
      List String

    nonPromotionBoundary :
      List String

currentNaturalP2ConvergencePromotionStatus :
  NaturalP2ConvergencePromotionCurrentStatus
currentNaturalP2ConvergencePromotionStatus =
  record
    { canonicalDynamicsLaw =
        CDT.canonicalDynamicsLawTheorem
    ; landedShiftConvergence =
        CDT.CanonicalDynamicsLawTheorem.boundedConvergenceRate
          CDT.canonicalDynamicsLawTheorem
    ; landedConcreteShiftTarget =
        CDT.CanonicalDynamicsLawTheorem.concreteConvergenceRateTarget
          CDT.canonicalDynamicsLawTheorem
    ; landedPointedMetricTarget =
        CDT.CanonicalDynamicsLawTheorem.pointedMetricConvergenceTarget
          CDT.canonicalDynamicsLawTheorem
    ; landedRealizationMetricFamily =
        CDT.CanonicalDynamicsLawTheorem.realizationMetricConvergenceFamily
          CDT.canonicalDynamicsLawTheorem
    ; impossibilityDiagnostic =
        record
          { authorityUnavailable =
              naturalP2ConvergencePromotionAuthorityUnavailable
          ; receiptImpossible =
              naturalP2ConvergencePromotionReceiptImpossible
          ; typedMissingFields =
              missingPromotionAuthorityToken
              ∷ missingNaturalBridgeOrObstruction
              ∷ missingNaturalityCarrier
              ∷ missingP2SingleStepCarrier
              ∷ missingP2DoubleStepCarrier
              ∷ missingP2NaturalityLaw
              ∷ missingP2CoherenceLaw
              ∷ missingCarrierTransportLaw
              ∷ missingTransportPreservesConvergenceLaw
              ∷ missingCarrierGeneralConvergenceRate
              ∷ missingRealizationUniformityLaw
              ∷ missingUniformRealizationRateBeyondShiftFlow
              ∷ missingOfflineL2ToCarrierRateLift
              ∷ []
          ; obstructionSummary =
              "NaturalP2ConvergencePromotionReceipt is uninhabitable here because the authority token has no constructor; landed shift-flow convergence does not provide natural p2 or carrier-general convergence authority"
          }
    ; sharperTypedObstruction =
        canonicalNaturalP2BridgeCarrierGeneralConvergenceObstruction
    ; pathBOfflineL2Result =
        canonicalOfflineL2InsufficientForConvergenceRate
    ; normalizeAddSumInvariant =
        naturalP2NormalizeAddSumInvariant
    ; missingFields =
        missingPromotionAuthorityToken
        ∷ missingNaturalityCarrier
        ∷ missingP2SingleStepCarrier
        ∷ missingP2DoubleStepCarrier
        ∷ missingP2NaturalityLaw
        ∷ missingP2CoherenceLaw
        ∷ missingCarrierTransportLaw
        ∷ missingTransportPreservesConvergenceLaw
        ∷ missingCarrierGeneralConvergenceRate
        ∷ missingRealizationUniformityLaw
        ∷ missingUniformRealizationRateBeyondShiftFlow
        ∷ missingOfflineL2ToCarrierRateLift
        ∷ []
    ; requiredNextReceipt =
        "lift normalizeAdd sum/p-adic invariance into the W2 carrier-general convergence-rate receipt, and provide the promotion authority token"
    ; landedBoundary =
        "finite convergence is landed for the concrete shift-flow carrier"
        ∷ "pointed metric convergence is landed for the concrete shift-flow carrier"
        ∷ "realization-indexed metric convergence is landed for realized shift-flow states"
        ∷ "offline L2 obstruction certificate is landed as a negative below-delta p2-key candidate result"
        ∷ "normalizeAdd preserves lhs+rhs and tracked-prime valuations of that sum by definitional equality"
        ∷ []
    ; nonPromotionBoundary =
        "This module is a W2 promotion-obligation surface only"
        ∷ "The carry-field obstruction target is superseded by the sum-invariance target"
        ∷ "No constructorless W2 promotion authority token is constructed here"
        ∷ "Offline L2 is not promoted to a carrier-general convergence-rate receipt"
        ∷ "No convergence-rate theorem beyond the shift-flow carrier is promoted here"
        ∷ []
    }

canonicalNaturalP2ConvergenceMissingFields :
  List NaturalP2ConvergenceMissingField
canonicalNaturalP2ConvergenceMissingFields =
  NaturalP2ConvergencePromotionCurrentStatus.missingFields
    currentNaturalP2ConvergencePromotionStatus
