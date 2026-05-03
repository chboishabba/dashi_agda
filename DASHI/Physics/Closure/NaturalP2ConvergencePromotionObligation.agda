module DASHI.Physics.Closure.NaturalP2ConvergencePromotionObligation where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CanonicalDynamicsLawTheorem as CDT
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

------------------------------------------------------------------------
-- Current non-promoting status.

data NaturalP2ConvergenceMissingField : Set where
  missingPromotionAuthorityToken :
    NaturalP2ConvergenceMissingField
  missingNaturalBridgeOrObstruction :
    NaturalP2ConvergenceMissingField
  missingP2NaturalityLaw :
    NaturalP2ConvergenceMissingField
  missingP2CoherenceLaw :
    NaturalP2ConvergenceMissingField
  missingCarrierTransportLaw :
    NaturalP2ConvergenceMissingField
  missingCarrierGeneralConvergenceRate :
    NaturalP2ConvergenceMissingField
  missingUniformRealizationRateBeyondShiftFlow :
    NaturalP2ConvergenceMissingField

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
    ; missingFields =
        missingPromotionAuthorityToken
        ∷ missingNaturalBridgeOrObstruction
        ∷ missingP2NaturalityLaw
        ∷ missingP2CoherenceLaw
        ∷ missingCarrierTransportLaw
        ∷ missingCarrierGeneralConvergenceRate
        ∷ missingUniformRealizationRateBeyondShiftFlow
        ∷ []
    ; requiredNextReceipt =
        "provide natural p2 bridge or obstruction plus carrier-general convergence-rate receipt beyond the shift-flow carrier"
    ; landedBoundary =
        "finite convergence is landed for the concrete shift-flow carrier"
        ∷ "pointed metric convergence is landed for the concrete shift-flow carrier"
        ∷ "realization-indexed metric convergence is landed for realized shift-flow states"
        ∷ []
    ; nonPromotionBoundary =
        "This module is a W2 promotion-obligation surface only"
        ∷ "No natural p2 bridge is constructed here"
        ∷ "No p2 obstruction over an admissible candidate family is constructed here"
        ∷ "No convergence-rate theorem beyond the shift-flow carrier is promoted here"
        ∷ []
    }

canonicalNaturalP2ConvergenceMissingFields :
  List NaturalP2ConvergenceMissingField
canonicalNaturalP2ConvergenceMissingFields =
  NaturalP2ConvergencePromotionCurrentStatus.missingFields
    currentNaturalP2ConvergencePromotionStatus
