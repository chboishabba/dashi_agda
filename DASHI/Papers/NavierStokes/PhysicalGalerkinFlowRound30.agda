module DASHI.Papers.NavierStokes.PhysicalGalerkinFlowRound30 where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNLuoPhysicalGalerkinFlowRound30Validation

record PhysicalGalerkinFlowRound30Status : Set where
  constructor physical-galerkin-flow-round30-status
  field
    physicalVectorFieldCodomainProduced : Bool
    positiveAndNegativeTransversalityProduced : Bool
    dependentPhysicalVectorFieldLiftProduced : Bool
    physicalCoordinateEquivalenceInterfaceProduced : Bool
    completeVectorLipschitzTransportProduced : Bool
    picardLindelofTransportProduced : Bool
    exhaustiveTriadCancellationFoldProduced : Bool
    differentialEnergyIdentityProduced : Bool
    integratedEnergyContinuationBridgeProduced : Bool
    noFiniteMaximalTimeReducerProduced : Bool
    timeDependentFiveSourceReducerProduced : Bool
    operatorCotlarSteinReducerProduced : Bool

    literalTriadCoefficientProducerSupplied : Bool
    concretePhysicalCoordinateEquivalenceSupplied : Bool
    realPicardLindelofAuthoritySupplied : Bool
    literalNavierStokesEnergyPacketIdentificationSupplied : Bool
    realTimeIntegrationAuthoritySupplied : Bool
    finiteGlobalPhysicalFlowInstantiated : Bool
    literalTrajectoryShellAuthoritySupplied : Bool
    physicalCrossShellOperatorDecaySupplied : Bool
    physicalNineOwnerEstimatesProduced : Bool
    unconditionalClayPromotion : Bool

open PhysicalGalerkinFlowRound30Status public

canonicalPhysicalGalerkinFlowRound30Status :
  PhysicalGalerkinFlowRound30Status
canonicalPhysicalGalerkinFlowRound30Status =
  physical-galerkin-flow-round30-status
    true true true true true true true true true true true true
    false false false false false false false false false false

physicalFiniteFlowReducerAdvanced :
  noFiniteMaximalTimeReducerProduced
    canonicalPhysicalGalerkinFlowRound30Status ≡ true
physicalFiniteFlowReducerAdvanced = refl

physicalShellReducerAdvanced :
  timeDependentFiveSourceReducerProduced
    canonicalPhysicalGalerkinFlowRound30Status ≡ true
physicalShellReducerAdvanced = refl

operatorCotlarReducerAdvanced :
  operatorCotlarSteinReducerProduced
    canonicalPhysicalGalerkinFlowRound30Status ≡ true
operatorCotlarReducerAdvanced = refl

literalPhysicalFlowStillRequiresProducers :
  finiteGlobalPhysicalFlowInstantiated
    canonicalPhysicalGalerkinFlowRound30Status ≡ false
literalPhysicalFlowStillRequiresProducers = refl

literalPhysicalShellStillOpen :
  literalTrajectoryShellAuthoritySupplied
    canonicalPhysicalGalerkinFlowRound30Status ≡ false
literalPhysicalShellStillOpen = refl

physicalOperatorDecayStillOpen :
  physicalCrossShellOperatorDecaySupplied
    canonicalPhysicalGalerkinFlowRound30Status ≡ false
physicalOperatorDecayStillOpen = refl

clayPromotionStillFalse :
  unconditionalClayPromotion
    canonicalPhysicalGalerkinFlowRound30Status ≡ false
clayPromotionStillFalse = refl
