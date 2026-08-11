module DASHI.Papers.NavierStokes.PhysicalGalerkinConcreteRound30 where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNLuoPhysicalGalerkinFlowRound30Validation

record PhysicalGalerkinConcreteRound30Status : Set where
  constructor physical-galerkin-concrete-round30-status
  field
    literalLerayOutputTransverse : Bool
    literalLerayIdempotent : Bool
    exhaustiveProjectedNonlinearityTransverse : Bool
    literalViscousQuadraticCoefficientConstructed : Bool
    literalCoefficientListConstructed : Bool
    concreteDependentFieldAdapterConstructed : Bool
    physicalCoordinateTransportConstructed : Bool
    picardTransportConstructed : Bool
    energyContinuationReducerConstructed : Bool
    timeDependentShellReducerConstructed : Bool
    operatorCotlarReducerConstructed : Bool

    dependentStateLookupBuilderConstructed : Bool
    realCoordinateEquivalenceInstantiated : Bool
    realPicardLindelofInstantiated : Bool
    literalThreeLegEnergyIdentificationInstantiated : Bool
    realTimeIntegrationInstantiated : Bool
    literalTrajectoryShellTermsInstantiated : Bool
    physicalCrossShellDecayInstantiated : Bool
    nineOwnerEstimatesInstantiated : Bool
    unconditionalClayPromotion : Bool

open PhysicalGalerkinConcreteRound30Status public

canonicalPhysicalGalerkinConcreteRound30Status :
  PhysicalGalerkinConcreteRound30Status
canonicalPhysicalGalerkinConcreteRound30Status =
  physical-galerkin-concrete-round30-status
    true true true true true true true true true true true
    false false false false false false false false false

literalCoefficientConstructionClosed :
  literalViscousQuadraticCoefficientConstructed
    canonicalPhysicalGalerkinConcreteRound30Status ≡ true
literalCoefficientConstructionClosed = refl

concreteDependentAdapterClosed :
  concreteDependentFieldAdapterConstructed
    canonicalPhysicalGalerkinConcreteRound30Status ≡ true
concreteDependentAdapterClosed = refl

stateLookupStillOpen :
  dependentStateLookupBuilderConstructed
    canonicalPhysicalGalerkinConcreteRound30Status ≡ false
stateLookupStillOpen = refl

physicalOperatorDecayStillOpen :
  physicalCrossShellDecayInstantiated
    canonicalPhysicalGalerkinConcreteRound30Status ≡ false
physicalOperatorDecayStillOpen = refl

clayPromotionStillFalse :
  unconditionalClayPromotion
    canonicalPhysicalGalerkinConcreteRound30Status ≡ false
clayPromotionStillFalse = refl
