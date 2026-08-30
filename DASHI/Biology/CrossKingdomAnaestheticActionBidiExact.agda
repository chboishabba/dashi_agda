module DASHI.Biology.CrossKingdomAnaestheticActionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Biology.Cell.BioelectricNetwork as Bioelectric

------------------------------------------------------------------------
-- Cross-kingdom anaesthetic action.
-- Sources: Yokawa et al. 2018 (10.1093/aob/mcx155), Kelz & Mashour 2019
-- (10.1016/j.cub.2019.09.071), Draguhn/Mallatt/Robinson 2021
-- (10.1007/s00709-020-01550-9). Plant anaesthetic sensitivity is not promoted
-- to evidence of pain or consciousness.
------------------------------------------------------------------------

data Lineage : Set where plantLineage animalLineage : Lineage

data ActionLayer : Set where
  molecularLayer membraneElectricalLayer cellularProcessLayer tissueNetworkLayer
  wholeOrganismLayer consciousStateLayer : ActionLayer

data SharedCellularSubstrate : Set where
  ionChannelSubstrate membraneSubstrate cytoskeletalSubstrate
  mitochondrialSubstrate coupledElectricalActivitySubstrate : SharedCellularSubstrate

data PlantAnaestheticEndpoint : Set where
  plantActionPotentialSuppressed plantOrganMovementSuppressed
  plantEndocyticRecyclingAltered plantROSHomeostasisAltered
  plantGerminationOrGrowthAltered plantRecoveryAfterRemoval : PlantAnaestheticEndpoint

data AnimalAnaestheticEndpoint : Set where
  neuronalExcitabilityAltered synapticTransmissionAltered
  neuralNetworkCoordinationDisrupted immobilityEndpoint amnesiaEndpoint
  unconsciousnessEndpoint recoveryAfterRemoval : AnimalAnaestheticEndpoint

data CrossKingdomEndpoint : Set where
  plantEndpointTag : PlantAnaestheticEndpoint → CrossKingdomEndpoint
  animalEndpointTag : AnimalAnaestheticEndpoint → CrossKingdomEndpoint

data EvidentiaryStatus : Set where
  directlyObserved mechanisticallySupported comparativeHypothesis notEstablished
  : EvidentiaryStatus

plantAndAnimalDistinct : plantLineage ≡ animalLineage → ⊥
plantAndAnimalDistinct ()
cellularAndConsciousLayersDistinct : cellularProcessLayer ≡ consciousStateLayer → ⊥
cellularAndConsciousLayersDistinct ()
plantAndAnimalEndpointTagsDistinct :
  (p : PlantAnaestheticEndpoint) → (a : AnimalAnaestheticEndpoint) →
  plantEndpointTag p ≡ animalEndpointTag a → ⊥
plantAndAnimalEndpointTagsDistinct _ _ ()

record ForwardAnaestheticTrace : Set₁ where
  constructor forwardAnaestheticTrace
  field
    Anaesthetic : Set
    anaesthetic : Anaesthetic
    sharedSubstrate : SharedCellularSubstrate
    PlantState AnimalState : Set
    plantBefore plantAfter : PlantState
    animalBefore animalAfter : AnimalState
    plantEndpoint : PlantAnaestheticEndpoint
    animalEndpoint : AnimalAnaestheticEndpoint
    plantPerturbation : Anaesthetic → PlantState → PlantState
    animalPerturbation : Anaesthetic → AnimalState → AnimalState
    plantTransitionIsActual : plantPerturbation anaesthetic plantBefore ≡ plantAfter
    animalTransitionIsActual : animalPerturbation anaesthetic animalBefore ≡ animalAfter
    sharedSubstrateReference plantEndpointReference animalEndpointReference : String
open ForwardAnaestheticTrace public

record BackwardAnaestheticAudit : Set₁ where
  constructor backwardAnaestheticAudit
  field
    observedPlantEndpoint : PlantAnaestheticEndpoint
    observedAnimalEndpoint : AnimalAnaestheticEndpoint
    plantMechanismStatus animalMechanismStatus : EvidentiaryStatus
    plantConsciousnessStatus animalConsciousnessStatus : EvidentiaryStatus
    plantEndpointToMechanismReference animalEndpointToMechanismReference : String
    consciousnessBoundaryReference : String
    plantAnaestheticResponseDoesNotEstablishConsciousness :
      plantConsciousnessStatus ≡ notEstablished
open BackwardAnaestheticAudit public

record CrossKingdomAnaestheticBidi : Set₁ where
  constructor crossKingdomAnaestheticBidi
  field
    forward : ForwardAnaestheticTrace
    backward : BackwardAnaestheticAudit
    samePlantEndpoint : plantEndpoint forward ≡ observedPlantEndpoint backward
    sameAnimalEndpoint : animalEndpoint forward ≡ observedAnimalEndpoint backward
    comparisonLevel : ActionLayer
    sourceSynthesisReference : String
open CrossKingdomAnaestheticBidi public

record BioelectricComparisonBridge (B : Bioelectric.BioelectricNetwork) : Set₁ where
  constructor bioelectricComparisonBridge
  field
    plantElectricalEndpoint : PlantAnaestheticEndpoint
    animalElectricalEndpoint : AnimalAnaestheticEndpoint
    sharedCarrierIsBioelectric : Set
    sharedCarrierWitness : sharedCarrierIsBioelectric
    plantSignalArchitectureReference animalNeuralArchitectureReference : String
    ionChannelComparisonReference : String
    plantElectricalSignallingIsAnimalNeuralNetwork : Bool
    plantElectricalSignallingIsAnimalNeuralNetworkIsFalse :
      plantElectricalSignallingIsAnimalNeuralNetwork ≡ false
open BioelectricComparisonBridge public

record AnaestheticInferenceBoundary : Set where
  constructor anaestheticInferenceBoundary
  field
    sharedCellularSensitivityImpliesSharedConsciousState : Bool
    sharedCellularSensitivityImpliesSharedConsciousStateIsFalse :
      sharedCellularSensitivityImpliesSharedConsciousState ≡ false
    plantActionPotentialBlockImpliesUnconsciousness : Bool
    plantActionPotentialBlockImpliesUnconsciousnessIsFalse :
      plantActionPotentialBlockImpliesUnconsciousness ≡ false
    plantMovementSuppressionImpliesPainCapacity : Bool
    plantMovementSuppressionImpliesPainCapacityIsFalse :
      plantMovementSuppressionImpliesPainCapacity ≡ false
    conservedIonChannelEffectsPermitCrossKingdomMechanisticComparison : Bool
    conservedIonChannelEffectsPermitCrossKingdomMechanisticComparisonIsTrue :
      conservedIonChannelEffectsPermitCrossKingdomMechanisticComparison ≡ true
    lineageSpecificNetworkArchitectureMustRemainExplicit : Bool
    lineageSpecificNetworkArchitectureMustRemainExplicitIsTrue :
      lineageSpecificNetworkArchitectureMustRemainExplicit ≡ true

canonicalAnaestheticInferenceBoundary : AnaestheticInferenceBoundary
canonicalAnaestheticInferenceBoundary =
  anaestheticInferenceBoundary false refl false refl false refl true refl true refl

plantActionPotentialSuppressionIsNotAnimalUnconsciousness :
  plantEndpointTag plantActionPotentialSuppressed ≡ animalEndpointTag unconsciousnessEndpoint → ⊥
plantActionPotentialSuppressionIsNotAnimalUnconsciousness ()
plantMovementSuppressionIsNotAnimalUnconsciousness :
  plantEndpointTag plantOrganMovementSuppressed ≡ animalEndpointTag unconsciousnessEndpoint → ⊥
plantMovementSuppressionIsNotAnimalUnconsciousness ()
notEstablishedIsNotDirectObservation : notEstablished ≡ directlyObserved → ⊥
notEstablishedIsNotDirectObservation ()

yokawaPlantAnaesthesiaDOI : String
yokawaPlantAnaesthesiaDOI = "10.1093/aob/mcx155"
kelzMashourComparativeAnaesthesiaDOI : String
kelzMashourComparativeAnaesthesiaDOI = "10.1016/j.cub.2019.09.071"
draguhnMallattRobinsonPlantConsciousnessBoundaryDOI : String
draguhnMallattRobinsonPlantConsciousnessBoundaryDOI = "10.1007/s00709-020-01550-9"
