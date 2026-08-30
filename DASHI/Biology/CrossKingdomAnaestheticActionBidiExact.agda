module DASHI.Biology.CrossKingdomAnaestheticActionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.Cell.BioelectricNetwork as Bioelectric

------------------------------------------------------------------------
-- CROSS-KINGDOM ANAESTHETIC ACTION: BIDI SOURCE / MECHANISM / ENDPOINT WELD
--
-- PRIMARY SOURCES
--
-- K. Yokawa, T. Kagenishi, A. Pavlovic, S. Gall, M. Weiland,
-- S. Mancuso, F. Baluska,
-- "Anaesthetics stop diverse plant organ movements, affect endocytic vesicle
-- recycling and ROS homeostasis, and block action potentials in Venus
-- flytraps", Annals of Botany 122(5) (2018), 747--756.
-- DOI: 10.1093/aob/mcx155.
--
-- M. B. Kelz and G. A. Mashour,
-- "The Biology of General Anesthesia from Paramecium to Primate",
-- Current Biology 29(22) (2019), R1199--R1210.
-- DOI: 10.1016/j.cub.2019.09.071.
--
-- A. Draguhn, D. G. Mallatt, K. R. Robinson,
-- "Anesthetics and plants: no pain, no brain, and therefore no
-- consciousness", Protoplasma 258 (2021), 239--248.
-- DOI: 10.1007/s00709-020-01550-9.
--
-- SOURCE BOUNDARY
-- Yokawa et al. support plant movement suppression, Venus-flytrap action-
-- potential blockade, altered endocytic vesicle recycling, altered ROS
-- homeostasis, and recovery after removal for the tested anaesthetic
-- exposures. Kelz/Mashour support a cross-organism comparison in which
-- several molecular/cellular substrates are conserved while organism-level
-- endpoints differ. Draguhn/Mallatt/Robinson explicitly reject the inference
-- from plant anaesthetic sensitivity to plant pain or consciousness.
--
-- The typed comparison below is a DASHI reconstruction. It does not identify
-- plant electrical signalling with animal neural computation, and it does not
-- infer consciousness from response suppression.
------------------------------------------------------------------------

data Lineage : Set where
  plantLineage
  animalLineage
  : Lineage

data ActionLayer : Set where
  molecularLayer
  membraneElectricalLayer
  cellularProcessLayer
  tissueNetworkLayer
  wholeOrganismLayer
  consciousStateLayer
  : ActionLayer

data SharedCellularSubstrate : Set where
  ionChannelSubstrate
  membraneSubstrate
  cytoskeletalSubstrate
  mitochondrialSubstrate
  coupledElectricalActivitySubstrate
  : SharedCellularSubstrate

data PlantAnaestheticEndpoint : Set where
  plantActionPotentialSuppressed
  plantOrganMovementSuppressed
  plantEndocyticRecyclingAltered
  plantROSHomeostasisAltered
  plantGerminationOrGrowthAltered
  plantRecoveryAfterRemoval
  : PlantAnaestheticEndpoint

data AnimalAnaestheticEndpoint : Set where
  neuronalExcitabilityAltered
  synapticTransmissionAltered
  neuralNetworkCoordinationDisrupted
  immobilityEndpoint
  amnesiaEndpoint
  unconsciousnessEndpoint
  recoveryAfterRemoval
  : AnimalAnaestheticEndpoint

data CrossKingdomEndpoint : Set where
  plantEndpointTag : PlantAnaestheticEndpoint → CrossKingdomEndpoint
  animalEndpointTag : AnimalAnaestheticEndpoint → CrossKingdomEndpoint

data EvidentiaryStatus : Set where
  directlyObserved
  mechanisticallySupported
  comparativeHypothesis
  notEstablished
  : EvidentiaryStatus

plantAndAnimalDistinct : plantLineage ≡ animalLineage → ⊥
plantAndAnimalDistinct ()

cellularAndConsciousLayersDistinct :
  cellularProcessLayer ≡ consciousStateLayer → ⊥
cellularAndConsciousLayersDistinct ()

plantAndAnimalEndpointTagsDistinct :
  (p : PlantAnaestheticEndpoint) →
  (a : AnimalAnaestheticEndpoint) →
  plantEndpointTag p ≡ animalEndpointTag a → ⊥
plantAndAnimalEndpointTagsDistinct _ _ ()

record ForwardAnaestheticTrace : Set₁ where
  constructor forwardAnaestheticTrace
  field
    Anaesthetic : Set
    anaesthetic : Anaesthetic
    sharedSubstrate : SharedCellularSubstrate
    PlantState : Set
    AnimalState : Set
    plantBefore : PlantState
    plantAfter : PlantState
    animalBefore : AnimalState
    animalAfter : AnimalState
    plantEndpoint : PlantAnaestheticEndpoint
    animalEndpoint : AnimalAnaestheticEndpoint
    plantPerturbation : Anaesthetic → PlantState → PlantState
    animalPerturbation : Anaesthetic → AnimalState → AnimalState
    plantTransitionIsActual :
      plantPerturbation anaesthetic plantBefore ≡ plantAfter
    animalTransitionIsActual :
      animalPerturbation anaesthetic animalBefore ≡ animalAfter
    sharedSubstrateReference : String
    plantEndpointReference : String
    animalEndpointReference : String

open ForwardAnaestheticTrace public

record BackwardAnaestheticAudit : Set₁ where
  constructor backwardAnaestheticAudit
  field
    observedPlantEndpoint : PlantAnaestheticEndpoint
    observedAnimalEndpoint : AnimalAnaestheticEndpoint
    plantMechanismStatus : EvidentiaryStatus
    animalMechanismStatus : EvidentiaryStatus
    plantConsciousnessStatus : EvidentiaryStatus
    animalConsciousnessStatus : EvidentiaryStatus
    plantEndpointToMechanismReference : String
    animalEndpointToMechanismReference : String
    consciousnessBoundaryReference : String
    plantAnaestheticResponseDoesNotEstablishConsciousness :
      plantConsciousnessStatus ≡ notEstablished

open BackwardAnaestheticAudit public

record CrossKingdomAnaestheticBidi : Set₁ where
  constructor crossKingdomAnaestheticBidi
  field
    forward : ForwardAnaestheticTrace
    backward : BackwardAnaestheticAudit
    samePlantEndpoint :
      plantEndpoint forward ≡ observedPlantEndpoint backward
    sameAnimalEndpoint :
      animalEndpoint forward ≡ observedAnimalEndpoint backward
    comparisonLevel : ActionLayer
    sourceSynthesisReference : String

open CrossKingdomAnaestheticBidi public

record BioelectricComparisonBridge
    (B : Bioelectric.BioelectricNetwork) : Set₁ where
  constructor bioelectricComparisonBridge
  field
    plantElectricalEndpoint : PlantAnaestheticEndpoint
    animalElectricalEndpoint : AnimalAnaestheticEndpoint
    sharedCarrierIsBioelectric : Set
    sharedCarrierWitness : sharedCarrierIsBioelectric
    plantSignalArchitectureReference : String
    animalNeuralArchitectureReference : String
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
  anaestheticInferenceBoundary
    false refl
    false refl
    false refl
    true refl
    true refl

plantActionPotentialSuppressionIsNotAnimalUnconsciousness :
  plantEndpointTag plantActionPotentialSuppressed
  ≡ animalEndpointTag unconsciousnessEndpoint → ⊥
plantActionPotentialSuppressionIsNotAnimalUnconsciousness ()

plantMovementSuppressionIsNotAnimalUnconsciousness :
  plantEndpointTag plantOrganMovementSuppressed
  ≡ animalEndpointTag unconsciousnessEndpoint → ⊥
plantMovementSuppressionIsNotAnimalUnconsciousness ()

notEstablishedIsNotDirectObservation :
  notEstablished ≡ directlyObserved → ⊥
notEstablishedIsNotDirectObservation ()

yokawaPlantAnaesthesiaDOI : String
yokawaPlantAnaesthesiaDOI = "10.1093/aob/mcx155"

kelzMashourComparativeAnaesthesiaDOI : String
kelzMashourComparativeAnaesthesiaDOI = "10.1016/j.cub.2019.09.071"

draguhnMallattRobinsonPlantConsciousnessBoundaryDOI : String
draguhnMallattRobinsonPlantConsciousnessBoundaryDOI =
  "10.1007/s00709-020-01550-9"
