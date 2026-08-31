module DASHI.Biology.CrossKingdomActionPotentialAnaestheticBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.CrossKingdomAnaestheticActionBidiExact as Anaesthesia
import DASHI.Physics.Electromagnetism.PoissonNernstPlanckElectrodiffusionExact as PNP

------------------------------------------------------------------------
-- CROSS-KINGDOM ACTION POTENTIAL / ANAESTHETIC BIDI WELD
--
-- PRIMARY SOURCES
-- Yokawa et al. 2018. DOI: 10.1093/aob/mcx155.
-- Scherzer et al. 2022. DOI: 10.1016/j.cub.2022.08.051.
-- Hedrich 2023. DOI: 10.1111/nph.19113.
-- Wann 1993. DOI: 10.1093/bja/71.1.2.
--
-- SOURCE BOUNDARY
-- The plant side records supported Dionaea features: Ca2+ signalling,
-- anion-dependent depolarisation, K+/H+-linked repolarisation, propagated
-- electrical/Ca2+ signals, and ether-sensitive action-potential propagation.
-- The animal side records the classical Na+/K+-dominated neuronal carrier.
-- Shared electrical excitability does not identify the ionic implementations.
------------------------------------------------------------------------

data IonicRole : Set where
  calciumEntryRole
  anionDepolarisationRole
  potassiumRepolarisationRole
  protonPumpRepolarisationRole
  sodiumDepolarisationRole
  potassiumAnimalRepolarisationRole
  : IonicRole

data APPhase : Set where
  restingPhase
  triggerPhase
  depolarisationPhase
  repolarisationPhase
  afterHyperpolarisationPhase
  recoveredPhase
  : APPhase

data PropagationStatus : Set where
  propagates
  propagationSuppressed
  recoveredPropagation
  : PropagationStatus

data ExcitabilityInvariant : Set where
  thresholdTriggeredTransition
  membranePotentialExcursion
  spatialPropagation
  refractoryOrRecoveryStructure
  reversibleSuppression
  : ExcitabilityInvariant

record PlantActionPotentialArchitecture : Set₁ where
  constructor plantActionPotentialArchitecture
  field
    calciumSpecies : PNP.IonicSpeciesState
    anionSpecies : PNP.IonicSpeciesState
    potassiumSpecies : PNP.IonicSpeciesState
    calciumRole : IonicRole
    calciumRoleIsEntry : calciumRole ≡ calciumEntryRole
    anionRole : IonicRole
    anionRoleIsDepolarisation : anionRole ≡ anionDepolarisationRole
    potassiumRole : IonicRole
    potassiumRoleIsRepolarisation : potassiumRole ≡ potassiumRepolarisationRole
    PhaseState : Set
    phase : PhaseState → APPhase
    propagation : PhaseState → PropagationStatus
    calciumPropagationReference : String
    anionDepolarisationReference : String
    potassiumRepolarisationReference : String
    protonPumpRepolarisationReference : String
    plantActionPotentialValidationReference : String

open PlantActionPotentialArchitecture public

record AnimalActionPotentialArchitecture : Set₁ where
  constructor animalActionPotentialArchitecture
  field
    sodiumSpecies : PNP.IonicSpeciesState
    potassiumSpecies : PNP.IonicSpeciesState
    sodiumRole : IonicRole
    sodiumRoleIsDepolarisation : sodiumRole ≡ sodiumDepolarisationRole
    potassiumRole : IonicRole
    potassiumRoleIsRepolarisation :
      potassiumRole ≡ potassiumAnimalRepolarisationRole
    PhaseState : Set
    phase : PhaseState → APPhase
    propagation : PhaseState → PropagationStatus
    sodiumDepolarisationReference : String
    potassiumRepolarisationReference : String
    neuronalPropagationReference : String
    animalActionPotentialValidationReference : String

open AnimalActionPotentialArchitecture public

record PNPCrossKingdomActionPotentialWeld : Set₁ where
  constructor pnpCrossKingdomActionPotentialWeld
  field
    plantApplication : PNP.ElectrodiffusionApplicationReceipt
    animalApplication : PNP.ElectrodiffusionApplicationReceipt
    plantApplicationIsExcitablePlantMembrane :
      PNP.application plantApplication ≡ PNP.plantExcitableMembrane
    animalApplicationIsNeuronal :
      PNP.application animalApplication ≡ PNP.neuronalMembrane
    sameElectrodiffusionFormalismReference : String
    constitutiveParametersRemainLineageSpecificReference : String
    actionPotentialMembraneReductionReference : String

open PNPCrossKingdomActionPotentialWeld public

record ActionPotentialSuppressionTrace : Set₁ where
  constructor actionPotentialSuppressionTrace
  field
    plantArchitecture : PlantActionPotentialArchitecture
    animalArchitecture : AnimalActionPotentialArchitecture
    Anaesthetic : Set
    anaesthetic : Anaesthetic
    PlantState : Set
    AnimalState : Set
    plantBefore : PlantState
    plantDuring : PlantState
    plantAfterRecovery : PlantState
    animalBefore : AnimalState
    animalDuring : AnimalState
    animalAfterRecovery : AnimalState
    plantPropagation : PlantState → PropagationStatus
    animalPropagation : AnimalState → PropagationStatus
    plantBeforePropagates : plantPropagation plantBefore ≡ propagates
    plantDuringSuppressed : plantPropagation plantDuring ≡ propagationSuppressed
    plantAfterRecovers : plantPropagation plantAfterRecovery ≡ recoveredPropagation
    animalBeforePropagates : animalPropagation animalBefore ≡ propagates
    animalDuringSuppressed : animalPropagation animalDuring ≡ propagationSuppressed
    animalAfterRecovers : animalPropagation animalAfterRecovery ≡ recoveredPropagation
    plantAnaestheticReference : String
    animalAnaestheticReference : String
    recoveryReference : String

open ActionPotentialSuppressionTrace public

record ActionPotentialBackwardAudit : Set where
  constructor actionPotentialBackwardAudit
  field
    sharedThresholdDynamics : Bool
    sharedThresholdDynamicsIsTrue : sharedThresholdDynamics ≡ true
    sharedPropagationPhenomenology : Bool
    sharedPropagationPhenomenologyIsTrue : sharedPropagationPhenomenology ≡ true
    identicalDominantDepolarisingIon : Bool
    identicalDominantDepolarisingIonIsFalse : identicalDominantDepolarisingIon ≡ false
    identicalChannelInventory : Bool
    identicalChannelInventoryIsFalse : identicalChannelInventory ≡ false
    actionPotentialSimilarityImpliesNeuralIdentity : Bool
    actionPotentialSimilarityImpliesNeuralIdentityIsFalse :
      actionPotentialSimilarityImpliesNeuralIdentity ≡ false
    actionPotentialSuppressionImpliesConsciousnessSuppressionInPlants : Bool
    actionPotentialSuppressionImpliesConsciousnessSuppressionInPlantsIsFalse :
      actionPotentialSuppressionImpliesConsciousnessSuppressionInPlants ≡ false

canonicalActionPotentialBackwardAudit : ActionPotentialBackwardAudit
canonicalActionPotentialBackwardAudit =
  actionPotentialBackwardAudit
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

record CrossKingdomActionPotentialBidi : Set₁ where
  constructor crossKingdomActionPotentialBidi
  field
    pnpWeld : PNPCrossKingdomActionPotentialWeld
    suppressionTrace : ActionPotentialSuppressionTrace
    backwardAudit : ActionPotentialBackwardAudit
    SharedInvariant : Set
    plantInvariant : SharedInvariant → ExcitabilityInvariant
    animalInvariant : SharedInvariant → ExcitabilityInvariant
    sameInvariantInterpretation :
      (i : SharedInvariant) → plantInvariant i ≡ animalInvariant i
    plantEndpoint : Anaesthesia.PlantAnaestheticEndpoint
    plantEndpointIsAPSuppression :
      plantEndpoint ≡ Anaesthesia.plantActionPotentialSuppressed
    animalEndpoint : Anaesthesia.AnimalAnaestheticEndpoint
    animalEndpointIsElectricalSuppression :
      animalEndpoint ≡ Anaesthesia.neuronalExcitabilityAltered
    crossKingdomComparisonReference : String

open CrossKingdomActionPotentialBidi public

plantCalciumRoleIsNotAnimalSodiumRole :
  calciumEntryRole ≡ sodiumDepolarisationRole → ⊥
plantCalciumRoleIsNotAnimalSodiumRole ()

plantAnionDepolarisationIsNotAnimalSodiumDepolarisation :
  anionDepolarisationRole ≡ sodiumDepolarisationRole → ⊥
plantAnionDepolarisationIsNotAnimalSodiumDepolarisation ()

plantAndAnimalPotassiumRolesRemainDistinct :
  potassiumRepolarisationRole ≡ potassiumAnimalRepolarisationRole → ⊥
plantAndAnimalPotassiumRolesRemainDistinct ()

yokawaDOI : String
yokawaDOI = "10.1093/aob/mcx155"

scherzerVenusFlytrapTransporterDOI : String
scherzerVenusFlytrapTransporterDOI = "10.1016/j.cub.2022.08.051"

hedrichVenusFlytrapAPDOI : String
hedrichVenusFlytrapAPDOI = "10.1111/nph.19113"

wannNeuronalNaKDOI : String
wannNeuronalNaKDOI = "10.1093/bja/71.1.2"
