module DASHI.Biology.CrossKingdomActionPotentialAnaestheticBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.CrossKingdomAnaestheticActionBidiExact as Anaesthesia
import DASHI.Physics.Electromagnetism.PoissonNernstPlanckElectrodiffusionExact as PNP

------------------------------------------------------------------------
-- CROSS-KINGDOM ACTION POTENTIAL / ANAESTHETIC BIDI WELD
--
-- PRIMARY SOURCES
--
-- K. Yokawa et al., Annals of Botany 122(5) (2018), 747--756.
-- DOI: 10.1093/aob/mcx155.
--
-- S. Scherzer et al., Current Biology 32(19) (2022), 4251--4260.e5.
-- "A unique inventory of ion transporters poises the Venus flytrap to
-- fast-propagating action potentials and calcium waves".
-- DOI: 10.1016/j.cub.2022.08.051.
--
-- R. Hedrich, New Phytologist 240(6) (2023), 2108--2117.
-- "Demystifying the Venus flytrap action potential".
-- DOI: 10.1111/nph.19113.
--
-- K. T. Wann, British Journal of Anaesthesia 71(1) (1993), 2--14.
-- "Neuronal sodium and potassium channels: structure and function".
-- DOI: 10.1093/bja/71.1.2.
--
-- SOURCE BOUNDARY
-- The plant side records the currently supported Dionaea sequence at the level
-- needed here: Ca2+ signalling, anion-dependent depolarisation, K+/H+-linked
-- repolarisation, propagated electrical/Ca2+ signals, and ether-sensitive
-- action-potential propagation. The animal side records the classical
-- Na+/K+-dominated neuronal action-potential carrier while leaving detailed
-- kinetics, cell class and anaesthetic pharmacology application-specific.
--
-- The shared formal object is therefore an electrical-excitability comparison,
-- not an assertion that the ionic implementations are identical.
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

------------------------------------------------------------------------
-- Lineage-specific ionic architectures.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Same physical formalism, different application receipts.
------------------------------------------------------------------------

record PNPCrossKingdomActionPotentialWeld : Set₁ where
  constructor pnpCrossKingdomActionPotentialWeld
  field
    plantApplication : PNP.ElectrodiffusionApplicationReceipt
    animalApplication : PNP.ElectrodiffusionApplicationReceipt

    plantApplicationIsPlant :
      PNP.application plantApplication ≡ PNP.plantRootIonTransport
    animalApplicationIsNeuronal :
      PNP.application animalApplication ≡ PNP.neuronalMembrane

    sameElectrodiffusionFormalismReference : String
    constitutiveParametersRemainLineageSpecificReference : String
    actionPotentialMembraneReductionReference : String

open PNPCrossKingdomActionPotentialWeld public

------------------------------------------------------------------------
-- Forward direction: anaesthetic exposure suppresses a concrete electrical
-- propagation endpoint in each lineage.
------------------------------------------------------------------------

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
    plantDuringSuppressed :
      plantPropagation plantDuring ≡ propagationSuppressed
    plantAfterRecovers :
      plantPropagation plantAfterRecovery ≡ recoveredPropagation

    animalBeforePropagates : animalPropagation animalBefore ≡ propagates
    animalDuringSuppressed :
      animalPropagation animalDuring ≡ propagationSuppressed
    animalAfterRecovers :
      animalPropagation animalAfterRecovery ≡ recoveredPropagation

    plantAnaestheticReference : String
    animalAnaestheticReference : String
    recoveryReference : String

open ActionPotentialSuppressionTrace public

------------------------------------------------------------------------
-- Backward direction: shared dynamical invariants do not license ionic or
-- organism-level identity.
------------------------------------------------------------------------

record ActionPotentialBackwardAudit : Set where
  constructor actionPotentialBackwardAudit
  field
    sharedThresholdDynamics : Bool
    sharedThresholdDynamicsIsTrue : sharedThresholdDynamics ≡ true

    sharedPropagationPhenomenology : Bool
    sharedPropagationPhenomenologyIsTrue :
      sharedPropagationPhenomenology ≡ true

    identicalDominantDepolarisingIon : Bool
    identicalDominantDepolarisingIonIsFalse :
      identicalDominantDepolarisingIon ≡ false

    identicalChannelInventory : Bool
    identicalChannelInventoryIsFalse :
      identicalChannelInventory ≡ false

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

------------------------------------------------------------------------
-- BIDI object: common invariants are explicitly recovered from both lineage
-- implementations, while lineage-specific carriers remain separate.
------------------------------------------------------------------------

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

    plantEndpointIsAnaestheticAPSuppression :
      Anaesthesia.PlantAnaestheticEndpoint
    plantEndpointIsAnaestheticAPSuppression =
      Anaesthesia.plantActionPotentialSuppressed

    animalEndpointIsElectricalSuppression :
      Anaesthesia.AnimalAnaestheticEndpoint
    animalEndpointIsElectricalSuppression =
      Anaesthesia.neuronalExcitabilityAltered

    crossKingdomComparisonReference : String

open CrossKingdomActionPotentialBidi public

------------------------------------------------------------------------
-- Exact non-identifications.
------------------------------------------------------------------------

plantCalciumRoleIsNotAnimalSodiumRole :
  calciumEntryRole ≡ sodiumDepolarisationRole → ⊥
plantCalciumRoleIsNotAnimalSodiumRole ()

plantAnionDepolarisationIsNotAnimalSodiumDepolarisation :
  anionDepolarisationRole ≡ sodiumDepolarisationRole → ⊥
plantAnionDepolarisationIsNotAnimalSodiumDepolarisation ()

plantAndAnimalPotassiumRolesRemainDistinct :
  potassiumRepolarisationRole ≡ potassiumAnimalRepolarisationRole → ⊥
plantAndAnimalPotassiumRolesRemainDistinct ()

------------------------------------------------------------------------
-- Source constants.
------------------------------------------------------------------------

yokawaDOI : String
yokawaDOI = "10.1093/aob/mcx155"

scherzerVenusFlytrapTransporterDOI : String
scherzerVenusFlytrapTransporterDOI = "10.1016/j.cub.2022.08.051"

hedrichVenusFlytrapAPDOI : String
hedrichVenusFlytrapAPDOI = "10.1111/nph.19113"

wannNeuronalNaKDOI : String
wannNeuronalNaKDOI = "10.1093/bja/71.1.2"
