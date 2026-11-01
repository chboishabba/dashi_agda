module DASHI.Biology.HeritableAgenticOrganisationEvolutionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.Evolution.EvolutionaryPopulationDynamics as Evolution
import DASHI.Biology.AgenticMaterialsControlCore as Agentic
import DASHI.Biology.ResourceCoupledLogisticReplicationExact as Resource
import DASHI.Biology.ResourceCoupledProtoAgencyRealisationExact as Proto

------------------------------------------------------------------------
-- HERITABLE AGENTIC ORGANISATION / EVOLUTION BRIDGE
--
-- EvolutionaryPopulationDynamics already owns genotype, inheritance, mutation,
-- recombination and selection.  AgenticMaterialsControlCore already owns
-- observation, policy, target and corrective action.  This module introduces
-- only the missing projection saying which genotype coordinate encodes the
-- agentic organisation, and explicit receipts for inheritance, variation and
-- selection of that coordinate.
--
-- A reproduced individual is not thereby a heritable agent.  Likewise a
-- mutation of the agency architecture code does not by itself establish a
-- changed phenotype, fitness advantage, open-ended evolution, or historical
-- abiogenesis path.
------------------------------------------------------------------------

record AgenticArchitectureProjection
    (E : Evolution.EvolutionarySystem) : Set₁ where
  constructor agentic-architecture-projection
  field
    Architecture : Set

    architectureOf :
      Evolution.EvolutionarySystem.Genotype E → Architecture

    architectureReference : String
    genotypeProjectionReference : String

open AgenticArchitectureProjection public

------------------------------------------------------------------------
-- Realisation into one existing AgenticMaterial interface.
--
-- Pointwise realisation is used instead of function extensionality.  Distinct
-- architecture codes may realise the same present AgenticMaterial behaviour;
-- injectivity is deliberately not assumed.
------------------------------------------------------------------------

record AgenticArchitectureRealisation
    {E : Evolution.EvolutionarySystem}
    (P : AgenticArchitectureProjection E)
    (M : Agentic.AgenticMaterial) : Set₁ where
  constructor agentic-architecture-realisation
  field
    architectureObserve :
      Architecture P → Agentic.State M → Agentic.Observation M

    architecturePolicy :
      Architecture P → Agentic.Observation M → Agentic.Action M

    architectureTarget :
      Architecture P → Agentic.State M

    observationRealises :
      (individual : Evolution.EvolutionarySystem.Individual E) →
      (state : Agentic.State M) →
      architectureObserve
        (architectureOf P
          (Evolution.EvolutionarySystem.genotypeOf E individual))
        state
      ≡ Agentic.observe M state

    policyRealises :
      (individual : Evolution.EvolutionarySystem.Individual E) →
      (observation : Agentic.Observation M) →
      architecturePolicy
        (architectureOf P
          (Evolution.EvolutionarySystem.genotypeOf E individual))
        observation
      ≡ Agentic.policy M observation

    targetRealises :
      (individual : Evolution.EvolutionarySystem.Individual E) →
      architectureTarget
        (architectureOf P
          (Evolution.EvolutionarySystem.genotypeOf E individual))
      ≡ Agentic.target M

    realisationReference : String

open AgenticArchitectureRealisation public

------------------------------------------------------------------------
-- Heredity of the agentic-architecture projection.
------------------------------------------------------------------------

record HeritableAgenticArchitectureLineage
    {E : Evolution.EvolutionarySystem}
    (P : AgenticArchitectureProjection E) : Set₁ where
  constructor heritable-agentic-architecture-lineage
  field
    parent child : Evolution.EvolutionarySystem.Individual E

    inherited :
      Evolution.EvolutionarySystem.Inherited E parent child

    architectureInherited :
      architectureOf P
        (Evolution.EvolutionarySystem.genotypeOf E child)
      ≡
      architectureOf P
        (Evolution.EvolutionarySystem.genotypeOf E parent)

    inheritanceReference : String

open HeritableAgenticArchitectureLineage public

------------------------------------------------------------------------
-- Typed variation of the same coordinate.
------------------------------------------------------------------------

record AgenticArchitectureVariation
    {E : Evolution.EvolutionarySystem}
    (P : AgenticArchitectureProjection E) : Set₁ where
  constructor agentic-architecture-variation
  field
    genotype : Evolution.EvolutionarySystem.Genotype E
    variation : Evolution.EvolutionarySystem.Variation E

    ArchitectureDiffers : Architecture P → Architecture P → Set

    variationChangesArchitecture :
      ArchitectureDiffers
        (architectureOf P genotype)
        (architectureOf P
          (Evolution.EvolutionarySystem.mutate E variation genotype))

    variationReference : String

open AgenticArchitectureVariation public

------------------------------------------------------------------------
-- Selection receipt.  Selection remains phenotype/environment indexed exactly
-- as in EvolutionaryPopulationDynamics; merely changing an architecture code
-- does not manufacture a fitness comparison.
------------------------------------------------------------------------

record AgenticArchitectureSelectionReceipt
    {E : Evolution.EvolutionarySystem}
    (P : AgenticArchitectureProjection E) : Set₁ where
  constructor agentic-architecture-selection-receipt
  field
    individual : Evolution.EvolutionarySystem.Individual E
    environment : Evolution.EvolutionarySystem.Environment E
    phenotype : Evolution.EvolutionarySystem.Phenotype E

    phenotypeRealisation :
      Evolution.EvolutionarySystem.RealisesPhenotype E
        (Evolution.EvolutionarySystem.genotypeOf E individual)
        environment
        phenotype

    architecture : Architecture P
    architectureMatchesGenotype :
      architecture
      ≡ architectureOf P
          (Evolution.EvolutionarySystem.genotypeOf E individual)

    fitness : Evolution.EvolutionarySystem.Fitness E
    fitnessIsSelectionResult :
      fitness ≡ Evolution.EvolutionarySystem.select E environment phenotype

    selectionReference : String

open AgenticArchitectureSelectionReceipt public

------------------------------------------------------------------------
-- Join to the resource-coupled proto-agency realisation.
--
-- This identifies each evolutionary individual with an underlying resource /
-- population state whose image is governed by the already-owned proto-agency
-- closed loop.  It does not claim all offspring preserve that realisation.
------------------------------------------------------------------------

record ResourceHeritableProtoAgencyJoin
    {S : Resource.ResourceCoupledLogisticSystem}
    {E : Evolution.EvolutionarySystem}
    {M : Agentic.AgenticMaterial}
    (Agency : Proto.ResourceCoupledProtoAgencyRealisation S M)
    (P : AgenticArchitectureProjection E)
    (A : AgenticArchitectureRealisation P M) : Set₁ where
  constructor resource-heritable-proto-agency-join
  field
    individualState :
      Evolution.EvolutionarySystem.Individual E →
      Resource.ResourcePopulationState S

    lineage : HeritableAgenticArchitectureLineage P

    parentStateReference : String
    offspringStateReference : String
    lineageRealisationReference : String

open ResourceHeritableProtoAgencyJoin public

parentClosedLoopCommutes :
  ∀ {S E M Agency P A} →
  (J : ResourceHeritableProtoAgencyJoin {S} {E} {M} Agency P A) →
  Proto.stateMap Agency
    (Resource.coupledStep S
      (individualState J (parent (lineage J))))
  ≡
  Agentic.closedLoopStep M
    (Proto.stateMap Agency
      (individualState J (parent (lineage J))))
parentClosedLoopCommutes {Agency = Agency} J =
  Proto.closedLoopCommutes Agency
    (individualState J (parent (lineage J)))

------------------------------------------------------------------------
-- Authority firewalls.
------------------------------------------------------------------------

data ReproductionMeansAgencyInheritedPermission : Set where

data InheritedIndividualMeansArchitectureInheritedPermission : Set where

data ArchitectureMutationMeansPhenotypeChangePermission : Set where

data ArchitectureMutationMeansFitnessAdvantagePermission : Set where

data HeritableAgencyMeansOpenEndedEvolutionPermission : Set where

data HeritableAgencyMeansAbiogenesisInevitablePermission : Set where

data SameAgenticRealisationMeansSameArchitectureCodePermission : Set where

reproductionDoesNotByItselfProveAgencyInheritance :
  ReproductionMeansAgencyInheritedPermission → ⊥
reproductionDoesNotByItselfProveAgencyInheritance ()

inheritanceDoesNotByItselfIdentifyAgenticArchitecture :
  InheritedIndividualMeansArchitectureInheritedPermission → ⊥
inheritanceDoesNotByItselfIdentifyAgenticArchitecture ()

architectureMutationDoesNotByItselfProvePhenotypeChange :
  ArchitectureMutationMeansPhenotypeChangePermission → ⊥
architectureMutationDoesNotByItselfProvePhenotypeChange ()

architectureMutationDoesNotByItselfProveFitnessAdvantage :
  ArchitectureMutationMeansFitnessAdvantagePermission → ⊥
architectureMutationDoesNotByItselfProveFitnessAdvantage ()

heritableAgencyDoesNotByItselfProveOpenEndedEvolution :
  HeritableAgencyMeansOpenEndedEvolutionPermission → ⊥
heritableAgencyDoesNotByItselfProveOpenEndedEvolution ()

heritableAgencyDoesNotProveAbiogenesisInevitable :
  HeritableAgencyMeansAbiogenesisInevitablePermission → ⊥
heritableAgencyDoesNotProveAbiogenesisInevitable ()

samePresentAgenticBehaviourDoesNotRecoverArchitectureCode :
  SameAgenticRealisationMeansSameArchitectureCodePermission → ⊥
samePresentAgenticBehaviourDoesNotRecoverArchitectureCode ()

record HeritableAgenticOrganisationBoundary : Set where
  constructor heritable-agentic-organisation-boundary
  field
    agencyArchitectureRequiresGenotypeProjection : Bool
    inheritanceRequiresArchitectureReceipt : Bool
    mutationMayTargetArchitectureCoordinate : Bool
    selectionRequiresPhenotypeEnvironmentReceipt : Bool
    architectureCodeMayHaveResidualFibre : Bool
    reproductionAutomaticallyInheritsAgency : Bool
    architectureMutationAutomaticallyChangesPhenotype : Bool
    heritableAgencyAutomaticallyImpliesOpenEndedEvolution : Bool
    heritableAgencyProvesAbiogenesisInevitable : Bool

canonicalHeritableAgenticOrganisationBoundary :
  HeritableAgenticOrganisationBoundary
canonicalHeritableAgenticOrganisationBoundary =
  heritable-agentic-organisation-boundary
    true true true true true false false false false
