module DASHI.Biology.OpenEndedAgenticRepertoireEvolutionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.Evolution.EvolutionaryPopulationDynamics as Evolution
import DASHI.Biology.HeritableAgenticOrganisationEvolutionExact as Heritable
import DASHI.Biology.Levin.ProblemSpaceAgency as Problem

------------------------------------------------------------------------
-- OPEN-ENDED AGENTIC REPERTOIRE EVOLUTION
--
-- Heredity, variation and selection can continue indefinitely while remaining
-- inside a fixed repertoire.  Open-endedness therefore needs a separate
-- non-stabilisation receipt.  The expanding object is not merely the finite
-- ProblemSpaceKind taxonomy; it is a typed capability repertoire whose members
-- may inhabit the same coarse problem-space kind while differing in target,
-- admissible moves, observation structure or corrective policy.
------------------------------------------------------------------------

record AgenticRepertoireModel
    {E : Evolution.EvolutionarySystem}
    (P : Heritable.AgenticArchitectureProjection E) : Set₁ where
  constructor agentic-repertoire-model
  field
    Capability : Set

    capabilityProblemSpace :
      Capability → Problem.ProblemSpaceNavigation

    ReachableArchitecture :
      Evolution.EvolutionarySystem.Generation E →
      Heritable.Architecture P → Set

    SupportsCapability :
      Heritable.Architecture P → Capability → Set

    Later :
      Evolution.EvolutionarySystem.Generation E →
      Evolution.EvolutionarySystem.Generation E → Set

    reachabilityReference : String
    capabilityReference : String
    temporalReference : String

open AgenticRepertoireModel public

------------------------------------------------------------------------
-- Architecture novelty: a later architecture is reachable and was not already
-- reachable at the earlier generation.  This is weaker than capability novelty.
------------------------------------------------------------------------

record LaterArchitectureNovelty
    {E : Evolution.EvolutionarySystem}
    {P : Heritable.AgenticArchitectureProjection E}
    (R : AgenticRepertoireModel P)
    (earlier : Evolution.EvolutionarySystem.Generation E) : Set₁ where
  constructor later-architecture-novelty
  field
    later : Evolution.EvolutionarySystem.Generation E
    architecture : Heritable.Architecture P

    laterThan : Later R earlier later
    reachableLater : ReachableArchitecture R later architecture
    notReachableEarlier : ReachableArchitecture R earlier architecture → ⊥

    noveltyReference : String

open LaterArchitectureNovelty public

record ArchitecturallyNonStabilising
    {E : Evolution.EvolutionarySystem}
    {P : Heritable.AgenticArchitectureProjection E}
    (R : AgenticRepertoireModel P) : Set₁ where
  constructor architecturally-non-stabilising
  field
    noveltyAfter :
      (generation : Evolution.EvolutionarySystem.Generation E) →
      LaterArchitectureNovelty R generation

    nonStabilisationReference : String

open ArchitecturallyNonStabilising public

------------------------------------------------------------------------
-- Capability novelty is stronger.  A later selected architecture supports a
-- capability for which no architecture reachable at the earlier generation
-- supplied a support witness.  Selection is paid by the already-owned
-- phenotype/environment indexed selection receipt.
------------------------------------------------------------------------

record LaterSelectedCapabilityNovelty
    {E : Evolution.EvolutionarySystem}
    {P : Heritable.AgenticArchitectureProjection E}
    (R : AgenticRepertoireModel P)
    (earlier : Evolution.EvolutionarySystem.Generation E) : Set₁ where
  constructor later-selected-capability-novelty
  field
    later : Evolution.EvolutionarySystem.Generation E
    architecture : Heritable.Architecture P
    capability : Capability R

    laterThan : Later R earlier later
    reachableLater : ReachableArchitecture R later architecture
    supportsLater : SupportsCapability R architecture capability

    selectionReceipt : Heritable.AgenticArchitectureSelectionReceipt P
    selectionArchitectureMatches :
      Heritable.AgenticArchitectureSelectionReceipt.architecture selectionReceipt
      ≡ architecture

    unavailableEarlier :
      (oldArchitecture : Heritable.Architecture P) →
      ReachableArchitecture R earlier oldArchitecture →
      SupportsCapability R oldArchitecture capability →
      ⊥

    noveltyReference : String
    selectionReference : String

open LaterSelectedCapabilityNovelty public

record CapabilityNonStabilising
    {E : Evolution.EvolutionarySystem}
    {P : Heritable.AgenticArchitectureProjection E}
    (R : AgenticRepertoireModel P) : Set₁ where
  constructor capability-non-stabilising
  field
    capabilityNoveltyAfter :
      (generation : Evolution.EvolutionarySystem.Generation E) →
      LaterSelectedCapabilityNovelty R generation

    nonStabilisationReference : String

open CapabilityNonStabilising public

------------------------------------------------------------------------
-- Full open-ended agentic innovation carries both coordinates.  Architecture
-- novelty is retained independently because new capability need not identify a
-- unique code, and a new code need not create a new capability.
------------------------------------------------------------------------

record OpenEndedAgenticInnovation
    {E : Evolution.EvolutionarySystem}
    {P : Heritable.AgenticArchitectureProjection E}
    (R : AgenticRepertoireModel P) : Set₁ where
  constructor open-ended-agentic-innovation
  field
    architectureDoesNotStabilise : ArchitecturallyNonStabilising R
    capabilityDoesNotStabilise : CapabilityNonStabilising R

    heredityVariationSelectionReference : String
    openEndednessReference : String

open OpenEndedAgenticInnovation public

architectureNoveltyFromOpenEndedness :
  ∀ {E P R} →
  OpenEndedAgenticInnovation {E} {P} R →
  (generation : Evolution.EvolutionarySystem.Generation E) →
  LaterArchitectureNovelty R generation
architectureNoveltyFromOpenEndedness O =
  noveltyAfter (architectureDoesNotStabilise O)

capabilityNoveltyFromOpenEndedness :
  ∀ {E P R} →
  OpenEndedAgenticInnovation {E} {P} R →
  (generation : Evolution.EvolutionarySystem.Generation E) →
  LaterSelectedCapabilityNovelty R generation
capabilityNoveltyFromOpenEndedness O =
  capabilityNoveltyAfter (capabilityDoesNotStabilise O)

------------------------------------------------------------------------
-- Problem-space projection remains typed but is not the novelty criterion by
-- itself.  Two genuinely novel capabilities may share one ProblemSpaceKind.
------------------------------------------------------------------------

problemSpaceOfNovelCapability :
  ∀ {E P R generation} →
  LaterSelectedCapabilityNovelty {E} {P} R generation →
  Problem.ProblemSpaceNavigation
problemSpaceOfNovelCapability {R = R} witness =
  capabilityProblemSpace R (capability witness)

------------------------------------------------------------------------
-- Authority firewalls.
------------------------------------------------------------------------

data ContinuedSelectionMeansOpenEndednessPermission : Set where

data ArchitectureNoveltyMeansCapabilityNoveltyPermission : Set where

data NewProblemSpaceKindRequiredForNoveltyPermission : Set where

data CapabilityNoveltyMeansHigherFitnessPermission : Set where

data OpenEndedAgenticInnovationMeansAbiogenesisInevitablePermission : Set where

data OpenEndedAgenticInnovationMeansHistoricalPathKnownPermission : Set where

continuedSelectionDoesNotByItselfProveOpenEndedness :
  ContinuedSelectionMeansOpenEndednessPermission → ⊥
continuedSelectionDoesNotByItselfProveOpenEndedness ()

architectureNoveltyDoesNotByItselfProveCapabilityNovelty :
  ArchitectureNoveltyMeansCapabilityNoveltyPermission → ⊥
architectureNoveltyDoesNotByItselfProveCapabilityNovelty ()

novelCapabilityNeedNotIntroduceNewProblemSpaceKind :
  NewProblemSpaceKindRequiredForNoveltyPermission → ⊥
novelCapabilityNeedNotIntroduceNewProblemSpaceKind ()

capabilityNoveltyDoesNotByItselfProveHigherFitness :
  CapabilityNoveltyMeansHigherFitnessPermission → ⊥
capabilityNoveltyDoesNotByItselfProveHigherFitness ()

openEndednessDoesNotProveAbiogenesisInevitable :
  OpenEndedAgenticInnovationMeansAbiogenesisInevitablePermission → ⊥
openEndednessDoesNotProveAbiogenesisInevitable ()

openEndednessDoesNotRecoverHistoricalPath :
  OpenEndedAgenticInnovationMeansHistoricalPathKnownPermission → ⊥
openEndednessDoesNotRecoverHistoricalPath ()

record OpenEndedAgenticRepertoireBoundary : Set where
  constructor open-ended-agentic-repertoire-boundary
  field
    continuedAdaptationAndOpenEndednessAreDistinct : Bool
    architectureAndCapabilityNoveltyAreDistinct : Bool
    noveltyCanOccurWithinSameProblemSpaceKind : Bool
    selectionRemainsPhenotypeEnvironmentIndexed : Bool
    openEndednessRequiresExplicitLaterRelation : Bool
    openEndednessAutomaticallyProvesAbiogenesis : Bool
    openEndednessAutomaticallyRecoversHistory : Bool

canonicalOpenEndedAgenticRepertoireBoundary :
  OpenEndedAgenticRepertoireBoundary
canonicalOpenEndedAgenticRepertoireBoundary =
  open-ended-agentic-repertoire-boundary
    true true true true true false false
