module DASHI.Biology.Ecology.EcologicalInteractionDynamics where

-- Ecology closes the biology tower with interacting populations, resources,
-- niches, environmental change, and organism-driven niche construction.
record EcologicalSystem : Set₁ where
  field
    Species      : Set
    Population   : Set
    Resource     : Set
    Environment  : Set
    Interaction  : Set
    Niche        : Set
    EcosystemState : Set

    populationOf : EcosystemState → Species → Population
    resourcesAt  : EcosystemState → Resource
    environmentAt : EcosystemState → Environment
    nicheOf      : Species → EcosystemState → Niche

    interact     : Interaction → EcosystemState → EcosystemState
    environmentalStep : Environment → EcosystemState → EcosystemState
    nicheConstruction : Species → EcosystemState → EcosystemState

    Coexists     : Species → Species → EcosystemState → Set
    Competes     : Species → Species → EcosystemState → Set
    Cooperates   : Species → Species → EcosystemState → Set
    Predates     : Species → Species → EcosystemState → Set

record EcoEvolutionaryFeedbackWitness
  (E : EcologicalSystem) : Set₁ where
  open EcologicalSystem E
  field
    state   : EcosystemState
    species : Species

    EvolutionaryChange : Set
    EcologicalChange   : Set

    evolutionChangesNiche : EvolutionaryChange
    nicheChangesSelection : EcologicalChange

record EcologicalStabilityBoundary
  (E : EcologicalSystem) : Set₁ where
  open EcologicalSystem E
  field
    StableRegion : EcosystemState → Set
    Perturbation : Set
    perturb      : Perturbation → EcosystemState → EcosystemState
    Recovers     : EcosystemState → EcosystemState → Set

record EcologyAuthorityBoundary : Set₁ where
  field
    ecosystemStabilityIsNotStaticEquilibrium : Set
    collectiveCoordinationIsNotGroupMindByDefinition : Set
    ecologicalFunctionIsNotMoralValue : Set
    modelNicheIsNotCompleteNaturalHistory : Set
