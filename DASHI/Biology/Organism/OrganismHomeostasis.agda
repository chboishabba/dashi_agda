module DASHI.Biology.Organism.OrganismHomeostasis where

-- Organism-level viability integrates tissues and organs, internal regulation,
-- sensation, and action.  It is not reducible to the independent viability of
-- every component, nor does behavioural competence imply consciousness.
record OrganismControlSystem : Set₁ where
  field
    CellState     : Set
    TissueState   : Set
    OrganState    : Set
    OrganismState : Set
    Environment   : Set
    Sensation     : Set
    Behaviour     : Set
    InternalSignal : Set
    Perturbation  : Set
    Goal          : Set

    integrateCells   : CellState → TissueState
    integrateTissues : TissueState → OrganState
    integrateOrgans  : OrganState → OrganismState

    sense       : Environment → OrganismState → Sensation
    regulate    : InternalSignal → OrganismState → OrganismState
    behave      : Behaviour → Environment → OrganismState → OrganismState
    perturb     : Perturbation → OrganismState → OrganismState

    Satisfies   : OrganismState → Goal → Set
    Viable      : Environment → OrganismState → Set

record OrganismHomeostasisWitness
  (O : OrganismControlSystem) : Set₁ where
  open OrganismControlSystem O
  field
    environment  : Environment
    state        : OrganismState
    goal         : Goal
    perturbation : Perturbation
    signal       : InternalSignal
    action       : Behaviour

    initiallyViable : Viable environment state

    regulatedViable :
      Viable environment (regulate signal (perturb perturbation state))

    behaviourMaintainsGoal :
      Satisfies
        (behave action environment
          (regulate signal (perturb perturbation state)))
        goal

record OrganismIntegrationBoundary : Set₁ where
  field
    cellViabilityDoesNotAloneImplyOrganismViability : Set
    organIntegrationRequiresCouplingWitness : Set
    behaviourIsNotConsciousnessByDefinition : Set
    modelGoalIsNotMoralPurpose : Set
