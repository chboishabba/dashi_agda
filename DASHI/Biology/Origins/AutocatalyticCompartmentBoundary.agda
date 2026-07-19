module DASHI.Biology.Origins.AutocatalyticCompartmentBoundary where

-- Origins-of-life claims are staged so that energy harvesting, autocatalysis,
-- compartmentalisation, heredity, and closed-loop agency are not conflated.
data OriginStage : Set where
  gradientHarvesting      : OriginStage
  autocatalyticClosure    : OriginStage
  compartmentalisedCycle : OriginStage
  hereditaryPersistence  : OriginStage
  viabilityControl       : OriginStage

record PrebioticChemicalSystem : Set₁ where
  field
    State       : Set
    Environment : Set
    Reaction    : Set
    Gradient    : Set
    Compartment : Set

    step        : Environment → Reaction → State → State
    gradientAt  : Environment → State → Gradient

    DissipatesGradient : Environment → Reaction → State → Set
    Autocatalytic      : Reaction → State → Set
    Compartments       : Compartment → State → Set
    Persists           : State → Set

record AutocatalyticCompartmentWitness
  (P : PrebioticChemicalSystem) : Set₁ where
  open PrebioticChemicalSystem P
  field
    state       : State
    environment : Environment
    reaction    : Reaction
    compartment : Compartment

    dissipative   : DissipatesGradient environment reaction state
    autocatalytic : Autocatalytic reaction state
    enclosed      : Compartments compartment state

-- Self-amplification and enclosure still do not establish agency.  A separate
-- closed loop must sense a target-relative defect and choose corrective action.
record ProtoAgencyExtension
  (P : PrebioticChemicalSystem) : Set₁ where
  open PrebioticChemicalSystem P
  field
    Observation : Set
    Action      : Set
    Goal        : State → Set
    Defect      : State → Set

    observe : State → Observation
    policy  : (x : State) → Observation → Defect x → Action
    act     : Action → State → State

    Corrective : State → Action → Set
    correctionWitness :
      (x : State) → (d : Defect x) →
      Corrective x (policy x (observe x) d)

-- Heredity and evolution require later rewrite/population witnesses.  Chemical
-- recurrence alone is not silently promoted to Darwinian evolution.
record OriginPromotionBoundary : Set₁ where
  field
    autocatalysisIsNotHeredity : Set
    compartmentIsNotCell      : Set
    persistenceIsNotAgency    : Set
    replicationIsNotEvolution : Set
