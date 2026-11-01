module DASHI.Biology.Cell.OpenMetabolicNetwork where

-- Metabolism is substrate-neutral here: an open reaction network harvesting and
-- dissipating gradients while maintaining bounded internal organisation.
record OpenMetabolicNetwork : Set₁ where
  field
    Species      : Set
    Reaction     : Set
    NetworkState : Set
    Environment  : Set
    Flux         : Set
    EnergyGradient : Set
    Cycle        : Set

    internalFlux : Reaction → NetworkState → Flux
    externalFlux : Environment → NetworkState → Flux
    gradientAt   : Environment → NetworkState → EnergyGradient
    step         : Environment → Reaction → NetworkState → NetworkState

    NontrivialCycle       : Cycle → Set
    DissipatesGradient    : Environment → Cycle → NetworkState → Set
    BoundedInternalState  : NetworkState → Set
    ClosedUnderComposition : Cycle → Cycle → Set
    Restoring             : Environment → Cycle → NetworkState → Set

record MetabolismAdmissibility
  (N : OpenMetabolicNetwork) : Set₁ where
  open OpenMetabolicNetwork N
  field
    environment : Environment
    state       : NetworkState
    generatingCycle : Cycle

    nontrivial : NontrivialCycle generatingCycle
    dissipative : DissipatesGradient environment generatingCycle state
    bounded     : BoundedInternalState state
    restoring   : Restoring environment generatingCycle state

    LowDescriptionComplexity : Cycle → Set
    PerturbationMargin       : NetworkState → Set

    lowComplexity : LowDescriptionComplexity generatingCycle
    positiveMargin : PerturbationMargin state

-- The DASHI admissibility objective keeps all penalties coupled rather than
-- treating cycle existence, boundedness, closure, MDL, and margin independently.
record MetabolicAdmissibilityCost
  (N : OpenMetabolicNetwork) : Set₁ where
  open OpenMetabolicNetwork N
  field
    Cost : Set
    networkDescriptionCost : NetworkState → Cost
    cycleFailurePenalty    : NetworkState → Cost
    boundednessPenalty     : NetworkState → Cost
    closurePenalty         : NetworkState → Cost
    marginPenalty          : NetworkState → Cost

record MetabolicMinimizerBoundary
  {N : OpenMetabolicNetwork}
  (J : MetabolicAdmissibilityCost N) : Set₁ where
  open OpenMetabolicNetwork N
  field
    candidate : NetworkState
    Competitor : NetworkState → Set
    NoWorse : NetworkState → NetworkState → Set

    familyRelativeMinimum :
      (other : NetworkState) → Competitor other →
      NoWorse candidate other

    finiteOrCompactCandidateFamily : Set

-- A metabolic network can support viability without being an agent unless an
-- observation–defect–action correction loop is separately supplied.
record MetabolismPromotionBoundary : Set₁ where
  field
    dissipationIsNotAgency : Set
    cycleIsNotHeredity     : Set
    boundednessIsNotLifeDefinition : Set
    MDLMinimumIsNotBiologicalTruth : Set
