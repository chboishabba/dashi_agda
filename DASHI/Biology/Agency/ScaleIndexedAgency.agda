module DASHI.Biology.Agency.ScaleIndexedAgency where

-- Agency is indexed by a scale, observation channel, action set, goal predicate,
-- disturbance class, and time horizon.  It is not a substance assigned once to
-- a protein, cell, tissue, organism, or collective.
record ScaleIndexedAgencySystem : Set₁ where
  field
    Scale : Set

    State       : Scale → Set
    Observation : Scale → Set
    Action      : Scale → Set
    Goal        : Scale → Set
    Barrier     : Scale → Set
    Horizon     : Scale → Set

    observe : (s : Scale) → State s → Observation s
    act     : (s : Scale) → Action s → State s → State s
    disturb : (s : Scale) → Barrier s → State s → State s
    policy  : (s : Scale) → Observation s → Goal s → Action s

    Satisfies : (s : Scale) → State s → Goal s → Set
    Corrects  : (s : Scale) → State s → Goal s → Barrier s → Set

record AgencyAt
  (A : ScaleIndexedAgencySystem)
  (s : ScaleIndexedAgencySystem.Scale A) : Set₁ where
  open ScaleIndexedAgencySystem A
  field
    state   : State s
    goal    : Goal s
    horizon : Horizon s

    sameEndByDifferentMeans :
      (barrier : Barrier s) →
      Corrects s state goal barrier

record AgencyScaleMap
  (A : ScaleIndexedAgencySystem) : Set₁ where
  open ScaleIndexedAgencySystem A
  field
    fine coarse : Scale
    coarseGrain : State fine → State coarse
    liftGoal    : Goal fine → Goal coarse
    liftBarrier : Barrier fine → Barrier coarse

record MultiscaleAgencyComposition
  {A : ScaleIndexedAgencySystem}
  (M : AgencyScaleMap A) : Set₁ where
  open ScaleIndexedAgencySystem A
  open AgencyScaleMap M
  field
    GoalPreservedAcrossScale : Set
    CorrectionCommutesAcrossScale : Set

    goalWitness : GoalPreservedAcrossScale
    correctionWitness : CorrectionCommutesAcrossScale

-- Identity and agent count may change when cells disconnect, reconnect, merge,
-- regenerate, or are re-embodied.  Persistence must be stated relative to a
-- scale map and goal/competency invariant.
record AgencyIdentityRemapping
  (A : ScaleIndexedAgencySystem) : Set₁ where
  field
    OldScale NewScale : ScaleIndexedAgencySystem.Scale A
    IdentityInvariant : Set
    MemoryInvariant   : Set
    CompetencyInvariant : Set

    identityPreserved : IdentityInvariant
    memoryRemapped    : MemoryInvariant
    competencyPreserved : CompetencyInvariant

record AgencyAuthorityBoundary : Set₁ where
  field
    predictionIsNotAgencyByDefinition : Set
    correctionIsNotConsciousness      : Set
    agencyIsNotPanpsychism            : Set
    goalDirectednessIsNotRetrocausality : Set
    collectiveAgencyIsNotGroupMindByDefinition : Set
