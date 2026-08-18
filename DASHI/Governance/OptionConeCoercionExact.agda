module DASHI.Governance.OptionConeCoercionExact where

------------------------------------------------------------------------
-- OPTION-CONE COERCION / LONG-HORIZON COMMUNITY SAFETY
--
-- Coercion is not reduced to visible force.  A state can be coercively
-- structured when dependence is present, every safe refusal path is penalised,
-- and the transition contracts the subject's reachable safe alternatives.
--
-- This module deliberately keeps "immediate threat reduction" separate from
-- long-horizon justice/safety.  A route may achieve the former while worsening
-- the latter; neither direction is promoted automatically.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Governance.SituatedInverseJusticeFibreExact as Justice

------------------------------------------------------------------------
-- Safe option cone as a proof-bearing availability relation.
------------------------------------------------------------------------

record SafeReachabilitySystem (State Option : Set) : Set₁ where
  constructor safeReachabilitySystem
  field
    Available : State → Option → Set

open SafeReachabilitySystem public

record StrictSafeReachabilityContraction
    {State Option : Set}
    (system : SafeReachabilitySystem State Option)
    (before after : State) : Set₁ where
  constructor strictSafeReachabilityContraction
  field
    afterIncludedInBefore :
      (option : Option) →
      Available system after option →
      Available system before option
    lostOption : Option
    lostBefore : Available system before lostOption
    lostAfterImpossible : Available system after lostOption → ⊥

open StrictSafeReachabilityContraction public

------------------------------------------------------------------------
-- Option-cone coercive control.
------------------------------------------------------------------------

record RefusalPenaltySystem
    {State Option : Set}
    (reachability : SafeReachabilitySystem State Option) : Set₁ where
  constructor refusalPenaltySystem
  field
    PenalisedRefusal : State → Option → Set

open RefusalPenaltySystem public

record OptionConeCoercion
    {State Option : Set}
    (reachability : SafeReachabilitySystem State Option)
    (penalty : RefusalPenaltySystem reachability)
    (before after : State) : Set₁ where
  constructor optionConeCoercion
  field
    DependencyPresent : Set
    dependencyPresent : DependencyPresent
    everySafeRefusalPenalised :
      (option : Option) →
      Available reachability before option →
      PenalisedRefusal penalty before option
    safeReachabilityContracts :
      StrictSafeReachabilityContraction reachability before after

open OptionConeCoercion public

EverySafeRefusalPathPenalisedWitnessesCoerciveControl :
  ∀ {State Option}
    {reachability : SafeReachabilitySystem State Option}
    {penalty : RefusalPenaltySystem reachability}
    {before after : State} →
  (DependencyPresent : Set) →
  DependencyPresent →
  ((option : Option) →
    Available reachability before option →
    PenalisedRefusal penalty before option) →
  StrictSafeReachabilityContraction reachability before after →
  OptionConeCoercion reachability penalty before after
EverySafeRefusalPathPenalisedWitnessesCoerciveControl
  DependencyPresent dependency allPenalised contraction =
  optionConeCoercion
    DependencyPresent
    dependency
    allPenalised
    contraction

------------------------------------------------------------------------
-- Exact finite long-horizon countermodel.
------------------------------------------------------------------------

data DemoState : Set where
  beforeResponse coerciveOutcome communityOutcome : DemoState

data DemoOption : Set where
  immediatePhysicalSafety housingContinuity kinParticipation futureHelpSeeking :
    DemoOption

data DemoAvailable : DemoState → DemoOption → Set where
  beforeImmediate : DemoAvailable beforeResponse immediatePhysicalSafety
  beforeHousing : DemoAvailable beforeResponse housingContinuity
  beforeKin : DemoAvailable beforeResponse kinParticipation
  beforeHelp : DemoAvailable beforeResponse futureHelpSeeking

  coerciveImmediate : DemoAvailable coerciveOutcome immediatePhysicalSafety
  coerciveHousing : DemoAvailable coerciveOutcome housingContinuity

  communityImmediate : DemoAvailable communityOutcome immediatePhysicalSafety
  communityHousing : DemoAvailable communityOutcome housingContinuity
  communityKin : DemoAvailable communityOutcome kinParticipation
  communityHelp : DemoAvailable communityOutcome futureHelpSeeking

demoReachability : SafeReachabilitySystem DemoState DemoOption
demoReachability = safeReachabilitySystem DemoAvailable

coerciveAfterIncluded :
  (option : DemoOption) →
  DemoAvailable coerciveOutcome option →
  DemoAvailable beforeResponse option
coerciveAfterIncluded immediatePhysicalSafety coerciveImmediate = beforeImmediate
coerciveAfterIncluded housingContinuity coerciveHousing = beforeHousing

canonicalCoerciveReachabilityContraction :
  StrictSafeReachabilityContraction
    demoReachability
    beforeResponse
    coerciveOutcome
canonicalCoerciveReachabilityContraction =
  strictSafeReachabilityContraction
    coerciveAfterIncluded
    futureHelpSeeking
    beforeHelp
    λ ()

communityRetainsLostCoerciveOption :
  DemoAvailable communityOutcome futureHelpSeeking
communityRetainsLostCoerciveOption = communityHelp

immediateThreatReduced : DemoState → Bool
immediateThreatReduced beforeResponse = false
immediateThreatReduced coerciveOutcome = true
immediateThreatReduced communityOutcome = true

sameImmediateThreatReduction :
  immediateThreatReduced coerciveOutcome
  ≡ immediateThreatReduced communityOutcome
sameImmediateThreatReduction = refl

record ImmediateThreatReductionNonSufficiencyWitness : Set₁ where
  constructor immediateThreatReductionNonSufficiencyWitness
  field
    sameImmediateOutcome :
      immediateThreatReduced coerciveOutcome
      ≡ immediateThreatReduced communityOutcome
    coerciveRouteContractsReachability :
      StrictSafeReachabilityContraction
        demoReachability
        beforeResponse
        coerciveOutcome
    comparisonRouteRetainsLostOption :
      DemoAvailable communityOutcome futureHelpSeeking

open ImmediateThreatReductionNonSufficiencyWitness public

ImmediateThreatReductionDoesNotDetermineJusticeOptimality :
  ImmediateThreatReductionNonSufficiencyWitness
ImmediateThreatReductionDoesNotDetermineJusticeOptimality =
  immediateThreatReductionNonSufficiencyWitness
    sameImmediateThreatReduction
    canonicalCoerciveReachabilityContraction
    communityRetainsLostCoerciveOption

------------------------------------------------------------------------
-- Justice-negative routing and reachability contraction remain separate proof
-- obligations.  When both witnesses are present they form the stronger dynamic
-- inverse-justice object; inverse-justice alone is not silently promoted to an
-- option-cone theorem.
------------------------------------------------------------------------

record JusticeNegativeRoutingContractsSafeReachability
    {beforeBase afterBase : Justice.SituatedJusticeBase}
    {beforeFibre : Justice.JusticeFibre beforeBase}
    {afterFibre : Justice.JusticeFibre afterBase}
    (transition : Justice.JusticeTransition beforeFibre afterFibre)
    {State Option : Set}
    (reachability : SafeReachabilitySystem State Option)
    (beforeState afterState : State) : Set₁ where
  constructor justiceNegativeRoutingContractsSafeReachability
  field
    inverseJustice : Justice.InverseJusticeOperator transition
    reachabilityContraction :
      StrictSafeReachabilityContraction
        reachability beforeState afterState

open JusticeNegativeRoutingContractsSafeReachability public

justiceNegativeRoutingWithContractionWitnessesDynamicHarm :
  ∀ {beforeBase afterBase}
    {beforeFibre : Justice.JusticeFibre beforeBase}
    {afterFibre : Justice.JusticeFibre afterBase}
    {transition : Justice.JusticeTransition beforeFibre afterFibre}
    {State Option}
    {reachability : SafeReachabilitySystem State Option}
    {beforeState afterState : State} →
  Justice.InverseJusticeOperator transition →
  StrictSafeReachabilityContraction reachability beforeState afterState →
  JusticeNegativeRoutingContractsSafeReachability
    transition reachability beforeState afterState
justiceNegativeRoutingWithContractionWitnessesDynamicHarm inverse contraction =
  justiceNegativeRoutingContractsSafeReachability inverse contraction

canonicalJusticeNegativeReachabilityContraction :
  JusticeNegativeRoutingContractsSafeReachability
    Justice.violatingAction
    demoReachability
    beforeResponse
    coerciveOutcome
canonicalJusticeNegativeReachabilityContraction =
  justiceNegativeRoutingWithContractionWitnessesDynamicHarm
    Justice.violatingActionIsInverseJustice
    canonicalCoerciveReachabilityContraction

------------------------------------------------------------------------
-- A simple double-bind-shaped penalty instance: every currently available
-- option is penalised.  This is structural only and does not diagnose a live
-- family or institution.
------------------------------------------------------------------------

data DemoPenalty :
  DemoState → DemoOption → Set where
  penaltyImmediate :
    DemoPenalty beforeResponse immediatePhysicalSafety
  penaltyHousing :
    DemoPenalty beforeResponse housingContinuity
  penaltyKin :
    DemoPenalty beforeResponse kinParticipation
  penaltyHelp :
    DemoPenalty beforeResponse futureHelpSeeking

demoPenaltySystem : RefusalPenaltySystem demoReachability
demoPenaltySystem = refusalPenaltySystem DemoPenalty

allDemoRefusalsPenalised :
  (option : DemoOption) →
  DemoAvailable beforeResponse option →
  DemoPenalty beforeResponse option
allDemoRefusalsPenalised immediatePhysicalSafety beforeImmediate =
  penaltyImmediate
allDemoRefusalsPenalised housingContinuity beforeHousing =
  penaltyHousing
allDemoRefusalsPenalised kinParticipation beforeKin =
  penaltyKin
allDemoRefusalsPenalised futureHelpSeeking beforeHelp =
  penaltyHelp

canonicalOptionConeCoercion :
  OptionConeCoercion
    demoReachability
    demoPenaltySystem
    beforeResponse
    coerciveOutcome
canonicalOptionConeCoercion =
  EverySafeRefusalPathPenalisedWitnessesCoerciveControl
    ⊤
    tt
    allDemoRefusalsPenalised
    canonicalCoerciveReachabilityContraction

record OptionConeCoercionBoundary : Set where
  constructor optionConeCoercionBoundary
  field
    visibleForceRequiredForCoerciveControl : Bool
    immediateSafetyDeterminesLongHorizonJustice : Bool
    incarcerationOrCustodyLabelAutomaticallyContractsReachability : Bool
    justiceNegativeLabelAloneProvesReachabilityContraction : Bool
    contractionRequiresExplicitLostOptionWitness : Bool

canonicalOptionConeCoercionBoundary : OptionConeCoercionBoundary
canonicalOptionConeCoercionBoundary =
  optionConeCoercionBoundary false false false false true
