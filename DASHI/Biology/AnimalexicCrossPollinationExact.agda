module DASHI.Biology.AnimalexicCrossPollinationExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Reuse the independent LES/DASHI gap-closure theorems directly in the
-- Animalexic formal surface.  This is deliberately theorem reuse rather than a
-- second Animalexic-local implementation of belief safety, active information,
-- stochastic quotient safety, fidelity pruning, provenance-root uncertainty,
-- temporal validity, or dependency closure.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.PartialObservationBeliefSafetyExact as Belief
import DASHI.Core.IdentifiabilityActiveInformationExact as ActiveInfo
import DASHI.Core.FiniteStochasticBisimulationExact as Stochastic
import DASHI.Core.SharedSourceUncertaintyExact as SharedUncertainty
import DASHI.Core.TemporalValidityPathDependenceExact as TemporalPath
import DASHI.Core.AdaptiveFidelityPruningExact as FidelityPrune
import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Core.AssumptionIndexedReopeningExact as Reopen
import DASHI.Core.ReopenableConsumerInterventionKernelExact as Base

------------------------------------------------------------------------
-- 1. Partial observation / predictive-state reuse.
------------------------------------------------------------------------

AnimalBeliefStateMachine :
  (History Action BeliefState Observation : Set) → Set₁
AnimalBeliefStateMachine = Belief.BeliefStateMachine

animalSameBeliefPreservesFiniteFutureObservation :
  ∀ {History Action BeliefState Observation}
    (machine : Belief.BeliefStateMachine History Action BeliefState Observation)
    (actions : List Action)
    {left right : History} →
  Belief.encodeBelief machine left ≡ Belief.encodeBelief machine right →
  Belief.currentObservation machine (Belief.runHistory machine actions left)
  ≡ Belief.currentObservation machine (Belief.runHistory machine actions right)
animalSameBeliefPreservesFiniteFutureObservation =
  Belief.sameBeliefPreservesFiniteFutureObservation

animalCurrentObservationCanBeFutureUnsafe :
  Belief.CurrentObservationTerminalisationDefect
animalCurrentObservationCanBeFutureUnsafe =
  Belief.canonicalCurrentObservationTerminalisationDefect

------------------------------------------------------------------------
-- 2. Active information / identifiability reuse.
------------------------------------------------------------------------

AnimalExperimentSystem : Set → Set → Set → Set₁
AnimalExperimentSystem = ActiveInfo.ExperimentSystem

AnimalDistinguishingExperiment :
  ∀ {Model Experiment Result} →
  ActiveInfo.ExperimentSystem Model Experiment Result →
  Model → Model → Set
AnimalDistinguishingExperiment = ActiveInfo.DistinguishingExperiment

animalActiveInformationHasExactDecisionValue :
  ActiveInfo.PositiveDecisionValueWitness
animalActiveInformationHasExactDecisionValue =
  ActiveInfo.canonicalPositiveDecisionValueWitness

------------------------------------------------------------------------
-- 3. Stochastic quotient safety and shared-source uncertainty are separate.
--    A stochastic transition defect is not an epistemic independence receipt.
------------------------------------------------------------------------

AnimalProjectedFiniteKernel : Set → Set → Set → Set₁
AnimalProjectedFiniteKernel = Stochastic.ProjectedFiniteKernel

animalStochasticProjectionDefectRecorded :
  Stochastic.KernelBisimulationDefect Stochastic.demoKernel
animalStochasticProjectionDefectRecorded = Stochastic.demoKernelDefect

animalSharedSourceUncertaintyRecorded :
  SharedUncertainty.SharedSourcePair
    SharedUncertainty.erosionDEM
    SharedUncertainty.machineryDEM
animalSharedSourceUncertaintyRecorded =
  SharedUncertainty.canonicalSharedDEMPair

------------------------------------------------------------------------
-- 4. Temporal validity/path dependence: equal visible present state can be a
--    safe quotient for one coarse consumer and unsafe for a finer consumer.
------------------------------------------------------------------------

animalPathDependenceNonDescentRecorded :
  Base.ConsumerDescentDefect TemporalPath.forgetHistory TemporalPath.fineResponse
animalPathDependenceNonDescentRecorded =
  TemporalPath.fineOutcomeDoesNotDescendThroughPresentState

------------------------------------------------------------------------
-- 5. Fidelity and dependency theorems are reused as execution constraints.
------------------------------------------------------------------------

animalSafeFidelityPruneRefutesImprovement :
  ∀ {Score}
    (order : FidelityPrune.OrderedScore Score)
    {incumbent actual lower : Score} →
  FidelityPrune.SafeMinimisationPrune order incumbent actual lower →
  FidelityPrune._<s_ order actual incumbent →
  ⊥
animalSafeFidelityPruneRefutesImprovement =
  FidelityPrune.safePruneRefutesImprovement

animalDependencyObligationsCompose :
  ∀ {Artifact}
    {Depends : Artifact → Artifact → Set}
    {changed middle target} →
  Dependency.ReopeningObligation Depends changed middle →
  Dependency.ReopeningObligation Depends middle target →
  Dependency.ReopeningObligation Depends changed target
animalDependencyObligationsCompose = Dependency.obligationsCompose

animalSharedEvidenceRootRefutesIndependence :
  ∀ {Root Evidence}
    {lineage : Reopen.EvidenceLineage Root Evidence}
    {left right : Evidence} →
  Reopen.SharedEvidenceRoot lineage left right →
  Reopen.IndependentEvidence lineage left right →
  ⊥
animalSharedEvidenceRootRefutesIndependence =
  Reopen.sharedRootRefutesIndependence

------------------------------------------------------------------------
-- Cross-pollination boundary.
------------------------------------------------------------------------

record AnimalexicCrossPollinationBoundary : Set where
  constructor animalexicCrossPollinationBoundary
  field
    presentObservationIsNotAssumedMarkov : Bool
    beliefPromotionNeedsUpdateCommutation : Bool
    activeExperimentCanSplitPassiveEquifinality : Bool
    informationValueNeedNotAssumeProbabilities : Bool
    stochasticProjectionNeedsTransitionLawSafety : Bool
    sharedUpstreamSourcePreventsNaiveIndependence : Bool
    visiblePresentStateMayErasePathDependence : Bool
    fidelityPruningNeedsCertifiedBound : Bool
    reopeningFollowsTransitiveDependencyEvidence : Bool
    oneBrokenEvidenceRouteNeedNotInvalidateAllRoutes : Bool

open AnimalexicCrossPollinationBoundary public

canonicalAnimalexicCrossPollinationBoundary :
  AnimalexicCrossPollinationBoundary
canonicalAnimalexicCrossPollinationBoundary =
  animalexicCrossPollinationBoundary
    true true true true true true true true true true
