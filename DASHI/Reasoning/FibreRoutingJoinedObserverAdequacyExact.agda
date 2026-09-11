module DASHI.Reasoning.FibreRoutingJoinedObserverAdequacyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Reasoning.FibreRoutingGrokkingMoEBrainCrossPollinationExact as Fibre
import DASHI.Reasoning.FibreRoutingProjectionAdequacyCrossPollinationExact as Projection
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query

------------------------------------------------------------------------
-- JOINED OBSERVER ADEQUACY
--
-- A routed fibre family, nuisance/control projection, atlas projection, or
-- learned representation is an observer surface.  Its adequacy is not intrinsic:
-- it is indexed by the scientific consumer.  When a collision exposes one
-- erased consumer-relevant axis, the canonical repair is to join only that axis
-- and test factorisation again.
--
-- This is the shared formal move behind:
--   * Fly hard-domain -> overlapping-domain repair;
--   * sparse/multiple-expert composition;
--   * grokking cleanup/stabilisation of a consumer-sufficient representation.
--
-- It does not identify those physical systems with one another.
------------------------------------------------------------------------

joinObserver :
  ∀ {Fine Left Right : Set} →
  (Fine → Left) →
  (Fine → Right) →
  Fine → Left × Right
joinObserver left right fine = left fine , right fine

leftOfJoin :
  ∀ {Left Right : Set} →
  Left × Right → Left
leftOfJoin (left , right) = left

rightOfJoin :
  ∀ {Left Right : Set} →
  Left × Right → Right
rightOfJoin (left , right) = right

------------------------------------------------------------------------
-- Concrete Fly witness: hard identity alone loses the overlap query, while the
-- joined observer retains both the legacy hard identity and the missing overlap
-- fibre.  This is a local repair theorem, not a universal sufficiency claim.
------------------------------------------------------------------------

flyHardPlusOverlap :
  Fibre.SelectedROISpecimen →
  Fibre.HardPaintedIdentity × Fibre.PaintedOverlapProfile
flyHardPlusOverlap =
  joinObserver Fibre.hardPaintedIdentity Fibre.paintedOverlapProfile

joinedObserverAdequateForHardIdentity :
  Query.AdequateFor
    flyHardPlusOverlap
    Projection.flyConsumerSemantics
    Projection.hardIdentityQuery
joinedObserverAdequateForHardIdentity =
  Query.factorsForQuery
    (λ joined → Projection.hardIdentityAnswer (leftOfJoin joined))
    (λ state → refl)

joinedObserverAdequateForOverlapProfile :
  Query.AdequateFor
    flyHardPlusOverlap
    Projection.flyConsumerSemantics
    Projection.overlapProfileQuery
joinedObserverAdequateForOverlapProfile =
  Query.factorsForQuery
    (λ joined → Projection.overlapProfileAnswer (rightOfJoin joined))
    (λ state → refl)

hardAloneStillFailsOverlap :
  Query.AdequateFor
    Fibre.hardPaintedIdentity
    Projection.flyConsumerSemantics
    Projection.overlapProfileQuery → ⊥
hardAloneStillFailsOverlap =
  Projection.hardWinnerCannotAnswerOverlapQuery

------------------------------------------------------------------------
-- Search coordinates for the next real Fly experiment.
--
-- These are candidate observer axes, not assumptions that every axis is needed.
-- The experiment should seek a small admissible joined observer whose declared
-- structure/function consumer factors, rather than blindly residualising all
-- available covariates.
------------------------------------------------------------------------

data FlyObserverAxis : Set where
  atlasOverlapAxis : FlyObserverAxis
  stimulusAxis : FlyObserverAxis
  coarseStrengthAxis : FlyObserverAxis
  trialIdentityAxis : FlyObserverAxis
  animalIdentityAxis : FlyObserverAxis

data AxisDisposition : Set where
  retainedFibre : AxisDisposition
  candidateRepairFibre : AxisDisposition
  unnecessaryForDeclaredConsumer : AxisDisposition

record QueryIndexedAxisDecision : Set where
  constructor queryIndexedAxisDecision
  field
    axis : FlyObserverAxis
    disposition : AxisDisposition
    decisionRequiresConsumerTest : Bool

open QueryIndexedAxisDecision public

atlasOverlapDecision : QueryIndexedAxisDecision
atlasOverlapDecision =
  queryIndexedAxisDecision
    atlasOverlapAxis
    retainedFibre
    true

stimulusDecision : QueryIndexedAxisDecision
stimulusDecision =
  queryIndexedAxisDecision
    stimulusAxis
    candidateRepairFibre
    true

coarseStrengthDecision : QueryIndexedAxisDecision
coarseStrengthDecision =
  queryIndexedAxisDecision
    coarseStrengthAxis
    candidateRepairFibre
    true

trialIdentityDecision : QueryIndexedAxisDecision
trialIdentityDecision =
  queryIndexedAxisDecision
    trialIdentityAxis
    candidateRepairFibre
    true

animalIdentityDecision : QueryIndexedAxisDecision
animalIdentityDecision =
  queryIndexedAxisDecision
    animalIdentityAxis
    candidateRepairFibre
    true

------------------------------------------------------------------------
-- MoE / grokking interpretation boundary.
--
-- Sparse expert routing and grokking cleanup become instances of the same
-- observer/refinement grammar only at the structural level: a selected fibre
-- family must still pay its consumer-specific adequacy obligation.
------------------------------------------------------------------------

record JoinedObserverCrossPollinationBoundary : Set where
  constructor joinedObserverCrossPollinationBoundary
  field
    sparseRoutingAutomaticallyAdequateForEveryConsumer : Bool
    routingStabilityAutomaticallyIdentifiesMechanism : Bool
    grokkingCleanupAutomaticallyProvesFutureSafeAdequacy : Bool
    joinedObserverMayRepairAProvedLostAxis : Bool
    oneJoinedRepairProvesUniversalSufficiency : Bool
    controlsMayBeRetainedAsExplicitFibres : Bool
    allCandidateControlsMustBeResidualised : Bool
    minimalObserverSearchMustRemainConsumerIndexed : Bool

canonicalJoinedObserverCrossPollinationBoundary :
  JoinedObserverCrossPollinationBoundary
canonicalJoinedObserverCrossPollinationBoundary =
  joinedObserverCrossPollinationBoundary
    false
    false
    false
    true
    false
    true
    false
    true
