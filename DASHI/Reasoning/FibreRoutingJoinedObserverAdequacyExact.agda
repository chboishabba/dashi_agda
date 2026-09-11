module DASHI.Reasoning.FibreRoutingJoinedObserverAdequacyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Reasoning.FibreRoutingGrokkingMoEBrainCrossPollinationExact as Fibre
import DASHI.Reasoning.FibreRoutingProjectionAdequacyCrossPollinationExact as Projection
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.IntersectionalNonFactorability as NonFactor

------------------------------------------------------------------------
-- JOINED OBSERVER ADEQUACY
--
-- A routed fibre family, nuisance/control projection, atlas projection, or
-- learned representation is an observer surface. Its adequacy is not intrinsic:
-- it is indexed by the scientific consumer. When a collision exposes one
-- erased consumer-relevant axis, the canonical repair is to join only that axis
-- and test factorisation again.
--
-- IMPORTANT CORRECTION:
-- residualising a nuisance is not automatically an information refinement. The
-- monotone observer operation is to retain the source observer and pair it with
-- the nuisance/context coordinate. A residualised target is a downstream
-- consumer of that retained joined carrier, not a replacement for provenance.
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
joinObserver = Observer.pairObserver

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
-- fibre. This is a local repair theorem, not a universal sufficiency claim.
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

hardPlusOverlapRefinesHard :
  Observer.Refines Fibre.hardPaintedIdentity flyHardPlusOverlap
hardPlusOverlapRefinesHard =
  Observer.pairRefinesLeft Fibre.hardPaintedIdentity Fibre.paintedOverlapProfile

------------------------------------------------------------------------
-- Exact finite joined-control specimen.
--
-- Atlas overlap and published stimulus drive are separate consumer axes. Each
-- one-axis joined observer is sufficient for its own query but remains
-- insufficient for a joint query. The full pair is therefore minimal among the
-- declared proper sub-observers in this finite specimen.
------------------------------------------------------------------------

data FlyControlState : Set where
  overlapDriven : FlyControlState
  overlapResidual : FlyControlState
  parentOnlyDriven : FlyControlState
  parentOnlyResidual : FlyControlState

data StimulusCoordinate : Set where
  publishedDrivePresent : StimulusCoordinate
  publishedDriveRemoved : StimulusCoordinate

hardControlSurface : FlyControlState → Fibre.HardPaintedIdentity
hardControlSurface state = Fibre.parentWinner

overlapCoordinate : FlyControlState → Fibre.PaintedOverlapProfile
overlapCoordinate overlapDriven = Fibre.parentAndChildProfile
overlapCoordinate overlapResidual = Fibre.parentAndChildProfile
overlapCoordinate parentOnlyDriven = Fibre.parentOnlyProfile
overlapCoordinate parentOnlyResidual = Fibre.parentOnlyProfile

stimulusCoordinate : FlyControlState → StimulusCoordinate
stimulusCoordinate overlapDriven = publishedDrivePresent
stimulusCoordinate overlapResidual = publishedDriveRemoved
stimulusCoordinate parentOnlyDriven = publishedDrivePresent
stimulusCoordinate parentOnlyResidual = publishedDriveRemoved

overlapJoinedControl :
  FlyControlState → Fibre.HardPaintedIdentity × Fibre.PaintedOverlapProfile
overlapJoinedControl = Observer.pairObserver hardControlSurface overlapCoordinate

stimulusJoinedControl :
  FlyControlState → Fibre.HardPaintedIdentity × StimulusCoordinate
stimulusJoinedControl = Observer.pairObserver hardControlSurface stimulusCoordinate

fullJoinedControl :
  FlyControlState →
  (Fibre.HardPaintedIdentity × Fibre.PaintedOverlapProfile) × StimulusCoordinate
fullJoinedControl = Observer.pairObserver overlapJoinedControl stimulusCoordinate

overlapControlRefinesHard : Observer.Refines hardControlSurface overlapJoinedControl
overlapControlRefinesHard = Observer.pairRefinesLeft hardControlSurface overlapCoordinate

stimulusControlRefinesHard : Observer.Refines hardControlSurface stimulusJoinedControl
stimulusControlRefinesHard = Observer.pairRefinesLeft hardControlSurface stimulusCoordinate

fullControlRefinesOverlapControl : Observer.Refines overlapJoinedControl fullJoinedControl
fullControlRefinesOverlapControl = Observer.pairRefinesLeft overlapJoinedControl stimulusCoordinate

data FlyControlQuery : Set where
  hardControlQuery : FlyControlQuery
  overlapControlQuery : FlyControlQuery
  stimulusControlQuery : FlyControlQuery
  jointControlQuery : FlyControlQuery

data FlyControlAnswer : Set where
  hardControlAnswer : Fibre.HardPaintedIdentity → FlyControlAnswer
  overlapControlAnswer : Fibre.PaintedOverlapProfile → FlyControlAnswer
  stimulusControlAnswer : StimulusCoordinate → FlyControlAnswer
  jointControlAnswer : Fibre.PaintedOverlapProfile → StimulusCoordinate → FlyControlAnswer

controlAnswer : FlyControlQuery → FlyControlState → FlyControlAnswer
controlAnswer hardControlQuery state = hardControlAnswer (hardControlSurface state)
controlAnswer overlapControlQuery state = overlapControlAnswer (overlapCoordinate state)
controlAnswer stimulusControlQuery state = stimulusControlAnswer (stimulusCoordinate state)
controlAnswer jointControlQuery state =
  jointControlAnswer (overlapCoordinate state) (stimulusCoordinate state)

controlSemantics : Query.QuerySemantics FlyControlState FlyControlQuery FlyControlAnswer
controlSemantics = Query.querySemantics controlAnswer

hardControlAdequateForHardQuery :
  Query.AdequateFor hardControlSurface controlSemantics hardControlQuery
hardControlAdequateForHardQuery =
  Query.factorsForQuery hardControlAnswer (λ state → refl)

overlapJoinAdequateForOverlapQuery :
  Query.AdequateFor overlapJoinedControl controlSemantics overlapControlQuery
overlapJoinAdequateForOverlapQuery =
  Query.factorsForQuery
    (λ joined → overlapControlAnswer (proj₂ joined))
    (λ state → refl)

stimulusJoinAdequateForStimulusQuery :
  Query.AdequateFor stimulusJoinedControl controlSemantics stimulusControlQuery
stimulusJoinAdequateForStimulusQuery =
  Query.factorsForQuery
    (λ joined → stimulusControlAnswer (proj₂ joined))
    (λ state → refl)

fullJoinAdequateForJointQuery :
  Query.AdequateFor fullJoinedControl controlSemantics jointControlQuery
fullJoinAdequateForJointQuery =
  Query.factorsForQuery
    (λ joined → jointControlAnswer (proj₂ (proj₁ joined)) (proj₂ joined))
    (λ state → refl)

hardJointDefect :
  Query.QueryAdequacyDefect hardControlSurface controlSemantics jointControlQuery
hardJointDefect =
  Query.queryAdequacyDefect
    overlapDriven parentOnlyResidual refl (λ ())

overlapJoinJointDefect :
  Query.QueryAdequacyDefect overlapJoinedControl controlSemantics jointControlQuery
overlapJoinJointDefect =
  Query.queryAdequacyDefect
    overlapDriven overlapResidual refl (λ ())

stimulusJoinJointDefect :
  Query.QueryAdequacyDefect stimulusJoinedControl controlSemantics jointControlQuery
stimulusJoinJointDefect =
  Query.queryAdequacyDefect
    overlapDriven parentOnlyDriven refl (λ ())

record DeclaredMinimalJoinedControl : Set₁ where
  constructor declared-minimal-joined-control
  field
    fullJoinAdequate :
      Query.AdequateFor fullJoinedControl controlSemantics jointControlQuery
    hardProperSubobserverDefective :
      Query.QueryAdequacyDefect hardControlSurface controlSemantics jointControlQuery
    overlapProperSubobserverDefective :
      Query.QueryAdequacyDefect overlapJoinedControl controlSemantics jointControlQuery
    stimulusProperSubobserverDefective :
      Query.QueryAdequacyDefect stimulusJoinedControl controlSemantics jointControlQuery

canonicalDeclaredMinimalJoinedControl : DeclaredMinimalJoinedControl
canonicalDeclaredMinimalJoinedControl =
  declared-minimal-joined-control
    fullJoinAdequateForJointQuery
    hardJointDefect
    overlapJoinJointDefect
    stimulusJoinJointDefect

intersectionalNoAutoPromotionAnchor :
  NonFactor.SeparateAxisSufficiencyImpliesIntersectionalSufficiencyPermission → ⊥
intersectionalNoAutoPromotionAnchor =
  NonFactor.separateAxisSufficiencyCannotAutoPromote

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
-- Thin empirical-frontier adapter. Numerical output remains authoritative in
-- dashiBRAIN; this records only which promotion gates have been paid.
------------------------------------------------------------------------

record FlyEmpiricalControlFrontier : Set where
  constructor fly-empirical-control-frontier
  field
    runtimeRepository : String
    runtimeBranch : String
    overlapControlledRunPaid : Bool
    overlapControlledLowResidualObserved : Bool
    overlapControlledStrengthNullRejected : Bool
    overlapControlledLabelNullRejected : Bool
    publishedStimulusControlImplemented : Bool
    publishedStimulusControlledDecisionRunPaid : Bool
    independentTrialOrAnimalReplicationPaid : Bool
    empiricalReading : String

open FlyEmpiricalControlFrontier public

currentFlyEmpiricalControlFrontier : FlyEmpiricalControlFrontier
currentFlyEmpiricalControlFrontier =
  fly-empirical-control-frontier
    "github.com/chboishabba/dashiBRAIN"
    "agent/malecns-real-benchmark-tranche"
    true
    true
    false
    false
    true
    false
    false
    "The 26-region overlap-controlled LORO result remains predictive, but the refitted strength and label nulls are not rejected. Published-stimulus control is implemented but its decision run remains unpaid; pair-specific wiring mechanism and independent replication are therefore not promoted."

------------------------------------------------------------------------
-- MoE / grokking interpretation boundary.
--
-- Sparse expert routing and grokking cleanup become instances of the same
-- observer/refinement grammar only at the structural level: a selected fibre
-- family must still pay its consumer-specific adequacy obligation.
------------------------------------------------------------------------

data ResidualizedSurfaceAutomaticallyRefinesRawObservation : Set where

residualizedSurfaceDoesNotAutomaticallyRefineRawObservation :
  ResidualizedSurfaceAutomaticallyRefinesRawObservation → ⊥
residualizedSurfaceDoesNotAutomaticallyRefineRawObservation ()

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
    pairWithNuisanceAxisIsMonotoneRefinement : Bool
    residualisationAutomaticallyIsMonotoneRefinement : Bool
    separateAxisAdequacyAutomaticallyImpliesJointAdequacy : Bool
    declaredFullJoinIsMinimalForFiniteJointSpecimen : Bool

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
    true
    false
    false
    true
