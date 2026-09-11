module DASHI.Reasoning.FlyJoinedObserverAdmissibilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Reasoning.FibreRoutingProjectionAdequacyCrossPollinationExact as Routing

------------------------------------------------------------------------
-- FLY JOINED-OBSERVER / ADMISSIBILITY ADAPTER
--
-- A nuisance residual is not automatically an information refinement.  The
-- monotone repo-native operation is to retain the source observation and pair
-- it with an additional nuisance/context coordinate:
--
--   O_joined x = (O_raw x , N x).
--
-- The residualized target may then be a downstream consumer of that joined
-- carrier.  This owner therefore models stimulus and atlas-overlap coordinates
-- as retained observer axes before any consumer-specific subtraction.
--
-- This is a finite exact specimen of the experiment-design rule now used by
-- the Fly lane.  It does not assert that these two coordinates exhaust the
-- biological state or establish a connectome mechanism.
------------------------------------------------------------------------

data FlyFineState : Set where
  overlapDriven : FlyFineState
  overlapResidual : FlyFineState
  parentOnlyDriven : FlyFineState
  parentOnlyResidual : FlyFineState

data OverlapAxis : Set where
  overlapPresent : OverlapAxis
  parentOnly : OverlapAxis

data StimulusAxis : Set where
  publishedDrivePresent : StimulusAxis
  publishedDriveRemoved : StimulusAxis

hardSurface : FlyFineState → Routing.Fibre.HardPaintedIdentity
hardSurface state = Routing.Fibre.parentWinner

overlapAxis : FlyFineState → OverlapAxis
overlapAxis overlapDriven = overlapPresent
overlapAxis overlapResidual = overlapPresent
overlapAxis parentOnlyDriven = parentOnly
overlapAxis parentOnlyResidual = parentOnly

stimulusAxis : FlyFineState → StimulusAxis
stimulusAxis overlapDriven = publishedDrivePresent
stimulusAxis overlapResidual = publishedDriveRemoved
stimulusAxis parentOnlyDriven = publishedDrivePresent
stimulusAxis parentOnlyResidual = publishedDriveRemoved

overlapJoinedObserver :
  FlyFineState → (Routing.Fibre.HardPaintedIdentity × OverlapAxis)
overlapJoinedObserver = Observer.pairObserver hardSurface overlapAxis

stimulusJoinedObserver :
  FlyFineState → (Routing.Fibre.HardPaintedIdentity × StimulusAxis)
stimulusJoinedObserver = Observer.pairObserver hardSurface stimulusAxis

fullJoinedObserver :
  FlyFineState → ((Routing.Fibre.HardPaintedIdentity × OverlapAxis) × StimulusAxis)
fullJoinedObserver = Observer.pairObserver overlapJoinedObserver stimulusAxis

-- Pairing is a genuine monotone refinement of the retained source observer.
overlapJoinRefinesHard : Observer.Refines hardSurface overlapJoinedObserver
overlapJoinRefinesHard = Observer.pairRefinesLeft hardSurface overlapAxis

stimulusJoinRefinesHard : Observer.Refines hardSurface stimulusJoinedObserver
stimulusJoinRefinesHard = Observer.pairRefinesLeft hardSurface stimulusAxis

fullJoinRefinesOverlapJoin : Observer.Refines overlapJoinedObserver fullJoinedObserver
fullJoinRefinesOverlapJoin = Observer.pairRefinesLeft overlapJoinedObserver stimulusAxis

------------------------------------------------------------------------
-- Consumer-indexed query semantics.
------------------------------------------------------------------------

data FlyControlQuery : Set where
  hardIdentityQuery : FlyControlQuery
  overlapQuery : FlyControlQuery
  stimulusQuery : FlyControlQuery
  jointOverlapStimulusQuery : FlyControlQuery

data FlyControlAnswer : Set where
  hardAnswer : Routing.Fibre.HardPaintedIdentity → FlyControlAnswer
  overlapAnswer : OverlapAxis → FlyControlAnswer
  stimulusAnswer : StimulusAxis → FlyControlAnswer
  jointAnswer : OverlapAxis → StimulusAxis → FlyControlAnswer

controlAnswer : FlyControlQuery → FlyFineState → FlyControlAnswer
controlAnswer hardIdentityQuery state = hardAnswer (hardSurface state)
controlAnswer overlapQuery state = overlapAnswer (overlapAxis state)
controlAnswer stimulusQuery state = stimulusAnswer (stimulusAxis state)
controlAnswer jointOverlapStimulusQuery state =
  jointAnswer (overlapAxis state) (stimulusAxis state)

controlSemantics : Query.QuerySemantics FlyFineState FlyControlQuery FlyControlAnswer
controlSemantics = Query.querySemantics controlAnswer

hardAdequateForHardIdentity :
  Query.AdequateFor hardSurface controlSemantics hardIdentityQuery
hardAdequateForHardIdentity =
  Query.factorsForQuery hardAnswer (λ state → refl)

overlapJoinAdequateForOverlap :
  Query.AdequateFor overlapJoinedObserver controlSemantics overlapQuery
overlapJoinAdequateForOverlap =
  Query.factorsForQuery
    (λ surface → overlapAnswer (proj₂ surface))
    (λ state → refl)

stimulusJoinAdequateForStimulus :
  Query.AdequateFor stimulusJoinedObserver controlSemantics stimulusQuery
stimulusJoinAdequateForStimulus =
  Query.factorsForQuery
    (λ surface → stimulusAnswer (proj₂ surface))
    (λ state → refl)

fullJoinAdequateForJointConsumer :
  Query.AdequateFor fullJoinedObserver controlSemantics jointOverlapStimulusQuery
fullJoinAdequateForJointConsumer =
  Query.factorsForQuery
    (λ surface → jointAnswer (proj₂ (proj₁ surface)) (proj₂ surface))
    (λ state → refl)

------------------------------------------------------------------------
-- Proper sub-observers fail the joined consumer for explicit collisions.
------------------------------------------------------------------------

hardJointDefect :
  Query.QueryAdequacyDefect hardSurface controlSemantics jointOverlapStimulusQuery
hardJointDefect =
  Query.queryAdequacyDefect
    overlapDriven parentOnlyResidual refl (λ ())

overlapJoinJointDefect :
  Query.QueryAdequacyDefect
    overlapJoinedObserver controlSemantics jointOverlapStimulusQuery
overlapJoinJointDefect =
  Query.queryAdequacyDefect
    overlapDriven overlapResidual refl (λ ())

stimulusJoinJointDefect :
  Query.QueryAdequacyDefect
    stimulusJoinedObserver controlSemantics jointOverlapStimulusQuery
stimulusJoinJointDefect =
  Query.queryAdequacyDefect
    overlapDriven parentOnlyDriven refl (λ ())

hardCannotAnswerJointConsumer :
  Query.AdequateFor hardSurface controlSemantics jointOverlapStimulusQuery → ⊥
hardCannotAnswerJointConsumer =
  Query.queryAdequacyDefectBlocksFactorisation hardJointDefect

overlapJoinCannotAnswerJointConsumer :
  Query.AdequateFor overlapJoinedObserver controlSemantics jointOverlapStimulusQuery → ⊥
overlapJoinCannotAnswerJointConsumer =
  Query.queryAdequacyDefectBlocksFactorisation overlapJoinJointDefect

stimulusJoinCannotAnswerJointConsumer :
  Query.AdequateFor stimulusJoinedObserver controlSemantics jointOverlapStimulusQuery → ⊥
stimulusJoinCannotAnswerJointConsumer =
  Query.queryAdequacyDefectBlocksFactorisation stimulusJoinJointDefect

record DeclaredMinimalJoinedObserver : Set₁ where
  constructor declared-minimal-joined-observer
  field
    joinedAdequate :
      Query.AdequateFor fullJoinedObserver controlSemantics jointOverlapStimulusQuery
    hardProperSubobserverDefective :
      Query.QueryAdequacyDefect hardSurface controlSemantics jointOverlapStimulusQuery
    overlapProperSubobserverDefective :
      Query.QueryAdequacyDefect overlapJoinedObserver controlSemantics jointOverlapStimulusQuery
    stimulusProperSubobserverDefective :
      Query.QueryAdequacyDefect stimulusJoinedObserver controlSemantics jointOverlapStimulusQuery

canonicalDeclaredMinimalJoinedObserver : DeclaredMinimalJoinedObserver
canonicalDeclaredMinimalJoinedObserver =
  declared-minimal-joined-observer
    fullJoinAdequateForJointConsumer
    hardJointDefect
    overlapJoinJointDefect
    stimulusJoinJointDefect

------------------------------------------------------------------------
-- Intersectional lesson: separate one-axis adequacy is not joint adequacy.
------------------------------------------------------------------------

data SeparateControlAdequacyImpliesJointAdequacy : Set where

separateControlAdequacyDoesNotAutoPromote :
  SeparateControlAdequacyImpliesJointAdequacy → ⊥
separateControlAdequacyDoesNotAutoPromote ()

intersectionalNoAutoPromotionAnchor :
  NonFactor.SeparateAxisSufficiencyImpliesIntersectionalSufficiencyPermission → ⊥
intersectionalNoAutoPromotionAnchor =
  NonFactor.separateAxisSufficiencyCannotAutoPromote

------------------------------------------------------------------------
-- Current empirical frontier adapter.
--
-- Values below are status only.  They do not promote mechanism.  The runtime
-- producer remains authoritative for numerical values and null distributions.
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
    "26-region overlap-controlled LORO remains predictive, but refitted strength/label nulls are not rejected; published-stimulus control is implemented but still awaits the decision run, so pair-specific wiring mechanism and population replication remain unpaid."

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data ResidualizedSurfaceAutomaticallyRefinesRawObservation : Set where
data OneAxisControlImpliesJointControlAdequacy : Set where
data JoinedObserverAdequacyImpliesBiologicalMechanism : Set where

residualizationDoesNotAutomaticallyCreateRefinement :
  ResidualizedSurfaceAutomaticallyRefinesRawObservation → ⊥
residualizationDoesNotAutomaticallyCreateRefinement ()

oneAxisControlDoesNotCreateJointAdequacy :
  OneAxisControlImpliesJointControlAdequacy → ⊥
oneAxisControlDoesNotCreateJointAdequacy ()

joinedAdequacyDoesNotCreateBiologicalMechanism :
  JoinedObserverAdequacyImpliesBiologicalMechanism → ⊥
joinedAdequacyDoesNotCreateBiologicalMechanism ()

record FlyJoinedObserverBoundary : Set where
  constructor fly-joined-observer-boundary
  field
    pairWithNuisanceAxisIsMonotoneRefinement : Bool
    residualizationAutomaticallyIsMonotoneRefinement : Bool
    adequacyRemainsConsumerIndexed : Bool
    separateAxisAdequacyAutomaticallyImpliesJointAdequacy : Bool
    declaredFullJoinIsMinimalForJointFiniteSpecimen : Bool
    empiricalNullFailureMayDriveFurtherAxisSearch : Bool
    joinedAdequacyAutomaticallyEstablishesPhysicalMechanism : Bool

canonicalFlyJoinedObserverBoundary : FlyJoinedObserverBoundary
canonicalFlyJoinedObserverBoundary =
  fly-joined-observer-boundary
    true false true false true true false
