module DASHI.Law.CoerciveEncounterTrajectoryBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Core.ResidualObserverDependencyExact as Residual
import DASHI.Law.QueenslandWandingReachabilityBidiExact as Wand

------------------------------------------------------------------------
-- Trajectory-level BIDI.
--
-- A downstream encounter conclusion is not treated as one opaque fact.  It is
-- represented as an ordered chain of transitions, each with its own producer.
-- Reverse proof search returns the first unsupported edge in historical order.
------------------------------------------------------------------------

data SupportState : Set where
  supported unsupported : SupportState

record TrajectoryEdge : Set where
  constructor trajectoryEdge
  field
    fromPhase toPhase : Wand.EncounterPhase
    producer : Wand.ProducerObligation
    support : SupportState
    edgeReference : String

open TrajectoryEdge public

data Trajectory : Set where
  [] : Trajectory
  _∷_ : TrajectoryEdge → Trajectory → Trajectory

infixr 5 _∷_

data ReverseResult : Set where
  trajectoryClosed : ReverseResult
  firstOpen : TrajectoryEdge → ReverseResult

firstUnsupported : Trajectory → ReverseResult
firstUnsupported [] = trajectoryClosed
firstUnsupported (edge ∷ rest) with support edge
... | unsupported = firstOpen edge
... | supported = firstUnsupported rest

------------------------------------------------------------------------
-- Exactness receipts for the recursive router.
------------------------------------------------------------------------

record FirstOpenReceipt (trajectory : Trajectory) : Set where
  constructor firstOpenReceipt
  field
    edge : TrajectoryEdge
    routerReturnsEdge : firstUnsupported trajectory ≡ firstOpen edge
    missingProducer : Wand.ProducerObligation
    producerIsEdgeProducer : missingProducer ≡ producer edge
    receiptReference : String

open FirstOpenReceipt public

firstOpenReceiptNamesExactProducer :
  ∀ {trajectory} →
  (receipt : FirstOpenReceipt trajectory) →
  missingProducer receipt ≡ producer (edge receipt)
firstOpenReceiptNamesExactProducer = producerIsEdgeProducer

------------------------------------------------------------------------
-- Concrete encounter spine.  This is a schema, not an assertion that every
-- encounter traverses every edge.
------------------------------------------------------------------------

wandAuthorityEdge : SupportState → TrajectoryEdge
wandAuthorityEdge state = trajectoryEdge
  Wand.publicPresence Wand.compelledContact
  Wand.wandAuthorityReceipt state
  "initial statutory wand authority"

wandRequirementEdge : SupportState → TrajectoryEdge
wandRequirementEdge state = trajectoryEdge
  Wand.compelledContact Wand.wandRequirement
  Wand.wandAuthorityReceipt state
  "compelled wand requirement"

responsePredicateEdge : SupportState → TrajectoryEdge
responsePredicateEdge state = trajectoryEdge
  Wand.wandRequirement Wand.downstreamPredicate
  Wand.transitionCrossTab state
  "alarm / response / non-compliance to downstream predicate"

searchEdge : SupportState → TrajectoryEdge
searchEdge state = trajectoryEdge
  Wand.downstreamPredicate Wand.personalSearch
  Wand.searchPredicateReceipt state
  "separate warrantless-search predicate"

canonicalEncounterTrajectory :
  SupportState → SupportState → SupportState → SupportState → Trajectory
canonicalEncounterTrajectory a b c d =
  wandAuthorityEdge a ∷
  wandRequirementEdge b ∷
  responsePredicateEdge c ∷
  searchEdge d ∷
  []

canonicalFirstGapAtTransition :
  firstUnsupported
    (canonicalEncounterTrajectory supported supported unsupported unsupported)
  ≡ firstOpen (responsePredicateEdge unsupported)
canonicalFirstGapAtTransition = refl

canonicalEarlierGapDominatesLaterGap :
  firstUnsupported
    (canonicalEncounterTrajectory supported unsupported unsupported unsupported)
  ≡ firstOpen (wandRequirementEdge unsupported)
canonicalEarlierGapDominatesLaterGap = refl

canonicalClosedTrajectory :
  firstUnsupported
    (canonicalEncounterTrajectory supported supported supported supported)
  ≡ trajectoryClosed
canonicalClosedTrajectory = refl

------------------------------------------------------------------------
-- Consumer-scoped trajectory obligations.
------------------------------------------------------------------------

claimTrajectory : Wand.ConsumerClaim → Trajectory
claimTrajectory Wand.lawfulInitialWand =
  wandAuthorityEdge unsupported ∷ []
claimTrajectory Wand.lawfulDownstreamSearch =
  canonicalEncounterTrajectory supported supported supported unsupported
claimTrajectory Wand.gatewayRate =
  responsePredicateEdge unsupported ∷ []
claimTrajectory Wand.selectionDisparity =
  trajectoryEdge Wand.publicPresence Wand.compelledContact
    Wand.eligiblePopulationDenominator unsupported
    "eligible-population denominator and selection frame" ∷ []
claimTrajectory Wand.deterrenceEffect =
  trajectoryEdge Wand.publicPresence Wand.arrestOrRelease
    Wand.counterfactualControl unsupported
    "counterfactual no-regime comparison" ∷ []
claimTrajectory Wand.forceHistoryReconstruction =
  trajectoryEdge Wand.arrestOrRelease Wand.arrestOrRelease
    Wand.recordingReceipt unsupported
    "independent recording / reconstruction channel" ∷ []

consumerReverseSearch : Wand.ConsumerClaim → ReverseResult
consumerReverseSearch claim = firstUnsupported (claimTrajectory claim)

gatewayRateReopensTransitionData :
  consumerReverseSearch Wand.gatewayRate
  ≡ firstOpen (responsePredicateEdge unsupported)
gatewayRateReopensTransitionData = refl

selectionDisparityReopensDenominator :
  consumerReverseSearch Wand.selectionDisparity
  ≡ firstOpen
      (trajectoryEdge Wand.publicPresence Wand.compelledContact
        Wand.eligiblePopulationDenominator unsupported
        "eligible-population denominator and selection frame")
selectionDisparityReopensDenominator = refl

------------------------------------------------------------------------
-- Residual x-pollination.
--
-- The unresolved edge is treated as an action-relevant residual coordinate.
-- A coarse endpoint label does not by itself determine which producer is open.
------------------------------------------------------------------------

data CoarseOutcome : Set where
  searchedOutcome releasedOutcome : CoarseOutcome

data ResidualCode : Set where
  noResidual authorityGap transitionGap searchGap recordingGap : ResidualCode

data ProbeAction : Set where
  inspectStatute inspectTransitionTable inspectSearchRecord inspectRecording : ProbeAction

data ProbeIndex : Set where
  encounterIndex : ProbeIndex

data ReconstructionState : Set where
  searchedWithClosedPath searchedWithTransitionGap : ReconstructionState

coarseOutcome : ReconstructionState → CoarseOutcome
coarseOutcome searchedWithClosedPath = searchedOutcome
coarseOutcome searchedWithTransitionGap = searchedOutcome

dependencyCode : ReconstructionState → ProbeAction → ResidualCode
dependencyCode searchedWithClosedPath inspectTransitionTable = noResidual
dependencyCode searchedWithTransitionGap inspectTransitionTable = transitionGap
dependencyCode searchedWithClosedPath inspectStatute = noResidual
dependencyCode searchedWithTransitionGap inspectStatute = noResidual
dependencyCode searchedWithClosedPath inspectSearchRecord = noResidual
dependencyCode searchedWithTransitionGap inspectSearchRecord = noResidual
dependencyCode searchedWithClosedPath inspectRecording = noResidual
dependencyCode searchedWithTransitionGap inspectRecording = noResidual

Influences : ReconstructionState → ProbeAction → ProbeIndex → ProbeIndex → Set
Influences state action i j = dependencyCode state action ≡ transitionGap

trajectoryResidualObserver :
  Residual.ResidualDependencyObserver
    ReconstructionState ProbeAction ProbeIndex ResidualCode
trajectoryResidualObserver = record
  { Influences = Influences
  ; dependencyCode = dependencyCode
  }

transitionGapHiddenByCoarseOutcome :
  Residual.HiddenResidualDependency
    trajectoryResidualObserver coarseOutcome inspectTransitionTable
transitionGapHiddenByCoarseOutcome =
  Residual.hiddenResidualDependency
    searchedWithClosedPath
    searchedWithTransitionGap
    refl
    (λ ())

coarseOutcomeCannotRecoverTransitionResidual :
  Residual.DependencyCodeDescendsAt
    trajectoryResidualObserver coarseOutcome inspectTransitionTable → ⊥
coarseOutcomeCannotRecoverTransitionResidual =
  Residual.hiddenResidualDependencyBlocksDescent
    transitionGapHiddenByCoarseOutcome

------------------------------------------------------------------------
-- Boundary: outcome success never fills an earlier evidentiary gap.
------------------------------------------------------------------------

record TrajectoryBidiBoundary : Set where
  constructor trajectoryBidiBoundary
  field
    laterSupportedEdgeClosesEarlierGap : Bool
    laterSupportedEdgeClosesEarlierGapIsFalse :
      laterSupportedEdgeClosesEarlierGap ≡ false
    endpointLabelDeterminesTransitionProvenance : Bool
    endpointLabelDeterminesTransitionProvenanceIsFalse :
      endpointLabelDeterminesTransitionProvenance ≡ false
    firstUnsupportedEdgeIsAcquisitionTarget : Bool
    firstUnsupportedEdgeIsAcquisitionTargetIsTrue :
      firstUnsupportedEdgeIsAcquisitionTarget ≡ true

canonicalTrajectoryBidiBoundary : TrajectoryBidiBoundary
canonicalTrajectoryBidiBoundary =
  trajectoryBidiBoundary false refl false refl true refl
