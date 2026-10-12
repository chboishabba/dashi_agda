module DASHI.Cognition.PNF.SensibLawFriendlyjordiesSouthAustraliaGovernanceWeldExact where

------------------------------------------------------------------------
-- FRIENDLYJORDIES MARCH GOVERNANCE MAX-CUT
--
-- This owner closes the representation seam between the existing SensibLaw
-- Friendlyjordies source-totality surface and the March O/R/C/S/L/P/G/F
-- governance carrier.
--
-- Current source status is deliberately asymmetric:
--
--   CPRS
--     pinned SensibLaw source unit
--       -> M12 SemanticTracePath
--       -> external-world demand
--       -> evidence-qualified governance-transition interface
--
--   South Australia renewables
--     archive-refresh producer recognises a `south_australia` theme and can
--     emit a candidate sentence
--       != pinned static source unit
--       -> explicit acquisition demand
--       -> governance transition remains blocked at source payment
--
-- No source trace, transition, delta, reachability change or lock-in witness
-- created here settles the underlying political/historical proposition or
-- creates a universal Labor/Greens ranking.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawPersistentStatementObservationEventSpineExact as Trace
import DASHI.Cognition.PNF.SensibLawChronologyContestationSpineExact as Contest
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesSourceTotalityExact as Total
import DASHI.Core.FriendlyjordiesGovernanceQuestionExact as March
import DASHI.Core.GovernanceTrajectoryRealisationExact as Gov
import DASHI.Core.HistoryConditionedChoiceExact as History
import DASHI.Core.RelationalHistoryFabricExact as Fabric
import DASHI.Core.ThresholdResidualTrajectoryGeometryExact as Threshold
import DASHI.Core.PoliticalContestabilityExact as Political

------------------------------------------------------------------------
-- Exact current source boundary.
------------------------------------------------------------------------

southAustraliaNamedCase : Bool
southAustraliaNamedCase = true

southAustraliaPinnedFixturePaid : Bool
southAustraliaPinnedFixturePaid = false

southAustraliaAcquisitionRoutePresent : Bool
southAustraliaAcquisitionRoutePresent = true

cprsSourcePaidTransitionPresent : Bool
cprsSourcePaidTransitionPresent = true

southAustraliaTransitionBlockedBySourcePayment : Bool
southAustraliaTransitionBlockedBySourcePayment = true

transitionCreatesWorldTruth : Bool
transitionCreatesWorldTruth = false

trajectoryCreatesUniversalPartyRanking : Bool
trajectoryCreatesUniversalPartyRanking = false

------------------------------------------------------------------------
-- South Australia is already present in the March question and in the
-- SensibLaw archive-refresh producer vocabulary, but not in the pinned static
-- friendlyjordies_chat_arguments.json source fixture at SensibLaw revision
-- f9c4670... .  Preserve producer capability and source payment separately.
------------------------------------------------------------------------

southAustraliaCase : March.MarchCase
southAustraliaCase = March.southAustraliaRenewables

southAustraliaRoot : Contest.PropositionRoot
southAustraliaRoot =
  Contest.proposition-root
    "prop:south-australia:high-renewable-grid"
    "South Australia battery / high-renewable-grid example"
    true refl
    false refl
    false refl
    false refl

record SouthAustraliaProducerReceipt : Set where
  constructor south-australia-producer-receipt
  field
    sensibLawRevisionRef : String
    producerRef : String
    themeKey : String
    themeNeedlesRef : String
    outputFixtureRef : String
    candidateLiteral : String
    conditionalOnArchiveTheme : Bool
    conditionalOnArchiveThemeIsTrue :
      conditionalOnArchiveTheme ≡ true
    pinnedStaticSourceUnitPresent : Bool
    pinnedStaticSourceUnitPresentIsFalse :
      pinnedStaticSourceUnitPresent ≡ false
    createsClaimTruth : Bool
    createsClaimTruthIsFalse : createsClaimTruth ≡ false

open SouthAustraliaProducerReceipt public

southAustraliaProducerReceipt : SouthAustraliaProducerReceipt
southAustraliaProducerReceipt =
  south-australia-producer-receipt
    "SensibLaw/main f9c4670ef04b40e8153caa7dd00fa1eba7013ef4"
    "SensibLaw/src/reporting/narrative_fixture_refresh.py::_build_chat_arguments_payload"
    "south_australia"
    "south australia + 70% renewable"
    ".cache_local/narrative/friendlyjordies_chat_arguments.archive.json"
    "FriendlyJordies said that South Australia uses large batteries to support a high-renewable grid."
    true refl
    false refl
    false refl

southAustraliaAcquisitionDemand : Total.AcquisitionDemand
southAustraliaAcquisitionDemand =
  Total.acquisition-demand
    "south_australia_renewables"
    (Contest.PropositionRoot.propositionRef southAustraliaRoot)
    "pinned archive-backed friendlyjordies_chat_arguments fixture containing the South Australia unit"
    "SensibLaw/src/reporting/narrative_fixture_refresh.py::_build_chat_arguments_payload"
    "producer support is present but the pinned static fixture does not yet pay an exact M12 statement/span"
    false refl

southAustraliaCurrentDisposition : Total.SourceDisposition
southAustraliaCurrentDisposition =
  Total.unresolvedAcquisition southAustraliaAcquisitionDemand

-- The current pinned-source state has no constructor.  This is a revision-
-- scoped repository fact, not a timeless claim that the archive lacks the
-- source material.
data SouthAustraliaPinnedFixtureSource : Set where

noCurrentSouthAustraliaPinnedFixtureSource :
  SouthAustraliaPinnedFixtureSource → ⊥
noCurrentSouthAustraliaPinnedFixtureSource ()

------------------------------------------------------------------------
-- CPRS already has a paid M12 trace and explicit external-world demand.
------------------------------------------------------------------------

record SourcePaidHistoricalCase : Set where
  constructor source-paid-historical-case
  field
    case : March.MarchCase
    propositionRef : String
    trace : Trace.SemanticTracePath
    worldDemand : Total.WorldDemand
    sourcePaymentCreatesWorldTruth : Bool
    sourcePaymentCreatesWorldTruthIsFalse :
      sourcePaymentCreatesWorldTruth ≡ false

open SourcePaidHistoricalCase public

cprsSourcePaidCase : SourcePaidHistoricalCase
cprsSourcePaidCase =
  source-paid-historical-case
    March.cprs2009
    "prop:cprs-blocking"
    Total.cprsSourceTrace
    Total.cprsWorldDemand
    false refl

------------------------------------------------------------------------
-- Current-case disposition is constructive: each named March case is either
-- source-paid or explicitly source-pending.  There is no silent third path.
------------------------------------------------------------------------

data CurrentMarchCaseDisposition : March.MarchCase → Set where
  cprsCurrentlySourcePaid :
    SourcePaidHistoricalCase →
    CurrentMarchCaseDisposition March.cprs2009
  southAustraliaCurrentlySourcePending :
    Total.AcquisitionDemand →
    CurrentMarchCaseDisposition March.southAustraliaRenewables

currentMarchCaseDisposition :
  (case : March.MarchCase) → CurrentMarchCaseDisposition case
currentMarchCaseDisposition March.cprs2009 =
  cprsCurrentlySourcePaid cprsSourcePaidCase
currentMarchCaseDisposition March.southAustraliaRenewables =
  southAustraliaCurrentlySourcePending southAustraliaAcquisitionDemand

------------------------------------------------------------------------
-- External-world payment is a separate premise from source payment.
-- A source trace establishes what the source says; a world transition requires
-- an independently reviewed premise about the historical/event relation.
------------------------------------------------------------------------

record WorldTransitionEvidence (source : SourcePaidHistoricalCase) : Set₁ where
  constructor world-transition-evidence
  field
    evidenceRef : String
    sourceRefs : List String
    reviewRef : String
    reviewed : Bool
    reviewedIsTrue : reviewed ≡ true
    TransitionPremise : Set
    transitionPremiseWitness : TransitionPremise
    sourceTraceAloneCreatesPremise : Bool
    sourceTraceAloneCreatesPremiseIsFalse :
      sourceTraceAloneCreatesPremise ≡ false

open WorldTransitionEvidence public

------------------------------------------------------------------------
-- Same-object O/R/C/S/L/P/G/F transition carrier.
--
-- The transition and lattice equations are literally the functions exported by
-- GovernanceTrajectoryRealisationExact.  The evidence object is part of the
-- same record, so a historical transition cannot enter this application owner
-- without both source payment and external-world payment.
------------------------------------------------------------------------

record EvidenceQualifiedGovernanceTransition
    {Organization Requirement Code State Lattice Proposal Gap : Set}
    (model :
      Gov.ZKPGovernanceModel
        Organization Requirement Code State Lattice Proposal Gap)
    (dynamics :
      Gov.GovernanceDynamics
        Organization Requirement Code State Lattice Proposal Gap model)
    : Set₁ where
  constructor evidence-qualified-governance-transition
  field
    sourceCase : SourcePaidHistoricalCase
    worldEvidence : WorldTransitionEvidence sourceCase
    organization : Organization
    requirement : Requirement
    proposal : Proposal
    code : Code
    beforeState afterState : State
    beforeLattice afterLattice : Lattice
    afterStateExact :
      afterState
      ≡ Gov.stepState dynamics organization beforeState proposal code
    afterLatticeExact :
      afterLattice
      ≡ Gov.stepLattice dynamics organization beforeLattice proposal code afterState
    transitionCreatesClaimTruth : Bool
    transitionCreatesClaimTruthIsFalse :
      transitionCreatesClaimTruth ≡ false

open EvidenceQualifiedGovernanceTransition public

------------------------------------------------------------------------
-- South Australia cannot currently instantiate the same-object transition.
-- Once a pinned M12 trace exists, it can use SourcePaidHistoricalCase and the
-- exact same downstream compiler as CPRS; no new governance representation is
-- required.
------------------------------------------------------------------------

record SouthAustraliaTransitionPrerequisite : Set where
  constructor south-australia-transition-prerequisite
  field
    pinnedFixtureSource : SouthAustraliaPinnedFixtureSource
    sourceTrace : Trace.SemanticTracePath
    sourceWorldDemand : Total.WorldDemand

southAustraliaTransitionPrerequisiteCurrentlyImpossible :
  SouthAustraliaTransitionPrerequisite → ⊥
southAustraliaTransitionPrerequisiteCurrentlyImpossible prerequisite =
  noCurrentSouthAustraliaPinnedFixtureSource
    (SouthAustraliaTransitionPrerequisite.pinnedFixtureSource prerequisite)

------------------------------------------------------------------------
-- Delta-F without subtraction: an application supplies the strict gap order.
-- This avoids manufacturing numeric semantics for an abstract Gap carrier.
------------------------------------------------------------------------

record GapOrder (Gap : Set) : Set₁ where
  constructor gap-order
  field
    Better : Gap → Gap → Set

open GapOrder public

record GapDeltaWitness
    {Organization Requirement Code State Lattice Proposal Gap : Set}
    {model :
      Gov.ZKPGovernanceModel
        Organization Requirement Code State Lattice Proposal Gap}
    {dynamics :
      Gov.GovernanceDynamics
        Organization Requirement Code State Lattice Proposal Gap model}
    (order : GapOrder Gap)
    (transition : EvidenceQualifiedGovernanceTransition model dynamics)
    : Set₁ where
  constructor gap-delta-witness
  field
    beforeGap afterGap : Gap
    beforeGapMatches :
      beforeGap
      ≡ Gov.F model
          (organization transition)
          (requirement transition)
          (code transition)
          (beforeState transition)
          (beforeLattice transition)
    afterGapMatches :
      afterGap
      ≡ Gov.F model
          (organization transition)
          (requirement transition)
          (code transition)
          (afterState transition)
          (afterLattice transition)
    improvement : Better order afterGap beforeGap

open GapDeltaWitness public

------------------------------------------------------------------------
-- Delta-L / future reachability: expansion and lock-in are dual witnesses over
-- an application-supplied reachability relation.
------------------------------------------------------------------------

record ReachabilitySemantics (Lattice Target : Set) : Set₁ where
  constructor reachability-semantics
  field
    Reachable : Lattice → Target → Set

open ReachabilitySemantics public

record ReachabilityExpansionWitness
    {Lattice Target : Set}
    (semantics : ReachabilitySemantics Lattice Target)
    (before after : Lattice) : Set₁ where
  constructor reachability-expansion-witness
  field
    target : Target
    notReachableBefore : Reachable semantics before target → ⊥
    reachableAfter : Reachable semantics after target

open ReachabilityExpansionWitness public

record LockInRiskWitness
    {Lattice Target : Set}
    (semantics : ReachabilitySemantics Lattice Target)
    (before after : Lattice) : Set₁ where
  constructor lock-in-risk-witness
  field
    target : Target
    reachableBefore : Reachable semantics before target
    notReachableAfter : Reachable semantics after target → ⊥

open LockInRiskWitness public

record NoLockInForTarget
    {Lattice Target : Set}
    (semantics : ReachabilitySemantics Lattice Target)
    (after : Lattice)
    (target : Target) : Set₁ where
  constructor no-lock-in-for-target
  field
    remainsReachable : Reachable semantics after target

open NoLockInForTarget public

------------------------------------------------------------------------
-- Contextual strategy assessments attach the deltas to the *same transition*.
-- Neither constructor creates a globally preferred strategy.
------------------------------------------------------------------------

record IncrementalTrajectoryAssessment
    {Organization Requirement Code State Lattice Proposal Gap Target : Set}
    {model :
      Gov.ZKPGovernanceModel
        Organization Requirement Code State Lattice Proposal Gap}
    {dynamics :
      Gov.GovernanceDynamics
        Organization Requirement Code State Lattice Proposal Gap model}
    (order : GapOrder Gap)
    (reachability : ReachabilitySemantics Lattice Target)
    (transition : EvidenceQualifiedGovernanceTransition model dynamics)
    : Set₁ where
  constructor incremental-trajectory-assessment
  field
    gapDelta : GapDeltaWitness order transition
    latticeExpansion :
      ReachabilityExpansionWitness
        reachability
        (beforeLattice transition)
        (afterLattice transition)
    contextRef : String
    createsGlobalStrategyRanking : Bool
    createsGlobalStrategyRankingIsFalse :
      createsGlobalStrategyRanking ≡ false

open IncrementalTrajectoryAssessment public

record ThresholdTrajectoryAssessment
    {Organization Requirement Code State Lattice Proposal Gap Target : Set}
    {model :
      Gov.ZKPGovernanceModel
        Organization Requirement Code State Lattice Proposal Gap}
    {dynamics :
      Gov.GovernanceDynamics
        Organization Requirement Code State Lattice Proposal Gap model}
    (reachability : ReachabilitySemantics Lattice Target)
    (transition : EvidenceQualifiedGovernanceTransition model dynamics)
    : Set₁ where
  constructor threshold-trajectory-assessment
  field
    ThresholdCleared : Set
    thresholdClearedWitness : ThresholdCleared
    protectedTarget : Target
    noLockIn :
      NoLockInForTarget
        reachability
        (afterLattice transition)
        protectedTarget
    contextRef : String
    createsGlobalStrategyRanking : Bool
    createsGlobalStrategyRankingIsFalse :
      createsGlobalStrategyRanking ≡ false

open ThresholdTrajectoryAssessment public

------------------------------------------------------------------------
-- Cross-pollination receipts from existing history / threshold / political
-- owners.  These are boundaries we reuse, not new domain assumptions.
------------------------------------------------------------------------

existingHistoryDoesNotCollapseFutureCone :
  History.samePresentObservationImpliesSameFutureCone
    History.canonicalHistoryConditionedChoiceBoundary ≡ false
existingHistoryDoesNotCollapseFutureCone = refl

existingHistoryPropagationCanBeApplicationWitnessed :
  Fabric.applicationWitnessCanEstablishHistoryToFuturePropagation
    Fabric.canonicalRelationalHistoryFabricBoundary ≡ true
existingHistoryPropagationCanBeApplicationWitnessed = refl

existingAggregateResidualDoesNotRecoverCoordinates :
  Threshold.aggregateResidualDeterminesCoordinateResiduals
    Threshold.canonicalThresholdTrajectoryBoundary ≡ false
existingAggregateResidualDoesNotRecoverCoordinates = refl

existingTechnicalResolutionDoesNotCreateDemocraticAuthority :
  Political.technicalResolutionImpliesDemocraticAuthorization
    Political.canonicalPoliticalAuthorityBoundary ≡ false
existingTechnicalResolutionDoesNotCreateDemocraticAuthority = refl

------------------------------------------------------------------------
-- Hard firewalls.
------------------------------------------------------------------------

data ProducerCapabilityIsPinnedSourcePayment : Set where
data SourcePaymentIsWorldTruth : Set where
data GovernanceTransitionIsHistoricalTruth : Set where
data GapImprovementCreatesUniversalPartyRanking : Set where
data ReachabilityExpansionEliminatesAllLockInRisk : Set where
data TechnicalResolutionCreatesPoliticalAuthority : Set where

producerCapabilityDoesNotEqualPinnedSourcePayment :
  ProducerCapabilityIsPinnedSourcePayment → ⊥
producerCapabilityDoesNotEqualPinnedSourcePayment ()

sourcePaymentDoesNotEqualWorldTruth : SourcePaymentIsWorldTruth → ⊥
sourcePaymentDoesNotEqualWorldTruth ()

governanceTransitionDoesNotCreateHistoricalTruth :
  GovernanceTransitionIsHistoricalTruth → ⊥
governanceTransitionDoesNotCreateHistoricalTruth ()

gapImprovementDoesNotCreateUniversalPartyRanking :
  GapImprovementCreatesUniversalPartyRanking → ⊥
gapImprovementDoesNotCreateUniversalPartyRanking ()

reachabilityExpansionDoesNotEliminateEveryLockInRisk :
  ReachabilityExpansionEliminatesAllLockInRisk → ⊥
reachabilityExpansionDoesNotEliminateEveryLockInRisk ()

technicalResolutionDoesNotCreatePoliticalAuthority :
  TechnicalResolutionCreatesPoliticalAuthority → ⊥
technicalResolutionDoesNotCreatePoliticalAuthority ()

------------------------------------------------------------------------
-- Current max-cut boundary.
------------------------------------------------------------------------

record FriendlyjordiesSouthAustraliaGovernanceBoundary : Set where
  constructor friendlyjordies-south-australia-governance-boundary
  field
    cprsSourceTracePaid : Bool
    cprsSourceTracePaidIsTrue : cprsSourceTracePaid ≡ true
    cprsExternalWorldTransitionStillPremiseBound : Bool
    cprsExternalWorldTransitionStillPremiseBoundIsTrue :
      cprsExternalWorldTransitionStillPremiseBound ≡ true
    southAustraliaProducerRoutePaid : Bool
    southAustraliaProducerRoutePaidIsTrue :
      southAustraliaProducerRoutePaid ≡ true
    southAustraliaPinnedM12TracePaid : Bool
    southAustraliaPinnedM12TracePaidIsFalse :
      southAustraliaPinnedM12TracePaid ≡ false
    sameTransitionCarrierReadyForBothCases : Bool
    sameTransitionCarrierReadyForBothCasesIsTrue :
      sameTransitionCarrierReadyForBothCases ≡ true
    deltaFRequiresApplicationGapOrder : Bool
    deltaFRequiresApplicationGapOrderIsTrue :
      deltaFRequiresApplicationGapOrder ≡ true
    deltaLRequiresApplicationReachability : Bool
    deltaLRequiresApplicationReachabilityIsTrue :
      deltaLRequiresApplicationReachability ≡ true
    transitionCreatesWorldTruth : Bool
    transitionCreatesWorldTruthIsFalse :
      transitionCreatesWorldTruth ≡ false
    trajectoryCreatesUniversalPartyRanking : Bool
    trajectoryCreatesUniversalPartyRankingIsFalse :
      trajectoryCreatesUniversalPartyRanking ≡ false

open FriendlyjordiesSouthAustraliaGovernanceBoundary public

canonicalFriendlyjordiesSouthAustraliaGovernanceBoundary :
  FriendlyjordiesSouthAustraliaGovernanceBoundary
canonicalFriendlyjordiesSouthAustraliaGovernanceBoundary =
  friendlyjordies-south-australia-governance-boundary
    true refl
    true refl
    true refl
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
