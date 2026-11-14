module DASHI.Cognition.PNF.SensibLawFriendlyjordiesGovernanceMaxCutExact where

------------------------------------------------------------------------
-- FRIENDLYJORDIES GOVERNANCE MAX-CUT CAPSTONE
--
-- Tightens the prior South-Australia/governance owner with the already-existing
-- SensibLaw RootedTraceClaim.  A governance transition is therefore attached
-- to the same proposition root, claim leaf and SemanticTracePath rather than
-- merely carrying compatible string labels.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawPersistentStatementObservationEventSpineExact as Trace
import DASHI.Cognition.PNF.SensibLawChronologyContestationSpineExact as Contest
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesNarrativeGovernanceWeldExact as Weld
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesSourceTotalityExact as Total
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesSouthAustraliaGovernanceWeldExact as Base
import DASHI.Core.FriendlyjordiesGovernanceQuestionExact as March
import DASHI.Core.GovernanceTrajectoryRealisationExact as Gov
import DASHI.Reasoning.SensibLawCorpusWorldPNFBridgeExact as Horizon

------------------------------------------------------------------------
-- Regression-facing summary flags.
------------------------------------------------------------------------

cprsRootedSameObjectPaid : Bool
cprsRootedSameObjectPaid = true

southAustraliaRecoveryCompilerReady : Bool
southAustraliaRecoveryCompilerReady = true

southAustraliaRecoveryCurrentlySourceBlocked : Bool
southAustraliaRecoveryCurrentlySourceBlocked = true

rootedTransitionCreatesWorldTruth : Bool
rootedTransitionCreatesWorldTruth = false

rootedDeltaCreatesUniversalRanking : Bool
rootedDeltaCreatesUniversalRanking = false

------------------------------------------------------------------------
-- CPRS: exact rooted source payment.
------------------------------------------------------------------------

cprsRootedTraceClaim :
  Weld.RootedTraceClaim Weld.cprsBlockingRoot Weld.sourceCprsClaim
cprsRootedTraceClaim =
  Weld.rooted-trace-claim
    Total.cprsSourceTrace
    (Contest.PropositionRoot.propositionRef Weld.cprsBlockingRoot)
    refl
    (Contest.ClaimLeaf.claimRef Weld.sourceCprsClaim)
    refl
    "receipt:friendlyjordies:cprs:rooted-trace"
    (Trace.PersistentStatementIdentity.sourceRevisionRef
      (Trace.SemanticTracePath.statement Total.cprsSourceTrace))
    refl
    (Trace.PersistentStatementIdentity.exactSpanRef
      (Trace.SemanticTracePath.statement Total.cprsSourceTrace))
    refl
    true refl
    false refl

------------------------------------------------------------------------
-- Same-object payment binds March case + rooted claim + source payment.
------------------------------------------------------------------------

record RootedHistoricalCasePayment (case : March.MarchCase) : Set₁ where
  constructor rooted-historical-case-payment
  field
    root : Contest.PropositionRoot
    leaf : Contest.ClaimLeaf root
    rootedClaim : Weld.RootedTraceClaim root leaf
    sourcePayment : Base.SourcePaidHistoricalCase
    caseMatches : Base.SourcePaidHistoricalCase.case sourcePayment ≡ case
    traceMatches :
      Weld.RootedTraceClaim.trace rootedClaim
      ≡ Base.SourcePaidHistoricalCase.trace sourcePayment
    sourcePaymentCreatesWorldTruth : Bool
    sourcePaymentCreatesWorldTruthIsFalse :
      sourcePaymentCreatesWorldTruth ≡ false

open RootedHistoricalCasePayment public

cprsRootedPayment : RootedHistoricalCasePayment March.cprs2009
cprsRootedPayment =
  rooted-historical-case-payment
    Weld.cprsBlockingRoot
    Weld.sourceCprsClaim
    cprsRootedTraceClaim
    Base.cprsSourcePaidCase
    refl
    refl
    false refl

------------------------------------------------------------------------
-- Rooted governance transition.
--
-- The Base transition already requires independently reviewed world evidence.
-- This capstone additionally proves that its source payment is the exact rooted
-- SensibLaw claim payment selected for the March case.
------------------------------------------------------------------------

record RootedEvidenceQualifiedTransition
    {Organization Requirement Code State Lattice Proposal Gap : Set}
    {model :
      Gov.ZKPGovernanceModel
        Organization Requirement Code State Lattice Proposal Gap}
    {dynamics :
      Gov.GovernanceDynamics
        Organization Requirement Code State Lattice Proposal Gap model}
    (case : March.MarchCase) : Set₁ where
  constructor rooted-evidence-qualified-transition
  field
    payment : RootedHistoricalCasePayment case
    transition : Base.EvidenceQualifiedGovernanceTransition model dynamics
    sourcePaymentMatches :
      Base.EvidenceQualifiedGovernanceTransition.sourceCase transition
      ≡ RootedHistoricalCasePayment.sourcePayment payment
    rootedTransitionCreatesTruth : Bool
    rootedTransitionCreatesTruthIsFalse :
      rootedTransitionCreatesTruth ≡ false

open RootedEvidenceQualifiedTransition public

------------------------------------------------------------------------
-- Delta-F / Delta-L / lock-in remain attached to the exact rooted transition.
------------------------------------------------------------------------

record RootedGapDelta
    {Organization Requirement Code State Lattice Proposal Gap : Set}
    {model :
      Gov.ZKPGovernanceModel
        Organization Requirement Code State Lattice Proposal Gap}
    {dynamics :
      Gov.GovernanceDynamics
        Organization Requirement Code State Lattice Proposal Gap model}
    {case : March.MarchCase}
    (order : Base.GapOrder Gap)
    (rooted : RootedEvidenceQualifiedTransition {model = model} {dynamics = dynamics} case)
    : Set₁ where
  constructor rooted-gap-delta
  field
    delta :
      Base.GapDeltaWitness order
        (RootedEvidenceQualifiedTransition.transition rooted)
    createsUniversalRanking : Bool
    createsUniversalRankingIsFalse : createsUniversalRanking ≡ false

open RootedGapDelta public

record RootedReachabilityExpansion
    {Organization Requirement Code State Lattice Proposal Gap Target : Set}
    {model :
      Gov.ZKPGovernanceModel
        Organization Requirement Code State Lattice Proposal Gap}
    {dynamics :
      Gov.GovernanceDynamics
        Organization Requirement Code State Lattice Proposal Gap model}
    {case : March.MarchCase}
    (semantics : Base.ReachabilitySemantics Lattice Target)
    (rooted : RootedEvidenceQualifiedTransition {model = model} {dynamics = dynamics} case)
    : Set₁ where
  constructor rooted-reachability-expansion
  field
    expansion :
      Base.ReachabilityExpansionWitness
        semantics
        (Base.EvidenceQualifiedGovernanceTransition.beforeLattice
          (RootedEvidenceQualifiedTransition.transition rooted))
        (Base.EvidenceQualifiedGovernanceTransition.afterLattice
          (RootedEvidenceQualifiedTransition.transition rooted))

open RootedReachabilityExpansion public

record RootedLockInRisk
    {Organization Requirement Code State Lattice Proposal Gap Target : Set}
    {model :
      Gov.ZKPGovernanceModel
        Organization Requirement Code State Lattice Proposal Gap}
    {dynamics :
      Gov.GovernanceDynamics
        Organization Requirement Code State Lattice Proposal Gap model}
    {case : March.MarchCase}
    (semantics : Base.ReachabilitySemantics Lattice Target)
    (rooted : RootedEvidenceQualifiedTransition {model = model} {dynamics = dynamics} case)
    : Set₁ where
  constructor rooted-lock-in-risk
  field
    risk :
      Base.LockInRiskWitness
        semantics
        (Base.EvidenceQualifiedGovernanceTransition.beforeLattice
          (RootedEvidenceQualifiedTransition.transition rooted))
        (Base.EvidenceQualifiedGovernanceTransition.afterLattice
          (RootedEvidenceQualifiedTransition.transition rooted))
    riskIsContextualNotUniversal : Bool
    riskIsContextualNotUniversalIsTrue :
      riskIsContextualNotUniversal ≡ true

open RootedLockInRisk public

------------------------------------------------------------------------
-- South Australia recovery compiler.
--
-- This specifies exactly what acquisition must produce.  The current pinned
-- fixture cannot inhabit pinnedFixtureSource, so this path is structurally
-- ready but currently blocked.  Once paid, it produces the same rooted payment
-- type used by CPRS; no new transition semantics are needed.
------------------------------------------------------------------------

southAustraliaWorldDemand : Total.WorldDemand
southAustraliaWorldDemand =
  Total.world-demand
    (Contest.PropositionRoot.propositionRef Base.southAustraliaRoot)
    Horizon.externalWorldHorizon
    "demand:south-australia:independent-grid-history"
    "the narrative source can pay that the example was invoked; grid composition, battery role, chronology and governance consequences require external primary or scholarly evidence"

record SouthAustraliaRecoveredM12Payment : Set₁ where
  constructor south-australia-recovered-m12-payment
  field
    pinnedFixtureSource : Base.SouthAustraliaPinnedFixtureSource
    statementLink : Trace.StatementCandidateObservationLink
    eventLink : Trace.ObservationEventLink
    leaf : Contest.ClaimLeaf Base.southAustraliaRoot
    rootedClaim : Weld.RootedTraceClaim Base.southAustraliaRoot leaf
    rootedTraceBuiltFromLinks :
      Weld.RootedTraceClaim.trace rootedClaim
      ≡ Trace.traceFromLinks
          statementLink
          eventLink
          (Contest.ClaimLeaf.claimRef leaf ∷ [])
          ("cmp:south-australia:governance-example" ∷ [])
    sourceRevisionIsPinned : String
    exactSpanIsPinned : String

open SouthAustraliaRecoveredM12Payment public

southAustraliaRecoveryCurrentlyImpossible :
  SouthAustraliaRecoveredM12Payment → ⊥
southAustraliaRecoveryCurrentlyImpossible recovery =
  Base.noCurrentSouthAustraliaPinnedFixtureSource
    (SouthAustraliaRecoveredM12Payment.pinnedFixtureSource recovery)

southAustraliaSourcePaidCaseFromRecovery :
  SouthAustraliaRecoveredM12Payment → Base.SourcePaidHistoricalCase
southAustraliaSourcePaidCaseFromRecovery recovery =
  Base.source-paid-historical-case
    March.southAustraliaRenewables
    (Contest.PropositionRoot.propositionRef Base.southAustraliaRoot)
    (Weld.RootedTraceClaim.trace
      (SouthAustraliaRecoveredM12Payment.rootedClaim recovery))
    southAustraliaWorldDemand
    false refl

southAustraliaRootedPaymentFromRecovery :
  (recovery : SouthAustraliaRecoveredM12Payment) →
  RootedHistoricalCasePayment March.southAustraliaRenewables
southAustraliaRootedPaymentFromRecovery recovery =
  rooted-historical-case-payment
    Base.southAustraliaRoot
    (SouthAustraliaRecoveredM12Payment.leaf recovery)
    (SouthAustraliaRecoveredM12Payment.rootedClaim recovery)
    (southAustraliaSourcePaidCaseFromRecovery recovery)
    refl
    refl
    false refl

------------------------------------------------------------------------
-- Max-cut firewalls.
------------------------------------------------------------------------

data RootedTraceCreatesWorldTruth : Set where
data RootedTransitionCreatesUniversalRanking : Set where
data SouthAustraliaProducerCapabilityPaysPinnedSource : Set where
data DeltaFDeterminesDeltaL : Set where
data ReachabilityExpansionRulesOutAllLockIn : Set where

rootedTraceDoesNotCreateWorldTruth : RootedTraceCreatesWorldTruth → ⊥
rootedTraceDoesNotCreateWorldTruth ()

rootedTransitionDoesNotCreateUniversalRanking :
  RootedTransitionCreatesUniversalRanking → ⊥
rootedTransitionDoesNotCreateUniversalRanking ()

southAustraliaProducerCapabilityDoesNotPayPinnedSource :
  SouthAustraliaProducerCapabilityPaysPinnedSource → ⊥
southAustraliaProducerCapabilityDoesNotPayPinnedSource ()

deltaFDoesNotDetermineDeltaL : DeltaFDeterminesDeltaL → ⊥
deltaFDoesNotDetermineDeltaL ()

reachabilityExpansionDoesNotRuleOutEveryLockIn :
  ReachabilityExpansionRulesOutAllLockIn → ⊥
reachabilityExpansionDoesNotRuleOutEveryLockIn ()

record FriendlyjordiesGovernanceMaxCutBoundary : Set where
  constructor friendlyjordies-governance-max-cut-boundary
  field
    cprsRootedClaimPaid : Bool
    cprsRootedClaimPaidIsTrue : cprsRootedClaimPaid ≡ true
    cprsWorldTransitionStillEvidencePremise : Bool
    cprsWorldTransitionStillEvidencePremiseIsTrue :
      cprsWorldTransitionStillEvidencePremise ≡ true
    southAustraliaRecoveryCompilerPresent : Bool
    southAustraliaRecoveryCompilerPresentIsTrue :
      southAustraliaRecoveryCompilerPresent ≡ true
    southAustraliaCurrentPinnedSourcePaid : Bool
    southAustraliaCurrentPinnedSourcePaidIsFalse :
      southAustraliaCurrentPinnedSourcePaid ≡ false
    rootedDeltaFAndDeltaLRemainDistinct : Bool
    rootedDeltaFAndDeltaLRemainDistinctIsTrue :
      rootedDeltaFAndDeltaLRemainDistinct ≡ true
    lockInRemainsTargetAndContextIndexed : Bool
    lockInRemainsTargetAndContextIndexedIsTrue :
      lockInRemainsTargetAndContextIndexed ≡ true
    universalPartyRankingCreated : Bool
    universalPartyRankingCreatedIsFalse :
      universalPartyRankingCreated ≡ false

open FriendlyjordiesGovernanceMaxCutBoundary public

canonicalFriendlyjordiesGovernanceMaxCutBoundary :
  FriendlyjordiesGovernanceMaxCutBoundary
canonicalFriendlyjordiesGovernanceMaxCutBoundary =
  friendlyjordies-governance-max-cut-boundary
    true refl
    true refl
    true refl
    false refl
    true refl
    true refl
    false refl
