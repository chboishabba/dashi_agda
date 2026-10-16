module DASHI.Cognition.PNF.SensibLawFriendlyjordiesCausalIdentificationMaxCutExact where

------------------------------------------------------------------------
-- FRIENDLYJORDIES CAUSAL-IDENTIFICATION MAX-CUT
--
-- The external-world owner pays narrow observed facts. This owner reuses the
-- repository causal-estimand and identification-family stack to make the next
-- promotion explicit:
--
--   observed institutional facts
--     != causal estimand
--     != identification design / admissibility receipt
--     != reviewed causal bridge
--     != governance trajectory / party ranking.
--
-- No canonical causal bridge is manufactured here. The point of the weld is
-- to replace an unstructured "reviewed causal premise" with proof-relevant
-- estimand + identification obligations before it may enter the existing
-- governance transition compiler.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.CausalEffectEstimandExact as Estimand
import DASHI.Biology.CausalIdentificationFamiliesExact as Identification
import DASHI.Environment.SustainableManagementCausalEstimandExperimentBridgeExact as Management
import DASHI.Core.FriendlyjordiesGovernanceQuestionExact as March
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesWorldEvidenceExact as World
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesSouthAustraliaGovernanceWeldExact as Governance

------------------------------------------------------------------------
-- Regression-facing status.
------------------------------------------------------------------------

cprsDirectFactsDoNotIdentifyEffect : Bool
cprsDirectFactsDoNotIdentifyEffect = true

southAustraliaOperationalFactsDoNotIdentifyGovernanceEffect : Bool
southAustraliaOperationalFactsDoNotIdentifyGovernanceEffect = true

identificationReceiptRequired : Bool
identificationReceiptRequired = true

sourcePaymentSeparateFromCausalIdentification : Bool
sourcePaymentSeparateFromCausalIdentification = true

identifiedLocalEffectCreatesUniversalPartyRanking : Bool
identifiedLocalEffectCreatesUniversalPartyRanking = false

------------------------------------------------------------------------
-- Case-indexed estimand demand.
--
-- The exact mathematical estimand is still supplied by the existing
-- CausalEffectEstimand owner. These references pin the political-history
-- question before an estimand can be admitted, preventing an effect estimate
-- for a different population/intervention/comparator/outcome/horizon from
-- silently paying this case.
------------------------------------------------------------------------

record GovernanceCausalEstimandDemand (case : March.MarchCase) : Set where
  constructor governance-causal-estimand-demand
  field
    observedBundle : World.ExternalWorldFactBundle case
    estimandKind : Estimand.CausalEstimandKind
    populationReference : String
    interventionReference : String
    comparatorReference : String
    outcomeReference : String
    horizonReference : String
    causalQuestionReference : String
    observedFactsIdentifyEffect : Bool
    observedFactsIdentifyEffectIsFalse : observedFactsIdentifyEffect ≡ false

open GovernanceCausalEstimandDemand public

cprsCausalEstimandDemand : GovernanceCausalEstimandDemand March.cprs2009
cprsCausalEstimandDemand =
  governance-causal-estimand-demand
    World.cprsExternalWorldBundle
    Estimand.trajectoryEffect
    "Australian federal climate-policy trajectory around the 2009 CPRS episode"
    "selected CPRS legislative/governance intervention history"
    "explicitly specified counterfactual policy/governance history"
    "subsequent climate-policy state / reachable-policy trajectory"
    "explicit finite historical horizon required by downstream study"
    "causal-question:cprs2009:trajectory"
    false refl

southAustraliaCausalEstimandDemand :
  GovernanceCausalEstimandDemand March.southAustraliaRenewables
southAustraliaCausalEstimandDemand =
  governance-causal-estimand-demand
    World.southAustraliaExternalWorldBundle
    Estimand.trajectoryEffect
    "South Australian electricity-system/governance trajectory"
    "explicitly specified policy/institutional intervention or governance history"
    "explicit comparator jurisdiction/history or counterfactual trajectory"
    "renewable integration, security, cost and reachable-system outcomes"
    "explicit finite system/governance horizon required by downstream study"
    "causal-question:south-australia-renewables:trajectory"
    false refl

------------------------------------------------------------------------
-- Identification-paid causal bridge.
--
-- An inhabitant must carry BOTH an explicit repository CausalEffectEstimand and
-- one admissible family-specific identification gate. The estimand's own scope
-- references must equal this case's demanded coordinates. Family choice remains
-- obligation-relative: this module does not decree randomisation,
-- observational adjustment, longitudinal analysis, or another family as the
-- universally correct historical design.
------------------------------------------------------------------------

record IdentifiedGovernanceCausalBridge
    (case : March.MarchCase)
    (demand : GovernanceCausalEstimandDemand case) : Set₂ where
  constructor identified-governance-causal-bridge
  field
    estimand : Estimand.CausalEffectEstimand

    estimandKindMatches :
      Estimand.kind estimand
      ≡ GovernanceCausalEstimandDemand.estimandKind demand
    populationMatches :
      Estimand.populationReference (Estimand.scope estimand)
      ≡ GovernanceCausalEstimandDemand.populationReference demand
    interventionMatches :
      Estimand.interventionReference (Estimand.scope estimand)
      ≡ GovernanceCausalEstimandDemand.interventionReference demand
    comparatorMatches :
      Estimand.comparatorReference (Estimand.scope estimand)
      ≡ GovernanceCausalEstimandDemand.comparatorReference demand
    outcomeMatches :
      Estimand.outcomeReference (Estimand.scope estimand)
      ≡ GovernanceCausalEstimandDemand.outcomeReference demand
    horizonMatches :
      Estimand.timeHorizonReference (Estimand.scope estimand)
      ≡ GovernanceCausalEstimandDemand.horizonReference demand

    identificationFamily : Identification.CausalIdentificationFamily
    identificationGate :
      Identification.IdentificationEvidenceGate identificationFamily

    reviewRef : String
    sourceRefs : List String

    CausalPremise : Set
    causalPremiseWitness : CausalPremise

    estimandAndIdentificationReviewedTogether : Bool
    estimandAndIdentificationReviewedTogetherIsTrue :
      estimandAndIdentificationReviewedTogether ≡ true

    directFactsAloneProvideIdentification : Bool
    directFactsAloneProvideIdentificationIsFalse :
      directFactsAloneProvideIdentification ≡ false

    createsUniversalPartyRanking : Bool
    createsUniversalPartyRankingIsFalse :
      createsUniversalPartyRanking ≡ false

open IdentifiedGovernanceCausalBridge public

------------------------------------------------------------------------
-- Only an identification-paid bridge may discharge the older generic reviewed
-- bridge slot. The older slot is retained for compatibility, but this is the
-- preferred compiler for the Friendlyjordies governance application.
------------------------------------------------------------------------

reviewedBridgeFromIdentification :
  ∀ {case}
    {demand : GovernanceCausalEstimandDemand case} →
  IdentifiedGovernanceCausalBridge case demand →
  World.ReviewedCausalBridge case
reviewedBridgeFromIdentification {case} bridge =
  World.reviewed-causal-bridge
    (sourceRefs bridge)
    (reviewRef bridge)
    (CausalPremise bridge)
    (causalPremiseWitness bridge)
    case
    refl
    false
    false

record IdentifiedTransitionAdmission
    (case : March.MarchCase)
    (demand : GovernanceCausalEstimandDemand case) : Set₂ where
  constructor identified-transition-admission
  field
    identifiedBridge : IdentifiedGovernanceCausalBridge case demand
    legacyAdmission :
      World.TransitionAdmission case (observedBundle demand)
    bridgeMatchesLegacySlot :
      World.TransitionAdmission.causalBridge legacyAdmission
      ≡ reviewedBridgeFromIdentification identifiedBridge

open IdentifiedTransitionAdmission public

cprsWorldTransitionEvidenceFromIdentifiedAdmission :
  IdentifiedTransitionAdmission March.cprs2009 cprsCausalEstimandDemand →
  Governance.WorldTransitionEvidence Governance.cprsSourcePaidCase
cprsWorldTransitionEvidenceFromIdentifiedAdmission admission =
  World.cprsWorldTransitionEvidenceFromAdmission
    (IdentifiedTransitionAdmission.legacyAdmission admission)

------------------------------------------------------------------------
-- South Australia remains doubly gated. Causal identification does not repair
-- the still-missing pinned Friendlyjordies M12 source unit; source provenance
-- and causal identification are orthogonal payments.
------------------------------------------------------------------------

record SouthAustraliaIdentifiedDualGate : Set₂ where
  constructor south-australia-identified-dual-gate
  field
    sourceRecovery : Governance.SouthAustraliaTransitionPrerequisite
    causalAdmission :
      IdentifiedTransitionAdmission
        March.southAustraliaRenewables
        southAustraliaCausalEstimandDemand

southAustraliaIdentifiedDualGateCurrentlyBlocked :
  SouthAustraliaIdentifiedDualGate → ⊥
southAustraliaIdentifiedDualGateCurrentlyBlocked gate =
  Governance.southAustraliaTransitionPrerequisiteCurrentlyImpossible
    (SouthAustraliaIdentifiedDualGate.sourceRecovery gate)

------------------------------------------------------------------------
-- Productive cross-pollination receipts from existing generic owners.
------------------------------------------------------------------------

existingObservedDifferenceDoesNotIdentifyCause :
  Management.ObservedDifferenceMeansCausalEffectPermission → ⊥
existingObservedDifferenceDoesNotIdentifyCause =
  Management.observedDifferenceDoesNotIdentifyCause

existingLongitudinalOrderDoesNotIdentifyCause :
  Identification.LongitudinalMeansCausationPermission → ⊥
existingLongitudinalOrderDoesNotIdentifyCause =
  Identification.longitudinalOrderDoesNotByItselfIdentifyCause

existingIdentificationFamilyDoesNotProveEffect :
  Identification.IdentificationFamilyAutomaticallyProvesCausalEffectPermission → ⊥
existingIdentificationFamilyDoesNotProveEffect =
  Identification.identificationFamilyDoesNotAutomaticallyProveCausalEffect

existingIdentificationDoesNotDetermineEstimand :
  Estimand.IdentificationMeansEstimandKnownPermission → ⊥
existingIdentificationDoesNotDetermineEstimand =
  Estimand.identificationDoesNotDetermineEstimand

------------------------------------------------------------------------
-- Hard application-level firewalls.
------------------------------------------------------------------------

data CPRSObservedVoteMeansCausalEffect : Set where
data SAHighRenewableEpisodeMeansGovernanceEffect : Set where
data SourceTraceMeansCausalIdentification : Set where
data LocalIdentifiedEffectMeansUniversalPartyRanking : Set where
data IdentificationRepairsMissingSourceTrace : Set where

cprsObservedVoteDoesNotIdentifyCausalEffect :
  CPRSObservedVoteMeansCausalEffect → ⊥
cprsObservedVoteDoesNotIdentifyCausalEffect ()

southAustraliaEpisodeDoesNotIdentifyGovernanceEffect :
  SAHighRenewableEpisodeMeansGovernanceEffect → ⊥
southAustraliaEpisodeDoesNotIdentifyGovernanceEffect ()

sourceTraceDoesNotIdentifyCause : SourceTraceMeansCausalIdentification → ⊥
sourceTraceDoesNotIdentifyCause ()

localEffectDoesNotCreateUniversalPartyRanking :
  LocalIdentifiedEffectMeansUniversalPartyRanking → ⊥
localEffectDoesNotCreateUniversalPartyRanking ()

identificationDoesNotRepairMissingSourceTrace :
  IdentificationRepairsMissingSourceTrace → ⊥
identificationDoesNotRepairMissingSourceTrace ()

record FriendlyjordiesCausalIdentificationBoundary : Set where
  constructor friendlyjordies-causal-identification-boundary
  field
    cprsObservedSubstratePaid : Bool
    cprsObservedSubstratePaidIsTrue : cprsObservedSubstratePaid ≡ true
    southAustraliaObservedSubstratePaid : Bool
    southAustraliaObservedSubstratePaidIsTrue :
      southAustraliaObservedSubstratePaid ≡ true
    explicitEstimandRequired : Bool
    explicitEstimandRequiredIsTrue : explicitEstimandRequired ≡ true
    admissibleIdentificationGateRequired : Bool
    admissibleIdentificationGateRequiredIsTrue :
      admissibleIdentificationGateRequired ≡ true
    sourceAndIdentificationOrthogonal : Bool
    sourceAndIdentificationOrthogonalIsTrue :
      sourceAndIdentificationOrthogonal ≡ true
    southAustraliaPinnedNarrativeSourceStillOpen : Bool
    southAustraliaPinnedNarrativeSourceStillOpenIsTrue :
      southAustraliaPinnedNarrativeSourceStillOpen ≡ true
    universalPartyRankingCreated : Bool
    universalPartyRankingCreatedIsFalse : universalPartyRankingCreated ≡ false

open FriendlyjordiesCausalIdentificationBoundary public

canonicalFriendlyjordiesCausalIdentificationBoundary :
  FriendlyjordiesCausalIdentificationBoundary
canonicalFriendlyjordiesCausalIdentificationBoundary =
  friendlyjordies-causal-identification-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
