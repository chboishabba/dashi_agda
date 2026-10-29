module DASHI.Biology.EmbodiedSocialEcologyRelationalHistoryObligationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Core.RelationalHistoryFabricExact as Fabric
import DASHI.Biology.EmbodiedCausalConeFeedbackExact as Causal
import DASHI.Biology.ObserverRelativeReachableSubfabricExact as Reach
import DASHI.Biology.NeurotypeProcessingGeometryExact as Processing
import DASHI.Biology.ProcessingGeometryActionGateExact as ProcessingGate
import DASHI.Biology.SocialEcologicalAffordanceConeExact as Ecology
import DASHI.Biology.TrustedFriendEcologyInteractionExact as FriendInteraction
import DASHI.Governance.OptionConeCoercionExact as Cone
import DASHI.Governance.HistoryConditionedSocialEcologyOptionConeExact as HistoryCone
import DASHI.Governance.HistoryObserverAuthorityOptionConeCapstoneExact as GovernanceCapstone

------------------------------------------------------------------------
-- EMBODIED SOCIAL-ECOLOGY RELATIONAL-HISTORY ADAPTER
--
-- This file used to record a cross-draft obligation between PR #606 and the
-- neurodivergent social-ecology work.  PR #606 is now merged.  The required
-- owners are on the same Agda tree, so this file now discharges that obligation.
--
-- Golden owner chain:
--
--   retained history
--     -> history-conditioned transition gate
--     -> observer/body-relative reachable subfabric
--     -> social-ecological relation gate
--     -> realised affordance
--     -> future option-cone code.
--
-- Processing geometry is present as an independent action-gate input.  The
-- concrete witness keeps it fixed so history and relation effects cannot be
-- misread as changes in diagnosis or scalar processing speed.
------------------------------------------------------------------------

_∧ᵇ_ : Bool → Bool → Bool
true ∧ᵇ value = value
false ∧ᵇ value = false

data SituatedCase : Set where
  ordinaryAlone : SituatedCase
  ordinaryFriend : SituatedCase
  threatAlone : SituatedCase
  threatFriend : SituatedCase

processingOf : SituatedCase → Processing.ProcessingGeometry
processingOf _ = Processing.deepRuleGeometry

observeLatency : SituatedCase → Processing.ResponseLatency
observeLatency state = Processing.latencyObserver (processingOf state)

historyOf : SituatedCase → Causal.HistoryState
historyOf ordinaryAlone = Causal.ordinaryHistory
historyOf ordinaryFriend = Causal.ordinaryHistory
historyOf threatAlone = Causal.learnedThreatHistory
historyOf threatFriend = Causal.learnedThreatHistory

relationOf : SituatedCase → FriendInteraction.RelationCondition
relationOf ordinaryAlone = FriendInteraction.aloneCondition
relationOf ordinaryFriend = FriendInteraction.trustedFriendCondition
relationOf threatAlone = FriendInteraction.aloneCondition
relationOf threatFriend = FriendInteraction.trustedFriendCondition

lawOf : SituatedCase → Causal.TransitionLaw
lawOf ordinaryAlone = Causal.baselineLaw
lawOf ordinaryFriend = Causal.baselineLaw
lawOf threatAlone = Causal.learnedThreatLaw
lawOf threatFriend = Causal.learnedThreatLaw

bodyContextOf : SituatedCase → Reach.BodyContext
bodyContextOf ordinaryAlone = Reach.regulatedContext
bodyContextOf ordinaryFriend = Reach.regulatedContext
bodyContextOf threatAlone = Reach.mobilisedContext
bodyContextOf threatFriend = Reach.mobilisedContext

historyGate : SituatedCase → Bool
historyGate state =
  Causal.gate (lawOf state) Causal.approachSafety

processingGate : SituatedCase → Bool
processingGate state =
  ProcessingGate.processingActionAvailable
    (processingOf state)
    Processing.quietContext
    ProcessingGate.sustainedRuleAnalysis

combinedGate : SituatedCase → Bool
combinedGate state = historyGate state ∧ᵇ processingGate state

reachablePlanning : SituatedCase → Bool
reachablePlanning state =
  Reach.live
    Reach.accessibleLayer
    (bodyContextOf state)
    Reach.flexiblePlanning

relationRemain : SituatedCase → Bool
relationRemain state =
  Ecology.available
    Ecology.canonicalAutisticPerson
    (FriendInteraction.ecologyFor
      FriendInteraction.highDemandCondition
      (relationOf state))
    Ecology.remainAction

realisedAffordance : SituatedCase → Bool
realisedAffordance state =
  reachablePlanning state ∧ᵇ relationRemain state

futureConeCode : SituatedCase → Bool
futureConeCode state =
  combinedGate state ∧ᵇ realisedAffordance state

------------------------------------------------------------------------
-- Domain instantiation of the existing generic relational-history fabric.
------------------------------------------------------------------------

situatedReachabilityFabric : Fabric.RelationalHistoryFabric
situatedReachabilityFabric =
  record
    { SituatedState = SituatedCase
    ; Observation = Processing.ResponseLatency
    ; HistoryCode = Causal.HistoryState
    ; RelationCode = FriendInteraction.RelationCondition
    ; GateCode = Bool
    ; ReachableCode = Bool
    ; AffordanceCode = Bool
    ; FutureConeCode = Bool
    ; observe = observeLatency
    ; historyOf = historyOf
    ; relationOf = relationOf
    ; gateOf = combinedGate
    ; reachableOf = reachablePlanning
    ; affordanceOf = realisedAffordance
    ; futureConeOf = futureConeCode
    ; fabricReading =
        "At fixed processing geometry and latency, retained history and trusted relation can independently change gates, reachable structure, realised affordance, and the future option-cone code."
    }

------------------------------------------------------------------------
-- History propagation.
--
-- Relation is held fixed as trusted-friend.  Processing geometry is fixed.
-- Only retained history/body context changes.
------------------------------------------------------------------------

historyWitnessSameProcessing :
  processingOf ordinaryFriend ≡ processingOf threatFriend
historyWitnessSameProcessing = refl

historyWitnessSameLatency :
  observeLatency ordinaryFriend ≡ observeLatency threatFriend
historyWitnessSameLatency = refl

historyWitnessRelationHeldFixed :
  relationOf ordinaryFriend ≡ relationOf threatFriend
historyWitnessRelationHeldFixed = refl

historyWitnessHistoryDiffers :
  historyOf ordinaryFriend ≡ historyOf threatFriend → ⊥
historyWitnessHistoryDiffers ()

historyWitnessGateDiffers :
  combinedGate ordinaryFriend ≡ combinedGate threatFriend → ⊥
historyWitnessGateDiffers ()

historyWitnessReachableDiffers :
  reachablePlanning ordinaryFriend ≡ reachablePlanning threatFriend → ⊥
historyWitnessReachableDiffers ()

historyWitnessAffordanceDiffers :
  realisedAffordance ordinaryFriend ≡ realisedAffordance threatFriend → ⊥
historyWitnessAffordanceDiffers ()

historyWitnessFutureDiffers :
  futureConeCode ordinaryFriend ≡ futureConeCode threatFriend → ⊥
historyWitnessFutureDiffers ()

canonicalHistoryPropagationWitness :
  Fabric.HistoryPropagationWitness situatedReachabilityFabric
canonicalHistoryPropagationWitness =
  record
    { propagationLeft = ordinaryFriend
    ; propagationRight = threatFriend
    ; propagationSameObservation = historyWitnessSameLatency
    ; propagationHistoryDiffers = historyWitnessHistoryDiffers
    ; propagationGateDiffers = historyWitnessGateDiffers
    ; propagationReachableDiffers = historyWitnessReachableDiffers
    ; propagationAffordanceDiffers = historyWitnessAffordanceDiffers
    ; propagationFutureDiffers = historyWitnessFutureDiffers
    }

canonicalHistoryEssentialWitness :
  Fabric.HistoryEssentialForFuture situatedReachabilityFabric
canonicalHistoryEssentialWitness =
  record
    { historyLeft = ordinaryFriend
    ; historyRight = threatFriend
    ; historySameObservation = historyWitnessSameLatency
    ; historyRelationHeldFixed = historyWitnessRelationHeldFixed
    ; historyActuallyDiffers = historyWitnessHistoryDiffers
    ; historyFutureDiffers = historyWitnessFutureDiffers
    }

------------------------------------------------------------------------
-- Relation essentiality.
--
-- History, processing geometry, latency and high-demand ecology are fixed.
-- Only the ordinary trusted-friend relation changes.
------------------------------------------------------------------------

relationWitnessSameProcessing :
  processingOf ordinaryAlone ≡ processingOf ordinaryFriend
relationWitnessSameProcessing = refl

relationWitnessSameLatency :
  observeLatency ordinaryAlone ≡ observeLatency ordinaryFriend
relationWitnessSameLatency = refl

relationWitnessHistoryHeldFixed :
  historyOf ordinaryAlone ≡ historyOf ordinaryFriend
relationWitnessHistoryHeldFixed = refl

relationWitnessRelationDiffers :
  relationOf ordinaryAlone ≡ relationOf ordinaryFriend → ⊥
relationWitnessRelationDiffers ()

relationWitnessFutureDiffers :
  futureConeCode ordinaryAlone ≡ futureConeCode ordinaryFriend → ⊥
relationWitnessFutureDiffers ()

canonicalRelationEssentialWitness :
  Fabric.RelationEssentialForFuture situatedReachabilityFabric
canonicalRelationEssentialWitness =
  record
    { relationLeft = ordinaryAlone
    ; relationRight = ordinaryFriend
    ; relationSameObservation = relationWitnessSameLatency
    ; relationHistoryHeldFixed = relationWitnessHistoryHeldFixed
    ; relationActuallyDiffers = relationWitnessRelationDiffers
    ; relationFutureDiffers = relationWitnessFutureDiffers
    }

------------------------------------------------------------------------
-- Coarse latency cannot reconstruct the future option cone.
------------------------------------------------------------------------

latencyCannotDetermineFutureCone :
  NonFactor.FactorsThrough
    (Fabric.observe situatedReachabilityFabric)
    (Fabric.futureConeOf situatedReachabilityFabric) →
  ⊥
latencyCannotDetermineFutureCone =
  Fabric.historyPropagationBlocksCoarseFutureDescent
    canonicalHistoryPropagationWitness

postprocessedLatencyCannotRecoverFutureCone :
  ∀ {Chart : Set} →
  (rechart : Processing.ResponseLatency → Chart) →
  NonFactor.FactorsThrough
    (λ state → rechart (observeLatency state))
    futureConeCode →
  ⊥
postprocessedLatencyCannotRecoverFutureCone rechart =
  NonFactor.rechartingCannotRecoverErasedPhenomenon
    rechart
    (Fabric.futureConeNonFactorability
      (record
        { leftState = ordinaryFriend
        ; rightState = threatFriend
        ; sameObservation = historyWitnessSameLatency
        ; differentFutureCone = historyWitnessFutureDiffers
        }))

------------------------------------------------------------------------
-- Reuse the generic friend x ecology nonseparability result.
------------------------------------------------------------------------

friendEcologyInteractionIsNonadditive :
  FriendInteraction.FriendEcologyEndpointAdditiveModel → ⊥
friendEcologyInteractionIsNonadditive =
  FriendInteraction.friendEcologyNotEndpointAdditive


------------------------------------------------------------------------
-- Reuse the existing proof-bearing social-ecology option-cone owner.
--
-- These generic contractions are not identified with the domain-specific
-- Boolean witness above.  They provide the canonical proof-bearing option-cone
-- interface for the same history/ecology theorem shape.
------------------------------------------------------------------------

genericHistoryOptionConeContraction :
  Cone.StrictSafeReachabilityContraction
    HistoryCone.socialReachability
    HistoryCone.regulatedSupportive
    HistoryCone.mobilisedSupportive
genericHistoryOptionConeContraction =
  HistoryCone.historyConditionedContraction

genericEcologyOptionConeContraction :
  Cone.StrictSafeReachabilityContraction
    HistoryCone.socialReachability
    HistoryCone.regulatedSupportive
    HistoryCone.regulatedHostile
genericEcologyOptionConeContraction =
  HistoryCone.ecologyConditionedContraction

genericJointOptionConeContraction :
  Cone.StrictSafeReachabilityContraction
    HistoryCone.socialReachability
    HistoryCone.regulatedSupportive
    HistoryCone.mobilisedHostile
genericJointOptionConeContraction =
  HistoryCone.jointHistoryEcologyContraction


genericObserverAffordanceAuthorityBoundary :
  GovernanceCapstone.HistoryObserverAuthorityCapstoneBoundary
genericObserverAffordanceAuthorityBoundary =
  GovernanceCapstone.canonicalHistoryObserverAuthorityCapstoneBoundary

------------------------------------------------------------------------
-- ZKP O/R/C/S/L/P/G/F audit frame.
--
-- These strings are audit coordinates.  The exact witnesses above remain the
-- proof authority.
------------------------------------------------------------------------

record SituatedReachabilityZKPFrame : Set where
  constructor situated-reachability-zkp-frame
  field
    O : String
    R : String
    C : String
    S : String
    L : String
    P : String
    G : String
    F : String
    preconditions : String
    invariants : String
    postconditions : String

canonicalSituatedReachabilityZKPFrame : SituatedReachabilityZKPFrame
canonicalSituatedReachabilityZKPFrame =
  situated-reachability-zkp-frame
    "DASHI neurodivergent social-ecology / embodied-hyperfabric lane"
    "Compose merged history, processing, relation, ecology and reachability owners without new ontology."
    "EmbodiedSocialEcologyRelationalHistoryObligationExact plus existing canonical owners"
    "One situated finite witness with processing held fixed and history/relation varied independently."
    "RelationalHistoryFabricExact observer/factorisation lattice."
    "Reuse merged owners; discharge the old adapter obligation; attach the receipt to TOE roots."
    "Prove that coarse latency cannot determine the guarded future option cone."
    "Remaining gap is empirical calibration of domain-specific transition/affordance functions, not the composition theorem."
    "All imported owners exist on one Agda ancestry; no ESD edits; no trust escapes."
    "Diagnosis, processing, history, relation, ecology, accessibility, actionability and authority remain distinct."
    "History propagation and relation essentiality are witnessed; latency-only future decoding is impossible in the finite specimen."

------------------------------------------------------------------------
-- TOE receipt and claim boundary.
------------------------------------------------------------------------

record SituatedReachabilityTOEReceipt : Set where
  constructor situated-reachability-toe-receipt
  field
    relationalHistoryOwnerReused : Bool
    relationalHistoryOwnerReusedIsTrue :
      relationalHistoryOwnerReused ≡ true
    embodiedHistoryGateOwnerReused : Bool
    embodiedHistoryGateOwnerReusedIsTrue :
      embodiedHistoryGateOwnerReused ≡ true
    reachableSubfabricOwnerReused : Bool
    reachableSubfabricOwnerReusedIsTrue :
      reachableSubfabricOwnerReused ≡ true
    processingActionGateOwnerReused : Bool
    processingActionGateOwnerReusedIsTrue :
      processingActionGateOwnerReused ≡ true
    trustedFriendEcologyInteractionReused : Bool
    trustedFriendEcologyInteractionReusedIsTrue :
      trustedFriendEcologyInteractionReused ≡ true
    proofBearingHistoryEcologyOptionConeReused : Bool
    proofBearingHistoryEcologyOptionConeReusedIsTrue :
      proofBearingHistoryEcologyOptionConeReused ≡ true
    observerAffordanceAuthorityCapstoneReused : Bool
    observerAffordanceAuthorityCapstoneReusedIsTrue :
      observerAffordanceAuthorityCapstoneReused ≡ true
    historyPropagationWitnessInstalled : Bool
    historyPropagationWitnessInstalledIsTrue :
      historyPropagationWitnessInstalled ≡ true
    relationEssentialWitnessInstalled : Bool
    relationEssentialWitnessInstalledIsTrue :
      relationEssentialWitnessInstalled ≡ true
    latencyOnlyFutureDecoderExists : Bool
    latencyOnlyFutureDecoderExistsIsFalse :
      latencyOnlyFutureDecoderExists ≡ false
    universalAutismMechanismPromoted : Bool
    universalAutismMechanismPromotedIsFalse :
      universalAutismMechanismPromoted ≡ false
    empiricalTransitionCalibrationInstalled : Bool
    empiricalTransitionCalibrationInstalledIsFalse :
      empiricalTransitionCalibrationInstalled ≡ false

canonicalSituatedReachabilityTOEReceipt : SituatedReachabilityTOEReceipt
canonicalSituatedReachabilityTOEReceipt =
  situated-reachability-toe-receipt
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl

record EmbodiedSocialEcologyCompositionBoundary : Set where
  constructor embodiedSocialEcologyCompositionBoundary
  field
    genericRelationalHistoryFabricConstructed : Bool
    genericRelationalHistoryFabricConstructedIsTrue :
      genericRelationalHistoryFabricConstructed ≡ true
    mergedEmbodiedGateAdapterInstalled : Bool
    mergedEmbodiedGateAdapterInstalledIsTrue :
      mergedEmbodiedGateAdapterInstalled ≡ true
    socialEcologyAdapterInstalled : Bool
    socialEcologyAdapterInstalledIsTrue :
      socialEcologyAdapterInstalled ≡ true
    copiedOwnersToSimulateIntegration : Bool
    copiedOwnersToSimulateIntegrationIsFalse :
      copiedOwnersToSimulateIntegration ≡ false
    compositionProvesUniversalAutismMechanism : Bool
    compositionProvesUniversalAutismMechanismIsFalse :
      compositionProvesUniversalAutismMechanism ≡ false

canonicalEmbodiedSocialEcologyCompositionBoundary :
  EmbodiedSocialEcologyCompositionBoundary
canonicalEmbodiedSocialEcologyCompositionBoundary =
  embodiedSocialEcologyCompositionBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
