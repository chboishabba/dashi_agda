module DASHI.Governance.ITIRPluralViabilityTSFVExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Core.HistoryConditionedChoiceExact as History
import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Governance.FederatedSubsidiarityGovernanceExact as Base
import DASHI.Governance.FederatedViabilityTransitionExact as Viability
import DASHI.Governance.CyberneticClinicalInstitutionalRepairBridge as Cyber
import DASHI.Physics.Closure.TSFVHistoryConditionedChoiceBridgeExact as TSFV
import DASHI.Physics.Closure.SU2SO3369HypervoxelBridge as Hyper

------------------------------------------------------------------------
-- PLURAL VIABILITY OVER THE EXISTING FEDERATED TRANSITION SPINE
--
-- The existing viability envelope already keeps governance, ecology, resources
-- and basic-needs access distinct. This owner adds only the governance
-- coordinates needed by the present thread: non-domination, affected-party
-- voice and institutional revisability.
------------------------------------------------------------------------

record PluralViabilityEnvelope (State : Set) : Set₁ where
  field
    baseEnvelope : Base.ViabilityEnvelope State
    nonDominationViable : State → Set
    affectedVoiceViable : State → Set
    revisabilityViable : State → Set

open PluralViabilityEnvelope public

PluralViable :
  ∀ {State : Set} →
  PluralViabilityEnvelope State →
  State →
  Set
PluralViable envelope state =
  Base.Viable (baseEnvelope envelope) state
  × nonDominationViable envelope state
  × affectedVoiceViable envelope state
  × revisabilityViable envelope state

record PluralViabilityPreservingTransition
  {State : Set}
  (transitionSystem : Base.TransitionSystem State)
  (envelope : PluralViabilityEnvelope State) : Set₁ where
  field
    preservesPluralStep :
      ∀ {kind source target} →
      Base.step transitionSystem kind source target →
      PluralViable envelope source →
      PluralViable envelope target

open PluralViabilityPreservingTransition public

reachablePreservesPluralViability :
  ∀ {State : Set}
    {transitionSystem : Base.TransitionSystem State}
    {envelope : PluralViabilityEnvelope State} →
  (preservation : PluralViabilityPreservingTransition transitionSystem envelope) →
  ∀ {source target} →
  Base.Reachable transitionSystem source target →
  PluralViable envelope source →
  PluralViable envelope target
reachablePreservesPluralViability preservation Base.reachableRefl viable = viable
reachablePreservesPluralViability preservation (Base.reachableByStep stepWitness) viable =
  preservesPluralStep preservation stepWitness viable
reachablePreservesPluralViability preservation
  (Base.reachableTrans sourceToMiddle middleToTarget) viable =
  reachablePreservesPluralViability preservation middleToTarget
    (reachablePreservesPluralViability preservation sourceToMiddle viable)

------------------------------------------------------------------------
-- HISTORY-CONDITIONED FUTURE-CONE SPECIMEN
--
-- Two institutional histories can have the same coarse present label while
-- retaining different continuation spaces for a non-domination/revisability
-- consumer. This is a consumer-relative future-sufficiency result, not a
-- prediction and not a signal propagating backwards from the future.
------------------------------------------------------------------------

data GovernanceHistory : Set where
  revisableHistory : GovernanceHistory
  capturedHistory : GovernanceHistory

data PresentObservation : Set where
  samePresentInstitution : PresentObservation

data PluralFutureCone : Set where
  revisablePluralCone : PluralFutureCone
  dominationLockedCone : PluralFutureCone

pluralFutureConeSurface : History.HistoryConditionedFutureConeSurface
pluralFutureConeSurface = record
  { FutureHistory = GovernanceHistory
  ; FutureObservation = PresentObservation
  ; FutureConeCode = PluralFutureCone
  ; observeFutureHistory = λ _ → samePresentInstitution
  ; futureCone = λ
      { revisableHistory → revisablePluralCone
      ; capturedHistory → dominationLockedCone
      }
  ; futureReading =
      "The same coarse present institution can hide different continuation spaces once non-domination, affected voice and revisability remain consumer-relevant."
  }

pluralFutureConeWitness :
  History.SameObservationDifferentFutureCone pluralFutureConeSurface
pluralFutureConeWitness = record
  { futureLeftHistory = revisableHistory
  ; futureRightHistory = capturedHistory
  ; futureSameObservation = refl
  ; futureConesDiffer = λ ()
  }

coarsePresentCannotDeterminePluralFutureCone :
  NonFactor.FactorsThrough
    (History.observeFutureHistory pluralFutureConeSurface)
    (History.futureCone pluralFutureConeSurface) → ⊥
coarsePresentCannotDeterminePluralFutureCone =
  History.futureConeCannotDescendThroughPresentObservation pluralFutureConeWitness

------------------------------------------------------------------------
-- Cross-pollination anchors.
------------------------------------------------------------------------

-- Cybersyn precedent: the highest identity/reference layer is people-steered,
-- while the source owner explicitly keeps this candidate-only.
cybersynAnchor : Cyber.GovernanceGateRow
cybersynAnchor = Cyber.cybersynSystemFiveRow

cybersynFeedbackSubjectRestored :
  Cyber.feedbackSubjectRestored cybersynAnchor ≡ true
cybersynFeedbackSubjectRestored = refl

-- TSFV precedent is used only for the theorem shape that fine histories can
-- matter to a later consumer despite a common coarse observation. The physics
-- owner itself explicitly says this does not validate a TSFV mechanism.
tsfvBoundaryAnchor : TSFV.TSFVHistoryConditionedChoiceBoundary
tsfvBoundaryAnchor = TSFV.canonicalTSFVHistoryConditionedChoiceBoundary

tsfvMechanismNotImported :
  TSFV.historyChoiceBridgeValidatesTSFVMechanism tsfvBoundaryAnchor ≡ false
tsfvMechanismNotImported = refl

-- 3/6/9/18/27 is a representation-size / carrier precedent only. The counts
-- are imported exactly; no political ontology, authority or normative weight
-- is inferred from them.
axisCountAnchor : Hyper.axisCarrierCount ≡ 3
axisCountAnchor = refl

sheetCountAnchor : Hyper.operatorSheetCount ≡ 9
sheetCountAnchor = Hyper.operatorSheetCountIs9

liftedSheetCountAnchor : Hyper.liftedOperatorSheetCount ≡ 18
liftedSheetCountAnchor = Hyper.liftedOperatorSheetCountIs18

voxelCountAnchor : Hyper.bracketVoxelCount ≡ 27
voxelCountAnchor = Hyper.bracketVoxelCountIs27

------------------------------------------------------------------------
-- Terminal boundary.
------------------------------------------------------------------------

record PluralViabilityBoundary : Set where
  constructor plural-viability-boundary
  field
    futureViabilityIsPrediction : Bool
    futureViabilityIsRetrocausalSignal : Bool
    coarsePresentDeterminesPluralFuture : Bool
    viabilityEnvelopeCreatesUniquePoliticalTelos : Bool
    oneScalarObjectiveExhaustsPluralViability : Bool
    governanceViabilityImpliesEcologicalViability : Bool
    affectedVoiceMayBeDroppedAfterDelegation : Bool
    revisabilityMayBeDroppedAfterSuccess : Bool

    cybersynPeopleSteerIdentityLayerRetained : Bool
    tsfvUsedAsConsumerRelativeHistoryPrecedentOnly : Bool
    triadicRepresentationCreatesPoliticalAuthority : Bool
    cardinalityMatchCreatesGovernanceMechanism : Bool

open PluralViabilityBoundary public

canonicalPluralViabilityBoundary : PluralViabilityBoundary
canonicalPluralViabilityBoundary =
  plural-viability-boundary
    false false false false false false false false
    true true false false

canonicalITIRPluralViabilityReceipt : GenericReceipt.GenericReceipt
canonicalITIRPluralViabilityReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "ITIR plural viability / TSFV history-conditioned governance bridge"
    "DASHI.Governance.ITIRPluralViabilityTSFVExact"
    "canonicalPluralViabilityBoundary"
    "extends the existing independent governance/ecology/resource/basic-needs viability envelope with non-domination, affected-party voice and revisability; proves preservation along explicitly witnessed transitions and gives a same-present/different-future-cone non-factorability specimen"
    "future viability is neither prediction nor retrocausal signalling; no unique political telos or scalar objective is manufactured; Cybersyn, TSFV and 3/9/18/27 are structural precedents only and do not transfer empirical or political authority"
    "agda -i . DASHI/Governance/AnarchistLeadershipNonDominationTSFVRegression.agda"
