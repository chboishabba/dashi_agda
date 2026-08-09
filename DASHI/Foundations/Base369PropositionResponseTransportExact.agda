module DASHI.Foundations.Base369PropositionResponseTransportExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- A visible yes is not a free-standing Boolean.  An actual response is indexed
-- by the exact guarded proposition node, decision episode and time.  Response
-- transport across descendants, contexts, modalities, scopes and times
-- requires independent witnesses.  Affirming that an option might be
-- considered preserves branch liveness without promising weighing, selection,
-- execution or obligation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.SSPTritCarrier using (SSPTrit; sspPosOne)
open import DASHI.Foundations.Base369SignedMembershipExact using (ZeroKind)

data DeliberativeStatus : Set where
  excluded live mightConsider willConsider : DeliberativeStatus

data SelectionStatus : Set where
  unselected preferred intended selected : SelectionStatus

data ObligationStatus : Set where
  noObligation selfPlan commitmentToAnother : ObligationStatus

record FactoredModality : Set where
  constructor factoredModality
  field
    deliberative : DeliberativeStatus
    selection : SelectionStatus
    obligation : ObligationStatus

open FactoredModality public

record PropositionNode : Set₁ where
  constructor propositionNode
  field
    Context Action Scope Exception UnresolvedCondition : Set
    contextWitness : Context
    contemplatedAction : Action
    modality : FactoredModality
    scopeWitness : Scope

open PropositionNode public

record DecisionEpisode : Set₁ where
  constructor decisionEpisode
  field
    ContextCarrier Alternative Version : Set
    decisionContext : ContextCarrier
    availableAlternative : Alternative → Set
    propositionVersion : Version
    openedAt closesAt : Nat

open DecisionEpisode public

data CapacityState : Set where
  noCapacity uncertainCapacity sufficientCapacity : CapacityState

data ProvenanceKind : Set where
  participantProduced observerAttributed recordingWitnessed reconstructed : ProvenanceKind

record ResponseState : Set where
  constructor responseState
  field
    stance : SSPTrit
    refinedZero : ZeroKind
    capacity : CapacityState
    provenance : ProvenanceKind

open ResponseState public

record ActualResponse
  (Participant : Set)
  (node : PropositionNode)
  (episode : DecisionEpisode)
  (time : Nat) : Set₁ where
  constructor actualResponse
  field
    participant : Participant
    response : ResponseState
    exactNodePresented : Set
    exactNodeUnderstood : Set

open ActualResponse public

record PositiveResponse
  {Participant : Set}
  {node : PropositionNode}
  {episode : DecisionEpisode}
  {time : Nat}
  (r : ActualResponse Participant node episode time) : Set₁ where
  constructor positiveResponse
  field stanceIsPositive : stance (response r) ≡ sspPosOne

open PositiveResponse public

considerModality : FactoredModality
considerModality = factoredModality mightConsider unselected noObligation

commitModality : FactoredModality
commitModality = factoredModality willConsider selected commitmentToAnother

------------------------------------------------------------------------
-- Might-consider means possible uptake, not guaranteed uptake.
------------------------------------------------------------------------

record MightConsiderSemantics : Set₁ where
  constructor mightConsiderSemantics
  field
    History Option : Set
    option : Option
    Weighed : History → Option → Set
    liveHistory : History
    possibleWeighing : Weighed liveHistory option

open MightConsiderSemantics public

record WillConsiderSemantics (might : MightConsiderSemantics) : Set₁ where
  constructor willConsiderSemantics
  field
    everyHistoryWeighs :
      (history : History might) → Weighed might history (option might)

open WillConsiderSemantics public

------------------------------------------------------------------------
-- Independent transport witnesses.
------------------------------------------------------------------------

record NodeTransportable (source target : PropositionNode) : Set₁ where
  constructor nodeTransportable
  field nodeTransportWitness : Set

record ContextTransportable (source target : PropositionNode) : Set₁ where
  constructor contextTransportable
  field contextTransportWitness : Set

record ModalityTransportable (source target : PropositionNode) : Set₁ where
  constructor modalityTransportable
  field modalityTransportWitness : Set

record ScopeTransportable (source target : PropositionNode) : Set₁ where
  constructor scopeTransportable
  field scopeTransportWitness : Set

record TemporalTransportable
  (sourceEpisode targetEpisode : DecisionEpisode)
  (sourceTime targetTime : Nat) : Set₁ where
  constructor temporalTransportable
  field temporalTransportWitness : Set

record ResponseTransportWitness
  (source target : PropositionNode)
  (sourceEpisode targetEpisode : DecisionEpisode)
  (sourceTime targetTime : Nat) : Set₁ where
  constructor responseTransportWitness
  field
    descendantWitness : NodeTransportable source target
    contextWitnessTransport : ContextTransportable source target
    modalityWitness : ModalityTransportable source target
    scopeWitnessTransport : ScopeTransportable source target
    temporalWitness :
      TemporalTransportable sourceEpisode targetEpisode sourceTime targetTime

open ResponseTransportWitness public

transportActualResponse :
  ∀ {Participant source target sourceEpisode targetEpisode sourceTime targetTime} →
  ResponseTransportWitness
    source target sourceEpisode targetEpisode sourceTime targetTime →
  ActualResponse Participant source sourceEpisode sourceTime →
  ActualResponse Participant target targetEpisode targetTime
transportActualResponse witness sourceResponse =
  actualResponse
    (participant sourceResponse)
    (response sourceResponse)
    (exactNodePresented sourceResponse)
    (exactNodeUnderstood sourceResponse)

------------------------------------------------------------------------
-- Consent adds refusal alternatives, capacity and participant provenance.
------------------------------------------------------------------------

record CounterfactualChoiceCone : Set₁ where
  constructor counterfactualChoiceCone
  field
    World : Set
    acceptWorld refuseWorld deferWorld : World
    refusalReachable : Set
    deferralReachable : Set

open CounterfactualChoiceCone public

record ValidConsent
  {Participant : Set}
  {node : PropositionNode}
  {episode : DecisionEpisode}
  {time : Nat}
  (r : ActualResponse Participant node episode time) : Set₁ where
  constructor validConsent
  field
    positive : PositiveResponse r
    refusalCone : CounterfactualChoiceCone
    capacitySufficient : capacity (response r) ≡ sufficientCapacity
    participantProvenance : provenance (response r) ≡ participantProduced

open ValidConsent public

record ReinstantiatedBranch
  (oldEpisode newEpisode : DecisionEpisode) : Set₁ where
  constructor reinstantiatedBranch
  field
    Branch : Set
    oldBranch newBranch : Branch
    provenanceFromOld : Set

open ReinstantiatedBranch public
