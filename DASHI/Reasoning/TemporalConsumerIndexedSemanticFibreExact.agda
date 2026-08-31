module DASHI.Reasoning.TemporalConsumerIndexedSemanticFibreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.BidiResidualApproximationExact as Bidi
import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Candidate
import DASHI.Reasoning.SemanticCandidateResidualBidiExact as Semantic

------------------------------------------------------------------------
-- TEMPORAL / HISTORY-INDEXED SEMANTIC FIBRE
--
-- The live semantic fibre is not a static object with an external consumer.
-- The consumer/version is part of the time/path-indexed reasoning state itself.
-- Producer refinement and authorised consumer revision are distinct transitions.
------------------------------------------------------------------------

data Time : Set where
  t0 t1 t2 : Time

data History : Set where
  historyAlpha historyBeta : History

data ConsumerVersion : Set where
  consumerV0 consumerV1 : ConsumerVersion

data ConsumerProvenance : Set where
  externallyFrozen authorisedRevision producerLocalRevision : ConsumerProvenance

data RevisionAuthority : Set where
  externalRevisionAuthority : RevisionAuthority

data RequirementStrength : Set where
  strongRequirement weakRequirement : RequirementStrength

record TemporalConsumer : Set where
  constructor temporalConsumer
  field
    consumerVersion : ConsumerVersion
    consumerProvenance : ConsumerProvenance
    requirementStrength : RequirementStrength
    consumerReading : Candidate.CandidateSemanticFragment → Bool
    consumerReference : String

open TemporalConsumer public

record HistoryIndexedSemanticFibre : Set₁ where
  constructor historyIndexedSemanticFibre
  field
    history : History
    time : Time
    liveFibre : Bidi.ResidualFibre Candidate.CandidateSemanticFragment
    consumer : TemporalConsumer
    fibreVersionReference : String
    derivationResidueReference : String
    admissibilityReference : String

open HistoryIndexedSemanticFibre public

------------------------------------------------------------------------
-- Two orthogonal transition kinds.
------------------------------------------------------------------------

record ProducerRefinement
    (before after : HistoryIndexedSemanticFibre) : Set₁ where
  constructor producerRefinement
  field
    sameHistory : history after ≡ history before
    fibreRefines : Bidi.FibreRefines (liveFibre after) (liveFibre before)
    consumerUnchanged : consumer after ≡ consumer before
    refinementReference : String

open ProducerRefinement public

record AuthorisedConsumerRevision
    (before after : HistoryIndexedSemanticFibre) : Set₁ where
  constructor authorisedConsumerRevision
  field
    sameHistory : history after ≡ history before
    sameSemanticFibre :
      (candidate : Candidate.CandidateSemanticFragment) →
      liveFibre after candidate ≡ liveFibre before candidate
    authority : RevisionAuthority
    targetProvenanceIsAuthorised :
      consumerProvenance (consumer after) ≡ authorisedRevision
    requirementPreserved :
      requirementStrength (consumer after)
      ≡ requirementStrength (consumer before)
    revisionReference : String

open AuthorisedConsumerRevision public

------------------------------------------------------------------------
-- Producer-side changes cannot silently mutate the target consumer.
------------------------------------------------------------------------

producerRefinementPreservesConsumer :
  ∀ {before after} →
  ProducerRefinement before after →
  consumer after ≡ consumer before
producerRefinementPreservesConsumer = consumerUnchanged

------------------------------------------------------------------------
-- Consumer closure is indexed by the whole temporal state.
------------------------------------------------------------------------

ConsumerClosed : HistoryIndexedSemanticFibre → Set
ConsumerClosed state =
  Bidi.PointIdentifies
    (liveFibre state)
    (consumerReading (consumer state))

producerRefinementPreservesClosure :
  ∀ {before after} →
  ProducerRefinement before after →
  ConsumerClosed before →
  ConsumerClosed after
producerRefinementPreservesClosure refinement closed left right leftLive rightLive =
  closed left right
    (fibreRefines refinement left leftLive)
    (fibreRefines refinement right rightLive)

------------------------------------------------------------------------
-- Same semantic fibre, revised consumer: closure must be re-evaluated.
-- There is intentionally no theorem transporting ConsumerClosed across an
-- authorised consumer revision, because the consumer function itself changed.
------------------------------------------------------------------------

record ConsumerClosureReaudit
    (before after : HistoryIndexedSemanticFibre) : Set₁ where
  constructor consumerClosureReaudit
  field
    revision : AuthorisedConsumerRevision before after
    oldClosureReference : String
    newConsumerReference : String
    reauditedClosure : ConsumerClosed after
    reauditingReference : String

open ConsumerClosureReaudit public

------------------------------------------------------------------------
-- Finite governance regression matching the live governed-consumer owner on
-- the sibling branch: route/producer-generated weakening cannot count as an
-- authorised revision.
------------------------------------------------------------------------

frozenConsumer : TemporalConsumer
frozenConsumer =
  temporalConsumer
    consumerV0 externallyFrozen strongRequirement
    (λ _ → true)
    "externally frozen consumer v0"

routeWeakenedConsumer : TemporalConsumer
routeWeakenedConsumer =
  temporalConsumer
    consumerV1 producerLocalRevision weakRequirement
    (λ _ → true)
    "producer-local weakened consumer"

authorisedConsumerV1 : TemporalConsumer
authorisedConsumerV1 =
  temporalConsumer
    consumerV1 authorisedRevision strongRequirement
    (λ _ → true)
    "externally authorised consumer v1"

routeGeneratedWeakeningCannotBeAuthorised :
  consumerProvenance routeWeakenedConsumer ≡ authorisedRevision → ⊥
routeGeneratedWeakeningCannotBeAuthorised ()

------------------------------------------------------------------------
-- Path/time reading.
------------------------------------------------------------------------

record TemporalConsumerBoundary : Set where
  constructor temporalConsumerBoundary
  field
    semanticFibreAndConsumerAreJointTemporalState : Bool
    semanticFibreAndConsumerAreJointTemporalStateIsTrue :
      semanticFibreAndConsumerAreJointTemporalState ≡ true
    producerRefinementMaySilentlyChangeConsumer : Bool
    producerRefinementMaySilentlyChangeConsumerIsFalse :
      producerRefinementMaySilentlyChangeConsumer ≡ false
    authorisedConsumerRevisionRequiresReaudit : Bool
    authorisedConsumerRevisionRequiresReauditIsTrue :
      authorisedConsumerRevisionRequiresReaudit ≡ true
    oldConsumerClosureAutomaticallyImpliesNewConsumerClosure : Bool
    oldConsumerClosureAutomaticallyImpliesNewConsumerClosureIsFalse :
      oldConsumerClosureAutomaticallyImpliesNewConsumerClosure ≡ false
    temporalFibreMayRetainDifferentHistoriesAtSameTime : Bool
    temporalFibreMayRetainDifferentHistoriesAtSameTimeIsTrue :
      temporalFibreMayRetainDifferentHistoriesAtSameTime ≡ true

canonicalTemporalConsumerBoundary : TemporalConsumerBoundary
canonicalTemporalConsumerBoundary =
  temporalConsumerBoundary
    true refl
    false refl
    true refl
    false refl
    true refl
