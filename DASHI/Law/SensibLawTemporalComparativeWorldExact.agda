module DASHI.Law.SensibLawTemporalComparativeWorldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.AppendOnlyEvidenceResidualRevisionExact as Revision
import DASHI.Reasoning.TemporalConsumerSelectiveReopeningExact as ConsumerRevision
import DASHI.Reasoning.TemporalConsumerIndexedSemanticFibreExact as Temporal
import DASHI.Law.SensibLawComparativeWorldIRExact as Comparative

------------------------------------------------------------------------
-- M11 / S26.7 TEMPORAL / AS-AT COMPARISON
--
-- Existing revision owners pay the hard semantic distinctions:
--   * append-only evidence may retain all prior evidence while changing the
--     current justified conclusion;
--   * an authorised consumer revision selectively reopens its dependent
--     certificates and is not a semantic-producer revision.
--
-- M11 contributes only the comparison reading: those transitions are typed
-- world/context deltas whose relevance is query/consumer indexed.
------------------------------------------------------------------------

data TemporalComparisonKind : Set where
  producerEvidenceRevision : TemporalComparisonKind
  authorisedConsumerRevision : TemporalComparisonKind
  asAtContextRevision : TemporalComparisonKind

data TemporalDeltaRelevance : Set where
  queryRelevant : TemporalDeltaRelevance
  queryIrrelevant : TemporalDeltaRelevance

record TemporalComparativeDelta : Set where
  constructor temporal-comparative-delta
  field
    comparisonKind : TemporalComparisonKind
    relevance : TemporalDeltaRelevance
    inputSide : Bool
    createsSemanticAuthority : Bool
    createsClaimTruth : Bool

open TemporalComparativeDelta public

appendOnlyRevisionIsInputDelta : TemporalComparativeDelta
appendOnlyRevisionIsInputDelta =
  temporal-comparative-delta
    producerEvidenceRevision
    queryRelevant
    true
    false
    false

authorisedConsumerRevisionIsInputDelta : TemporalComparativeDelta
authorisedConsumerRevisionIsInputDelta =
  temporal-comparative-delta
    authorisedConsumerRevision
    queryRelevant
    true
    false
    false

------------------------------------------------------------------------
-- Reuse existing exact revision witnesses.
------------------------------------------------------------------------

existingConclusionRevision :
  Revision.ConclusionRevision Revision.fixtureSystem
existingConclusionRevision =
  Revision.canonicalConclusionRevision

oldEvidenceRetainedAcrossRevision :
  Revision.FixtureContains
    Revision.supportObservation
    (Revision.appendFixture
      Revision.supportOnly
      Revision.defeaterObservation)
oldEvidenceRetainedAcrossRevision =
  Revision.supportPersistsAfterDefeater

conclusionActuallyChanges :
  Revision.fixtureConclusion Revision.supportOnly
    ≡ Revision.fixtureConclusion
        (Revision.appendFixture
          Revision.supportOnly
          Revision.defeaterObservation)
  → ⊥
conclusionActuallyChanges =
  Revision.conclusionChangesAfterAppend

------------------------------------------------------------------------
-- Consumer revision remains distinct from producer revision.
------------------------------------------------------------------------

consumerRevisionDoesNotBecomeProducerRevision :
  ConsumerRevision.ConsumerDepends
    ConsumerRevision.consumerDefinitionCertificate
    ConsumerRevision.semanticProducerCertificate
  → ⊥
consumerRevisionDoesNotBecomeProducerRevision =
  ConsumerRevision.consumerRevisionIsNotSemanticProducerChange

producerRevisionDoesNotBecomeConsumerRevision :
  ConsumerRevision.ConsumerDepends
    ConsumerRevision.semanticProducerCertificate
    ConsumerRevision.consumerDefinitionCertificate
  → ⊥
producerRevisionDoesNotBecomeConsumerRevision =
  ConsumerRevision.semanticProducerChangeIsNotConsumerRevision

------------------------------------------------------------------------
-- Query relevance is not intrinsic to a timestamp/revision event.
------------------------------------------------------------------------

data SameTemporalDeltaDifferentConsumerRelevance : Set where
  sameDeltaDifferentConsumerRelevance : SameTemporalDeltaDifferentConsumerRelevance

data EveryAsAtChangeChangesEveryAnswer : Set where
data TemporalDifferenceDeletesHistoricalEvidence : Set where
data ConsumerRevisionCreatesProducerAuthority : Set where
data TemporalComparisonCreatesTruth : Set where

sameTemporalDeltaMayHaveDifferentConsumerRelevance :
  SameTemporalDeltaDifferentConsumerRelevance
sameTemporalDeltaMayHaveDifferentConsumerRelevance =
  sameDeltaDifferentConsumerRelevance

asAtChangeDoesNotChangeEveryAnswer :
  EveryAsAtChangeChangesEveryAnswer → ⊥
asAtChangeDoesNotChangeEveryAnswer ()

temporalDifferenceDoesNotDeleteHistory :
  TemporalDifferenceDeletesHistoricalEvidence → ⊥
temporalDifferenceDoesNotDeleteHistory ()

consumerRevisionDoesNotCreateProducerAuthority :
  ConsumerRevisionCreatesProducerAuthority → ⊥
consumerRevisionDoesNotCreateProducerAuthority ()

temporalComparisonDoesNotCreateTruth :
  TemporalComparisonCreatesTruth → ⊥
temporalComparisonDoesNotCreateTruth ()

record TemporalComparativeBoundary : Set where
  constructor temporalComparativeBoundary
  field
    earlierEvidenceMayRemainWhileConclusionChanges : Bool
    earlierEvidenceMayRemainWhileConclusionChangesIsTrue :
      earlierEvidenceMayRemainWhileConclusionChanges ≡ true

    consumerRevisionAndProducerRevisionDistinct : Bool
    consumerRevisionAndProducerRevisionDistinctIsTrue :
      consumerRevisionAndProducerRevisionDistinct ≡ true

    temporalDeltaRelevanceIsConsumerIndexed : Bool
    temporalDeltaRelevanceIsConsumerIndexedIsTrue :
      temporalDeltaRelevanceIsConsumerIndexed ≡ true

    everyAsAtChangeChangesEveryAnswer : Bool
    everyAsAtChangeChangesEveryAnswerIsFalse :
      everyAsAtChangeChangesEveryAnswer ≡ false

    temporalComparisonCreatesAuthority : Bool
    temporalComparisonCreatesAuthorityIsFalse :
      temporalComparisonCreatesAuthority ≡ false

    temporalComparisonCreatesTruth : Bool
    temporalComparisonCreatesTruthIsFalse :
      temporalComparisonCreatesTruth ≡ false

open TemporalComparativeBoundary public

canonicalTemporalComparativeBoundary : TemporalComparativeBoundary
canonicalTemporalComparativeBoundary =
  temporalComparativeBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
