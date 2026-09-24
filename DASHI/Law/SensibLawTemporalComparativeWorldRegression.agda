module DASHI.Law.SensibLawTemporalComparativeWorldRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawTemporalComparativeWorldExact as T

evidenceStillRetainedAcrossConclusionRevision :
  T.earlierEvidenceMayRemainWhileConclusionChanges
    T.canonicalTemporalComparativeBoundary
  ≡ true
evidenceStillRetainedAcrossConclusionRevision = refl

consumerAndProducerRevisionStillDistinct :
  T.consumerRevisionAndProducerRevisionDistinct
    T.canonicalTemporalComparativeBoundary
  ≡ true
consumerAndProducerRevisionStillDistinct = refl

temporalRelevanceStillConsumerIndexed :
  T.temporalDeltaRelevanceIsConsumerIndexed
    T.canonicalTemporalComparativeBoundary
  ≡ true
temporalRelevanceStillConsumerIndexed = refl

asAtStillDoesNotChangeEveryAnswer :
  T.everyAsAtChangeChangesEveryAnswer
    T.canonicalTemporalComparativeBoundary
  ≡ false
asAtStillDoesNotChangeEveryAnswer = refl

temporalComparisonStillDoesNotCreateAuthority :
  T.temporalComparisonCreatesAuthority
    T.canonicalTemporalComparativeBoundary
  ≡ false
temporalComparisonStillDoesNotCreateAuthority = refl

temporalComparisonStillDoesNotCreateTruth :
  T.temporalComparisonCreatesTruth
    T.canonicalTemporalComparativeBoundary
  ≡ false
temporalComparisonStillDoesNotCreateTruth = refl

historicalEvidenceStillNotDeletedByTemporalDifference :
  T.TemporalDifferenceDeletesHistoricalEvidence → ⊥
historicalEvidenceStillNotDeletedByTemporalDifference =
  T.temporalDifferenceDoesNotDeleteHistory
