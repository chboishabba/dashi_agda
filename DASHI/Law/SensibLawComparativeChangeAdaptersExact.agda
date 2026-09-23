module DASHI.Law.SensibLawComparativeChangeAdaptersExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawChangeLocusExact as Locus
import DASHI.Law.SensibLawPersonalProfessionalComparativeWorldExact as Fibre
import DASHI.Law.SensibLawTemporalComparativeWorldExact as Temporal

------------------------------------------------------------------------
-- M11.1 DOMAIN -> CHANGE-LAYER ADAPTERS
--
-- Existing domain receipts already explain WHY a coordinate is absent or
-- revised.  This module only maps those established reasons into the common
-- ChangeLayer vocabulary.
------------------------------------------------------------------------

data ConsumerDifferenceKind : Set where
  scopeBlockedDifference : ConsumerDifferenceKind
  reviewNotReadyDifference : ConsumerDifferenceKind
  dependencyIrrelevantDifference : ConsumerDifferenceKind

consumerDifferenceLayer : ConsumerDifferenceKind → Locus.ChangeLayer
consumerDifferenceLayer scopeBlockedDifference = Locus.scopeLayer
consumerDifferenceLayer reviewNotReadyDifference = Locus.reviewLayer
consumerDifferenceLayer dependencyIrrelevantDifference =
  Locus.consumerProjectionLayer

privateHypothesisMapsToScope :
  consumerDifferenceLayer scopeBlockedDifference ≡ Locus.scopeLayer
privateHypothesisMapsToScope = refl

notReadyMapsToReview :
  consumerDifferenceLayer reviewNotReadyDifference ≡ Locus.reviewLayer
notReadyMapsToReview = refl

dependencyIrrelevantMapsToConsumerProjection :
  consumerDifferenceLayer dependencyIrrelevantDifference
  ≡ Locus.consumerProjectionLayer
dependencyIrrelevantMapsToConsumerProjection = refl

fibreBoundary : Fibre.PersonalProfessionalComparativeBoundary
fibreBoundary = Fibre.canonicalPersonalProfessionalComparativeBoundary

fibreComparisonKeepsWorldFixed :
  Fibre.sameCanonicalWorld fibreBoundary ≡ true
fibreComparisonKeepsWorldFixed = refl

scopeReasonAlreadyPaid :
  Fibre.privateDifferenceExplainedByScope fibreBoundary ≡ true
scopeReasonAlreadyPaid = refl

reviewReasonAlreadyPaid :
  Fibre.notReadyDifferenceExplainedByReadiness fibreBoundary ≡ true
reviewReasonAlreadyPaid = refl

dependencyReasonAlreadyPaid :
  Fibre.dependencyDifferenceExplainedByConsumerSlice fibreBoundary ≡ true
dependencyReasonAlreadyPaid = refl

------------------------------------------------------------------------
-- Temporal/revision adapter.
------------------------------------------------------------------------

data TemporalDifferenceKind : Set where
  sourceRevisionDifference : TemporalDifferenceKind
  asAtDifference : TemporalDifferenceKind
  authorisedConsumerDefinitionDifference : TemporalDifferenceKind

temporalDifferenceLayer : TemporalDifferenceKind → Locus.ChangeLayer
temporalDifferenceLayer sourceRevisionDifference = Locus.worldEvidenceLayer
temporalDifferenceLayer asAtDifference = Locus.worldLayer
temporalDifferenceLayer authorisedConsumerDefinitionDifference =
  Locus.consumerProjectionLayer

sourceRevisionMapsToWorldEvidence :
  temporalDifferenceLayer sourceRevisionDifference ≡ Locus.worldEvidenceLayer
sourceRevisionMapsToWorldEvidence = refl

asAtMapsToWorldContext :
  temporalDifferenceLayer asAtDifference ≡ Locus.worldLayer
asAtMapsToWorldContext = refl

consumerRevisionMapsToConsumerProjection :
  temporalDifferenceLayer authorisedConsumerDefinitionDifference
  ≡ Locus.consumerProjectionLayer
consumerRevisionMapsToConsumerProjection = refl

temporalBoundary : Temporal.TemporalComparativeBoundary
temporalBoundary = Temporal.canonicalTemporalComparativeBoundary

temporalRelevanceAlreadyConsumerIndexed :
  Temporal.temporalDeltaRelevanceIsConsumerIndexed temporalBoundary ≡ true
temporalRelevanceAlreadyConsumerIndexed = refl

consumerRevisionStillDistinctFromProducerRevision :
  Temporal.consumerRevisionAndProducerRevisionDistinct temporalBoundary ≡ true
consumerRevisionStillDistinctFromProducerRevision = refl

data ScopeDifferenceIsWorldDifference : Set where
data ConsumerProjectionDifferenceIsWorldDifference : Set where
data SourceRevisionDifferenceIsWorldIdentityDifference : Set where
data ReviewDifferenceCreatesClaimTruth : Set where

scopeDifferenceDoesNotBecomeWorldDifference :
  ScopeDifferenceIsWorldDifference → ⊥
scopeDifferenceDoesNotBecomeWorldDifference ()

consumerProjectionDoesNotBecomeWorldDifference :
  ConsumerProjectionDifferenceIsWorldDifference → ⊥
consumerProjectionDoesNotBecomeWorldDifference ()

sourceRevisionDoesNotBecomeWorldIdentityDifference :
  SourceRevisionDifferenceIsWorldIdentityDifference → ⊥
sourceRevisionDoesNotBecomeWorldIdentityDifference ()

reviewDifferenceDoesNotCreateTruth :
  ReviewDifferenceCreatesClaimTruth → ⊥
reviewDifferenceDoesNotCreateTruth ()

record ComparativeChangeAdapterBoundary : Set where
  constructor comparativeChangeAdapterBoundary
  field
    personalProfessionalScopeDifferenceTyped : Bool
    personalProfessionalScopeDifferenceTypedIsTrue :
      personalProfessionalScopeDifferenceTyped ≡ true

    personalProfessionalReviewDifferenceTyped : Bool
    personalProfessionalReviewDifferenceTypedIsTrue :
      personalProfessionalReviewDifferenceTyped ≡ true

    personalProfessionalDependencyDifferenceTyped : Bool
    personalProfessionalDependencyDifferenceTypedIsTrue :
      personalProfessionalDependencyDifferenceTyped ≡ true

    sourceRevisionDifferenceTypedAsWorldEvidence : Bool
    sourceRevisionDifferenceTypedAsWorldEvidenceIsTrue :
      sourceRevisionDifferenceTypedAsWorldEvidence ≡ true

    sourceRevisionAutomaticallyMeansWorldIdentityChanged : Bool
    sourceRevisionAutomaticallyMeansWorldIdentityChangedIsFalse :
      sourceRevisionAutomaticallyMeansWorldIdentityChanged ≡ false

    adapterCreatesClaimTruth : Bool
    adapterCreatesClaimTruthIsFalse :
      adapterCreatesClaimTruth ≡ false

open ComparativeChangeAdapterBoundary public

canonicalComparativeChangeAdapterBoundary : ComparativeChangeAdapterBoundary
canonicalComparativeChangeAdapterBoundary =
  comparativeChangeAdapterBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
