module DASHI.Law.SensibLawLongitudinalHousingHealthExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawHealthRecordEvidenceExact as Health
import DASHI.Law.SensibLawHousingEpisodeEvidenceLineageExact as Housing

------------------------------------------------------------------------
-- GENERIC LONGITUDINAL HOUSING / HEALTH PRODUCT
--
-- The generic object is not "three evictions caused one illness".  It is an
-- ordered family of separately sourced housing episodes carrying separately
-- sourced health observations.  Cross-episode propositions remain their own
-- source-conditioned consumers.
------------------------------------------------------------------------

record HousingHealthEpisode : Set₁ where
  constructor housingHealthEpisode
  field
    housingEpisode : Housing.HousingEpisode
    healthArtifacts : List Health.HealthRecordArtifact
    healthAtoms : List Health.HealthAtom
    submittedEvidenceReferences : List String
    terminalOutcomeReference : String
    episodeHealthReceipt : Set

open HousingHealthEpisode public

record LongitudinalHealthHousingSequence : Set₁ where
  constructor longitudinalHealthHousingSequence
  field
    sequenceReference : String
    episodes : List HousingHealthEpisode
    sameSubjectReference : String
    chronologyReference : String
    sameSubjectReceipt : Set
    chronologyReceipt : Set

open LongitudinalHealthHousingSequence public

data CrossEpisodeHealthAtomKind : Set where
  repeatedHousingDisplacement : CrossEpisodeHealthAtomKind
  persistentSymptomAcrossEpisodes : CrossEpisodeHealthAtomKind
  conditionPresentAcrossEpisodes : CrossEpisodeHealthAtomKind
  aggravationAcrossEpisodes : CrossEpisodeHealthAtomKind
  cumulativeCausation : CrossEpisodeHealthAtomKind

record CrossEpisodeHealthAtom : Set where
  constructor crossEpisodeHealthAtom
  field
    atomKind : CrossEpisodeHealthAtomKind
    propositionReference : String
    sourceReference : String

open CrossEpisodeHealthAtom public

record SourceConditionedCrossEpisodeHealthAtom
    (atom : CrossEpisodeHealthAtom) : Set₁ where
  constructor sourceConditionedCrossEpisodeHealthAtom
  field
    sequence : LongitudinalHealthHousingSequence
    outcomeSourceReference : String
    outcomeReceipt : Set
    atomReference : String

open SourceConditionedCrossEpisodeHealthAtom public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data OrderedEpisodesAutomaticallySingleCausalChain : Set where
data RepeatedDisplacementAutomaticallySystemicWrongdoing : Set where
data PersistentSymptomsAutomaticallyAggravation : Set where
data AggravationAutomaticallyCumulativeCausation : Set where

data CrossEpisodeObservationAutomaticallyEpisodeSpecificCausation : Set where

orderedEpisodesDoNotAutoBecomeSingleCausalChain :
  OrderedEpisodesAutomaticallySingleCausalChain → ⊥
orderedEpisodesDoNotAutoBecomeSingleCausalChain ()

repeatedDisplacementDoesNotAutoProveSystemicWrongdoing :
  RepeatedDisplacementAutomaticallySystemicWrongdoing → ⊥
repeatedDisplacementDoesNotAutoProveSystemicWrongdoing ()

persistentSymptomsDoNotAutoProveAggravation :
  PersistentSymptomsAutomaticallyAggravation → ⊥
persistentSymptomsDoNotAutoProveAggravation ()

aggravationDoesNotAutoProveCumulativeCausation :
  AggravationAutomaticallyCumulativeCausation → ⊥
aggravationDoesNotAutoProveCumulativeCausation ()

crossEpisodeObservationDoesNotAutoPayEpisodeCausation :
  CrossEpisodeObservationAutomaticallyEpisodeSpecificCausation → ⊥
crossEpisodeObservationDoesNotAutoPayEpisodeCausation ()

record LongitudinalHousingHealthBoundary : Set where
  constructor longitudinalHousingHealthBoundary
  field
    episodeOrderingIsObservational : Bool
    episodeOrderingIsObservationalIsTrue :
      episodeOrderingIsObservational ≡ true
    crossEpisodeAtomsRequireOwnOutcomeSources : Bool
    crossEpisodeAtomsRequireOwnOutcomeSourcesIsTrue :
      crossEpisodeAtomsRequireOwnOutcomeSources ≡ true
    repeatedDisplacementDoesNotEncodeCommonCause : Bool
    repeatedDisplacementDoesNotEncodeCommonCauseIsTrue :
      repeatedDisplacementDoesNotEncodeCommonCause ≡ true
    persistentSymptomsDoNotEncodeAggravation : Bool
    persistentSymptomsDoNotEncodeAggravationIsTrue :
      persistentSymptomsDoNotEncodeAggravation ≡ true
    cumulativeCausationRemainsIndependentConsumer : Bool
    cumulativeCausationRemainsIndependentConsumerIsTrue :
      cumulativeCausationRemainsIndependentConsumer ≡ true

canonicalLongitudinalHousingHealthBoundary :
  LongitudinalHousingHealthBoundary
canonicalLongitudinalHousingHealthBoundary =
  longitudinalHousingHealthBoundary
    true refl
    true refl
    true refl
    true refl
    true refl
