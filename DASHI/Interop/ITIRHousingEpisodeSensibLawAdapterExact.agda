module DASHI.Interop.ITIRHousingEpisodeSensibLawAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.ITIRSuiteNormalizedCompilerParityExact as ITIR
import DASHI.Law.SensibLawHousingEpisodeEvidenceLineageExact as Housing

------------------------------------------------------------------------
-- ITIR NORMALIZED SPINE -> LONGITUDINAL HOUSING EPISODES
--
-- Each tenancy episode remains source-native.  ITIR may compile several
-- episodes into a longitudinal state and expose a reviewable cross-episode
-- claim, but promotion remains explicit and cannot manufacture common cause.
------------------------------------------------------------------------

record ITIRHousingEpisode : Set₁ where
  constructor itirHousingEpisode
  field
    housingEpisode : Housing.HousingEpisode
    sourceArtifact : ITIR.NormalizedArtifact
    compiledEpisodeState : ITIR.NormalizedArtifact
    sourceIsArtifact : ITIR.concept sourceArtifact ≡ ITIR.sourceArtifact
    episodeIsCompiledState :
      ITIR.concept compiledEpisodeState ≡ ITIR.compiledState
    episodeCompilationReceipt : Set
    adapterReference : String

open ITIRHousingEpisode public

record ITIRLongitudinalHousingClaim : Set₁ where
  constructor itirLongitudinalHousingClaim
  field
    housingSequence : Housing.LongitudinalHousingSequence
    compiledSequenceState : ITIR.NormalizedArtifact
    reviewableSequenceClaim : ITIR.NormalizedArtifact
    sequenceIsCompiledState :
      ITIR.concept compiledSequenceState ≡ ITIR.compiledState
    claimIsReviewable :
      ITIR.concept reviewableSequenceClaim ≡ ITIR.reviewableClaim
    sequenceCompilationReceipt : Set
    claimReference : String

open ITIRLongitudinalHousingClaim public

record PromotedLongitudinalHousingRecord
    (claim : ITIRLongitudinalHousingClaim) : Set₁ where
  constructor promotedLongitudinalHousingRecord
  field
    promotedArtifact : ITIR.NormalizedArtifact
    promotedIsRecord : ITIR.concept promotedArtifact ≡ ITIR.promotedRecord
    promotionReceipt :
      ITIR.PromotionReceipt
        (ITIRLongitudinalHousingClaim.reviewableSequenceClaim claim)
        promotedArtifact
    promotionReference : String

open PromotedLongitudinalHousingRecord public

------------------------------------------------------------------------
-- Parity boundary.
------------------------------------------------------------------------

record ITIRHousingEpisodeParityBoundary : Set where
  constructor itirHousingEpisodeParityBoundary
  field
    episodeSourceStartsAsSourceArtifact : Bool
    episodeSourceStartsAsSourceArtifactIsTrue :
      episodeSourceStartsAsSourceArtifact ≡ true

    episodeCompilesAsState : Bool
    episodeCompilesAsStateIsTrue : episodeCompilesAsState ≡ true

    crossEpisodePatternStartsReviewable : Bool
    crossEpisodePatternStartsReviewableIsTrue :
      crossEpisodePatternStartsReviewable ≡ true

    crossEpisodePatternMayBypassPromotion : Bool
    crossEpisodePatternMayBypassPromotionIsFalse :
      crossEpisodePatternMayBypassPromotion ≡ false

    repeatedEpisodesAutomaticallyBecomeCommonCause : Bool
    repeatedEpisodesAutomaticallyBecomeCommonCauseIsFalse :
      repeatedEpisodesAutomaticallyBecomeCommonCause ≡ false

    retrospectiveCarrierMayReplacePrimaryEpisodeSource : Bool
    retrospectiveCarrierMayReplacePrimaryEpisodeSourceIsFalse :
      retrospectiveCarrierMayReplacePrimaryEpisodeSource ≡ false

canonicalITIRHousingEpisodeParityBoundary : ITIRHousingEpisodeParityBoundary
canonicalITIRHousingEpisodeParityBoundary =
  itirHousingEpisodeParityBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CrossEpisodePatternBypassesPromotion : Set where
data RepeatedEpisodesAutomaticallyCommonCause : Set where
data RetrospectiveCarrierAutomaticallyPrimarySource : Set where

crossEpisodePatternDoesNotBypassPromotion :
  CrossEpisodePatternBypassesPromotion → ⊥
crossEpisodePatternDoesNotBypassPromotion ()

repeatedEpisodesDoNotAutoBecomeCommonCause :
  RepeatedEpisodesAutomaticallyCommonCause → ⊥
repeatedEpisodesDoNotAutoBecomeCommonCause ()

retrospectiveCarrierDoesNotReplacePrimarySource :
  RetrospectiveCarrierAutomaticallyPrimarySource → ⊥
retrospectiveCarrierDoesNotReplacePrimarySource ()
