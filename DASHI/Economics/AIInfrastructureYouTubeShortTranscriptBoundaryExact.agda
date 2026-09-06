module DASHI.Economics.AIInfrastructureYouTubeShortTranscriptBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- USER-SUPPLIED YOUTUBE SHORT SOURCE BOUNDARY
--
-- URL supplied for cross-pollination:
-- https://youtube.com/shorts/IYjxiGUMMKE
--
-- The available retrieval surfaces did not expose the video transcript or
-- captions.  Therefore no speaker, quotation, proposition, or attribution is
-- manufactured here.  This module owns the residual producer explicitly.
------------------------------------------------------------------------

record YouTubeShortSourceBoundary : Set where
  constructor youtubeShortSourceBoundary
  field
    videoID : String
    suppliedURL : String
    transcriptRecovered : Bool
    speakerIdentified : Bool
    boundedPropositionRecovered : Bool
    transcriptProducerRequired : Bool
    residualReference : String

open YouTubeShortSourceBoundary public

canonicalYouTubeShortSourceBoundary : YouTubeShortSourceBoundary
canonicalYouTubeShortSourceBoundary = youtubeShortSourceBoundary
  "IYjxiGUMMKE"
  "https://youtube.com/shorts/IYjxiGUMMKE"
  false false false true
  "recover captions/transcript or a source-equivalent speaker transcript before promoting any proposition"

data URLImpliesTranscriptContentPermission : Set where

data VideoIdentityImpliesSpeakerIdentityPermission : Set where

data UnrecoveredTranscriptImpliesEconomicClaimPermission : Set where

urlDoesNotAutoPromoteTranscriptContent :
  URLImpliesTranscriptContentPermission → ⊥
urlDoesNotAutoPromoteTranscriptContent ()

videoIdentityDoesNotAutoPromoteSpeakerIdentity :
  VideoIdentityImpliesSpeakerIdentityPermission → ⊥
videoIdentityDoesNotAutoPromoteSpeakerIdentity ()

unrecoveredTranscriptDoesNotAutoPromoteEconomicClaim :
  UnrecoveredTranscriptImpliesEconomicClaimPermission → ⊥
unrecoveredTranscriptDoesNotAutoPromoteEconomicClaim ()
