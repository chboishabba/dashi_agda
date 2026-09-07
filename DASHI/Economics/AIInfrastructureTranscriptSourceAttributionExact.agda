module DASHI.Economics.AIInfrastructureTranscriptSourceAttributionExact where

open import DASHI.Core.Prelude

import DASHI.Economics.SourceAttributionPromotionBoundaryExact as Attribution
import DASHI.Economics.AIInfrastructureYouTubeShortTranscriptBoundaryExact as Transcript

------------------------------------------------------------------------
-- CLAIM-LEVEL ATTRIBUTION FOR USER-SUPPLIED SHORT TRANSCRIPT
--
-- The transcript carrier and the independent source owner are separate.
-- `independentlyVerified = true` in the transcript owner is consumed here only
-- together with an explicit source-attribution receipt.
------------------------------------------------------------------------

transcriptCarrier : Attribution.SourceAttributionReceipt
transcriptCarrier = Attribution.sourceAttributionReceipt
  "unknown / unrecovered"
  "speaker identity unresolved"
  "YouTube Short IYjxiGUMMKE"
  "https://youtube.com/shorts/IYjxiGUMMKE"
  "user-supplied transcript in conversation"
  Attribution.userSuppliedCarrier
  "claim segmentation in AIInfrastructureYouTubeShortTranscriptBoundaryExact"
  "transcript carrier for the listed AI infrastructure propositions"
  Attribution.transcriptProposition
  "DASHI.Economics.AIInfrastructureYouTubeShortTranscriptBoundaryExact"
  "transcript carriage only; independent empirical authority must come from a separately owned source"
  false false true

epochGapSource : Attribution.SourceAttributionReceipt
epochGapSource = Attribution.sourceAttributionReceipt
  "Epoch AI"
  "Epoch AI"
  "Epoch AI ECI data insight"
  "Epoch AI canonical publication surface"
  "Epoch AI access surface"
  Attribution.canonicalCarrier
  "US-vs-China ECI capability-gap result since 2023"
  "Epoch AI reports a mean US-China frontier capability gap of seven months since 2023, with a reported range of four to fourteen months under its ECI methodology."
  Attribution.primarySourceProposition
  "DASHI.Economics.AIInfrastructureYouTubeShortTranscriptBoundaryExact / ChinaUSAITrainingServingComputeSeparation2026Exact"
  "bounded capability-gap proposition only; no authority to infer chip-share ratios, serving economics, or export-control counterfactuals"
  true true true

moonshotServingSource : Attribution.SourceAttributionReceipt
moonshotServingSource = Attribution.sourceAttributionReceipt
  "Reuters / AP / Moonshot reporting surface"
  "Reuters/AP reporting on Moonshot subscription suspension; underlying company event separately identified"
  "news reporting plus company-event surface"
  "2026-07-20 reporting on Kimi subscription pause"
  "secondary reporting carrier"
  Attribution.secondaryReportingCarrier
  "bounded subscription-suspension / compute-capacity proposition"
  "new Kimi subscriptions were paused after demand strained available compute capacity."
  Attribution.secondarySourceReport
  "DASHI.Economics.AIInfrastructureYouTubeShortTranscriptBoundaryExact / ChinaUSAITrainingServingComputeSeparation2026Exact"
  "supports the bounded serving-capacity event; does not by itself establish the exact eight-day open-weight causal sequence"
  false true true

deepSeekServingSource : Attribution.SourceAttributionReceipt
deepSeekServingSource = Attribution.sourceAttributionReceipt
  "DeepSeek"
  "DeepSeek infrastructure publication owner"
  "DeepSeek open-infrastructure production overview"
  "DeepSeek open-infra canonical publication/repository surface"
  "access representation used by the recovered infrastructure overview"
  Attribution.primaryCarrierMirror
  "V3/R1 online-service peak-node description"
  "DeepSeek reports a peak of 278 nodes with eight H800 GPUs per node for the reported V3/R1 online-service period."
  Attribution.primarySourceProposition
  "DASHI.Economics.AIInfrastructureYouTubeShortTranscriptBoundaryExact / ChinaUSAITrainingServingComputeSeparation2026Exact"
  "bounded production-footprint proposition only; no authority to infer global serving sufficiency, profitability, or national chip stock"
  true true true

asmlFleetSecondarySource : Attribution.SourceAttributionReceipt
asmlFleetSecondarySource = Attribution.sourceAttributionReceipt
  "ASML document as reported by secondary coverage"
  "secondary reporting on ASML document"
  "secondary report carrying ASML fleet-count proposition"
  "underlying ASML 2026 document not separately bound in this owner"
  "secondary access carrier"
  Attribution.secondaryReportingCarrier
  "reported 314 operational-EUV fleet proposition"
  "secondary coverage reports an ASML document stating 314 operational EUV systems worldwide and none in China."
  Attribution.secondarySourceReport
  "DASHI.Economics.AIInfrastructureYouTubeShortTranscriptBoundaryExact / ChinaUSAITrainingServingComputeSeparation2026Exact"
  "secondary authority only until the exact ASML primary document/location is recovered"
  false true false

------------------------------------------------------------------------
-- Independent-verification joins.  Each join preserves the transcript as a
-- transcript carrier and the independent source as the empirical authority.
------------------------------------------------------------------------

epochGapIndependentJoin : Attribution.IndependentVerificationReceipt
epochGapIndependentJoin = Attribution.independentVerificationReceipt
  transcriptCarrier epochGapSource true true

moonshotIndependentJoin : Attribution.IndependentVerificationReceipt
moonshotIndependentJoin = Attribution.independentVerificationReceipt
  transcriptCarrier moonshotServingSource true true

deepSeekIndependentJoin : Attribution.IndependentVerificationReceipt
deepSeekIndependentJoin = Attribution.independentVerificationReceipt
  transcriptCarrier deepSeekServingSource true true

-- ASML remains a secondary-source join here; the empirical proposition may be
-- supported, but this object does not pretend the primary ASML document was
-- recovered at exact location.
asmlSecondaryJoin : Attribution.IndependentVerificationReceipt
asmlSecondaryJoin = Attribution.independentVerificationReceipt
  transcriptCarrier asmlFleetSecondarySource true true

------------------------------------------------------------------------
-- Open claims retain explicit residual producers.
------------------------------------------------------------------------

data TranscriptResidualClaim : Set where
  fivePercentChinaChipShare
  exactEightDayOpenWeightCausalSequence
  macroPolo38Percent
  macroPolo24Percent
  macroPolo72Percent
  ferrariGasolineQuotationSpeakerIdentity
  : TranscriptResidualClaim

data TranscriptResidualProducer : Set where
  patronusInterviewPrimaryProducer
  moonshotReleaseTimelineProducer
  macroPoloPrimaryTrackerProducer
  speakerIdentityProducer
  : TranscriptResidualProducer

requiredResidualProducer : TranscriptResidualClaim → TranscriptResidualProducer
requiredResidualProducer fivePercentChinaChipShare = patronusInterviewPrimaryProducer
requiredResidualProducer exactEightDayOpenWeightCausalSequence = moonshotReleaseTimelineProducer
requiredResidualProducer macroPolo38Percent = macroPoloPrimaryTrackerProducer
requiredResidualProducer macroPolo24Percent = macroPoloPrimaryTrackerProducer
requiredResidualProducer macroPolo72Percent = macroPoloPrimaryTrackerProducer
requiredResidualProducer ferrariGasolineQuotationSpeakerIdentity = speakerIdentityProducer

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

transcriptStillDoesNotVerifyItsOwnClaims :
  Attribution.TranscriptImpliesIndependentVerificationPermission → ⊥
transcriptStillDoesNotVerifyItsOwnClaims =
  Attribution.transcriptDoesNotAutoPromoteToIndependentVerification

secondaryASMLCarrierStillDoesNotBecomePrimaryAuthority :
  Attribution.SecondaryReportImpliesPrimarySourceAuthorityPermission → ⊥
secondaryASMLCarrierStillDoesNotBecomePrimaryAuthority =
  Attribution.secondaryReportDoesNotAutoPromoteToPrimaryAuthority

sameClaimTextStillDoesNotProveIndependentProducer :
  Attribution.SameContentImpliesIndependentProducerPermission → ⊥
sameClaimTextStillDoesNotProveIndependentProducer =
  Attribution.sameContentDoesNotAutoPromoteToIndependentProducer

transcriptBoundary : Transcript.YouTubeShortSourceBoundary
transcriptBoundary = Transcript.canonicalYouTubeShortSourceBoundary
