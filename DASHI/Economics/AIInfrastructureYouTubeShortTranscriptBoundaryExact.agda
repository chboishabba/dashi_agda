module DASHI.Economics.AIInfrastructureYouTubeShortTranscriptBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- USER-SUPPLIED YOUTUBE SHORT TRANSCRIPT BOUNDARY
--
-- The transcript text was supplied by the user in-chat for video IYjxiGUMMKE.
-- It is now recoverable as a transcript carrier, but its individual empirical
-- claims retain separate source-verification status below.  Transcript content
-- is not treated as independent verification of the sources it cites.
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
  true false true false
  "user-supplied transcript recovered; speaker identity remains separately unresolved"

------------------------------------------------------------------------
-- Transcript propositions and independent verification state.
------------------------------------------------------------------------

data TranscriptClaim : Set where
  chinaFrontierGapSevenMonths : TranscriptClaim
  chinaChipShareFivePercent : TranscriptClaim
  trainingFiniteServingPersistent : TranscriptClaim
  moonshotServingCapacitySuspension : TranscriptClaim
  moonshotOpenWeightReleaseAfterSuspension : TranscriptClaim
  deepSeekPeak278Nodes : TranscriptClaim
  macroPoloChinaTalent38Percent : TranscriptClaim
  macroPoloUSTalent24Percent : TranscriptClaim
  macroPoloChinaEducatedToUS72Percent : TranscriptClaim
  euvManufacturingChokepoint : TranscriptClaim
  asml314OperationalEUV : TranscriptClaim
  noASMLEUVInChina : TranscriptClaim
  openWeightsExternaliseServingCompute : TranscriptClaim


record TranscriptClaimReceipt : Set where
  constructor transcriptClaimReceipt
  field
    claim : TranscriptClaim
    transcriptCarriesClaim : Bool
    independentlyVerified : Bool
    verificationReference : String

open TranscriptClaimReceipt public

frontierGapReceipt : TranscriptClaimReceipt
frontierGapReceipt = transcriptClaimReceipt chinaFrontierGapSevenMonths true true
  "Epoch AI, 2026-01-02: mean US-China ECI capability gap since 2023 = 7 months, range 4-14"

chipShareReceipt : TranscriptClaimReceipt
chipShareReceipt = transcriptClaimReceipt chinaChipShareFivePercent true false
  "transcript attributes rough 5 percent estimate to Patronus AI interview; independent primary receipt not recovered in this pass"

trainingServingReceipt : TranscriptClaimReceipt
trainingServingReceipt = transcriptClaimReceipt trainingFiniteServingPersistent true false
  "interpretive proposition from transcript; requires explicit workload/compute model rather than transcript promotion"

moonshotCapacityReceipt : TranscriptClaimReceipt
moonshotCapacityReceipt = transcriptClaimReceipt moonshotServingCapacitySuspension true true
  "Reuters/AP/TechNode, 2026-07-20: new Kimi subscriptions paused after demand strained compute capacity"

moonshotOpenWeightTimingReceipt : TranscriptClaimReceipt
moonshotOpenWeightTimingReceipt = transcriptClaimReceipt moonshotOpenWeightReleaseAfterSuspension true false
  "exact eight-day timing and causal inference from capacity suspension to open-weight release not independently closed here"

deepSeekNodesReceipt : TranscriptClaimReceipt
deepSeekNodesReceipt = transcriptClaimReceipt deepSeekPeak278Nodes true true
  "DeepSeek open-infra production overview: 278 peak nodes, 8 H800 GPUs/node, about 2,214 peak GPUs"

macroPoloChinaReceipt : TranscriptClaimReceipt
macroPoloChinaReceipt = transcriptClaimReceipt macroPoloChinaTalent38Percent true false
  "recent secondary summaries attribute 38 percent undergraduate-origin share to MacroPolo Talent Tracker 3.0; primary page not recovered here"

macroPoloUSReceipt : TranscriptClaimReceipt
macroPoloUSReceipt = transcriptClaimReceipt macroPoloUSTalent24Percent true false
  "recent secondary summaries attribute 24 percent US undergraduate-origin share to MacroPolo Talent Tracker 3.0; primary page not recovered here"

macroPoloMigrationReceipt : TranscriptClaimReceipt
macroPoloMigrationReceipt = transcriptClaimReceipt macroPoloChinaEducatedToUS72Percent true false
  "recent secondary summaries attribute 72 percent migration to US institutions to MacroPolo Talent Tracker 3.0; primary page not recovered here"

asmlCountReceipt : TranscriptClaimReceipt
asmlCountReceipt = transcriptClaimReceipt asml314OperationalEUV true true
  "2026 ASML document reported by Bloomberg-linked coverage: 314 operational EUV systems worldwide"

asmlChinaReceipt : TranscriptClaimReceipt
asmlChinaReceipt = transcriptClaimReceipt noASMLEUVInChina true true
  "ASML states it has never shipped an EUV machine to China; 2026 company document says none of 314 operational systems are in China"

openWeightsServingReceipt : TranscriptClaimReceipt
openWeightsServingReceipt = transcriptClaimReceipt openWeightsExternaliseServingCompute true false
  "DASHI interpretation candidate: open weights can shift some inference hardware burden to downstream operators; not a universal causal theorem"

------------------------------------------------------------------------
-- Strongest new reusable distinction: training and serving demand are separate
-- compute obligations.  A lab can close a finite training run while remaining
-- unable to provide persistent hosted inference at desired demand.
------------------------------------------------------------------------

record TrainingServingComputeSeparation : Set₁ where
  constructor trainingServingComputeSeparation
  field
    TrainingObligation ServingObligation : Set
    trainingObligation : TrainingObligation
    servingObligation : ServingObligation
    trainingCompletionDoesNotPayServingObligation : Set

open TrainingServingComputeSeparation public

record OpenWeightServingExternalisation : Set₁ where
  constructor openWeightServingExternalisation
  field
    PublisherCompute DownstreamOperatorCompute : Set
    publisherCompute : PublisherCompute
    downstreamOperatorCompute : DownstreamOperatorCompute
    redistributionReceipt : Set

open OpenWeightServingExternalisation public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data TranscriptImpliesIndependentVerificationPermission : Set where

data TrainingSuccessImpliesServingCapacityPermission : Set where

data OpenWeightsImplyZeroServingCostPermission : Set where

data SevenMonthGapImpliesChipControlsIneffectivePermission : Set where

data ComputeScarcityImpliesModelInferiorityPermission : Set where

transcriptDoesNotAutoPromoteToIndependentVerification :
  TranscriptImpliesIndependentVerificationPermission → ⊥
transcriptDoesNotAutoPromoteToIndependentVerification ()

trainingSuccessDoesNotAutoPromoteToServingCapacity :
  TrainingSuccessImpliesServingCapacityPermission → ⊥
trainingSuccessDoesNotAutoPromoteToServingCapacity ()

openWeightsDoNotAutoPromoteToZeroServingCost :
  OpenWeightsImplyZeroServingCostPermission → ⊥
openWeightsDoNotAutoPromoteToZeroServingCost ()

sevenMonthGapDoesNotAutoPromoteToChipControlsIneffective :
  SevenMonthGapImpliesChipControlsIneffectivePermission → ⊥
sevenMonthGapDoesNotAutoPromoteToChipControlsIneffective ()

computeScarcityDoesNotAutoPromoteToModelInferiority :
  ComputeScarcityImpliesModelInferiorityPermission → ⊥
computeScarcityDoesNotAutoPromoteToModelInferiority ()
