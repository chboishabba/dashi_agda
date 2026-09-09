module DASHI.Cognition.PNF.SensibLawDiscourseRuntimeImplementationRoadmapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Completion roadmap for the ABC 7.30 discourse-reconstruction benchmark.
-- This owner records what is already paid, what the runtime sidecar must emit,
-- and what remains a source/admission residual.
------------------------------------------------------------------------

data RoadmapStage : Set where
  freezeParserPolicy : RoadmapStage
  deterministicSentiment : RoadmapStage
  intraSentenceCutInference : RoadmapStage
  blindSpeakerReconstruction : RoadmapStage
  speakerRepairedPNFRerun : RoadmapStage
  substantivePolicyComparison : RoadmapStage

data StageStatus : Set where
  completed : StageStatus
  implementedPendingRun : StageStatus
  runtimePending : StageStatus
  sourceResidual : StageStatus

record StageReceipt : Set where
  constructor stageReceipt
  field
    stage : RoadmapStage
    status : StageStatus
    ownerOrRuntime : String
    acceptanceCriterion : String

open StageReceipt public

parserPolicyStage : StageReceipt
parserPolicyStage = stageReceipt freezeParserPolicy implementedPendingRun
  "SensibLawDeterministicSentimentProducerExact + runtime metadata receipt"
  "Record whether project policy is strict no-learned-weights or pinned-local-replayable; record exact spaCy/en_core_web_sm versions and digests if retained."

sentimentStage : StageReceipt
sentimentStage = stageReceipt deterministicSentiment implementedPendingRun
  "tools/slr-discourse-reconstruct; vader_parity = 0.1.0"
  "Emit exact VADER neg/neu/pos/compound scores per source span without truth promotion."

cutStage : StageReceipt
cutStage = stageReceipt intraSentenceCutInference implementedPendingRun
  "tools/slr-discourse-reconstruct"
  "Rank token-boundary cut candidates from dependency-edge crossings, punctuation/discourse markers, perspective shift, residual density and left/right VADER delta."

blindStage : StageReceipt
blindStage = stageReceipt blindSpeakerReconstruction runtimePending
  "optional speaker-profile TSV + held-out gold labels"
  "Hide gold names; compare profile/world-model candidate rankings against Wong/Husic/Shoebridge/Leeser sequence."

rerunStage : StageReceipt
rerunStage = stageReceipt speakerRepairedPNFRerun runtimePending
  "existing spaCy -> SLR -> PNF admission pipeline"
  "Feed candidate repaired spans back through the existing attribution/admission owners; no model output self-verifies identity or proposition truth."

policyStage : StageReceipt
policyStage = stageReceipt substantivePolicyComparison sourceResidual
  "ABC730 claim ledger + speaker promotion receipts"
  "Only after speaker segmentation: compare Wong rationale, Husic criticism, likely Shoebridge gaslighting characterization, Leeser effectiveness objection and Thornberry counterarguments."

record RoadmapBoundary : Set where
  constructor roadmapBoundary
  field
    moreAgdaRequiredBeforeRuntimeRun : Bool
    moreAgdaRequiredBeforeRuntimeRunIsFalse : moreAgdaRequiredBeforeRuntimeRun ≡ false
    runtimeCandidateMayPromoteTruth : Bool
    runtimeCandidateMayPromoteTruthIsFalse : runtimeCandidateMayPromoteTruth ≡ false
    runtimeCandidateMayPromoteVerifiedSpeaker : Bool
    runtimeCandidateMayPromoteVerifiedSpeakerIsFalse : runtimeCandidateMayPromoteVerifiedSpeaker ≡ false
    currentHighestAlphaIsRuntimeMeasurement : Bool
    currentHighestAlphaIsRuntimeMeasurementIsTrue : currentHighestAlphaIsRuntimeMeasurement ≡ true

canonicalRoadmapBoundary : RoadmapBoundary
canonicalRoadmapBoundary = roadmapBoundary false refl false refl false refl true refl
