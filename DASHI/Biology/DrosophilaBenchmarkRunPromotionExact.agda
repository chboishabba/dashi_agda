module DASHI.Biology.DrosophilaBenchmarkRunPromotionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.DrosophilaConsumerIndexedEvidencePromotionExact as Consumer

------------------------------------------------------------------------
-- A benchmark can be mechanically runnable without being empirically promotable.
-- This owner separates execution mode from consumer evidence sufficiency.
------------------------------------------------------------------------

data BenchmarkRunMode : Set where
  dryRun : BenchmarkRunMode
  mockRun : BenchmarkRunMode
  syntheticRun : BenchmarkRunMode
  realUnverifiedRun : BenchmarkRunMode
  realHashVerifiedRun : BenchmarkRunMode

data PromotionLevel : Set where
  pipelineOnly : PromotionLevel
  diagnosticOnly : PromotionLevel
  empiricalCandidate : PromotionLevel
  empiricallyPromotable : PromotionLevel

data RunBoundary : Set where
  noMockRunPromotesEmpiricalClaim : RunBoundary
  noSyntheticRunPromotesEmpiricalClaim : RunBoundary
  noUnverifiedArtifactsPromoteEmpiricalClaim : RunBoundary
  noConsumerSufficiencyOverridesRunAuthority : RunBoundary
  noSameTrialOnlySemanticPromotion : RunBoundary

record BenchmarkRunReceipt : Set where
  field
    mode : BenchmarkRunMode
    inputHashesVerified : Bool
    registrationVerified : Bool
    heldOutSplitVerified : Bool
    outputHashVerified : Bool
    sameTrialOnly : Bool
    syntheticObservationsPresent : Bool
    runID : String
    resultHash : String

open BenchmarkRunReceipt public

record RunPromotionAssessment : Set where
  field
    run : BenchmarkRunReceipt
    consumerBundle : Consumer.ConsumerEvidenceBundle
    level : PromotionLevel
    consumerBundleSufficient : Bool
    runAuthoritySufficient : Bool
    promotionAdmissible : Bool
    reading : String

open RunPromotionAssessment public

mockPipelineOnly : PromotionLevel
mockPipelineOnly = pipelineOnly

syntheticDiagnosticOnly : PromotionLevel
syntheticDiagnosticOnly = diagnosticOnly

realUnverifiedCandidateOnly : PromotionLevel
realUnverifiedCandidateOnly = empiricalCandidate

realHashVerifiedEligible : PromotionLevel
realHashVerifiedEligible = empiricallyPromotable

record MockRunNonPromotionWitness : Set where
  field
    run : BenchmarkRunReceipt
    modeIsMock : mode run ≡ mockRun
    promotedEmpiricalClaim : Bool
    promotedEmpiricalClaimIsFalse : promotedEmpiricalClaim ≡ false

open MockRunNonPromotionWitness public

record SyntheticRunNonPromotionWitness : Set where
  field
    run : BenchmarkRunReceipt
    modeIsSynthetic : mode run ≡ syntheticRun
    promotedEmpiricalClaim : Bool
    promotedEmpiricalClaimIsFalse : promotedEmpiricalClaim ≡ false

open SyntheticRunNonPromotionWitness public

record SemanticSameTrialBoundary : Set where
  field
    consumer : Consumer.EvidenceConsumer
    consumerIsSemantic : consumer ≡ Consumer.semanticConsumer
    sameTrialOnly : Bool
    sameTrialOnlyIsTrue : sameTrialOnly ≡ true
    semanticPromotionAdmissible : Bool
    semanticPromotionAdmissibleIsFalse : semanticPromotionAdmissible ≡ false

open SemanticSameTrialBoundary public

canonicalRunBoundaries : List RunBoundary
canonicalRunBoundaries =
  noMockRunPromotesEmpiricalClaim
  ∷ noSyntheticRunPromotesEmpiricalClaim
  ∷ noUnverifiedArtifactsPromoteEmpiricalClaim
  ∷ noConsumerSufficiencyOverridesRunAuthority
  ∷ noSameTrialOnlySemanticPromotion
  ∷ []
