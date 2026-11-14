module DASHI.Economics.AICapitalProducerBoundedEvidence2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Economics.AICapitalParetoAcquisitionSourceAtlas2026Exact as Sources
import DASHI.Economics.AICapitalObservedStateTimeSeries2026Exact as Time

data EvidenceStage : Set where
  noEvidenceStage : EvidenceStage
  qualitativeStage : EvidenceStage
  directionStage : EvidenceStage
  intervalStage : EvidenceStage
  pointStage : EvidenceStage

data EvidenceSource : Set where
  noEvidenceSource : EvidenceSource
  attributedEvidenceSource : Source.AttributedSource → EvidenceSource

record ProducerEvidenceStatus : Set where
  constructor producerEvidenceStatus
  field
    producerReference : String
    stage : EvidenceStage
    evidenceSource : EvidenceSource
    diagnosticReference : String
    pointProducerClosed : Bool
    promotesCapitalRecoveryAuthority : Bool

open ProducerEvidenceStatus public

anthropicCapitalSpreadEvidence : ProducerEvidenceStatus
anthropicCapitalSpreadEvidence = producerEvidenceStatus
  "capital_spread" directionStage
  (attributedEvidenceSource Sources.anthropicProfitabilityReuters20261007)
  "negative operating-return diagnostic only, not realised ROIC-WACC"
  false false

fundingPressureEvidence : ProducerEvidenceStatus
fundingPressureEvidence = producerEvidenceStatus
  "funding_pressure" pointStage
  (attributedEvidenceSource Sources.aiCreditReuters20260922)
  "115 bp AI-related IG versus 78 bp broad IG; declared funding-pressure point only"
  true false

inferenceSpreadEvidence : ProducerEvidenceStatus
inferenceSpreadEvidence = producerEvidenceStatus
  "inference_spread" directionStage
  (attributedEvidenceSource Sources.vercelGatewaySeptember2026)
  "average platform token price fell 23.2 percent; marginal serving cost and quality-adjusted margin absent"
  false false

scarcitySpreadEvidence : ProducerEvidenceStatus
scarcitySpreadEvidence = producerEvidenceStatus
  "scarcity_spread" intervalStage
  (attributedEvidenceSource Sources.vercelGatewaySeptember2026)
  "56 percent open-weight token share versus 14 percent spend share; not same-quality global scarcity rent"
  false false

capabilityCompressionEvidence : ProducerEvidenceStatus
capabilityCompressionEvidence = producerEvidenceStatus
  "capability_compression" directionStage
  (attributedEvidenceSource Sources.vercelGatewaySeptember2026)
  "open-weight majority usage plus falling price supports substitution direction; capability-distance point absent"
  false false

gpuReplacementEvidence : ProducerEvidenceStatus
gpuReplacementEvidence = producerEvidenceStatus
  "replacement_depreciation" intervalStage
  (attributedEvidenceSource Sources.gpuCollateralReuters20261001)
  "roughly 3-4 year lender GPU depreciation horizon; entity-specific replacement capex absent"
  false false

rolloverEvidence : ProducerEvidenceStatus
rolloverEvidence = producerEvidenceStatus
  "rollover_dependence" intervalStage
  (attributedEvidenceSource Sources.aiBorrowersReuters20260930)
  "high funding yields without same-borrower maturity/refinancing schedule"
  false false

policyBackstopEvidence : ProducerEvidenceStatus
policyBackstopEvidence = producerEvidenceStatus
  "policy_backstop_salience" qualitativeStage
  (attributedEvidenceSource Sources.fercPJMReuters20260930)
  "grid-policy salience established; normalized backstop probability absent"
  false false

marketFlipEvidence : ProducerEvidenceStatus
marketFlipEvidence = producerEvidenceStatus
  "market_flip_rate" noEvidenceStage noEvidenceSource
  "fixed comparable AI-linked market series not yet acquired"
  false false

marketVolEvidence : ProducerEvidenceStatus
marketVolEvidence = producerEvidenceStatus
  "market_vol_stress" noEvidenceStage noEvidenceSource
  "fixed-window AI-linked volatility series not yet acquired"
  false false

terminalPayerCoverageEvidence : ProducerEvidenceStatus
terminalPayerCoverageEvidence = producerEvidenceStatus
  "terminal_payer_coverage" noEvidenceStage noEvidenceSource
  "aligned independent-terminal-payer provenance absent"
  false false

revenueVectorEvidence : ProducerEvidenceStatus
revenueVectorEvidence = producerEvidenceStatus
  "revenue_vector_coverage" intervalStage
  (attributedEvidenceSource Sources.anthropicRevenueVectorReuters20260929)
  "two 12-percent customers fix 24 percent of 2025 revenue; 76 percent unresolved"
  false false

persistenceTrajectoryEvidence : ProducerEvidenceStatus
persistenceTrajectoryEvidence = producerEvidenceStatus
  "persistence_trajectory" noEvidenceStage noEvidenceSource
  "one current comparable X_t cannot establish persistence; acquire another state under identical comparison definitions"
  false false

evidenceFor : Time.MissingCapitalProducer → ProducerEvidenceStatus
evidenceFor Time.capitalSpreadProducerOpen = anthropicCapitalSpreadEvidence
evidenceFor Time.inferenceSpreadProducerOpen = inferenceSpreadEvidence
evidenceFor Time.scarcitySpreadProducerOpen = scarcitySpreadEvidence
evidenceFor Time.capabilityCompressionProducerOpen = capabilityCompressionEvidence
evidenceFor Time.replacementDepreciationProducerOpen = gpuReplacementEvidence
evidenceFor Time.rolloverProducerOpen = rolloverEvidence
evidenceFor Time.policyBackstopProducerOpen = policyBackstopEvidence
evidenceFor Time.marketFlipProducerOpen = marketFlipEvidence
evidenceFor Time.marketVolProducerOpen = marketVolEvidence
evidenceFor Time.terminalPayerCoverageOpen = terminalPayerCoverageEvidence
evidenceFor Time.revenueVectorCoverageOpen = revenueVectorEvidence
evidenceFor Time.persistenceTrajectoryOpen = persistenceTrajectoryEvidence

stageFor : Time.MissingCapitalProducer → EvidenceStage
stageFor residual = stage (evidenceFor residual)

capitalSpreadDirectionDoesNotClosePoint :
  pointProducerClosed anthropicCapitalSpreadEvidence ≡ false
capitalSpreadDirectionDoesNotClosePoint = refl

fundingObservationClosesItsDeclaredPoint :
  pointProducerClosed fundingPressureEvidence ≡ true
fundingObservationClosesItsDeclaredPoint = refl

marketFlipAbsenceIsExplicit :
  stageFor Time.marketFlipProducerOpen ≡ noEvidenceStage
marketFlipAbsenceIsExplicit = refl

marketVolAbsenceIsExplicit :
  stageFor Time.marketVolProducerOpen ≡ noEvidenceStage
marketVolAbsenceIsExplicit = refl

terminalPayerAbsenceIsExplicit :
  stageFor Time.terminalPayerCoverageOpen ≡ noEvidenceStage
terminalPayerAbsenceIsExplicit = refl

persistenceAbsenceIsExplicit :
  stageFor Time.persistenceTrajectoryOpen ≡ noEvidenceStage
persistenceAbsenceIsExplicit = refl

boundedEvidenceNeverCreatesTerminalAuthority :
  promotesCapitalRecoveryAuthority anthropicCapitalSpreadEvidence ≡ false
boundedEvidenceNeverCreatesTerminalAuthority = refl

acquisitionAtlasStillNonPromoting :
  Source.atlasCreatesAuthority Sources.aiCapitalParetoAcquisitionAtlas ≡ false
acquisitionAtlasStillNonPromoting = Sources.atlasDoesNotCreateAuthority
