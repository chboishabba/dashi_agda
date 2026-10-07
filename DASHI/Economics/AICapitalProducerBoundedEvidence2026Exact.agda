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
  "capital_spread" directionStage (attributedEvidenceSource Sources.anthropicProfitabilityReuters20261007)
  "Anthropic 2025 revenue USD 4.6B, operating loss USD 8.06B, compute/infrastructure spend USD 7.3B; negative operating-return diagnostic only, not realised ROIC-WACC"
  false false

fundingPressureEvidence : ProducerEvidenceStatus
fundingPressureEvidence = producerEvidenceStatus
  "funding_pressure" pointStage (attributedEvidenceSource Sources.aiCreditReuters20260922)
  "AI-related IG spread about 115 bp versus broad IG about 78 bp; observed premium 37 bp; runtime normalization remains an explicitly declared transform"
  true false

inferenceSpreadEvidence : ProducerEvidenceStatus
inferenceSpreadEvidence = producerEvidenceStatus
  "inference_spread" directionStage (attributedEvidenceSource Sources.vercelGatewaySeptember2026)
  "average platform token price fell 23.2 percent in August; price-side direction only, not quality-adjusted revenue minus marginal serving cost"
  false false

scarcitySpreadEvidence : ProducerEvidenceStatus
scarcitySpreadEvidence = producerEvidenceStatus
  "scarcity_spread" intervalStage (attributedEvidenceSource Sources.vercelGatewaySeptember2026)
  "open-weight token share 56 percent versus spend share 14 percent on Vercel; 42-point platform usage-spend gap, not same-quality global scarcity rent"
  false false

capabilityCompressionEvidence : ProducerEvidenceStatus
capabilityCompressionEvidence = producerEvidenceStatus
  "capability_compression" directionStage (attributedEvidenceSource Sources.vercelGatewaySeptember2026)
  "open-weight majority usage plus falling average token price supports substitution pressure; no declared same-task capability-distance point"
  false false

gpuReplacementEvidence : ProducerEvidenceStatus
gpuReplacementEvidence = producerEvidenceStatus
  "replacement_depreciation" intervalStage (attributedEvidenceSource Sources.gpuCollateralReuters20261001)
  "lenders commonly apply roughly 3-4 year GPU depreciation assumptions; lender-practice interval, not company-specific replacement capex"
  false false

rolloverEvidence : ProducerEvidenceStatus
rolloverEvidence = producerEvidenceStatus
  "rollover_dependence" intervalStage (attributedEvidenceSource Sources.aiBorrowersReuters20260930)
  "AI-related leveraged finance USD 88B and SoftBank reported yields 8.625-9.75 percent; funding interval does not supply same-borrower maturity/refinancing dependence"
  false false

policyBackstopEvidence : ProducerEvidenceStatus
policyBackstopEvidence = producerEvidenceStatus
  "policy_backstop_salience" qualitativeStage (attributedEvidenceSource Sources.fercPJMReuters20260930)
  "FERC required revision/further proceedings on PJM backstop procurement and data-centre cost allocation; establishes policy salience, not normalized probability"
  false false

marketFlipEvidence : ProducerEvidenceStatus
marketFlipEvidence = producerEvidenceStatus
  "market_flip_rate" noEvidenceStage noEvidenceSource
  "no fixed declared AI-linked basket and benchmark series has yet been acquired on one sampling window"
  false false

marketVolEvidence : ProducerEvidenceStatus
marketVolEvidence = producerEvidenceStatus
  "market_vol_stress" noEvidenceStage noEvidenceSource
  "no fixed-window AI-linked volatility series has yet been acquired under the runtime coordinate"
  false false

terminalPayerCoverageEvidence : ProducerEvidenceStatus
terminalPayerCoverageEvidence = producerEvidenceStatus
  "terminal_payer_coverage" noEvidenceStage noEvidenceSource
  "complete aligned independent-terminal-payer revenue provenance is absent; global conductance remains unconstrained"
  false false

revenueVectorEvidence : ProducerEvidenceStatus
revenueVectorEvidence = producerEvidenceStatus
  "revenue_vector_coverage" intervalStage (attributedEvidenceSource Sources.anthropicRevenueVectorReuters20260929)
  "two customers each represented 12 percent of 2025 revenue, fixing 24 percent while 76 percent remains undisclosed"
  false false

------------------------------------------------------------------------
-- Total same-object map from every live residual to its current evidence stage.
------------------------------------------------------------------------

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

stageFor : Time.MissingCapitalProducer → EvidenceStage
stageFor residual = stage (evidenceFor residual)

capitalSpreadDirectionDoesNotClosePoint : pointProducerClosed anthropicCapitalSpreadEvidence ≡ false
capitalSpreadDirectionDoesNotClosePoint = refl

fundingObservationClosesItsDeclaredPoint : pointProducerClosed fundingPressureEvidence ≡ true
fundingObservationClosesItsDeclaredPoint = refl

inferenceDirectionDoesNotCloseMargin : pointProducerClosed inferenceSpreadEvidence ≡ false
inferenceDirectionDoesNotCloseMargin = refl

scarcityIntervalDoesNotCloseRent : pointProducerClosed scarcitySpreadEvidence ≡ false
scarcityIntervalDoesNotCloseRent = refl

capabilityDirectionDoesNotCloseDistance : pointProducerClosed capabilityCompressionEvidence ≡ false
capabilityDirectionDoesNotCloseDistance = refl

gpuDepreciationIntervalDoesNotCloseReplacementCapex : pointProducerClosed gpuReplacementEvidence ≡ false
gpuDepreciationIntervalDoesNotCloseReplacementCapex = refl

policySalienceDoesNotCloseBackstopProbability : pointProducerClosed policyBackstopEvidence ≡ false
policySalienceDoesNotCloseBackstopProbability = refl

rolloverFundingIntervalDoesNotCloseRefinancingDependence : pointProducerClosed rolloverEvidence ≡ false
rolloverFundingIntervalDoesNotCloseRefinancingDependence = refl

marketFlipAbsenceIsExplicit : stageFor Time.marketFlipProducerOpen ≡ noEvidenceStage
marketFlipAbsenceIsExplicit = refl

marketVolAbsenceIsExplicit : stageFor Time.marketVolProducerOpen ≡ noEvidenceStage
marketVolAbsenceIsExplicit = refl

terminalPayerAbsenceIsExplicit : stageFor Time.terminalPayerCoverageOpen ≡ noEvidenceStage
terminalPayerAbsenceIsExplicit = refl

revenueVectorPartialDoesNotCloseCoverage : pointProducerClosed revenueVectorEvidence ≡ false
revenueVectorPartialDoesNotCloseCoverage = refl

boundedEvidenceNeverCreatesTerminalAuthority : promotesCapitalRecoveryAuthority anthropicCapitalSpreadEvidence ≡ false
boundedEvidenceNeverCreatesTerminalAuthority = refl

acquisitionAtlasStillNonPromoting : Source.atlasCreatesAuthority Sources.aiCapitalParetoAcquisitionAtlas ≡ false
acquisitionAtlasStillNonPromoting = Sources.atlasDoesNotCreateAuthority
