module DASHI.Economics.AICapitalProducerBoundedEvidence2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Economics.AICapitalParetoAcquisitionSourceAtlas2026Exact as Sources

------------------------------------------------------------------------
-- BOUNDED / DIRECTIONAL PRODUCER EVIDENCE
--
-- A source may close a direction, interval, or qualitative salience fact while
-- the point-valued runtime producer remains open.  This owner makes that
-- intermediate evidence state explicit so partial acquisition cannot silently
-- become a numeric producer or terminal capital-recovery authority.
------------------------------------------------------------------------

data EvidenceStage : Set where
  noEvidenceStage : EvidenceStage
  qualitativeStage : EvidenceStage
  directionStage : EvidenceStage
  intervalStage : EvidenceStage
  pointStage : EvidenceStage

record ProducerEvidenceStatus : Set where
  constructor producerEvidenceStatus
  field
    producerReference : String
    stage : EvidenceStage
    diagnosticReference : String
    pointProducerClosed : Bool
    promotesCapitalRecoveryAuthority : Bool

open ProducerEvidenceStatus public

anthropicCapitalSpreadEvidence : ProducerEvidenceStatus
anthropicCapitalSpreadEvidence = producerEvidenceStatus
  "capital_spread"
  directionStage
  "Reuters 2026-10-07: Anthropic 2025 revenue USD 4.6B, operating loss USD 8.06B, compute/infrastructure spend USD 7.3B; negative operating-return diagnostic only, not realised ROIC-WACC"
  false false

fundingPressureEvidence : ProducerEvidenceStatus
fundingPressureEvidence = producerEvidenceStatus
  "funding_pressure"
  pointStage
  "Reuters 2026-09-22: AI-related IG spread about 115 bp versus broad IG about 78 bp; observed premium 37 bp"
  true false

gpuReplacementEvidence : ProducerEvidenceStatus
gpuReplacementEvidence = producerEvidenceStatus
  "replacement_depreciation"
  intervalStage
  "Reuters 2026-10-01: lenders commonly apply roughly 3-4 year GPU depreciation assumptions; lender-practice interval, not company-specific replacement capex"
  false false

openWeightScarcityCapabilityEvidence : ProducerEvidenceStatus
openWeightScarcityCapabilityEvidence = producerEvidenceStatus
  "scarcity_capability"
  intervalStage
  "Vercel August 2026 platform telemetry: open-weight token share 56 percent and spend share 14 percent; 42 percentage-point platform usage-spend gap, not global scarcity rent"
  false false

policyBackstopEvidence : ProducerEvidenceStatus
policyBackstopEvidence = producerEvidenceStatus
  "policy_backstop_salience"
  qualitativeStage
  "Reuters 2026-09-30: FERC required revision/further proceedings on PJM backstop procurement and data-centre cost allocation amid reported 6800 MW shortfall; establishes salience, not normalized probability"
  false false

rolloverEvidence : ProducerEvidenceStatus
rolloverEvidence = producerEvidenceStatus
  "rollover_dependence"
  intervalStage
  "Reuters 2026-09-30: AI-related leveraged finance USD 88B and SoftBank reported yields 8.625-9.75 percent; funding interval does not supply same-borrower maturity/refinancing dependence"
  false false

------------------------------------------------------------------------
-- Exact fail-closed reductions.
------------------------------------------------------------------------

capitalSpreadDirectionDoesNotClosePoint :
  pointProducerClosed anthropicCapitalSpreadEvidence ≡ false
capitalSpreadDirectionDoesNotClosePoint = refl

fundingObservationClosesItsDeclaredPoint :
  pointProducerClosed fundingPressureEvidence ≡ true
fundingObservationClosesItsDeclaredPoint = refl

gpuDepreciationIntervalDoesNotCloseReplacementCapex :
  pointProducerClosed gpuReplacementEvidence ≡ false
gpuDepreciationIntervalDoesNotCloseReplacementCapex = refl

policySalienceDoesNotCloseBackstopProbability :
  pointProducerClosed policyBackstopEvidence ≡ false
policySalienceDoesNotCloseBackstopProbability = refl

rolloverFundingIntervalDoesNotCloseRefinancingDependence :
  pointProducerClosed rolloverEvidence ≡ false
rolloverFundingIntervalDoesNotCloseRefinancingDependence = refl

boundedEvidenceNeverCreatesTerminalAuthority :
  promotesCapitalRecoveryAuthority anthropicCapitalSpreadEvidence ≡ false
boundedEvidenceNeverCreatesTerminalAuthority = refl

acquisitionAtlasStillNonPromoting :
  Source.atlasCreatesAuthority Sources.aiCapitalParetoAcquisitionAtlas ≡ false
acquisitionAtlasStillNonPromoting = Sources.atlasDoesNotCreateAuthority
