module DASHI.Economics.AIEntanglementSourceWrittenChecks2026 where

open import DASHI.Core.Prelude

import DASHI.Economics.AICapitalRecoveryEntanglement2026Exact as Capital
import DASHI.Economics.AnthropicProspectusCapitalRecovery2026Exact as Anthropic
import DASHI.Economics.AICerebrasChinaOpenWeightCalibration2026Exact as Competitive
import DASHI.Economics.AISlimMoECostCompression2026Exact as SlimMoE
import DASHI.Economics.AIOpenWeightMarketTransition2026Exact as OpenTransition
import DASHI.Economics.AIGeometricMarketStressOperator2026Exact as Geometry
import DASHI.Economics.AIPolicyBackstopCommercialMoat2026Exact as Policy
import DASHI.Economics.AIAntitrustCompetitiveIndependence2026Exact as Antitrust

------------------------------------------------------------------------
-- Source-written reduction checks.  These are deliberately small `refl`
-- endpoints: if a future edit silently promotes a candidate/source receipt,
-- the aggregation target should stop reducing as recorded here.
------------------------------------------------------------------------

cerebrasAcquisitionNotEstablished :
  Capital.provesBubble Capital.cerebrasOpenAIIsPartnershipNotAcquisition ≡ false
cerebrasAcquisitionNotEstablished = refl

cerebrasAntitrustNotEstablished :
  Capital.provesAntitrustLiability Capital.cerebrasOpenAIIsPartnershipNotAcquisition ≡ false
cerebrasAntitrustNotEstablished = refl

broadcomLoopNotCircularRevenueTheorem :
  Anthropic.provesCircularRevenue Anthropic.anthropicBroadcomLoop ≡ false
broadcomLoopNotCircularRevenueTheorem = refl

broadcomLoopNotFraudTheorem :
  Anthropic.provesFraud Anthropic.anthropicBroadcomLoop ≡ false
broadcomLoopNotFraudTheorem = refl

openWeightFlipNotGlobalMarketTheorem :
  OpenTransition.exactGlobalEightyTwentyFlipEstablished
    OpenTransition.sourceBoundedOpenWeightFlip
  ≡ false
openWeightFlipNotGlobalMarketTheorem = refl

slimMoEDoesNotCloseNoMoat :
  SlimMoE.provesFrontierClosedNoMoat SlimMoE.canonicalSlimMoEReceipt ≡ false
slimMoEDoesNotCloseNoMoat = refl

chinaCompetitiveCalibrationDoesNotCloseNoMoat :
  Competitive.provesClosedModelNoMoat
    Competitive.candidateCompetitiveSubstitution2026
  ≡ false
chinaCompetitiveCalibrationDoesNotCloseNoMoat = refl

jointStressPolicySalienceIsCandidatePositive :
  Geometry.policyBackstopSalienceRising Geometry.candidateOctober2026JointStress
  ≡ true
jointStressPolicySalienceIsCandidatePositive = refl

policyCausalCaptureStillOpen :
  Policy.causalCaptureEstablished Policy.candidateBackstopTransition ≡ false
policyCausalCaptureStillOpen = refl

antitrustLegalConclusionStillOpen :
  Antitrust.legalAntitrustViolationEstablished
    Antitrust.candidateHyperscalerLabEntanglement2026
  ≡ false
antitrustLegalConclusionStillOpen = refl
