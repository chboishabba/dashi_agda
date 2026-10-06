module DASHI.Economics.AICapitalRecoveryEntanglement2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Economics.ReflexiveFlowValidationExact as Flow
import DASHI.Economics.AIFinancingReflexivityExact as Reflexive
import DASHI.Economics.AITerminalPayerEconomicValidationExact as Terminal
import DASHI.Economics.AIEnergyInfrastructureFundingStress2026Exact as Funding
import DASHI.Economics.AIUbiquityRentInversionExact as Ubiquity

------------------------------------------------------------------------
-- AI CAPITAL-RECOVERY / ENTANGLEMENT CALIBRATION, OCTOBER 2026
--
-- This owner formalises the joint state discussed across the AI-capex,
-- circular-financing, open-weight substitution, funding-stress and China
-- calibration lanes.  It deliberately separates:
--   * named source receipts,
--   * graph/topology witnesses,
--   * commercial-margin / capital-recovery observables,
--   * policy-backstop / strategic-value hypotheses.
--
-- No named-company observation below automatically proves fraud, insolvency,
-- antitrust liability, regulatory capture, a bubble, or an inevitable crash.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Source receipts
------------------------------------------------------------------------

cerebrasOpenAIPartnershipSource : Source.AttributedSource
cerebrasOpenAIPartnershipSource = Source.mkNoDOISource
  "OpenAI"
  "OpenAI partners with Cerebras"
  "OpenAI"
  "2026-01-14"
  "https://openai.com/index/cerebras-partnership/"
  Source.primarySource
  "OpenAI announced a partnership, not an acquisition: Cerebras will add 750 MW of low-latency inference capacity to OpenAI's platform in tranches through 2028."
  Source.publicAttribution

cerebrasQ12026Source : Source.AttributedSource
cerebrasQ12026Source = Source.mkNoDOISource
  "Cerebras Systems"
  "Cerebras Systems Announces Strong First Quarter 2026 Results"
  "Cerebras investor relations"
  "2026-06-23"
  "https://investors.cerebras.ai/news-releases/news-release-details/cerebras-systems-announces-strong-first-quarter-2026-results"
  Source.primarySource
  "Primary-source carrier for the >USD 20 billion 750 MW OpenAI agreement, AWS partnership and Cerebras operating results."
  Source.publicAttribution

softbankCreditReuters2026 : Source.AttributedSource
softbankCreditReuters2026 = Source.mkNoDOISource
  "Reuters"
  "AI borrowers face tough sell in risky corners of US credit market"
  "Reuters"
  "2026-09-30"
  "https://www.reuters.com/legal/transactional/ai-borrowers-face-tough-sell-risky-corners-us-credit-market-2026-09-30/"
  Source.newsSource
  "Secondary source for AI leveraged-finance growth and SoftBank borrowing yields reported in the 8.625%-9.75% range; this is evidence of funding stress, not a universal 10% minimum hurdle rule."
  Source.publicAttribution

kiloOpenWeightShare2026 : Source.AttributedSource
kiloOpenWeightShare2026 = Source.mkNoDOISource
  "Kilo"
  "Open Weights Is All You Need"
  "Kilo AI"
  "2026-07"
  "https://blog.kilo.ai/p/open-weights-is-all-you-need"
  Source.primarySource
  "Platform-specific usage observation: open-weight models represented 79.1% of token usage on Kilo in the week of 20 July 2026; this is not a global market-share theorem."
  Source.publicAttribution

vercelOpenWeightShare2026 : Source.AttributedSource
vercelOpenWeightShare2026 = Source.mkNoDOISource
  "Vercel"
  "AI Gateway Production Index — July 2026"
  "Vercel"
  "2026-07-13"
  "https://vercel.com/blog/ai-gateway-production-index-july-2026"
  Source.primarySource
  "Platform-specific production-router observation: open-weight models were 29% of June 2026 token volume but under 4% of spend, supporting a usage-versus-rent separation."
  Source.publicAttribution

------------------------------------------------------------------------
-- Bounded empirical observations
------------------------------------------------------------------------

record BoundedObservation : Set where
  constructor boundedObservation
  field
    subject : String
    reading : String
    source : Source.AttributedSource
    provesFraud : Bool
    provesInsolvency : Bool
    provesBubble : Bool
    provesAntitrustLiability : Bool
    provesRegulatoryCapture : Bool

open BoundedObservation public

cerebrasOpenAIIsPartnershipNotAcquisition : BoundedObservation
cerebrasOpenAIIsPartnershipNotAcquisition = boundedObservation
  "OpenAI / Cerebras"
  "Current primary-source evidence supports a large compute partnership; it does not support the proposition that OpenAI acquired Cerebras."
  cerebrasOpenAIPartnershipSource
  false false false false false

softbankFundingStressObservation : BoundedObservation
softbankFundingStressObservation = boundedObservation
  "SoftBank / AI leveraged finance"
  "Reported borrowing yields in the high-single-digit to near-10% range are evidence that marginal AI-linked funding can be expensive."
  softbankCreditReuters2026
  false false false false false

kiloOpenWeightUsageObservation : BoundedObservation
kiloOpenWeightUsageObservation = boundedObservation
  "Kilo production token mix"
  "Open-weight models reached 79.1% of platform token usage in the cited week, while the source itself does not establish global AI usage share."
  kiloOpenWeightShare2026
  false false false false false

vercelUsageSpendDivergenceObservation : BoundedObservation
vercelUsageSpendDivergenceObservation = boundedObservation
  "Vercel AI Gateway"
  "Open-weight models represented a materially larger share of token volume than spend, consistent with lower proprietary rent per token on that platform."
  vercelOpenWeightShare2026
  false false false false false

------------------------------------------------------------------------
-- Multiplex economic graph coordinates
------------------------------------------------------------------------

data FlowChannel : Set where
  equity capital debt guarantee hardware cloud services revenue
    valuationExposure policySupport : FlowChannel

record MultiplexEdge : Set where
  constructor multiplexEdge
  field
    from : String
    to : String
    channel : FlowChannel
    sourceBounded : Bool
    independentTerminalCash : Bool

open MultiplexEdge public

record EntanglementCoordinates : Set where
  constructor entanglementCoordinates
  field
    internalCycleWeight : Trit
    supplierFinancedDemand : Trit
    customerSupplierOwnershipOverlap : Trit
    customerConcentration : Trit
    terminalPayerConductance : Trit
    fundingCostStress : Trit
    rolloverDependence : Trit

open EntanglementCoordinates public

-- Candidate calibration only.  "neg" terminal conductance means weak / not
-- established independent terminal-flow evidence, not literal negative cash.
candidateOctober2026Entanglement : EntanglementCoordinates
candidateOctober2026Entanglement =
  entanglementCoordinates pos pos pos pos neg pos pos

------------------------------------------------------------------------
-- Crack-spread analogues
------------------------------------------------------------------------

record AIInferenceCrackSpread : Set₁ where
  field
    RevenuePerQualityUnit : Set
    MarginalInferenceCostPerQualityUnit : Set
    inferenceSpread : RevenuePerQualityUnit → MarginalInferenceCostPerQualityUnit → Set

record AICapitalCrackSpread : Set₁ where
  field
    RealisedROIC : Set
    WeightedFundingCost : Set
    capitalSpread : RealisedROIC → WeightedFundingCost → Set

record AIScarcityRentSpread : Set₁ where
  field
    ClosedPricePerQualityUnit : Set
    OpenSubstitutePricePerQualityUnit : Set
    scarcitySpread : ClosedPricePerQualityUnit → OpenSubstitutePricePerQualityUnit → Set

-- These are interfaces, not numeric claims.  Concrete owners must choose a
-- quality-normalisation and source the corresponding price/cost observations.

data TokenPriceImpliesQualityAdjustedSpreadPermission : Set where
data PositiveGrossMarginImpliesPositiveCapitalSpreadPermission : Set where
data HighClosedModelPriceImpliesProtectedScarcityRentPermission : Set where

tokenPriceDoesNotAutoCloseQualityAdjustedSpread :
  TokenPriceImpliesQualityAdjustedSpreadPermission → ⊥
tokenPriceDoesNotAutoCloseQualityAdjustedSpread ()

positiveGrossMarginDoesNotAutoCloseCapitalSpread :
  PositiveGrossMarginImpliesPositiveCapitalSpreadPermission → ⊥
positiveGrossMarginDoesNotAutoCloseCapitalSpread ()

highClosedPriceDoesNotAutoCloseProtectedScarcityRent :
  HighClosedModelPriceImpliesProtectedScarcityRentPermission → ⊥
highClosedPriceDoesNotAutoCloseProtectedScarcityRent ()

------------------------------------------------------------------------
-- Two-geometry state: financial entanglement vs capability substitution
------------------------------------------------------------------------

record FinancialGeometryState : Set where
  constructor financialGeometryState
  field
    connectivityRising : Bool
    cycleWeightRising : Bool
    fundingHurdleRising : Bool
    terminalConductanceStrong : Bool

record CapabilityGeometryState : Set where
  constructor capabilityGeometryState
  field
    openClosedCapabilityDistanceFalling : Bool
    openWeightUsageRising : Bool
    inferenceUnitCostFalling : Bool
    localOrDistributedServingFeasible : Bool

record TwoGeometryCapitalRecoveryState : Set where
  constructor twoGeometryCapitalRecoveryState
  field
    finance : FinancialGeometryState
    capability : CapabilityGeometryState
    sunkCapitalRecoveryAutomaticallyImproves : Bool
    sunkCapitalRecoveryAutomaticallyImprovesIsFalse :
      sunkCapitalRecoveryAutomaticallyImproves ≡ false

candidateTwoGeometryState2026 : TwoGeometryCapitalRecoveryState
candidateTwoGeometryState2026 = twoGeometryCapitalRecoveryState
  (financialGeometryState true true true false)
  (capabilityGeometryState true true true true)
  false refl

------------------------------------------------------------------------
-- Commercial-moat -> strategic/policy-backstop hypothesis
------------------------------------------------------------------------

record MoatDecomposition : Set where
  constructor moatDecomposition
  field
    modelWeightScarcity : Trit
    distributionIntegration : Trit
    enterpriseCompliance : Trit
    proprietaryDataFeedback : Trit
    capitalScale : Trit
    nationalSecurityDesignation : Trit
    policyBackstop : Trit

open MoatDecomposition public

record StrategicBackstopTransitionHypothesis : Set where
  constructor strategicBackstopTransitionHypothesis
  field
    commercialScarcityRentFalling : Bool
    sunkCapitalExposureRising : Bool
    strategicImportanceRising : Bool
    policyBackstopProbabilityRising : Bool
    sourceBackedAsCausalTransition : Bool

-- This is deliberately *not* promoted to a factual causal claim.  It records
-- the testable hypothesis discussed in the political-economy lane.
candidateCommercialToStrategicMoatHypothesis : StrategicBackstopTransitionHypothesis
candidateCommercialToStrategicMoatHypothesis =
  strategicBackstopTransitionHypothesis true true true true false

data StrategicImportanceImpliesRegulatoryCapturePermission : Set where
data SunkCapitalImpliesTooBigToFailPermission : Set where
data OpenWeightsImplyNoCommercialMoatPermission : Set where

strategicImportanceDoesNotAutoProveRegulatoryCapture :
  StrategicImportanceImpliesRegulatoryCapturePermission → ⊥
strategicImportanceDoesNotAutoProveRegulatoryCapture ()

sunkCapitalDoesNotAutoProveTooBigToFail :
  SunkCapitalImpliesTooBigToFailPermission → ⊥
sunkCapitalDoesNotAutoProveTooBigToFail ()

openWeightsDoNotAutoProveNoCommercialMoat :
  OpenWeightsImplyNoCommercialMoatPermission → ⊥
openWeightsDoNotAutoProveNoCommercialMoat ()

------------------------------------------------------------------------
-- Existing-owner bridges
------------------------------------------------------------------------

fundingClockStillRequiresRealisedReturn : Funding.FundingClock
fundingClockStillRequiresRealisedReturn = Funding.candidateBurryStyleFundingClock

ubiquityRentInversionBoundary : Ubiquity.TechnologySuccessCapitalLossBoundary
ubiquityRentInversionBoundary = Ubiquity.canonicalTechnologySuccessCapitalLossBoundary

markedGainStillDoesNotCloseExternalCash :
  Flow.MarkedGainImpliesExternalCashPermission → ⊥
markedGainStillDoesNotCloseExternalCash = Reflexive.markedGainDoesNotCloseExternalCash

surroundingSignalsStillDoNotCloseEconomicValidation :
  Terminal.SurroundingSignalsImplyEconomicValidationPermission → ⊥
surroundingSignalsStillDoNotCloseEconomicValidation =
  Terminal.surroundingSignalsDoNotAutoPromoteToEconomicValidation
