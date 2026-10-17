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
-- Source receipts, graph/topology witnesses, margin/capital-recovery
-- observables and policy hypotheses remain distinct.  No named-company
-- observation automatically proves fraud, insolvency, antitrust liability,
-- regulatory capture, a bubble or an inevitable crash.
------------------------------------------------------------------------

primaryPublicationKind : Source.SourceKind
primaryPublicationKind = Source.namedSourceKind "primary company publication"

platformTelemetryKind : Source.SourceKind
platformTelemetryKind = Source.namedSourceKind "primary platform telemetry"

cerebrasOpenAIPartnershipSource : Source.AttributedSource
cerebrasOpenAIPartnershipSource = Source.mkNoDOISource
  "OpenAI"
  "OpenAI partners with Cerebras"
  "OpenAI"
  "2026-01-14"
  "https://openai.com/index/cerebras-partnership/"
  primaryPublicationKind
  "primary carrier for a 750 MW partnership; does not establish an acquisition"
  Source.publicAttribution

cerebrasQ12026Source : Source.AttributedSource
cerebrasQ12026Source = Source.mkNoDOISource
  "Cerebras Systems"
  "Cerebras Systems Announces Strong First Quarter 2026 Results"
  "Cerebras investor relations"
  "2026-06-23"
  "https://investors.cerebras.ai/news-releases/news-release-details/cerebras-systems-announces-strong-first-quarter-2026-results"
  primaryPublicationKind
  "primary carrier for the >USD 20 billion 750 MW OpenAI agreement, AWS partnership and company-reported operating results"
  Source.publicAttribution

softbankCreditReuters2026 : Source.AttributedSource
softbankCreditReuters2026 = Source.mkNoDOISource
  "Reuters"
  "AI borrowers face tough sell in risky corners of US credit market"
  "Reuters"
  "2026-09-30"
  "https://www.reuters.com/legal/transactional/ai-borrowers-face-tough-sell-risky-corners-us-credit-market-2026-09-30/"
  Source.newsSource
  "secondary carrier for AI leveraged-finance growth and reported SoftBank yields of 8.625%-9.75%; not a universal 10% minimum rule"
  Source.publicAttribution

kiloOpenWeightShare2026 : Source.AttributedSource
kiloOpenWeightShare2026 = Source.mkNoDOISource
  "Kilo"
  "Open Weights Is All You Need"
  "Kilo AI"
  "2026-07"
  "https://blog.kilo.ai/p/open-weights-is-all-you-need"
  platformTelemetryKind
  "platform-local observation: 79.1% open-weight token usage in the week of 20 July 2026; not global market share"
  Source.publicAttribution

vercelOpenWeightShare2026 : Source.AttributedSource
vercelOpenWeightShare2026 = Source.mkNoDOISource
  "Vercel"
  "AI Gateway Production Index — July 2026"
  "Vercel"
  "2026-07-13"
  "https://vercel.com/blog/ai-gateway-production-index-july-2026"
  platformTelemetryKind
  "platform-local observation: open weights were 29% of June 2026 token volume and under 4% of spend; not global market share"
  Source.publicAttribution

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
  "High-single-digit to near-10% reported borrowing yields support a funding-stress coordinate."
  softbankCreditReuters2026
  false false false false false

kiloOpenWeightUsageObservation : BoundedObservation
kiloOpenWeightUsageObservation = boundedObservation
  "Kilo production token mix"
  "Open weights reached 79.1% of platform token usage in the cited week; global share is not established."
  kiloOpenWeightShare2026
  false false false false false

vercelUsageSpendDivergenceObservation : BoundedObservation
vercelUsageSpendDivergenceObservation = boundedObservation
  "Vercel AI Gateway"
  "Open-weight token share materially exceeded spend share in the cited window."
  vercelOpenWeightShare2026
  false false false false false

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

candidateOctober2026Entanglement : EntanglementCoordinates
candidateOctober2026Entanglement =
  entanglementCoordinates pos pos pos pos neg pos pos

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

record StrategicBackstopTransitionHypothesis : Set where
  constructor strategicBackstopTransitionHypothesis
  field
    commercialScarcityRentFalling : Bool
    sunkCapitalExposureRising : Bool
    strategicImportanceRising : Bool
    policyBackstopProbabilityRising : Bool
    sourceBackedAsCausalTransition : Bool

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
