module DASHI.Economics.AIScalingEvidenceAuthorityCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.NeuralProposalEvidenceBoundaryExact as Neural
import DASHI.Economics.AIScalingLawRegimeMonitorExact as Monitor
import DASHI.Economics.ComputeScalingUnitEconomicsExact as Scaling

------------------------------------------------------------------------
-- AI SCALING EVIDENCE / AUTHORITY CROSS-POLLINATION
--
-- Reuses the existing neural-proposal discipline: a model/benchmark output may
-- contribute evidence pressure but does not itself promote ontology truth.
-- Here, benchmark and vendor observations may update a scaling hypothesis but
-- cannot directly promote future-law or economic-value conclusions.
------------------------------------------------------------------------

data ScalingEvidenceRole : Set where
  vendorBenchmark
  independentBenchmark
  productionTelemetry
  customerWorkload
  accountingDisclosure
  marketPriceObservation
  : ScalingEvidenceRole

record ScalingEvidenceReceipt : Set where
  constructor scalingEvidenceReceipt
  field
    role : ScalingEvidenceRole
    sourceReference : String
    Metric : Set
    metric : Metric
    sameWorkload : Set
    sameMetricDefinition : Set
    sameHardwareOrExplicitTransport : Set

open ScalingEvidenceReceipt public

record ScalingHypothesisPressure : Set₁ where
  constructor scalingHypothesisPressure
  field
    evidence : ScalingEvidenceReceipt
    priorHypothesis : Monitor.ScalingLawHypothesis
    Pressure : Set
    pressure : Pressure
    pressureReference : String

open ScalingHypothesisPressure public

record EconomicScalingPromotion : Set₁ where
  constructor economicScalingPromotion
  field
    evidencePressure : ScalingHypothesisPressure
    IndependentEconomicReceipt : Set
    independentEconomicReceipt : IndependentEconomicReceipt
    promotionReference : String

open EconomicScalingPromotion public

data BenchmarkImpliesEconomicValuePermission : Set where

data VendorClaimImpliesIndependentBenchmarkPermission : Set where

data ScalingPressureImpliesFutureLawPermission : Set where

data ProductionTelemetryImpliesTerminalPayerViabilityPermission : Set where

benchmarkDoesNotAutoPromoteToEconomicValue :
  BenchmarkImpliesEconomicValuePermission → ⊥
benchmarkDoesNotAutoPromoteToEconomicValue ()

vendorClaimDoesNotAutoPromoteToIndependentBenchmark :
  VendorClaimImpliesIndependentBenchmarkPermission → ⊥
vendorClaimDoesNotAutoPromoteToIndependentBenchmark ()

scalingPressureDoesNotAutoPromoteToFutureLaw :
  ScalingPressureImpliesFutureLawPermission → ⊥
scalingPressureDoesNotAutoPromoteToFutureLaw ()

productionTelemetryDoesNotAutoPromoteToTerminalPayerViability :
  ProductionTelemetryImpliesTerminalPayerViabilityPermission → ⊥
productionTelemetryDoesNotAutoPromoteToTerminalPayerViability ()

-- Canonical AI evidence-authority donor retained explicitly.
neuralEvidenceBoundary : Neural.NeuralEvidenceBoundary
neuralEvidenceBoundary = Neural.canonicalNeuralEvidenceBoundary

neuralProposalCannotPromoteOntologyTruth :
  Neural.Pressure.TypePressurePromotionPermission → ⊥
neuralProposalCannotPromoteOntologyTruth =
  Neural.neuralPressureCannotPromoteOntologyType

scalingCapabilityDoesNotCloseEconomicValue :
  Scaling.HigherCapabilityImpliesHigherEconomicValuePermission → ⊥
scalingCapabilityDoesNotCloseEconomicValue =
  Scaling.higherCapabilityDoesNotAutoPromoteToHigherEconomicValue
