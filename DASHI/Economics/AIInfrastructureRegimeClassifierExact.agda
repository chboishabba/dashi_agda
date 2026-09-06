module DASHI.Economics.AIInfrastructureRegimeClassifierExact where

open import DASHI.Core.Prelude
import DASHI.Economics.AIFinancingReflexivityExact as Reflexive
import DASHI.Economics.AITerminalPayerEconomicValidationExact as Terminal
import DASHI.Economics.AIManufacturingChokepointTimescaleExact as Manufacturing
import DASHI.Economics.AIStructuredInfrastructureCommonFactorRiskExact as AIStructured
import DASHI.Economics.AIScalingLawRegimeMonitorExact as ScalingMonitor
import DASHI.Economics.AICriticalInfrastructurePoliticsCrossPollinationExact as Politics
import DASHI.Economics.ReflexiveFlowValidationExact as Econ
import DASHI.Economics.CommonFactorStructuredFinanceExact as Structured
import DASHI.Economics.ManufacturingScarcityTimescaleExact as Scarcity
import DASHI.Economics.UnitEconomicsMarginExact as Unit
import DASHI.Economics.PolicyBackstopCommercialDisciplineExact as Policy
import DASHI.Economics.ComputeScalingUnitEconomicsExact as Scaling

------------------------------------------------------------------------
-- MULTI-AXIS AI INFRASTRUCTURE REGIME CLASSIFIER
--
-- Deliberately not a linear enum and deliberately not `Bubble : Bool`.
-- The axes are logically independent receipts.  A concrete current-regime
-- classification must provide source-backed inhabitants for each promoted axis.
------------------------------------------------------------------------

record AIInfrastructureRegimeVector : Set₁ where
  field
    ExternalCashValidation CircularityIntensity ValuationReflexivity
      LeverageIntensity MarginPressure ManufacturingScarcity PolicyBackstop
      ComputeScalingPressure : Set

    externalCashValidation : ExternalCashValidation
    circularityIntensity   : CircularityIntensity
    valuationReflexivity   : ValuationReflexivity
    leverageIntensity      : LeverageIntensity
    marginPressure         : MarginPressure
    manufacturingScarcity  : ManufacturingScarcity
    policyBackstop         : PolicyBackstop
    computeScalingPressure : ComputeScalingPressure

open AIInfrastructureRegimeVector public

record TechnologicalSuccessSignals : Set₁ where
  field
    CapabilityGrowth UsageGrowth EfficiencyGrowth PhysicalDeployment : Set
    capabilityGrowth : CapabilityGrowth
    usageGrowth      : UsageGrowth
    efficiencyGrowth : EfficiencyGrowth
    physicalDeployment : PhysicalDeployment

open TechnologicalSuccessSignals public

data TechnologicalSuccessImpliesFinancialViabilityPermission : Set where

data RegimeVectorImpliesBubblePermission : Set where

technologicalSuccessDoesNotAutoPromoteToFinancialViability :
  TechnologicalSuccessImpliesFinancialViabilityPermission → ⊥
technologicalSuccessDoesNotAutoPromoteToFinancialViability ()

regimeVectorDoesNotAutoPromoteToBubble :
  RegimeVectorImpliesBubblePermission → ⊥
regimeVectorDoesNotAutoPromoteToBubble ()

-- Cross-owner firewalls kept at the aggregate surface.
markedGainDoesNotCloseExternalCash :
  Econ.MarkedGainImpliesExternalCashPermission → ⊥
markedGainDoesNotCloseExternalCash = Reflexive.markedGainDoesNotCloseExternalCash

highUsageDoesNotClosePositiveUnitEconomics :
  Unit.HighUsageImpliesPositiveUnitEconomicsPermission → ⊥
highUsageDoesNotClosePositiveUnitEconomics =
  Unit.highUsageDoesNotAutoPromoteToPositiveUnitEconomics

scarcityDoesNotCloseDownstreamViability :
  Scarcity.ScarcityRentImpliesDownstreamViabilityPermission → ⊥
scarcityDoesNotCloseDownstreamViability =
  Manufacturing.scarcityRentDoesNotCloseDownstreamViability

projectMultiplicityDoesNotCloseRiskIndependence :
  Structured.ProjectMultiplicityImpliesRiskIndependencePermission → ⊥
projectMultiplicityDoesNotCloseRiskIndependence =
  AIStructured.projectMultiplicityDoesNotCloseRiskIndependence

policySupportDoesNotCloseCommercialViability :
  Policy.PolicySupportImpliesCommercialViabilityPermission → ⊥
policySupportDoesNotCloseCommercialViability =
  Policy.policySupportDoesNotAutoPromoteToCommercialViability

surroundingSignalsDoNotCloseEconomicValidation :
  Terminal.SurroundingSignalsImplyEconomicValidationPermission → ⊥
surroundingSignalsDoNotCloseEconomicValidation =
  Terminal.surroundingSignalsDoNotAutoPromoteToEconomicValidation

computeDeflationDoesNotCloseLowerAggregateDemand :
  Scaling.LowerCostPerTokenImpliesLowerTotalComputeDemandPermission → ⊥
computeDeflationDoesNotCloseLowerAggregateDemand =
  Scaling.lowerCostPerTokenDoesNotAutoPromoteToLowerTotalComputeDemand

historicalScalingFitDoesNotCloseFutureLaw :
  ScalingMonitor.HistoricalFitImpliesUniversalFutureLawPermission → ⊥
historicalScalingFitDoesNotCloseFutureLaw =
  ScalingMonitor.historicalFitDoesNotAutoPromoteToUniversalFutureLaw

criticalInfrastructureSupportDoesNotCloseCommercialViability :
  Policy.PolicySupportImpliesCommercialViabilityPermission → ⊥
criticalInfrastructureSupportDoesNotCloseCommercialViability =
  Politics.policySupportDoesNotCloseCommercialViability
