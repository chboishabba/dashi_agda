module DASHI.Physics.YangMills.BalabanClayGate4FiveActivityEngineOwnershipExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; _+_; _*_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4FiveActivityTenthToHalfExact as Allocation

------------------------------------------------------------------------
-- Distinct analytic ownership of the five H-R_beta activity channels.
--
-- The R-operation and localization sources do not prove the determinant,
-- chart, or gauge channels automatically. Each activity receives a named
-- engine and its own Delta/10 estimate before the exact half allocation.
------------------------------------------------------------------------

record FiveActivityAnalyticEngines
    (order : Allocation.RationalAdditiveOrder) : Set₁ where
  field
    delta determinant interaction chart gauge localization total : ℚ

    totalMeaning :
      total
      ≡ determinant
        + (interaction + (chart + (gauge + localization)))

    RelativeSpectrumTraceLog : Set
    NormalizedTaylorInteraction : Set
    BishopHaarChartControl : Set
    BackgroundGaugeNormalInverseControl : Set
    PropagatorLocalizationTail : Set

    relativeSpectrumTraceLogEvidence : RelativeSpectrumTraceLog
    normalizedTaylorInteractionEvidence : NormalizedTaylorInteraction
    bishopHaarChartControlEvidence : BishopHaarChartControl
    backgroundGaugeNormalInverseEvidence :
      BackgroundGaugeNormalInverseControl
    propagatorLocalizationTailEvidence : PropagatorLocalizationTail

    determinantBelowTenth :
      Allocation.LessEqual order
        determinant (delta * Allocation.oneTenthℚ)
    interactionBelowTenth :
      Allocation.LessEqual order
        interaction (delta * Allocation.oneTenthℚ)
    chartBelowTenth :
      Allocation.LessEqual order
        chart (delta * Allocation.oneTenthℚ)
    gaugeBelowTenth :
      Allocation.LessEqual order
        gauge (delta * Allocation.oneTenthℚ)
    localizationBelowTenth :
      Allocation.LessEqual order
        localization (delta * Allocation.oneTenthℚ)

open FiveActivityAnalyticEngines public

asFiveActivityTenthAllocation :
  ∀ {order : Allocation.RationalAdditiveOrder} →
  FiveActivityAnalyticEngines order →
  Allocation.FiveActivityTenthAllocation order
asFiveActivityTenthAllocation engines = record
  { Allocation.FiveActivityTenthAllocation.delta = delta engines
  ; Allocation.FiveActivityTenthAllocation.determinant = determinant engines
  ; Allocation.FiveActivityTenthAllocation.interaction = interaction engines
  ; Allocation.FiveActivityTenthAllocation.chart = chart engines
  ; Allocation.FiveActivityTenthAllocation.gauge = gauge engines
  ; Allocation.FiveActivityTenthAllocation.localization = localization engines
  ; Allocation.FiveActivityTenthAllocation.total = total engines
  ; Allocation.FiveActivityTenthAllocation.totalMeaning = totalMeaning engines
  ; Allocation.FiveActivityTenthAllocation.determinantBelowTenth =
      determinantBelowTenth engines
  ; Allocation.FiveActivityTenthAllocation.interactionBelowTenth =
      interactionBelowTenth engines
  ; Allocation.FiveActivityTenthAllocation.chartBelowTenth =
      chartBelowTenth engines
  ; Allocation.FiveActivityTenthAllocation.gaugeBelowTenth =
      gaugeBelowTenth engines
  ; Allocation.FiveActivityTenthAllocation.localizationBelowTenth =
      localizationBelowTenth engines
  }

fiveActivityEngineTotalBelowHalf :
  ∀ {order : Allocation.RationalAdditiveOrder} →
  (engines : FiveActivityAnalyticEngines order) →
  Allocation.LessEqual order
    (total engines)
    (delta engines * Allocation.halfℚ)
fiveActivityEngineTotalBelowHalf engines =
  Allocation.fiveActivityTotalBelowHalf
    (asFiveActivityTenthAllocation engines)

fiveActivityEngineOwnershipLevel : ProofLevel
fiveActivityEngineOwnershipLevel = machineChecked

fiveActivityEngineHalfAllocationLevel : ProofLevel
fiveActivityEngineHalfAllocationLevel = machineChecked

physicalDeterminantEngineInputsLevel : ProofLevel
physicalDeterminantEngineInputsLevel = conditional

physicalInteractionEngineInputsLevel : ProofLevel
physicalInteractionEngineInputsLevel = conditional

physicalChartEngineInputsLevel : ProofLevel
physicalChartEngineInputsLevel = conditional

physicalGaugeEngineInputsLevel : ProofLevel
physicalGaugeEngineInputsLevel = conditional

physicalLocalizationEngineInputsLevel : ProofLevel
physicalLocalizationEngineInputsLevel = conditional
