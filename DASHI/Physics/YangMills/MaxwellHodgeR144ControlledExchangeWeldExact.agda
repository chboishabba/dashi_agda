module DASHI.Physics.YangMills.MaxwellHodgeR144ControlledExchangeWeldExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Laws.GaugeInteractionLaws as Gauge
import DASHI.Physics.GR.MaxwellMetricHodgeStressEnergyExact as MaxwellStress
import DASHI.Physics.GR.ControlledEMGravitationalWaveEnergyExchangeExact as Exchange
import DASHI.Physics.YangMills.R144EMGWControlledExchangeInstantiationExact as R144GW

------------------------------------------------------------------------
-- MAXWELL/HODGE -> HILBERT STRESS -> R144 -> CONTROLLED EM-GW EXCHANGE
--
-- This module removes the false frontier "Maxwell/Hodge missing".  Those
-- objects already exist in GaugeInteractionLaws.  The exact remaining seam is
-- the physical Hilbert first variation and its same-object identification with
-- the R144 stress insertion and metric tangent.
------------------------------------------------------------------------

record MaxwellHodgeR144ExchangeWeld
    (maxwell : Gauge.MaxwellFieldLaw)
    (state : MaxwellStress.MaxwellMetricHodgeState maxwell)
    (stress : MaxwellStress.MaxwellHilbertStressEnergy maxwell state) : Set₁ where
  constructor maxwell-hodge-r144-exchange-weld
  field
    hilbertExchange :
      MaxwellStress.MaxwellHilbertExchangeWeld maxwell state stress

    r144 : R144GW.R144EMGWStressVariationWeld

    SameInteractionReceipt : Set
    sameInteractionReceipt : SameInteractionReceipt

    SameMetricTangentReceipt : Set
    sameMetricTangentReceipt : SameMetricTangentReceipt

    SameEMStressInsertionReceipt : Set
    sameEMStressInsertionReceipt : SameEMStressInsertionReceipt

    SameFirstVariationReceipt : Set
    sameFirstVariationReceipt : SameFirstVariationReceipt

open MaxwellHodgeR144ExchangeWeld public

interactionFromMaxwellHodge :
  ∀ {maxwell state stress} →
  MaxwellHodgeR144ExchangeWeld maxwell state stress →
  Exchange.EMGWInteractionCarrier
interactionFromMaxwellHodge weld =
  MaxwellStress.MaxwellHilbertExchangeWeld.interaction
    (MaxwellHodgeR144ExchangeWeld.hilbertExchange weld)

interactionFromR144 :
  ∀ {maxwell state stress} →
  MaxwellHodgeR144ExchangeWeld maxwell state stress →
  Exchange.EMGWInteractionCarrier
interactionFromR144 weld =
  R144GW.R144EMGWStressVariationWeld.interaction
    (MaxwellHodgeR144ExchangeWeld.r144 weld)

record MaxwellHodgeR144Boundary : Set where
  constructor maxwell-hodge-r144-boundary
  field
    maxwellCarrierAlreadyExists : Bool
    metricDependentHodgeAlreadyExists : Bool
    finiteHodgeVariationMachineryAlreadyExists : Bool
    r144MetricStressVariationAlreadyExists : Bool
    newIndependentMaxwellTheoryRequired : Bool
    newIndependentHodgeTheoryRequired : Bool
    hilbertSameObjectWeldRemainsPhysicalSeam : Bool

canonicalMaxwellHodgeR144Boundary : MaxwellHodgeR144Boundary
canonicalMaxwellHodgeR144Boundary =
  maxwell-hodge-r144-boundary
    true true true true false false true
