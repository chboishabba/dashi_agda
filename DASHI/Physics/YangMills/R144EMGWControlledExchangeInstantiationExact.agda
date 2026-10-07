module DASHI.Physics.YangMills.R144EMGWControlledExchangeInstantiationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.GR.ControlledEMGravitationalWaveEnergyExchangeExact as Exchange
import DASHI.Physics.YangMills.BalabanCompositeStressFirstVariationRound144Exact as R144

------------------------------------------------------------------------
-- R144 x CONTROLLED EM-GW EXCHANGE
--
-- Purpose: expose the exact remaining same-object weld without pretending the
-- concrete electromagnetic stress tensor or gravitational-wave metric tangent
-- has already been identified with an R144 inhabitant.
------------------------------------------------------------------------

record R144EMGWStressVariationWeld : Set₁ where
  constructor r144-emgw-stress-variation-weld
  field
    interaction : Exchange.EMGWInteractionCarrier

    R144MetricTangentCarrier : Set
    r144MetricTangent : R144MetricTangentCarrier

    R144StressInsertionCarrier : Set
    r144StressInsertion : R144StressInsertionCarrier

    MetricTangentSameObjectReceipt : Set
    metricTangentSameObjectReceipt : MetricTangentSameObjectReceipt

    EMStressSameObjectReceipt : Set
    emStressSameObjectReceipt : EMStressSameObjectReceipt

    FirstVariationPairingReceipt : Set
    firstVariationPairingReceipt : FirstVariationPairingReceipt

    LocalizedInteractionReceipt : Set
    localizedInteractionReceipt : LocalizedInteractionReceipt

open R144EMGWStressVariationWeld public

record R144EMGWBoundary : Set where
  constructor r144-emgw-boundary
  field
    r144StressVariationMachineryExists : Bool
    importingR144IdentifiesLaserStressTensor : Bool
    importingR144IdentifiesGWMetricTangent : Bool
    sameObjectReceiptsStillRequired : Bool
    firstVariationPairingIsNaturalBridgeTarget : Bool
    exchangeReadoutMayCalibrateStressMetricPairing : Bool

canonicalR144EMGWBoundary : R144EMGWBoundary
canonicalR144EMGWBoundary =
  r144-emgw-boundary true false false true true true

------------------------------------------------------------------------
-- Exact max-cut: the controlled carrier itself is definitionally constrained
-- to be the carrier stored in the R144 weld.  No arbitrary proposition can
-- stand in for this same-object equality.
------------------------------------------------------------------------

record R144ControlledExchangeMaxCut : Set₁ where
  constructor r144-controlled-exchange-max-cut
  field
    weld : R144EMGWStressVariationWeld
    controlledExchange : Exchange.EMGWInteractionCarrier

    controlledExchangeIsWeldInteraction :
      controlledExchange ≡ R144EMGWStressVariationWeld.interaction weld

    R144ToControlledInteractionReceipt : Set
    r144ToControlledInteractionReceipt : R144ToControlledInteractionReceipt

open R144ControlledExchangeMaxCut public
