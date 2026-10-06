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
--
-- R144 supplies the repo's composite stress first-variation spine.  The new
-- Schützhold interaction supplies a concrete physical target in which the
-- metric perturbation h_{mu nu} is paired with EM stress-energy T_{mu nu}.
-- The bridge is therefore stated as an explicit receipt package.
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

------------------------------------------------------------------------
-- Fail-closed scope: importing R144 is not itself the physical weld.
------------------------------------------------------------------------

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
-- Explicit max-cut: once the two same-object identifications and the pairing
-- receipt are supplied, the existing controlled-exchange carrier can consume
-- the result without any additional promotion axiom.
------------------------------------------------------------------------

record R144ControlledExchangeMaxCut : Set₁ where
  constructor r144-controlled-exchange-max-cut
  field
    weld : R144EMGWStressVariationWeld
    controlledExchange : Exchange.EMGWInteractionCarrier

    SameControlledInteractionReceipt : Set
    sameControlledInteractionReceipt : SameControlledInteractionReceipt

    R144ToControlledInteractionReceipt : Set
    r144ToControlledInteractionReceipt : R144ToControlledInteractionReceipt

open R144ControlledExchangeMaxCut public
