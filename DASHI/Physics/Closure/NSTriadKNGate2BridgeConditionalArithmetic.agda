module DASHI.Physics.Closure.NSTriadKNGate2BridgeConditionalArithmetic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.Closure.NSTriadKNGate2BridgeConditionalHypotheses
  using ( NSTriadKNGate2BridgeConditionalHypotheses
        ; mkNSTriadKNGate2BridgeConditionalHypotheses
        ; mkBridgeExactGate2TransferConsequences
        ; mkBridgeExactGate2OutsideConsequences
        ; mkBridgeExactGate2NoPollutionConsequences
        ; projectSplitConditionalHypothesesFromBridge
        )
open import DASHI.Physics.Closure.NSTriadKNGate2ExactConditionalArithmetic
  using ( canonicalExactGate2ConditionalTheoremModel
        ; canonicalExactGate2ConditionalBound
        ; canonicalExactGate2NoPollutionConditionalBound
        ; canonicalExactTrueCarrierHypotheses
        )
import DASHI.Physics.Closure.NSTriadKNGate2ExactTrueCarrierHypotheses
  as TrueCarrier
open import DASHI.Physics.Closure.NSTriadKNGate2SplitConditionalHypotheses
  using (NSTriadKNGate2SplitConditionalHypotheses)

----------------------------------------------------------------------
-- Concrete arithmetic inhabitant of the bridge-only exact Gate 2 package.
--
-- This is the sharpest local arithmetic closure surface: it keeps only the
-- two live analytic bridge packages and the theorem carrier.

canonicalBridgeConditionalHypotheses :
  NSTriadKNGate2BridgeConditionalHypotheses
canonicalBridgeConditionalHypotheses =
  mkNSTriadKNGate2BridgeConditionalHypotheses
    canonicalExactGate2ConditionalTheoremModel
    "Bridge-only exact Gate 2 package: once the true carrier supplies the exact-transfer bridge from the directional factor route, the outside-seam absorption bridge, and the quarter-to-unit margin on the same theorem carrier, the exact Gate 2 quarter inputs and conditional theorem all follow."
    refl
    (TrueCarrier.exactTransferFromFactorRoute
      canonicalExactTrueCarrierHypotheses)
    (TrueCarrier.outsideSeamHypotheses
      canonicalExactTrueCarrierHypotheses)
    (TrueCarrier.exactTransferBridgeModelIsUnderlying
      canonicalExactTrueCarrierHypotheses)
    (TrueCarrier.outsideSeamHypothesesModelIsUnderlying
      canonicalExactTrueCarrierHypotheses)
    (TrueCarrier.quarterLeqUnitWitness
      canonicalExactTrueCarrierHypotheses)
    (TrueCarrier.exactTransferInputBound
      canonicalExactTrueCarrierHypotheses)
    (TrueCarrier.outsideSeamInputBound
      canonicalExactTrueCarrierHypotheses)
    (TrueCarrier.noPollutionInputBound
      canonicalExactTrueCarrierHypotheses)
    canonicalExactGate2ConditionalBound
    canonicalExactGate2NoPollutionConditionalBound
    true
    refl
    true
    refl
    false
    refl

canonicalBridgeTransferInputBound =
  mkBridgeExactGate2TransferConsequences
    canonicalBridgeConditionalHypotheses

canonicalBridgeOutsideInputBound =
  mkBridgeExactGate2OutsideConsequences
    canonicalBridgeConditionalHypotheses

canonicalBridgeNoPollutionInputBound =
  mkBridgeExactGate2NoPollutionConsequences
    canonicalBridgeConditionalHypotheses

canonicalProjectedSplitFromBridge :
  NSTriadKNGate2SplitConditionalHypotheses
canonicalProjectedSplitFromBridge =
  projectSplitConditionalHypothesesFromBridge
    canonicalBridgeConditionalHypotheses
