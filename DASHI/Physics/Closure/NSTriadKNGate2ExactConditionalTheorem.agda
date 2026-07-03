module DASHI.Physics.Closure.NSTriadKNGate2ExactConditionalTheorem where

open import DASHI.Physics.Closure.ExactGate2ConditionalTheoremBase
  using (ExactGate2ConditionalTheoremModel)
open import DASHI.Physics.Closure.NSTriadKNGate2BridgeConditionalHypotheses
  using ( NSTriadKNGate2BridgeConditionalHypotheses
        ; mkBridgeExactGate2TransferConsequences
        ; mkBridgeExactGate2OutsideConsequences
        ; mkBridgeExactGate2NoPollutionConsequences
        ; mkBridgeExactGate2ConditionalConsequences
        ; mkBridgeExactGate2NoPollutionConditionalConsequences
        )
open import DASHI.Physics.Closure.OutsideSeamAbsorptionBase
  using (OutsideSeamAbsorptionModel)
open import DASHI.Physics.Closure.NSTriadKNGate2ExactKNAOperatorTransfer
  using (exactKNAExtremizerAwareConditionalBound)
open import DASHI.Physics.Closure.NSTriadKNGate2OutsideSeamAbsorption
  using ( outsideSeamDirectionalConditionalBound
        ; outsideSeamZeroBudgetConditionalBound
        )

----------------------------------------------------------------------
-- Exact Gate 2 conditional theorem surface.
--
-- This is the first full true-carrier Gate 2 theorem shape:
--
--   exact K_N(A) transfer
--     + exact outside-seam absorption
--     + quarter-to-unit margin
--   ------------------------------------------------
--          exact Gate 2 conditional theorem
--
-- What remains after this surface is no longer algebraic composition.
-- It is the actual analytic instantiation of the true-carrier hypotheses.

exactGate2ConditionalBound :
  (m : ExactGate2ConditionalTheoremModel) →
  ExactGate2ConditionalTheoremModel._≤_ m
    (ExactGate2ConditionalTheoremModel.total-leakage m)
    (ExactGate2ConditionalTheoremModel.unit-threshold m)
exactGate2ConditionalBound =
  ExactGate2ConditionalTheoremModel.exactGate2ConditionalTheorem

exactGate2TransferInputBound :
  (m : ExactGate2ConditionalTheoremModel) →
  ExactGate2ConditionalTheoremModel._≤_ m
    (ExactGate2ConditionalTheoremModel.exact-kna-ratio m)
    (ExactGate2ConditionalTheoremModel.one-quarter m)
exactGate2TransferInputBound m =
  exactKNAExtremizerAwareConditionalBound
    (OutsideSeamAbsorptionModel.exactTransferModel
      (ExactGate2ConditionalTheoremModel.outsideSeamModel m))

exactGate2OutsideSeamInputBound :
  (m : ExactGate2ConditionalTheoremModel) →
  ExactGate2ConditionalTheoremModel._≤_ m
    (ExactGate2ConditionalTheoremModel.total-leakage m)
    (ExactGate2ConditionalTheoremModel.one-quarter m)
exactGate2OutsideSeamInputBound m =
  outsideSeamDirectionalConditionalBound
    (ExactGate2ConditionalTheoremModel.outsideSeamModel m)

exactGate2NoPollutionConditionalBound :
  (m : ExactGate2ConditionalTheoremModel) →
  ExactGate2ConditionalTheoremModel._≤_ m
    (ExactGate2ConditionalTheoremModel._+_ m
      (ExactGate2ConditionalTheoremModel.exact-kna-ratio m)
      (ExactGate2ConditionalTheoremModel.0# m))
    (ExactGate2ConditionalTheoremModel.unit-threshold m)
exactGate2NoPollutionConditionalBound =
  ExactGate2ConditionalTheoremModel.exactGate2NoPollutionConditionalTheorem

exactGate2NoPollutionInputBound :
  (m : ExactGate2ConditionalTheoremModel) →
  ExactGate2ConditionalTheoremModel._≤_ m
    (ExactGate2ConditionalTheoremModel._+_ m
      (ExactGate2ConditionalTheoremModel.exact-kna-ratio m)
      (ExactGate2ConditionalTheoremModel.0# m))
    (ExactGate2ConditionalTheoremModel.one-quarter m)
exactGate2NoPollutionInputBound m =
  outsideSeamZeroBudgetConditionalBound
    (ExactGate2ConditionalTheoremModel.outsideSeamModel m)

exactGate2ConditionalFromBridgeBound :
  (h : NSTriadKNGate2BridgeConditionalHypotheses) →
  ExactGate2ConditionalTheoremModel._≤_
    (NSTriadKNGate2BridgeConditionalHypotheses.theoremModel h)
    (ExactGate2ConditionalTheoremModel.total-leakage
      (NSTriadKNGate2BridgeConditionalHypotheses.theoremModel h))
    (ExactGate2ConditionalTheoremModel.unit-threshold
      (NSTriadKNGate2BridgeConditionalHypotheses.theoremModel h))
exactGate2ConditionalFromBridgeBound h =
  mkBridgeExactGate2ConditionalConsequences
    (NSTriadKNGate2BridgeConditionalHypotheses.theoremModel h)

exactGate2TransferInputFromBridgeBound :
  (h : NSTriadKNGate2BridgeConditionalHypotheses) →
  ExactGate2ConditionalTheoremModel._≤_
    (NSTriadKNGate2BridgeConditionalHypotheses.theoremModel h)
    (ExactGate2ConditionalTheoremModel.exact-kna-ratio
      (NSTriadKNGate2BridgeConditionalHypotheses.theoremModel h))
    (ExactGate2ConditionalTheoremModel.one-quarter
      (NSTriadKNGate2BridgeConditionalHypotheses.theoremModel h))
exactGate2TransferInputFromBridgeBound =
  mkBridgeExactGate2TransferConsequences

exactGate2OutsideInputFromBridgeBound :
  (h : NSTriadKNGate2BridgeConditionalHypotheses) →
  ExactGate2ConditionalTheoremModel._≤_
    (NSTriadKNGate2BridgeConditionalHypotheses.theoremModel h)
    (ExactGate2ConditionalTheoremModel.total-leakage
      (NSTriadKNGate2BridgeConditionalHypotheses.theoremModel h))
    (ExactGate2ConditionalTheoremModel.one-quarter
      (NSTriadKNGate2BridgeConditionalHypotheses.theoremModel h))
exactGate2OutsideInputFromBridgeBound =
  mkBridgeExactGate2OutsideConsequences

exactGate2NoPollutionInputFromBridgeBound :
  (h : NSTriadKNGate2BridgeConditionalHypotheses) →
  ExactGate2ConditionalTheoremModel._≤_
    (NSTriadKNGate2BridgeConditionalHypotheses.theoremModel h)
    (ExactGate2ConditionalTheoremModel._+_
      (NSTriadKNGate2BridgeConditionalHypotheses.theoremModel h)
      (ExactGate2ConditionalTheoremModel.exact-kna-ratio
        (NSTriadKNGate2BridgeConditionalHypotheses.theoremModel h))
      (ExactGate2ConditionalTheoremModel.0#
        (NSTriadKNGate2BridgeConditionalHypotheses.theoremModel h)))
    (ExactGate2ConditionalTheoremModel.one-quarter
      (NSTriadKNGate2BridgeConditionalHypotheses.theoremModel h))
exactGate2NoPollutionInputFromBridgeBound =
  mkBridgeExactGate2NoPollutionConsequences

exactGate2NoPollutionConditionalFromBridgeBound :
  (h : NSTriadKNGate2BridgeConditionalHypotheses) →
  ExactGate2ConditionalTheoremModel._≤_
    (NSTriadKNGate2BridgeConditionalHypotheses.theoremModel h)
    (ExactGate2ConditionalTheoremModel._+_
      (NSTriadKNGate2BridgeConditionalHypotheses.theoremModel h)
      (ExactGate2ConditionalTheoremModel.exact-kna-ratio
        (NSTriadKNGate2BridgeConditionalHypotheses.theoremModel h))
      (ExactGate2ConditionalTheoremModel.0#
        (NSTriadKNGate2BridgeConditionalHypotheses.theoremModel h)))
    (ExactGate2ConditionalTheoremModel.unit-threshold
      (NSTriadKNGate2BridgeConditionalHypotheses.theoremModel h))
exactGate2NoPollutionConditionalFromBridgeBound h =
  mkBridgeExactGate2NoPollutionConditionalConsequences
    (NSTriadKNGate2BridgeConditionalHypotheses.theoremModel h)
