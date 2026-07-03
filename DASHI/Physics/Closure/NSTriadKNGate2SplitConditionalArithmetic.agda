module DASHI.Physics.Closure.NSTriadKNGate2SplitConditionalArithmetic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.Closure.NSTriadKNGate2ExactConditionalArithmetic
  using ( canonicalExactGate2ConditionalTheoremModel
        ; canonicalExactGate2ConditionalBound
        ; canonicalExactGate2NoPollutionConditionalBound
        )
open import DASHI.Physics.Closure.NSTriadKNGate2ExactConditionalTheorem
  using ( exactGate2TransferInputBound
        ; exactGate2OutsideSeamInputBound
        )
open import DASHI.Physics.Closure.NSTriadKNGate2ExactFactorRouteArithmetic
  using (canonicalExactFactorRouteHypotheses)
open import DASHI.Physics.Closure.NSTriadKNGate2ExactTransferFromFactorRouteArithmetic
  using (canonicalExactTransferFromFactorRoute)
open import DASHI.Physics.Closure.NSTriadKNGate2OutsideSeamArithmetic
  using (canonicalOutsideSeamTrueCarrierHypotheses)
open import DASHI.Physics.Closure.NSTriadKNGate2SplitConditionalHypotheses
  using ( NSTriadKNGate2SplitConditionalHypotheses
        ; mkNSTriadKNGate2SplitConditionalHypotheses
        ; mkSplitExactGate2TransferConsequences
        ; mkSplitExactGate2TransferFromBridgeConsequences
        ; mkSplitExactGate2OutsideConsequences
        ; mkSplitExactGate2OutsideFromBridgeConsequences
        ; mkSplitExactGate2NoPollutionFromOutsideBridgeConsequences
        )

----------------------------------------------------------------------
-- Concrete arithmetic inhabitant of the split exact Gate 2 hypothesis
-- package.
--
-- This remains seam-local arithmetic.  Its value is to show that the
-- exact Gate 2 theorem can now be assembled from the two sharpened
-- analytic lanes separately: factor-route transfer and outside-seam
-- absorption.

canonicalSplitConditionalHypotheses :
  NSTriadKNGate2SplitConditionalHypotheses
canonicalSplitConditionalHypotheses =
  mkNSTriadKNGate2SplitConditionalHypotheses
    canonicalExactGate2ConditionalTheoremModel
    "Split exact Gate 2 hypothesis package: once the true carrier supplies an exact K_N(A) quarter bound through the directional factor route, an exact outside-seam absorption package on the same quarter carrier, and the quarter-to-unit margin, the full exact Gate 2 conditional theorem follows immediately."
    refl
    canonicalExactFactorRouteHypotheses
    canonicalExactTransferFromFactorRoute
    canonicalOutsideSeamTrueCarrierHypotheses
    refl
    refl
    refl
    (exactGate2TransferInputBound
      canonicalExactGate2ConditionalTheoremModel)
    (exactGate2OutsideSeamInputBound
      canonicalExactGate2ConditionalTheoremModel)
    canonicalExactGate2ConditionalBound
    canonicalExactGate2NoPollutionConditionalBound
    true
    refl
    true
    refl
    false
    refl

canonicalSplitExactGate2TransferInputBound =
  mkSplitExactGate2TransferConsequences
    canonicalSplitConditionalHypotheses

canonicalSplitExactGate2TransferFromBridgeBound =
  mkSplitExactGate2TransferFromBridgeConsequences
    canonicalSplitConditionalHypotheses

canonicalSplitExactGate2OutsideInputBound =
  mkSplitExactGate2OutsideConsequences
    canonicalSplitConditionalHypotheses

canonicalSplitExactGate2OutsideFromBridgeBound =
  mkSplitExactGate2OutsideFromBridgeConsequences
    canonicalSplitConditionalHypotheses

canonicalSplitExactGate2NoPollutionFromOutsideBridgeBound =
  mkSplitExactGate2NoPollutionFromOutsideBridgeConsequences
    canonicalSplitConditionalHypotheses
