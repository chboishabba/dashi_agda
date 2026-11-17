module DASHI.Physics.Closure.NSTriadKNGate2BridgeConditionalHypotheses where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl; subst; sym)
open import Agda.Builtin.String using (String)
open import DASHI.Physics.Closure.ExactGate2ConditionalTheoremBase
  using (ExactGate2ConditionalTheoremModel)
open import DASHI.Physics.Closure.ExactKNAOperatorTransferBase
  using (ExactKNAOperatorTransferModel)
open import DASHI.Physics.Closure.NSTriadKNGate2ExactConditionalTheorem
  using ( exactGate2ConditionalBound
        ; exactGate2NoPollutionConditionalBound
        )
open import DASHI.Physics.Closure.NSTriadKNGate2ExactTransferFromFactorRoute
  using (NSTriadKNGate2ExactTransferFromFactorRoute)
open import DASHI.Physics.Closure.NSTriadKNGate2OutsideSeamTrueCarrierHypotheses
  using (NSTriadKNGate2OutsideSeamTrueCarrierHypotheses)
open import DASHI.Physics.Closure.NSTriadKNGate2SplitConditionalHypotheses
  using ( NSTriadKNGate2SplitConditionalHypotheses
        ; mkNSTriadKNGate2SplitConditionalHypotheses
        )
open import DASHI.Physics.Closure.OutsideSeamAbsorptionBase
  using (OutsideSeamAbsorptionModel)

----------------------------------------------------------------------
-- Bridge-only exact Gate 2 conditional package.
--
-- This is the sharpest algebraic Gate 2 surface still worth carrying:
--
--   1. exact-transfer bridge from the directional factor route
--   2. outside-seam true-carrier absorption bridge
--   3. quarter-to-unit margin
--
-- From these three ingredients, all theorem-facing Gate 2 inputs and the
-- full exact conditional theorem follow.  This isolates the remaining NS
-- work to exactly two analytic bridge packages on the true carrier.

canonicalBoundaryText : String
canonicalBoundaryText =
  "Bridge-only exact Gate 2 package: once the true carrier supplies the exact-transfer bridge from the directional factor route, the outside-seam absorption bridge, and the quarter-to-unit margin on the same theorem carrier, the exact Gate 2 quarter inputs and conditional theorem all follow."

record NSTriadKNGate2BridgeConditionalHypotheses : Setω where
  constructor mkNSTriadKNGate2BridgeConditionalHypotheses
  field
    theoremModel : ExactGate2ConditionalTheoremModel

    boundaryText : String
    boundaryTextIsCanonical :
      boundaryText ≡ canonicalBoundaryText

    exactTransferBridge :
      NSTriadKNGate2ExactTransferFromFactorRoute

    outsideSeamBridge :
      NSTriadKNGate2OutsideSeamTrueCarrierHypotheses

    exactTransferBridgeModelIsUnderlying :
      NSTriadKNGate2ExactTransferFromFactorRoute.exactTransferModel
        exactTransferBridge
      ≡ OutsideSeamAbsorptionModel.exactTransferModel
          (ExactGate2ConditionalTheoremModel.outsideSeamModel theoremModel)

    outsideSeamBridgeModelIsUnderlying :
      NSTriadKNGate2OutsideSeamTrueCarrierHypotheses.outsideSeamModel
        outsideSeamBridge
      ≡ ExactGate2ConditionalTheoremModel.outsideSeamModel theoremModel

    quarterLeqUnitWitness :
      ExactGate2ConditionalTheoremModel.quarter≤unit theoremModel

    exactTransferInputBound :
      ExactGate2ConditionalTheoremModel._≤_ theoremModel
        (ExactGate2ConditionalTheoremModel.exact-kna-ratio theoremModel)
        (ExactGate2ConditionalTheoremModel.one-quarter theoremModel)

    outsideSeamInputBound :
      ExactGate2ConditionalTheoremModel._≤_ theoremModel
        (ExactGate2ConditionalTheoremModel.total-leakage theoremModel)
        (ExactGate2ConditionalTheoremModel.one-quarter theoremModel)

    noPollutionInputBound :
      ExactGate2ConditionalTheoremModel._≤_ theoremModel
        (ExactGate2ConditionalTheoremModel._+_ theoremModel
          (ExactGate2ConditionalTheoremModel.exact-kna-ratio theoremModel)
          (ExactGate2ConditionalTheoremModel.0# theoremModel))
        (ExactGate2ConditionalTheoremModel.one-quarter theoremModel)

    exactGate2ConditionalBound :
      ExactGate2ConditionalTheoremModel._≤_ theoremModel
        (ExactGate2ConditionalTheoremModel.total-leakage theoremModel)
        (ExactGate2ConditionalTheoremModel.unit-threshold theoremModel)

    exactGate2NoPollutionConditionalBound :
      ExactGate2ConditionalTheoremModel._≤_ theoremModel
        (ExactGate2ConditionalTheoremModel._+_ theoremModel
          (ExactGate2ConditionalTheoremModel.exact-kna-ratio theoremModel)
          (ExactGate2ConditionalTheoremModel.0# theoremModel))
        (ExactGate2ConditionalTheoremModel.unit-threshold theoremModel)

    packageInstalled : Bool
    packageInstalledIsTrue :
      packageInstalled ≡ true

    hypothesesAreAnalyticNotYetGeneralNS : Bool
    hypothesesAreAnalyticNotYetGeneralNSIsTrue :
      hypothesesAreAnalyticNotYetGeneralNS ≡ true

    bridgeConditionalTheoremProved : Bool
    bridgeConditionalTheoremProvedIsFalse :
      bridgeConditionalTheoremProved ≡ false

open NSTriadKNGate2BridgeConditionalHypotheses public

mkBridgeExactGate2TransferConsequences :
  (h : NSTriadKNGate2BridgeConditionalHypotheses) →
  ExactGate2ConditionalTheoremModel._≤_
    (theoremModel h)
    (ExactGate2ConditionalTheoremModel.exact-kna-ratio
      (theoremModel h))
    (ExactGate2ConditionalTheoremModel.one-quarter
      (theoremModel h))
mkBridgeExactGate2TransferConsequences h =
  subst
    (λ m →
      ExactGate2ConditionalTheoremModel._≤_
        (theoremModel h)
        (ExactKNAOperatorTransferModel.exact-kna-ratio m)
        (ExactKNAOperatorTransferModel.one-quarter m))
    (sym (exactTransferBridgeModelIsUnderlying h))
    (NSTriadKNGate2ExactTransferFromFactorRoute.exactTransferQuarterBound
      (exactTransferBridge h))

mkBridgeExactGate2OutsideConsequences :
  (h : NSTriadKNGate2BridgeConditionalHypotheses) →
  ExactGate2ConditionalTheoremModel._≤_
    (theoremModel h)
    (ExactGate2ConditionalTheoremModel.total-leakage
      (theoremModel h))
    (ExactGate2ConditionalTheoremModel.one-quarter
      (theoremModel h))
mkBridgeExactGate2OutsideConsequences h =
  subst
    (λ m →
      ExactGate2ConditionalTheoremModel._≤_
        (theoremModel h)
        (OutsideSeamAbsorptionModel.total-leakage m)
        (OutsideSeamAbsorptionModel.one-quarter m))
    (sym (outsideSeamBridgeModelIsUnderlying h))
    (NSTriadKNGate2OutsideSeamTrueCarrierHypotheses.totalLeakageQuarterBound
      (outsideSeamBridge h))

mkBridgeExactGate2NoPollutionConsequences :
  (h : NSTriadKNGate2BridgeConditionalHypotheses) →
  ExactGate2ConditionalTheoremModel._≤_
    (theoremModel h)
    (ExactGate2ConditionalTheoremModel._+_ (theoremModel h)
      (ExactGate2ConditionalTheoremModel.exact-kna-ratio
        (theoremModel h))
      (ExactGate2ConditionalTheoremModel.0#
        (theoremModel h)))
    (ExactGate2ConditionalTheoremModel.one-quarter
      (theoremModel h))
mkBridgeExactGate2NoPollutionConsequences h =
  subst
    (λ m →
      ExactGate2ConditionalTheoremModel._≤_
        (theoremModel h)
        (OutsideSeamAbsorptionModel._+_ m
          (OutsideSeamAbsorptionModel.exact-kna-ratio m)
          (OutsideSeamAbsorptionModel.0# m))
        (OutsideSeamAbsorptionModel.one-quarter m))
    (sym (outsideSeamBridgeModelIsUnderlying h))
    (NSTriadKNGate2OutsideSeamTrueCarrierHypotheses.exactPlusZeroQuarterBound
      (outsideSeamBridge h))

mkBridgeExactGate2ConditionalConsequences :
  (m : ExactGate2ConditionalTheoremModel) →
  ExactGate2ConditionalTheoremModel._≤_ m
    (ExactGate2ConditionalTheoremModel.total-leakage m)
    (ExactGate2ConditionalTheoremModel.unit-threshold m)
mkBridgeExactGate2ConditionalConsequences =
  exactGate2ConditionalBound

mkBridgeExactGate2NoPollutionConditionalConsequences :
  (m : ExactGate2ConditionalTheoremModel) →
  ExactGate2ConditionalTheoremModel._≤_ m
    (ExactGate2ConditionalTheoremModel._+_ m
      (ExactGate2ConditionalTheoremModel.exact-kna-ratio m)
      (ExactGate2ConditionalTheoremModel.0# m))
    (ExactGate2ConditionalTheoremModel.unit-threshold m)
mkBridgeExactGate2NoPollutionConditionalConsequences =
  exactGate2NoPollutionConditionalBound

projectSplitConditionalHypothesesFromBridge :
  (h : NSTriadKNGate2BridgeConditionalHypotheses) →
  NSTriadKNGate2SplitConditionalHypotheses
projectSplitConditionalHypothesesFromBridge h =
  mkNSTriadKNGate2SplitConditionalHypotheses
    (theoremModel h)
    "Split exact Gate 2 hypothesis package: once the true carrier supplies an exact K_N(A) quarter bound through the directional factor route, an exact outside-seam absorption package on the same quarter carrier, and the quarter-to-unit margin, the full exact Gate 2 conditional theorem follows immediately."
    refl
    (NSTriadKNGate2ExactTransferFromFactorRoute.factorRouteHypotheses
      (exactTransferBridge h))
    (exactTransferBridge h)
    (outsideSeamBridge h)
    refl
    (outsideSeamBridgeModelIsUnderlying h)
    (exactTransferBridgeModelIsUnderlying h)
    (quarterLeqUnitWitness h)
    (mkBridgeExactGate2TransferConsequences h)
    (mkBridgeExactGate2OutsideConsequences h)
    (exactGate2ConditionalBound h)
    (exactGate2NoPollutionConditionalBound h)
    true
    refl
    true
    refl
    false
    refl
