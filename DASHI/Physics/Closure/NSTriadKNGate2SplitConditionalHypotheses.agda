module DASHI.Physics.Closure.NSTriadKNGate2SplitConditionalHypotheses where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl; subst; sym)
open import Agda.Builtin.String using (String)
open import DASHI.Physics.Closure.ExactGate2ConditionalTheoremBase
  using (ExactGate2ConditionalTheoremModel)
open import DASHI.Physics.Closure.NSTriadKNGate2ExactConditionalTheorem
  using ( exactGate2ConditionalBound
        ; exactGate2NoPollutionConditionalBound
        )
open import DASHI.Physics.Closure.NSTriadKNGate2ExactFactorRouteHypotheses
  using (NSTriadKNGate2ExactFactorRouteHypotheses)
open import DASHI.Physics.Closure.NSTriadKNGate2ExactTransferFromFactorRoute
  using (NSTriadKNGate2ExactTransferFromFactorRoute)
open import DASHI.Physics.Closure.NSTriadKNGate2OutsideSeamTrueCarrierHypotheses
  using (NSTriadKNGate2OutsideSeamTrueCarrierHypotheses)
open import DASHI.Physics.Closure.ExactKNAOperatorTransferBase
  using (ExactKNAOperatorTransferModel)
open import DASHI.Physics.Closure.OutsideSeamAbsorptionBase
  using (OutsideSeamAbsorptionModel)

----------------------------------------------------------------------
-- Split exact Gate 2 hypothesis package.
--
-- This is the sharpened composition of the two remaining analytic lanes:
--
--   1. exact K_N(A) quarter control via the directional factor route; and
--   2. exact outside-seam absorption / no-pollution on the true carrier.
--
-- Together with the quarter-to-unit margin, these yield the full exact
-- Gate 2 conditional theorem.  This package makes that composition
-- explicit, so the remaining NS burden is split into two concrete witness
-- families rather than hidden inside one monolithic record.

canonicalBoundaryText : String
canonicalBoundaryText =
  "Split exact Gate 2 hypothesis package: once the true carrier supplies an exact K_N(A) quarter bound through the directional factor route, an exact outside-seam absorption package on the same quarter carrier, and the quarter-to-unit margin, the full exact Gate 2 conditional theorem follows immediately."

record NSTriadKNGate2SplitConditionalHypotheses : Setω where
  constructor mkNSTriadKNGate2SplitConditionalHypotheses
  field
    theoremModel : ExactGate2ConditionalTheoremModel

    boundaryText : String
    boundaryTextIsCanonical :
      boundaryText ≡ canonicalBoundaryText

    factorRouteHypotheses :
      NSTriadKNGate2ExactFactorRouteHypotheses

    exactTransferFromFactorRoute :
      NSTriadKNGate2ExactTransferFromFactorRoute

    outsideSeamHypotheses :
      NSTriadKNGate2OutsideSeamTrueCarrierHypotheses

    factorRouteHypothesesBridgeIsUnderlying :
      NSTriadKNGate2ExactTransferFromFactorRoute.factorRouteHypotheses
        exactTransferFromFactorRoute
      ≡ factorRouteHypotheses

    outsideSeamModelIsUnderlying :
      NSTriadKNGate2OutsideSeamTrueCarrierHypotheses.outsideSeamModel
        outsideSeamHypotheses
      ≡ ExactGate2ConditionalTheoremModel.outsideSeamModel theoremModel

    exactTransferBridgeModelIsUnderlying :
      NSTriadKNGate2ExactTransferFromFactorRoute.exactTransferModel
        exactTransferFromFactorRoute
      ≡ OutsideSeamAbsorptionModel.exactTransferModel
          (ExactGate2ConditionalTheoremModel.outsideSeamModel theoremModel)

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

    splitExactGate2ConditionalTheoremProved : Bool
    splitExactGate2ConditionalTheoremProvedIsFalse :
      splitExactGate2ConditionalTheoremProved ≡ false

open NSTriadKNGate2SplitConditionalHypotheses public

mkSplitExactGate2TransferConsequences :
  (h : NSTriadKNGate2SplitConditionalHypotheses) →
  ExactGate2ConditionalTheoremModel._≤_
    (NSTriadKNGate2SplitConditionalHypotheses.theoremModel h)
    (ExactGate2ConditionalTheoremModel.exact-kna-ratio
      (NSTriadKNGate2SplitConditionalHypotheses.theoremModel h))
    (ExactGate2ConditionalTheoremModel.one-quarter
    (NSTriadKNGate2SplitConditionalHypotheses.theoremModel h))
mkSplitExactGate2TransferConsequences =
  exactTransferInputBound

mkSplitExactGate2TransferFromBridgeConsequences :
  (h : NSTriadKNGate2SplitConditionalHypotheses) →
  ExactGate2ConditionalTheoremModel._≤_
    (NSTriadKNGate2SplitConditionalHypotheses.theoremModel h)
    (ExactGate2ConditionalTheoremModel.exact-kna-ratio
      (NSTriadKNGate2SplitConditionalHypotheses.theoremModel h))
    (ExactGate2ConditionalTheoremModel.one-quarter
      (NSTriadKNGate2SplitConditionalHypotheses.theoremModel h))
mkSplitExactGate2TransferFromBridgeConsequences h =
  subst
    (λ m →
      ExactGate2ConditionalTheoremModel._≤_
        (theoremModel h)
        (ExactKNAOperatorTransferModel.exact-kna-ratio m)
        (ExactKNAOperatorTransferModel.one-quarter m))
    (sym (exactTransferBridgeModelIsUnderlying h))
    (NSTriadKNGate2ExactTransferFromFactorRoute.exactTransferQuarterBound
      (exactTransferFromFactorRoute h))

mkSplitExactGate2OutsideConsequences :
  (h : NSTriadKNGate2SplitConditionalHypotheses) →
  ExactGate2ConditionalTheoremModel._≤_
    (NSTriadKNGate2SplitConditionalHypotheses.theoremModel h)
    (ExactGate2ConditionalTheoremModel.total-leakage
      (NSTriadKNGate2SplitConditionalHypotheses.theoremModel h))
    (ExactGate2ConditionalTheoremModel.one-quarter
      (NSTriadKNGate2SplitConditionalHypotheses.theoremModel h))
mkSplitExactGate2OutsideConsequences =
  outsideSeamInputBound

mkSplitExactGate2OutsideFromBridgeConsequences :
  (h : NSTriadKNGate2SplitConditionalHypotheses) →
  ExactGate2ConditionalTheoremModel._≤_
    (NSTriadKNGate2SplitConditionalHypotheses.theoremModel h)
    (ExactGate2ConditionalTheoremModel.total-leakage
      (NSTriadKNGate2SplitConditionalHypotheses.theoremModel h))
    (ExactGate2ConditionalTheoremModel.one-quarter
      (NSTriadKNGate2SplitConditionalHypotheses.theoremModel h))
mkSplitExactGate2OutsideFromBridgeConsequences h =
  subst
    (λ m →
      ExactGate2ConditionalTheoremModel._≤_
        (theoremModel h)
        (OutsideSeamAbsorptionModel.total-leakage m)
        (OutsideSeamAbsorptionModel.one-quarter m))
    (sym (outsideSeamModelIsUnderlying h))
    (NSTriadKNGate2OutsideSeamTrueCarrierHypotheses.totalLeakageQuarterBound
      (outsideSeamHypotheses h))

mkSplitExactGate2NoPollutionFromOutsideBridgeConsequences :
  (h : NSTriadKNGate2SplitConditionalHypotheses) →
  ExactGate2ConditionalTheoremModel._≤_
    (NSTriadKNGate2SplitConditionalHypotheses.theoremModel h)
    (ExactGate2ConditionalTheoremModel._+_
      (NSTriadKNGate2SplitConditionalHypotheses.theoremModel h)
      (ExactGate2ConditionalTheoremModel.exact-kna-ratio
        (NSTriadKNGate2SplitConditionalHypotheses.theoremModel h))
      (ExactGate2ConditionalTheoremModel.0#
        (NSTriadKNGate2SplitConditionalHypotheses.theoremModel h)))
    (ExactGate2ConditionalTheoremModel.one-quarter
      (NSTriadKNGate2SplitConditionalHypotheses.theoremModel h))
mkSplitExactGate2NoPollutionFromOutsideBridgeConsequences h =
  subst
    (λ m →
      ExactGate2ConditionalTheoremModel._≤_
        (theoremModel h)
        (OutsideSeamAbsorptionModel._+_ m
          (OutsideSeamAbsorptionModel.exact-kna-ratio m)
          (OutsideSeamAbsorptionModel.0# m))
        (OutsideSeamAbsorptionModel.one-quarter m))
    (sym (outsideSeamModelIsUnderlying h))
    (NSTriadKNGate2OutsideSeamTrueCarrierHypotheses.exactPlusZeroQuarterBound
      (outsideSeamHypotheses h))

mkSplitExactGate2ConditionalConsequences :
  (m : ExactGate2ConditionalTheoremModel) →
  ExactGate2ConditionalTheoremModel._≤_ m
    (ExactGate2ConditionalTheoremModel.total-leakage m)
    (ExactGate2ConditionalTheoremModel.unit-threshold m)
mkSplitExactGate2ConditionalConsequences =
  exactGate2ConditionalBound

mkSplitExactGate2NoPollutionConsequences :
  (m : ExactGate2ConditionalTheoremModel) →
  ExactGate2ConditionalTheoremModel._≤_ m
    (ExactGate2ConditionalTheoremModel._+_ m
      (ExactGate2ConditionalTheoremModel.exact-kna-ratio m)
      (ExactGate2ConditionalTheoremModel.0# m))
    (ExactGate2ConditionalTheoremModel.unit-threshold m)
mkSplitExactGate2NoPollutionConsequences =
  exactGate2NoPollutionConditionalBound
