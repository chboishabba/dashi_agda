module DASHI.Physics.Closure.NSTriadKNGate2ExactTrueCarrierHypotheses where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl; subst; sym)
open import Agda.Builtin.String using (String)
open import DASHI.Physics.Closure.ExactGate2ConditionalTheoremBase
  using ( ExactGate2ConditionalTheoremModel
        )
open import DASHI.Physics.Closure.ExactKNAOperatorTransferBase
  using (ExactKNAOperatorTransferModel)
open import DASHI.Physics.Closure.NSTriadKNGate2ExactConditionalTheorem
  using ( exactGate2ConditionalBound
        ; exactGate2NoPollutionConditionalBound
        ; exactGate2TransferInputBound
        ; exactGate2OutsideSeamInputBound
        ; exactGate2NoPollutionInputBound
        )
open import DASHI.Physics.Closure.NSTriadKNGate2ExactFactorRouteHypotheses
  using (NSTriadKNGate2ExactFactorRouteHypotheses)
open import DASHI.Physics.Closure.NSTriadKNGate2ExactTransferFromFactorRoute
  using (NSTriadKNGate2ExactTransferFromFactorRoute)
open import DASHI.Physics.Closure.NSTriadKNGate2OutsideSeamTrueCarrierHypotheses
  using (NSTriadKNGate2OutsideSeamTrueCarrierHypotheses)
open import DASHI.Physics.Closure.NSTriadKNGate2BridgeConditionalHypotheses
  using ( NSTriadKNGate2BridgeConditionalHypotheses
        ; mkNSTriadKNGate2BridgeConditionalHypotheses
        )
open import DASHI.Physics.Closure.NSTriadKNGate2SplitConditionalHypotheses
  using ( NSTriadKNGate2SplitConditionalHypotheses
        ; mkNSTriadKNGate2SplitConditionalHypotheses
        )
open import DASHI.Physics.Closure.OutsideSeamAbsorptionBase
  using (OutsideSeamAbsorptionModel)

----------------------------------------------------------------------
-- Exact true-carrier Gate 2 hypothesis package.
--
-- This is the sharp boundary between completed algebra and missing NS
-- analysis.  A witness of this record is exactly what the real PDE proof
-- must construct on the true carrier.  Once supplied, the exact Gate 2
-- conditional theorem follows immediately.

canonicalBoundaryText : String
canonicalBoundaryText =
  "Exact Gate 2 true-carrier hypothesis package: once the true carrier supplies exact restriction identity, Schur linearity transfer, directional transport budget, outside-seam decomposition/absorption, and quarter-to-unit margin, the full exact Gate 2 conditional theorem is immediate."

record NSTriadKNGate2ExactTrueCarrierHypotheses : Setω where
  constructor mkNSTriadKNGate2ExactTrueCarrierHypotheses
  field
    theoremModel : ExactGate2ConditionalTheoremModel

    boundaryText : String
    boundaryTextIsCanonical :
      boundaryText ≡ canonicalBoundaryText

    exactTransferModel :
      ExactKNAOperatorTransferModel
    exactTransferModelIsUnderlying :
      exactTransferModel
        ≡ OutsideSeamAbsorptionModel.exactTransferModel
            (ExactGate2ConditionalTheoremModel.outsideSeamModel theoremModel)

    outsideSeamModel :
      OutsideSeamAbsorptionModel
    outsideSeamModelIsUnderlying :
      outsideSeamModel
        ≡ ExactGate2ConditionalTheoremModel.outsideSeamModel theoremModel

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

    exactTransferBridgeModelIsUnderlying :
      NSTriadKNGate2ExactTransferFromFactorRoute.exactTransferModel
        exactTransferFromFactorRoute
      ≡ exactTransferModel

    outsideSeamHypothesesModelIsUnderlying :
      NSTriadKNGate2OutsideSeamTrueCarrierHypotheses.outsideSeamModel
        outsideSeamHypotheses
      ≡ outsideSeamModel

    schurLinearityTransferWitness :
      ExactKNAOperatorTransferModel.seam-transported-ratio
        exactTransferModel
      ≡
      ExactKNAOperatorTransferModel.transported-ratio
        exactTransferModel

    exactRestrictionIdentityWitness :
      ExactKNAOperatorTransferModel.exact-kna-ratio
        exactTransferModel
      ≡
      ExactKNAOperatorTransferModel.seam-transported-ratio
        exactTransferModel

    directionalTransportBoundWitness :
      ExactKNAOperatorTransferModel._≤_ exactTransferModel
        (ExactKNAOperatorTransferModel.seam-transported-ratio
          exactTransferModel)
        (ExactKNAOperatorTransferModel._*_
          exactTransferModel
          (ExactKNAOperatorTransferModel.directional-transport-factor
            exactTransferModel)
          (ExactKNAOperatorTransferModel.seam-rayleigh-ratio
            exactTransferModel))

    subcriticalDirectionalBudgetWitness :
      ExactKNAOperatorTransferModel._≤_ exactTransferModel
        (ExactKNAOperatorTransferModel._*_
          exactTransferModel
          (ExactKNAOperatorTransferModel.directional-transport-factor
            exactTransferModel)
          (ExactKNAOperatorTransferModel.seam-rayleigh-ratio
            exactTransferModel))
        (ExactKNAOperatorTransferModel.one-quarter exactTransferModel)

    outsideSeamDecompositionWitness :
      OutsideSeamAbsorptionModel.totalDecomposition
        outsideSeamModel

    outsideSeamAbsorbedWitness :
      OutsideSeamAbsorptionModel._≤_ outsideSeamModel
        (OutsideSeamAbsorptionModel.outside-seam-pollution outsideSeamModel)
        (OutsideSeamAbsorptionModel.absorbable-outside-budget
          outsideSeamModel)

    outsideSeamQuarterWitness :
      OutsideSeamAbsorptionModel._≤_ outsideSeamModel
        (OutsideSeamAbsorptionModel._+_ outsideSeamModel
          (OutsideSeamAbsorptionModel.exact-kna-ratio outsideSeamModel)
          (OutsideSeamAbsorptionModel.absorbable-outside-budget
            outsideSeamModel))
        (OutsideSeamAbsorptionModel.one-quarter outsideSeamModel)

    absorbedOutsideVanishesWitness :
      OutsideSeamAbsorptionModel.absorbable-outside-budget outsideSeamModel
      ≡
      OutsideSeamAbsorptionModel.0# outsideSeamModel

    quarterLeqUnitWitness :
      ExactGate2ConditionalTheoremModel._≤_ theoremModel
        (ExactGate2ConditionalTheoremModel.one-quarter theoremModel)
        (ExactGate2ConditionalTheoremModel.unit-threshold theoremModel)

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

    gate2ExactTransferConditionalTheoremProved : Bool
    gate2ExactTransferConditionalTheoremProvedIsTrue :
      gate2ExactTransferConditionalTheoremProved ≡ true

open NSTriadKNGate2ExactTrueCarrierHypotheses public

mkExactGate2HypothesisConsequences :
  (m : ExactGate2ConditionalTheoremModel) →
  ExactGate2ConditionalTheoremModel._≤_ m
    (ExactGate2ConditionalTheoremModel.total-leakage m)
    (ExactGate2ConditionalTheoremModel.unit-threshold m)
mkExactGate2HypothesisConsequences =
  exactGate2ConditionalBound

mkExactGate2NoPollutionHypothesisConsequences :
  (m : ExactGate2ConditionalTheoremModel) →
  ExactGate2ConditionalTheoremModel._≤_ m
    (ExactGate2ConditionalTheoremModel._+_ m
      (ExactGate2ConditionalTheoremModel.exact-kna-ratio m)
      (ExactGate2ConditionalTheoremModel.0# m))
    (ExactGate2ConditionalTheoremModel.unit-threshold m)
mkExactGate2NoPollutionHypothesisConsequences =
  exactGate2NoPollutionConditionalBound

mkExactGate2TransferInputConsequences :
  (m : ExactGate2ConditionalTheoremModel) →
  ExactGate2ConditionalTheoremModel._≤_ m
    (ExactGate2ConditionalTheoremModel.exact-kna-ratio m)
    (ExactGate2ConditionalTheoremModel.one-quarter m)
mkExactGate2TransferInputConsequences =
  exactGate2TransferInputBound

mkExactGate2OutsideSeamInputConsequences :
  (m : ExactGate2ConditionalTheoremModel) →
  ExactGate2ConditionalTheoremModel._≤_ m
    (ExactGate2ConditionalTheoremModel.total-leakage m)
    (ExactGate2ConditionalTheoremModel.one-quarter m)
mkExactGate2OutsideSeamInputConsequences =
  exactGate2OutsideSeamInputBound

mkExactGate2NoPollutionInputConsequences :
  (m : ExactGate2ConditionalTheoremModel) →
  ExactGate2ConditionalTheoremModel._≤_ m
    (ExactGate2ConditionalTheoremModel._+_ m
      (ExactGate2ConditionalTheoremModel.exact-kna-ratio m)
      (ExactGate2ConditionalTheoremModel.0# m))
    (ExactGate2ConditionalTheoremModel.one-quarter m)
mkExactGate2NoPollutionInputConsequences =
  exactGate2NoPollutionInputBound

mkExactTransferBridgeQuarterConsequences :
  (h : NSTriadKNGate2ExactTrueCarrierHypotheses) →
  ExactKNAOperatorTransferModel._≤_
    (exactTransferModel h)
    (ExactKNAOperatorTransferModel.exact-kna-ratio
      (exactTransferModel h))
    (ExactKNAOperatorTransferModel.one-quarter
      (exactTransferModel h))
mkExactTransferBridgeQuarterConsequences h =
  subst
    (λ m →
      ExactKNAOperatorTransferModel._≤_
        m
        (ExactKNAOperatorTransferModel.exact-kna-ratio m)
        (ExactKNAOperatorTransferModel.one-quarter m))
    (sym (exactTransferBridgeModelIsUnderlying h))
    (NSTriadKNGate2ExactTransferFromFactorRoute.exactTransferQuarterBound
      (exactTransferFromFactorRoute h))

mkOutsideSeamBridgeQuarterConsequences :
  (h : NSTriadKNGate2ExactTrueCarrierHypotheses) →
  OutsideSeamAbsorptionModel._≤_
    (outsideSeamModel h)
    (OutsideSeamAbsorptionModel.total-leakage
      (outsideSeamModel h))
    (OutsideSeamAbsorptionModel.one-quarter
      (outsideSeamModel h))
mkOutsideSeamBridgeQuarterConsequences h =
  subst
    (λ m →
      OutsideSeamAbsorptionModel._≤_
        m
        (OutsideSeamAbsorptionModel.total-leakage m)
        (OutsideSeamAbsorptionModel.one-quarter m))
    (sym (outsideSeamHypothesesModelIsUnderlying h))
    (NSTriadKNGate2OutsideSeamTrueCarrierHypotheses.totalLeakageQuarterBound
      (outsideSeamHypotheses h))

mkExactGate2TransferInputFromBridgeHypotheses :
  (h : NSTriadKNGate2ExactTrueCarrierHypotheses) →
  ExactGate2ConditionalTheoremModel._≤_
    (theoremModel h)
    (ExactGate2ConditionalTheoremModel.exact-kna-ratio
      (theoremModel h))
    (ExactGate2ConditionalTheoremModel.one-quarter
      (theoremModel h))
mkExactGate2TransferInputFromBridgeHypotheses h =
  subst
    (λ m →
      ExactGate2ConditionalTheoremModel._≤_
        (theoremModel h)
        (ExactKNAOperatorTransferModel.exact-kna-ratio m)
        (ExactKNAOperatorTransferModel.one-quarter m))
    (sym (exactTransferModelIsUnderlying h))
    (mkExactTransferBridgeQuarterConsequences h)

mkExactGate2OutsideInputFromBridgeHypotheses :
  (h : NSTriadKNGate2ExactTrueCarrierHypotheses) →
  ExactGate2ConditionalTheoremModel._≤_
    (theoremModel h)
    (ExactGate2ConditionalTheoremModel.total-leakage
      (theoremModel h))
    (ExactGate2ConditionalTheoremModel.one-quarter
      (theoremModel h))
mkExactGate2OutsideInputFromBridgeHypotheses h =
  subst
    (λ m →
      ExactGate2ConditionalTheoremModel._≤_
        (theoremModel h)
        (OutsideSeamAbsorptionModel.total-leakage m)
        (OutsideSeamAbsorptionModel.one-quarter m))
    (sym (outsideSeamModelIsUnderlying h))
    (mkOutsideSeamBridgeQuarterConsequences h)

mkExactGate2NoPollutionInputFromOutsideBridgeHypotheses :
  (h : NSTriadKNGate2ExactTrueCarrierHypotheses) →
  ExactGate2ConditionalTheoremModel._≤_
    (theoremModel h)
    (ExactGate2ConditionalTheoremModel._+_ (theoremModel h)
      (ExactGate2ConditionalTheoremModel.exact-kna-ratio
        (theoremModel h))
      (ExactGate2ConditionalTheoremModel.0#
        (theoremModel h)))
    (ExactGate2ConditionalTheoremModel.one-quarter
      (theoremModel h))
mkExactGate2NoPollutionInputFromOutsideBridgeHypotheses h =
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

projectSplitConditionalHypotheses :
  (h : NSTriadKNGate2ExactTrueCarrierHypotheses) →
  NSTriadKNGate2SplitConditionalHypotheses
projectSplitConditionalHypotheses h =
  mkNSTriadKNGate2SplitConditionalHypotheses
    (theoremModel h)
    "Split exact Gate 2 hypothesis package: once the true carrier supplies an exact K_N(A) quarter bound through the directional factor route, an exact outside-seam absorption package on the same quarter carrier, and the quarter-to-unit margin, the full exact Gate 2 conditional theorem follows immediately."
    refl
    (factorRouteHypotheses h)
    (exactTransferFromFactorRoute h)
    (outsideSeamHypotheses h)
    (factorRouteHypothesesBridgeIsUnderlying h)
    (outsideSeamHypothesesModelIsUnderlying h)
    (exactTransferBridgeModelIsUnderlying h)
    (quarterLeqUnitWitness h)
    (mkExactGate2TransferInputFromBridgeHypotheses h)
    (mkExactGate2OutsideInputFromBridgeHypotheses h)
    (exactGate2ConditionalBound h)
    (exactGate2NoPollutionConditionalBound h)
    true
    refl
    true
    refl
    false
    refl

projectBridgeConditionalHypotheses :
  (h : NSTriadKNGate2ExactTrueCarrierHypotheses) →
  NSTriadKNGate2BridgeConditionalHypotheses
projectBridgeConditionalHypotheses h =
  mkNSTriadKNGate2BridgeConditionalHypotheses
    (theoremModel h)
    "Bridge-only exact Gate 2 package: once the true carrier supplies the exact-transfer bridge from the directional factor route, the outside-seam absorption bridge, and the quarter-to-unit margin on the same theorem carrier, the exact Gate 2 quarter inputs and conditional theorem all follow."
    refl
    (exactTransferFromFactorRoute h)
    (outsideSeamHypotheses h)
    (exactTransferBridgeModelIsUnderlying h)
    (outsideSeamHypothesesModelIsUnderlying h)
    (quarterLeqUnitWitness h)
    (mkExactGate2TransferInputFromBridgeHypotheses h)
    (mkExactGate2OutsideInputFromBridgeHypotheses h)
    (mkExactGate2NoPollutionInputFromOutsideBridgeHypotheses h)
    (exactGate2ConditionalBound h)
    (exactGate2NoPollutionConditionalBound h)
    true
    refl
    true
    refl
    false
    refl
