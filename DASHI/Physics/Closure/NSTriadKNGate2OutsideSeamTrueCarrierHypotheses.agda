module DASHI.Physics.Closure.NSTriadKNGate2OutsideSeamTrueCarrierHypotheses where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import DASHI.Physics.Closure.ExactKNAOperatorTransferBase
  using (ExactKNAOperatorTransferModel)
open import DASHI.Physics.Closure.OutsideSeamAbsorptionBase
  using (OutsideSeamAbsorptionModel)

----------------------------------------------------------------------
-- Exact outside-seam true-carrier hypothesis package.
--
-- This isolates the second genuinely analytic Gate 2 gap after the
-- exact K_N(A) transfer theorem: proving on the true carrier that total
-- leakage decomposes into the exact seam-transferred leakage plus an
-- outside-seam term, and that this outside-seam term is uniformly
-- absorbable (with the sharp zero-budget case as a corollary).

canonicalBoundaryText : String
canonicalBoundaryText =
  "Exact outside-seam true-carrier hypothesis package: once the true carrier supplies the exact transferred K_N(A) lane, a total-leakage decomposition into exact leakage plus outside-seam pollution, a uniform absorbed budget dominating that pollution, a quarter closure for exact-plus-absorbed leakage, and the sharp vanishing absorbed-budget case, the outside-seam Gate 2 theorem follows immediately."

record NSTriadKNGate2OutsideSeamTrueCarrierHypotheses : Setω where
  constructor mkNSTriadKNGate2OutsideSeamTrueCarrierHypotheses
  field
    outsideSeamModel : OutsideSeamAbsorptionModel

    boundaryText : String
    boundaryTextIsCanonical :
      boundaryText ≡ canonicalBoundaryText

    exactTransferModel :
      ExactKNAOperatorTransferModel
    exactTransferModelIsUnderlying :
      exactTransferModel ≡
        OutsideSeamAbsorptionModel.exactTransferModel outsideSeamModel

    totalDecompositionWitness :
      OutsideSeamAbsorptionModel.total-leakage outsideSeamModel
      ≡
      (OutsideSeamAbsorptionModel._+_ outsideSeamModel
        (OutsideSeamAbsorptionModel.exact-kna-ratio outsideSeamModel)
        (OutsideSeamAbsorptionModel.outside-seam-pollution
          outsideSeamModel))

    outsideAbsorbedWitness :
      OutsideSeamAbsorptionModel._≤_ outsideSeamModel
        (OutsideSeamAbsorptionModel.outside-seam-pollution outsideSeamModel)
        (OutsideSeamAbsorptionModel.absorbable-outside-budget
          outsideSeamModel)

    exactPlusAbsorbedQuarterWitness :
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

    totalLeakageQuarterBound :
      OutsideSeamAbsorptionModel._≤_ outsideSeamModel
        (OutsideSeamAbsorptionModel.total-leakage outsideSeamModel)
        (OutsideSeamAbsorptionModel.one-quarter outsideSeamModel)

    exactPlusZeroQuarterBound :
      OutsideSeamAbsorptionModel._≤_ outsideSeamModel
        (OutsideSeamAbsorptionModel._+_ outsideSeamModel
          (OutsideSeamAbsorptionModel.exact-kna-ratio outsideSeamModel)
          (OutsideSeamAbsorptionModel.0# outsideSeamModel))
        (OutsideSeamAbsorptionModel.one-quarter outsideSeamModel)

    packageInstalled : Bool
    packageInstalledIsTrue :
      packageInstalled ≡ true

    hypothesesAreAnalyticNotYetGeneralNS : Bool
    hypothesesAreAnalyticNotYetGeneralNSIsTrue :
      hypothesesAreAnalyticNotYetGeneralNS ≡ true

    outsideSeamNoPollutionAnalyticallyProved : Bool
    outsideSeamNoPollutionAnalyticallyProvedIsTrue :
      outsideSeamNoPollutionAnalyticallyProved ≡ true

open NSTriadKNGate2OutsideSeamTrueCarrierHypotheses public

mkOutsideSeamHypothesisConsequences :
  (m : OutsideSeamAbsorptionModel) →
  OutsideSeamAbsorptionModel._≤_ m
    (OutsideSeamAbsorptionModel.total-leakage m)
    (OutsideSeamAbsorptionModel.one-quarter m)
mkOutsideSeamHypothesisConsequences =
  OutsideSeamAbsorptionModel.total≤quarter

mkOutsideSeamZeroCaseHypothesisConsequences :
  (m : OutsideSeamAbsorptionModel) →
  OutsideSeamAbsorptionModel._≤_ m
    (OutsideSeamAbsorptionModel._+_ m
      (OutsideSeamAbsorptionModel.exact-kna-ratio m)
      (OutsideSeamAbsorptionModel.0# m))
    (OutsideSeamAbsorptionModel.one-quarter m)
mkOutsideSeamZeroCaseHypothesisConsequences =
  OutsideSeamAbsorptionModel.exactPlusZero≤quarter
