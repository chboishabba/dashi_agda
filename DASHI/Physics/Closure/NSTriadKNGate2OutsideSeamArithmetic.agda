module DASHI.Physics.Closure.NSTriadKNGate2OutsideSeamArithmetic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.Closure.NSTriadKNGate2ExactConditionalArithmetic
  using ( canonicalExactKNAOperatorTransferModel
        ; canonicalOutsideSeamAbsorptionModel
        )
open import DASHI.Physics.Closure.NSTriadKNGate2OutsideSeamTrueCarrierHypotheses
  using ( NSTriadKNGate2OutsideSeamTrueCarrierHypotheses
        ; mkNSTriadKNGate2OutsideSeamTrueCarrierHypotheses
        )
open import DASHI.Physics.Closure.OutsideSeamAbsorptionBase
  as Outside

----------------------------------------------------------------------
-- Concrete arithmetic inhabitant of the exact outside-seam hypothesis
-- package on the seam-local twelfths carrier.
--
-- This remains a local arithmetic model, not the true NS carrier.  Its
-- value is to inhabit the exact outside-seam theorem surface directly.

canonicalTotalDecomposition :
  Outside.totalDecomposition
    canonicalOutsideSeamAbsorptionModel
canonicalTotalDecomposition = refl

canonicalOutsideAbsorbed :
  Outside.outside≤absorbed
    canonicalOutsideSeamAbsorptionModel
canonicalOutsideAbsorbed =
  Outside.outside≤absorbed
    canonicalOutsideSeamAbsorptionModel

canonicalExactPlusAbsorbedQuarter :
  Outside.exactPlusAbsorbed≤quarter
    canonicalOutsideSeamAbsorptionModel
canonicalExactPlusAbsorbedQuarter =
  Outside.exactPlusAbsorbed≤quarter
    canonicalOutsideSeamAbsorptionModel

canonicalAbsorbedOutsideVanishes :
  Outside.absorbedOutsideVanishes
    canonicalOutsideSeamAbsorptionModel
canonicalAbsorbedOutsideVanishes = refl

canonicalTotalLeakageQuarterBound :
  Outside._≤_
    canonicalOutsideSeamAbsorptionModel
    (Outside.total-leakage canonicalOutsideSeamAbsorptionModel)
    (Outside.one-quarter canonicalOutsideSeamAbsorptionModel)
canonicalTotalLeakageQuarterBound =
  Outside.total≤quarter
    canonicalOutsideSeamAbsorptionModel

canonicalExactPlusZeroQuarterBound :
  Outside._≤_
    canonicalOutsideSeamAbsorptionModel
    (Outside._+_
      canonicalOutsideSeamAbsorptionModel
      (Outside.exact-kna-ratio canonicalOutsideSeamAbsorptionModel)
      (Outside.0# canonicalOutsideSeamAbsorptionModel))
    (Outside.one-quarter canonicalOutsideSeamAbsorptionModel)
canonicalExactPlusZeroQuarterBound =
  Outside.exactPlusZero≤quarter
    canonicalOutsideSeamAbsorptionModel

canonicalOutsideSeamTrueCarrierHypotheses :
  NSTriadKNGate2OutsideSeamTrueCarrierHypotheses
canonicalOutsideSeamTrueCarrierHypotheses =
  mkNSTriadKNGate2OutsideSeamTrueCarrierHypotheses
    canonicalOutsideSeamAbsorptionModel
    "Exact outside-seam true-carrier hypothesis package: once the true carrier supplies the exact transferred K_N(A) lane, a total-leakage decomposition into exact leakage plus outside-seam pollution, a uniform absorbed budget dominating that pollution, a quarter closure for exact-plus-absorbed leakage, and the sharp vanishing absorbed-budget case, the outside-seam Gate 2 theorem follows immediately."
    refl
    canonicalExactKNAOperatorTransferModel
    refl
    canonicalTotalDecomposition
    canonicalOutsideAbsorbed
    canonicalExactPlusAbsorbedQuarter
    canonicalAbsorbedOutsideVanishes
    canonicalTotalLeakageQuarterBound
    canonicalExactPlusZeroQuarterBound
    true
    refl
    true
    refl
    false
    refl
