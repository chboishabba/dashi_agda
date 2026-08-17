module DASHI.Foundations.BishopArctanSeptimicLowerExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Errett Bishop and Douglas Bridges,
-- "Constructive Analysis", Springer, 1985.
-- DOI: 10.1007/978-3-642-61667-9.
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant", 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Extend the existing concrete arctangent bracket by one alternating pair.
-- On the nonnegative half-ball the actual Bishop arctangent series satisfies
--
--   x - x^3/3 + x^5/5 - x^7/7 <= atan_B(x).
--
-- This is proved from the existing concrete term magnitudes and alternating
-- interlacing; no analytic arctangent oracle or decimal approximation is used.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Foundations.BishopMachinArctanConstructionExact as Atan
import DASHI.Foundations.BishopArctanHalfBallInterlacingExact as Interlace
import DASHI.Foundations.BishopArctanCubicQuinticPolynomialExact as Poly
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as Concrete
import DASHI.Physics.YangMills.BalabanBishopAlternatingInterlacingFromDecreasingTermsExact as Alternating
import DASHI.Physics.YangMills.BalabanBishopAlternatingBracketFromMonotoneLimitsExact as Limits
open import DASHI.Physics.YangMills.CompactLieProofLevel

oneSeventh : Bishop.ℝ
oneSeventh = Bishop._⋆ (+ 1 / 7)

seventhPower : Bishop.ℝ → Bishop.ℝ
seventhPower x = Bishop._*_ (Poly.fifthPower x) (Bishop._*_ x x)

atanSeptimic : Bishop.ℝ → Bishop.ℝ
atanSeptimic x =
  Bishop._-_
    (Poly.atanQuintic x)
    (Bishop._*_ oneSeventh (seventhPower x))

magnitudeThreeIsSeptimic : ∀ {value} →
  Bishop.NonNegative value →
  Bishop._≃_
    (Atan.atanMagnitudeTerm value (suc (suc (suc zero))))
    (Bishop._*_ oneSeventh (seventhPower value))
magnitudeThreeIsSeptimic {value} valueNN =
  let
    exponent = suc (suc (suc (suc (suc (suc (suc zero))))))
    powerNN = Concrete.powNonnegative valueNN exponent
  in
  BishopP.≃-trans
    (BishopP.*-congˡ
      (BishopP.nonNegx⇒∣x∣≃x powerNN))
    (let open BishopP.ℝ-Solver
     in solve 1
        (λ x →
          Κ (+ 1 / 7) ⊗
            (((((((Κ (+ 1 / 1) ⊗ x) ⊗ x) ⊗ x) ⊗ x) ⊗ x) ⊗ x) ⊗ x)
          ⊜
          Κ (+ 1 / 7) ⊗
            ((((x ⊗ x) ⊗ x) ⊗ (x ⊗ x)) ⊗ (x ⊗ x)))
        BishopP.≃-refl value)

lowerPartialTwoIsSeptimic : ∀ {value} →
  (point : Interlace.PositiveHalfBallPoint value) →
  Bishop._≃_
    (Alternating.lowerPartial
      (Interlace.atanAlternatingSeriesData point)
      (suc (suc zero)))
    (atanSeptimic value)
lowerPartialTwoIsSeptimic {value} point =
  let
    dataSet = Interlace.atanAlternatingSeriesData point
    valueNN = Interlace.nonnegative point
    raw = Alternating.lowerSuccessorExpansion dataSet (suc zero)
    terms :
      Bishop._≃_
        (Bishop._+_
          (Alternating.lowerPartial dataSet (suc zero))
          (Bishop._-_
            (Atan.atanMagnitudeTerm value (suc (suc zero)))
            (Atan.atanMagnitudeTerm value (suc (suc (suc zero))))))
        (Bishop._+_
          (Poly.atanCubic value)
          (Bishop._-_
            (Bishop._*_ Poly.oneFifth (Poly.fifthPower value))
            (Bishop._*_ oneSeventh (seventhPower value))))
    terms =
      BishopP.+-cong
        (Poly.lowerPartialOneIsCubic point)
        (BishopP.+-cong
          (Poly.magnitudeTwoIsQuintic valueNN)
          (BishopP.-‿cong (magnitudeThreeIsSeptimic valueNN)))
    reassociate :
      Bishop._≃_
        (Bishop._+_
          (Poly.atanCubic value)
          (Bishop._-_
            (Bishop._*_ Poly.oneFifth (Poly.fifthPower value))
            (Bishop._*_ oneSeventh (seventhPower value))))
        (atanSeptimic value)
    reassociate =
      let open BishopP.ℝ-Solver
      in solve 3
        (λ c q s → c ⊕ (q ⊖ s) ⊜ (c ⊕ q) ⊖ s)
        BishopP.≃-refl
        (Poly.atanCubic value)
        (Bishop._*_ Poly.oneFifth (Poly.fifthPower value))
        (Bishop._*_ oneSeventh (seventhPower value))
  in
  BishopP.≃-trans raw (BishopP.≃-trans terms reassociate)

atanSeptimicLower : ∀ {value} →
  (point : Interlace.PositiveHalfBallPoint value) →
  Bishop._≤_
    (atanSeptimic value)
    (Atan.bishopAtanHalfBall value (Interlace.insideHalf point))
atanSeptimicLower point =
  BishopP.≤-respˡ-≃
    (BishopP.≃-symm (lowerPartialTwoIsSeptimic point))
    (Limits.lowerPartialBelowRepresentedLimit
      (Interlace.atanInterlacing point)
      (suc (suc zero)))

bishopArctanSeptimicLowerLevel : ProofLevel
bishopArctanSeptimicLowerLevel = machineChecked
