module DASHI.Foundations.BishopArctanCubicQuinticPolynomialExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Errett Bishop and Douglas Bridges, "Constructive Analysis", Springer 1985.
-- DOI: 10.1007/978-3-642-61667-9.
--
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant", 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- DASHI CONTRIBUTION
-- Identify the first three concrete magnitudes in the constructive arctangent
-- series and therefore turn the abstract alternating partial sums into the
-- literal polynomials
--
--     x - x^3/3 <= atan_B(x) <= x - x^3/3 + x^5/5
--
-- on the nonnegative half-ball.  This is the finite algebraic bridge needed by
-- the Machin pi bounds; no decimal approximation and no arctangent oracle is
-- used.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Foundations.BishopMachinArctanConstructionExact as Atan
import DASHI.Foundations.BishopArctanHalfBallInterlacingExact as Interlace
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as Concrete
import DASHI.Physics.YangMills.BalabanBishopAlternatingInterlacingFromDecreasingTermsExact as Alternating
import DASHI.Physics.YangMills.BalabanBishopAlternatingBracketFromMonotoneLimitsExact as Limits
import DASHI.Physics.YangMills.BalabanP33BishopLowOrderTaylorBracketsExact as Low
open import DASHI.Physics.YangMills.CompactLieProofLevel

oneThird oneFifth : Bishop.ℝ
oneThird = Bishop._⋆ (+ 1 / 3)
oneFifth = Bishop._⋆ (+ 1 / 5)

cube fifthPower : Bishop.ℝ → Bishop.ℝ
cube x = Bishop._*_ (Bishop._*_ x x) x
fifthPower x = Bishop._*_ (cube x) (Bishop._*_ x x)

atanCubic atanQuintic : Bishop.ℝ → Bishop.ℝ
atanCubic x = Bishop._-_ x (Bishop._*_ oneThird (cube x))
atanQuintic x = Bishop._+_ (atanCubic x) (Bishop._*_ oneFifth (fifthPower x))

magnitudeZeroIsValue : ∀ {value} →
  Bishop.NonNegative value →
  Bishop._≃_ (Atan.atanMagnitudeTerm value zero) value
magnitudeZeroIsValue {value} valueNN =
  let
    powerNN = Concrete.powNonnegative valueNN (suc zero)
  in
  BishopP.≃-trans
    (BishopP.*-congˡ
      (BishopP.nonNegx⇒∣x∣≃x powerNN))
    (let open BishopP.ℝ-Solver
     in solve 1
        (λ x → Κ (+ 1 / 1) ⊗ (Κ (+ 1 / 1) ⊗ x) ⊜ x)
        BishopP.≃-refl value)

magnitudeOneIsCubic : ∀ {value} →
  Bishop.NonNegative value →
  Bishop._≃_
    (Atan.atanMagnitudeTerm value (suc zero))
    (Bishop._*_ oneThird (cube value))
magnitudeOneIsCubic {value} valueNN =
  let
    powerNN = Concrete.powNonnegative valueNN (suc (suc (suc zero)))
  in
  BishopP.≃-trans
    (BishopP.*-congˡ
      (BishopP.nonNegx⇒∣x∣≃x powerNN))
    (let open BishopP.ℝ-Solver
     in solve 1
        (λ x →
          Κ (+ 1 / 3) ⊗ (((Κ (+ 1 / 1) ⊗ x) ⊗ x) ⊗ x)
          ⊜ Κ (+ 1 / 3) ⊗ ((x ⊗ x) ⊗ x))
        BishopP.≃-refl value)

magnitudeTwoIsQuintic : ∀ {value} →
  Bishop.NonNegative value →
  Bishop._≃_
    (Atan.atanMagnitudeTerm value (suc (suc zero)))
    (Bishop._*_ oneFifth (fifthPower value))
magnitudeTwoIsQuintic {value} valueNN =
  let
    exponent = suc (suc (suc (suc (suc zero))))
    powerNN = Concrete.powNonnegative valueNN exponent
  in
  BishopP.≃-trans
    (BishopP.*-congˡ
      (BishopP.nonNegx⇒∣x∣≃x powerNN))
    (let open BishopP.ℝ-Solver
     in solve 1
        (λ x →
          Κ (+ 1 / 5) ⊗ (((((Κ (+ 1 / 1) ⊗ x) ⊗ x) ⊗ x) ⊗ x) ⊗ x)
          ⊜ Κ (+ 1 / 5) ⊗ (((x ⊗ x) ⊗ x) ⊗ (x ⊗ x)))
        BishopP.≃-refl value)

lowerPartialOneIsCubic : ∀ {value} →
  (point : Interlace.PositiveHalfBallPoint value) →
  Bishop._≃_
    (Alternating.lowerPartial (Interlace.atanAlternatingSeriesData point) (suc zero))
    (atanCubic value)
lowerPartialOneIsCubic {value} point =
  let dataSet = Interlace.atanAlternatingSeriesData point
  in
  BishopP.≃-trans
    (Low.lowerOneEquivalentFirstMinusSecondMagnitude dataSet)
    (BishopP.≃-trans
      (BishopP.+-cong
        (magnitudeZeroIsValue (Interlace.nonnegative point))
        (BishopP.-‿cong
          (magnitudeOneIsCubic (Interlace.nonnegative point))))
      BishopP.≃-refl)

upperPartialOneIsQuintic : ∀ {value} →
  (point : Interlace.PositiveHalfBallPoint value) →
  Bishop._≃_
    (Alternating.upperPartial (Interlace.atanAlternatingSeriesData point) (suc zero))
    (atanQuintic value)
upperPartialOneIsQuintic {value} point =
  let
    dataSet = Interlace.atanAlternatingSeriesData point
    lower = Alternating.lowerPartial dataSet (suc zero)
    upper = Alternating.upperPartial dataSet (suc zero)
    third = Atan.atanMagnitudeTerm value (suc (suc zero))
    difference = Alternating.upperMinusLowerIsEvenMagnitude dataSet (suc zero)
    upperAsLowerPlusThird : Bishop._≃_ upper (Bishop._+_ lower third)
    upperAsLowerPlusThird =
      let open BishopP.ℝ-Solver
      in solve 3
        (λ u l t → u ⊖ l ⊜ t → u ⊜ l ⊕ t)
        BishopP.≃-refl upper lower third difference
  in
  BishopP.≃-trans upperAsLowerPlusThird
    (BishopP.+-cong
      (lowerPartialOneIsCubic point)
      (magnitudeTwoIsQuintic (Interlace.nonnegative point)))

atanCubicLower : ∀ {value} →
  (point : Interlace.PositiveHalfBallPoint value) →
  Bishop._≤_ (atanCubic value) (Atan.bishopAtanHalfBall value (Interlace.insideHalf point))
atanCubicLower point =
  BishopP.≤-respˡ-≃
    (BishopP.≃-symm (lowerPartialOneIsCubic point))
    (Limits.lowerPartialBelowRepresentedLimit (Interlace.atanInterlacing point) (suc zero))

atanQuinticUpper : ∀ {value} →
  (point : Interlace.PositiveHalfBallPoint value) →
  Bishop._≤_ (Atan.bishopAtanHalfBall value (Interlace.insideHalf point)) (atanQuintic value)
atanQuinticUpper point =
  BishopP.≤-respʳ-≃
    (upperPartialOneIsQuintic point)
    (Limits.representedLimitBelowUpperPartial (Interlace.atanInterlacing point) (suc zero))

bishopArctanConcreteMagnitude012Level : ProofLevel
bishopArctanConcreteMagnitude012Level = machineChecked

bishopArctanCubicQuinticPolynomialBracketLevel : ProofLevel
bishopArctanCubicQuinticPolynomialBracketLevel = machineChecked
