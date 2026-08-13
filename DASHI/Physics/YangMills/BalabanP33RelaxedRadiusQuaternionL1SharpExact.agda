module DASHI.Physics.YangMills.BalabanP33RelaxedRadiusQuaternionL1SharpExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Sharpen the coordinatewise 1/1024 l1 estimate by proving the exact
-- four-coordinate Cauchy inequality without square roots:
--
--   (|q0|+|q1|+|q2|+|q3|)^2 <= 4 N(q).
--
-- The defect radius N(q)<=4 rho^2 with rho=1/8192 then gives
--
--   ||q||_1^2 <= 16 rho^2 = (1/2048)^2,
--   ||q||_1 <= 1/2048.
--
-- This factor-two improvement matters for the selected CMP109 contour
-- diameter: two independent length-24 paths then remain comfortably inside
-- the CMP98 equation-(38) |Y|<=1/12 chart after the logarithm bound.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; ∣_∣; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanStrongCouplingLiteralQuaternionScalarBudgetExact as Strong
import DASHI.Physics.YangMills.BalabanP33RelaxedRadiusQuaternionL1DefectExact as Coarse

sharpL1Budget : ℚ
sharpL1Budget = + 1 / 2048

four : ℚ
four = + 4 / 1

sumSixSquaresNonnegative : ∀ a b c d →
  0ℚ ≤
    (a - b) * (a - b)
    + (a - c) * (a - c)
    + (a - d) * (a - d)
    + (b - c) * (b - c)
    + (b - d) * (b - d)
    + (c - d) * (c - d)
sumSixSquaresNonnegative a b c d =
  FiniteL2.addNonnegative
    (FiniteL2.addNonnegative
      (FiniteL2.addNonnegative
        (FiniteL2.addNonnegative
          (FiniteL2.addNonnegative
            (FiniteL2.squareNonnegative (a - b))
            (FiniteL2.squareNonnegative (a - c)))
          (FiniteL2.squareNonnegative (a - d)))
        (FiniteL2.squareNonnegative (b - c)))
      (FiniteL2.squareNonnegative (b - d)))
    (FiniteL2.squareNonnegative (c - d))

fourCoordinateCauchySquared : ∀ a b c d →
  (a + b + c + d) * (a + b + c + d)
  ≤ four * (a * a + b * b + c * c + d * d)
fourCoordinateCauchySquared a b c d =
  Norm.nonnegativeDifferenceImpliesBelow
    (subst
      (λ selected → 0ℚ ≤ selected)
      (ℚRing.solve-∀ a b c d)
      (sumSixSquaresNonnegative a b c d))

absoluteSquaresToSquares : ∀ a b c d →
  ∣ a ∣ * ∣ a ∣ + ∣ b ∣ * ∣ b ∣
    + ∣ c ∣ * ∣ c ∣ + ∣ d ∣ * ∣ d ∣
  ≡ a * a + b * b + c * c + d * d
absoluteSquaresToSquares a b c d =
  ℚRing.solve-∀ a b c d

quaternionL1SquaredBelowFourNormSq : ∀ value →
  Coarse.quaternionDefectL1 value * Coarse.quaternionDefectL1 value
  ≤ four * Norm.normSq value
quaternionL1SquaredBelowFourNormSq (Q.quat q0 q1 q2 q3) =
  let
    raw = fourCoordinateCauchySquared ∣ q0 ∣ ∣ q1 ∣ ∣ q2 ∣ ∣ q3 ∣
  in
  subst
    (λ upper →
      Coarse.quaternionDefectL1 (Q.quat q0 q1 q2 q3)
        * Coarse.quaternionDefectL1 (Q.quat q0 q1 q2 q3)
      ≤ four * upper)
    (absoluteSquaresToSquares q0 q1 q2 q3)
    raw

sharpBudgetSquareExact :
  sharpL1Budget * sharpL1Budget
  ≡ four * Relaxed.fourRhoSquare
sharpBudgetSquareExact = ℚRing.solve []

relaxedNormSqImpliesSharpQuaternionL1Budget :
  ∀ value →
  Norm.normSq value ≤ Relaxed.fourRhoSquare →
  Coarse.quaternionDefectL1 value ≤ sharpL1Budget
relaxedNormSqImpliesSharpQuaternionL1Budget value radius =
  let
    l1Square = quaternionL1SquaredBelowFourNormSq value
    scaledRadius = Norm.scaleNonnegative four
      (ℚP.nonNegative⁻¹ four) radius
    squareBound :
      Coarse.quaternionDefectL1 value * Coarse.quaternionDefectL1 value
      ≤ sharpL1Budget * sharpL1Budget
    squareBound =
      ℚP.≤-trans l1Square
        (subst
          (λ upper → four * Norm.normSq value ≤ upper)
          (sym sharpBudgetSquareExact)
          scaledRadius)
    l1NN : 0ℚ ≤ Coarse.quaternionDefectL1 value
    l1NN =
      let
        Q.quat q0 q1 q2 q3 = value
      in
      FiniteL2.addNonnegative
        (FiniteL2.addNonnegative
          (FiniteL2.addNonnegative
            (ℚP.0≤∣p∣ q0)
            (ℚP.0≤∣p∣ q1))
          (ℚP.0≤∣p∣ q2))
        (ℚP.0≤∣p∣ q3)
  in
  Strong.nonnegativeSquareReflectsOrder
    (Coarse.quaternionDefectL1 value)
    sharpL1Budget
    l1NN
    (ℚP.nonNegative⁻¹ sharpL1Budget)
    squareBound

p33RelaxedRadiusQuaternionL1CauchyLevel : ProofLevel
p33RelaxedRadiusQuaternionL1CauchyLevel = machineChecked

p33RelaxedRadiusQuaternionL1SharpLevel : ProofLevel
p33RelaxedRadiusQuaternionL1SharpLevel = machineChecked
