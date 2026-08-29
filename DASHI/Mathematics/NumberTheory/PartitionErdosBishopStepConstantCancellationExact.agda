module DASHI.Mathematics.NumberTheory.PartitionErdosBishopStepConstantCancellationExact where

------------------------------------------------------------------------
-- EXACT ERDOS CONSTANT CANCELLATION
--
-- For the canonical step
--
--   x_n = c * (2 sqrt n)^(-1),
--   c   = pi_M * sqrt(2/3),
--
-- prove
--
--   n* * x_n^2 ~= pi_M^2 / 6
--
-- and hence, for positive n,
--
--   (pi_M^2 / 6) * x_n^(-2) ~= n*.
--
-- The proof uses the actual constructed root and Machin pi.  The key scalar
-- normalization is simply
--
--   (2 sqrt n)^(-1) * sqrt n ~= 1/2,
--
-- obtained from the vendored inverse cancellation law.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Integer.Base using (+_)
open import Data.Nat.Base using (_≤_)
open import Data.Rational.Unnormalised using (_/_)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopBaselSineProductCoefficientBoundaryExact as BaselBoundary
import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal
import DASHI.Foundations.BishopNatSquareRootDividedTangentExact as Tangent
import DASHI.Foundations.BishopNatSquareRootSemanticSquareExact as RootSquare
import DASHI.Foundations.BishopSqrtTwoThirdsMachinConstantExact as Constant
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopCubicStepRateExact as Rate
open import DASHI.Physics.YangMills.CompactLieProofLevel

half : BishopReal.ℝ
half = BishopReal._⋆ (+ 1 / 2)

embeddedNat : Nat → BishopReal.ℝ
embeddedNat = Tangent.embedNat

square : BishopReal.ℝ → BishopReal.ℝ
square value = BishopReal._*_ value value

inverseDenominatorTimesRootIsHalf :
  ∀ {n : Nat} →
  (nPositive : suc 0 ≤ n) →
  BishopReal._≃_
    (BishopReal._*_
      (Tangent.inverseDenominator n nPositive)
      (Tangent.rootNat n))
    half
inverseDenominatorTimesRootIsHalf {n} nPositive =
  let
    inv = Tangent.inverseDenominator n nPositive
    root = Tangent.rootNat n
    denom = Tangent.denominator n
    inverseLaw =
      BishopInverse.*-inverseˡ denom (Tangent.denominatorNonzero nPositive)
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (solve 2
      (λ i r →
        i ⊗ r
        ⊜ Κ (+ 1 / 2) ⊗ (i ⊗ (Κ (+ 2 / 1) ⊗ r)))
      BishopP.≃-refl inv root)
    (BishopP.≃-trans
      (BishopP.*-congˡ inverseLaw)
      (BishopP.≃-trans
        (BishopP.*-identityʳ half)
        BishopP.≃-refl))

canonicalStepSquareWeightedByNat :
  ∀ {n : Nat} →
  (nPositive : suc 0 ≤ n) →
  let rate = Rate.canonicalErdosStepRate n nPositive in
  BishopReal._≃_
    (BishopReal._*_
      (embeddedNat n)
      (square (Rate.step rate)))
    BaselBoundary.piSquareOverSix
canonicalStepSquareWeightedByNat {n} nPositive =
  let
    rate = Rate.canonicalErdosStepRate n nPositive
    pi = Constant.Machin.bishopMachinPi
    s = Constant.sqrtTwoThirds
    root = Tangent.rootNat n
    inv = Tangent.inverseDenominator n nPositive

    rootSquare :
      BishopReal._≃_ (square root) (embeddedNat n)
    rootSquare = RootSquare.canonicalFloorSquareRootSquaresToNat n

    halfLaw : BishopReal._≃_ (BishopReal._*_ inv root) half
    halfLaw = inverseDenominatorTimesRootIsHalf nPositive

    normalized :
      BishopReal._≃_
        (BishopReal._*_
          (embeddedNat n)
          (square (Rate.step rate)))
        (BishopReal._*_
          (square pi)
          (BishopReal._*_
            (square s)
            (square (BishopReal._*_ inv root))))
    normalized =
      BishopP.≃-trans
        (BishopP.*-congʳ (BishopP.≃-symm rootSquare))
        (let open BishopP.ℝ-Solver
         in solve 4
           (λ r p s′ i →
             (r ⊗ r) ⊗ ((p ⊗ s′ ⊗ i) ⊗ (p ⊗ s′ ⊗ i))
             ⊜ (p ⊗ p) ⊗ ((s′ ⊗ s′) ⊗ ((i ⊗ r) ⊗ (i ⊗ r))))
           BishopP.≃-refl root pi s inv)
  in
  BishopP.≃-trans
    normalized
    (BishopP.≃-trans
      (BishopP.*-congˡ
        (BishopP.*-cong
          Constant.sqrtTwoThirdsSquaresToTwoThirds
          (BishopP.*-cong halfLaw halfLaw)))
      (let open BishopP.ℝ-Solver
       in solve 1
         (λ p →
           (p ⊗ p) ⊗ (Κ (+ 2 / 3) ⊗ (Κ (+ 1 / 2) ⊗ Κ (+ 1 / 2)))
           ⊜ Κ (+ 1 / 6) ⊗ (p ⊗ p))
         BishopP.≃-refl pi))

piSquareOverSixTimesStepInverseSquareIsNat :
  ∀ {n : Nat} →
  (nPositive : suc 0 ≤ n) →
  let rate = Rate.canonicalErdosStepRate n nPositive in
  BishopReal._≃_
    (BishopReal._*_
      BaselBoundary.piSquareOverSix
      (Reciprocal.inverseSquare
        (Rate.step rate)
        (Reciprocal.xNonzero (Rate.stepPositive rate))))
    (embeddedNat n)
piSquareOverSixTimesStepInverseSquareIsNat {n} nPositive =
  let
    rate = Rate.canonicalErdosStepRate n nPositive
    step = Rate.step rate
    inv2 =
      Reciprocal.inverseSquare
        step
        (Reciprocal.xNonzero (Rate.stepPositive rate))
    weightedSquare = canonicalStepSquareWeightedByNat nPositive
    cancel =
      Reciprocal.inverseSquareCancelsSquare
        step
        (Reciprocal.xNonzero (Rate.stepPositive rate))
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (BishopP.*-congʳ (BishopP.≃-symm weightedSquare))
    (BishopP.≃-trans
      (solve 3
        (λ n′ s2 i2 →
          (n′ ⊗ s2) ⊗ i2
          ⊜ n′ ⊗ (i2 ⊗ s2))
        BishopP.≃-refl
        (embeddedNat n) (square step) inv2)
      (BishopP.≃-trans
        (BishopP.*-congˡ cancel)
        (BishopP.*-identityʳ (embeddedNat n))))

partitionErdosBishopStepConstantCancellationLevel : ProofLevel
partitionErdosBishopStepConstantCancellationLevel = machineChecked
