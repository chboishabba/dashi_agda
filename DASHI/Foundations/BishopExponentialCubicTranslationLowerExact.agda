module DASHI.Foundations.BishopExponentialCubicTranslationLowerExact where

------------------------------------------------------------------------
-- A TRANSLATION LOWER BOUND WITHOUT exp(x+y)=exp(x)exp(y)
--
-- For nonnegative z,x let
--
--   D3(x) = 1 + x + x^2/2 + x^3/6.
--
-- The first four x-columns of the nonnegative Cauchy/binomial expansion give
--
--   D3(x) * exp(z) <= exp(z+x).
--
-- The proof is finite-first:
--
--   S_N(z) S_4(x) <= T_{N+4}(z,x) = S_{N+4}(z+x),
--
-- then the pinned Bishop subsequence/order-limit theorems pass N -> infinity.
-- No global exponential addition law or infinite Cauchy-product rearrangement
-- is used.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc; _+_)
open import Data.Fin.Base using (toℕ)
open import Data.Integer.Base using (+_)
import Data.Nat.Properties as NatP
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ; _/_)
open import Relation.Binary.PropositionalEquality using (cong)

import Algebra.Properties.Semiring.Sum as SemiringSum
import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialPositiveOrderExact as Positive
import DASHI.Foundations.BishopExponentialFiniteCauchyCoefficientExact as Coeff
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopFiniteRectangleInsideCauchyTriangleExact as RectangleTriangle
import DASHI.Foundations.BishopFinSumSeriesBridgeExact as FinSum
open import DASHI.Physics.YangMills.CompactLieProofLevel

module BishopSum = SemiringSum BishopP.+-*-semiring

half oneSixth : BishopReal.ℝ
half = Exp.embed (+ 1 / 2)
oneSixth = Exp.embed (+ 1 / 6)

square cube : BishopReal.ℝ → BishopReal.ℝ
square value = BishopReal._*_ value value
cube value = BishopReal._*_ (square value) value

cubicTranslationFactor : BishopReal.ℝ → BishopReal.ℝ
cubicTranslationFactor x =
  BishopReal._+_
    (BishopReal._+_
      (BishopReal._+_ BishopReal.1ℝ x)
      (BishopReal._*_ half (square x)))
    (BishopReal._*_ oneSixth (cube x))

expFirstFourTerms :
  ∀ x →
  BishopReal._≃_
    (BishopSequence.SeriesOf (Exp.expTerm x) 4)
    (cubicTranslationFactor x)
expFirstFourTerms x =
  let open BishopP.ℝ-Solver in
  solve 1
    (λ x′ →
      ((((Κ 0ℚᵘ ⊕ (Κ 1ℚᵘ ⊗ Κ (+ 1 / 1)))
          ⊕ ((Κ 1ℚᵘ ⊗ x′) ⊗ Κ (+ 1 / 1)))
          ⊕ ((((Κ 1ℚᵘ ⊗ x′) ⊗ x′) ⊗ Κ (+ 1 / 2))))
          ⊕ (((((Κ 1ℚᵘ ⊗ x′) ⊗ x′) ⊗ x′) ⊗ Κ (+ 1 / 6)))
      ⊜ (((Κ 1ℚᵘ ⊕ x′)
          ⊕ (Κ (+ 1 / 2) ⊗ (x′ ⊗ x′)))
          ⊕ (Κ (+ 1 / 6) ⊗ ((x′ ⊗ x′) ⊗ x′))))
    BishopP.≃-refl x

expTriangleIsPartialSum :
  ∀ left right total →
  BishopReal._≃_
    (Row.trianglePartial
      (Exp.expTerm left)
      (Exp.expTerm right)
      total)
    (BishopSequence.SeriesOf
      (Exp.expTerm (BishopReal._+_ left right))
      total)
expTriangleIsPartialSum left right total =
  BishopP.≃-trans
    (BishopSum.sum-cong-≋
      (λ index →
        Coeff.finiteExponentialCauchyCoefficient
          left right (toℕ index)))
    (FinSum.finSumIsSeriesOf
      (Exp.expTerm (BishopReal._+_ left right)) total)

finiteCubicTranslationLower :
  ∀ {z x} →
  (zNonnegative : BishopReal.NonNegative z) →
  (xNonnegative : BishopReal.NonNegative x) →
  ∀ count →
  BishopReal._≤_
    (BishopReal._*_
      (BishopSequence.SeriesOf (Exp.expTerm z) count)
      (cubicTranslationFactor x))
    (BishopSequence.SeriesOf
      (Exp.expTerm (BishopReal._+_ z x))
      (count + 4))
finiteCubicTranslationLower {z} {x} zNonnegative xNonnegative count =
  BishopP.≤-respʳ-≃
    (expTriangleIsPartialSum z x (count + 4))
    (BishopP.≤-respˡ-≃
      (BishopP.*-congˡ (expFirstFourTerms x))
      (RectangleTriangle.rectangleProductInsideTriangle
        (Positive.expTermNonnegative zNonnegative)
        (Positive.expTermNonnegative xNonnegative)
        count 4))

rightShiftedPartial :
  BishopReal.ℝ → Nat → BishopReal.ℝ
rightShiftedPartial value count =
  BishopSequence.shift
    (BishopSequence.SeriesOf (Exp.expTerm value)) 4 count

finiteCubicTranslationLowerShifted :
  ∀ {z x} →
  (zNonnegative : BishopReal.NonNegative z) →
  (xNonnegative : BishopReal.NonNegative x) →
  ∀ count →
  BishopReal._≤_
    (BishopReal._*_
      (BishopSequence.SeriesOf (Exp.expTerm z) count)
      (cubicTranslationFactor x))
    (rightShiftedPartial (BishopReal._+_ z x) count)
finiteCubicTranslationLowerShifted {z} {x} zNonnegative xNonnegative count =
  BishopP.≤-respʳ-≃
    (BishopP.≃-refl₂
      (cong
        (BishopSequence.SeriesOf
          (Exp.expTerm (BishopReal._+_ z x)))
        (NatP.+-comm count 4)))
    (finiteCubicTranslationLower zNonnegative xNonnegative count)

leftProductConvergent :
  ∀ z x →
  BishopSequence._isConvergent
    (λ count →
      BishopReal._*_
        (BishopSequence.SeriesOf (Exp.expTerm z) count)
        (cubicTranslationFactor x))
leftProductConvergent z x =
  let
    expZ : BishopSequence._isConvergent
      (BishopSequence.SeriesOf (Exp.expTerm z))
    expZ = Exp.bishopExp z , Exp.bishopExpConverges z

    constantFactor : BishopSequence._isConvergent
      (λ _ → cubicTranslationFactor x)
    constantFactor =
      cubicTranslationFactor x ,
      BishopSequence.xₙ≃c⇒xₙ→c
        (λ {(suc n) → BishopP.≃-refl})
  in
  BishopReal._*_ (Exp.bishopExp z) (cubicTranslationFactor x) ,
  BishopSequence.xₙyₙ→x₀y₀ expZ constantFactor

rightShiftedConvergent :
  ∀ value →
  BishopSequence._isConvergent (rightShiftedPartial value)
rightShiftedConvergent value =
  let
    full : BishopSequence._isConvergent
      (BishopSequence.SeriesOf (Exp.expTerm value))
    full = Exp.bishopExp value , Exp.bishopExpConverges value
  in
  Exp.bishopExp value ,
  BishopSequence.fast-xₙ⊆yₙ∧yₙ→y⇒xₙ→y
    (BishopSequence.shift-is-subsequence
      (BishopSequence.SeriesOf (Exp.expTerm value)) 4)
    full

cubicTranslationLower :
  ∀ {z x} →
  BishopReal.NonNegative z →
  BishopReal.NonNegative x →
  BishopReal._≤_
    (BishopReal._*_
      (Exp.bishopExp z)
      (cubicTranslationFactor x))
    (Exp.bishopExp (BishopReal._+_ z x))
cubicTranslationLower {z} {x} zNonnegative xNonnegative =
  BishopSequence.xₙ≤yₙ⇒limxₙ≤limyₙ
    (finiteCubicTranslationLowerShifted zNonnegative xNonnegative)
    (leftProductConvergent z x)
    (rightShiftedConvergent (BishopReal._+_ z x))

bishopExponentialCubicTranslationLowerLevel : ProofLevel
bishopExponentialCubicTranslationLowerLevel = machineChecked
