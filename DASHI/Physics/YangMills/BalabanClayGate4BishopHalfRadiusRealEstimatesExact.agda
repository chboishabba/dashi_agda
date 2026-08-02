module DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (ℚᵘ; mkℚᵘ; _/_)

import Real as BishopReal
import RealProperties as BishopProps

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Constructive-real inhabitants for the round-six Bishop cutset.
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- Master's thesis, University of Canterbury (2022).
-- arXiv:2205.08354.
--
-- Concrete statements:
--
--   halfBallSquareBelowQuarter :  |x| <= 1/2  ==>  x^2 <= 1/4
--
--   sineCoefficientRecurrence  : successive sine   term magnitudes
--                                shrink by factor 1/24 on the half ball,
--   cosineCoefficientRecurrence: successive cosine term magnitudes
--                                shrink by factor 1/8  on the half ball.
--
-- The real ratio constants are the closed rational targets 1/24 and 1/8
-- from BalabanClayGate4BishopHalfRadiusRationalConstantsExact:
-- (1/4)/6 = 1/24 and (1/4)/2 = 1/8.  The factorial denominators below
-- express the successive-term ratios
--
--   |x|^2 / ((2k+1)!)  ->  |x|^2 / ((2k+3)!)  (sine,    ratio <= 1/24)
--   |x|^2 / ((2k)!)    ->  |x|^2 / ((2k+2)!)  (cosine,  ratio <= 1/8)
--
-- once multiplied out into the division-free real form used below.
------------------------------------------------------------------------

half quarter oneTwentyFourth oneEighth : ℚᵘ
half = + 1 / 2
quarter = + 1 / 4
oneTwentyFourth = + 1 / 24
oneEighth = + 1 / 8

two : Nat
two = suc (suc zero)

oddExponent evenExponent : Nat → Nat
oddExponent n = two * n + suc zero
evenExponent n = two * n

factorial : Nat → Nat
factorial zero = 1
factorial (suc n) = suc n * factorial n

inverseFactorialRational : Nat → ℚᵘ
inverseFactorialRational n = mkℚᵘ (+ 1) (factorial n)

square : BishopReal.ℝ → BishopReal.ℝ
square x = x BishopReal.* x

halfBallSquareBelowQuarter : Set
halfBallSquareBelowQuarter =
  ∀ {x : BishopReal.ℝ} →
  BishopReal.∣ x ∣ BishopReal.≤ half BishopReal.⋆ →
  square x BishopReal.≤ quarter BishopReal.⋆

halfBallSquareBelowQuarterProof : halfBallSquareBelowQuarter
halfBallSquareBelowQuarterProof {x} halfBall =
  BishopProps.≤-trans
    xx≤absabs
    (BishopProps.≤-respʳ-≃ halfHalf≃quarter absabs≤halfhalf)
  where
    abs : BishopReal.ℝ
    abs = BishopReal.∣ x ∣

    abs-x-nonneg : BishopReal.NonNegative (abs BishopReal.- x)
    abs-x-nonneg = BishopProps.x≤∣x∣ {x}

    negx-abs-nonneg :
      BishopReal.NonNegative
        (abs BishopReal.+ (BishopReal.- (BishopReal.- x)))
    negx-abs-nonneg =
      BishopProps.≤-respʳ-≃
        (BishopProps.∣-x∣≃∣x∣ {x})
        (BishopProps.x≤∣x∣ {BishopReal.- x})

    abs+x-nonneg : BishopReal.NonNegative (abs BishopReal.+ x)
    abs+x-nonneg =
      BishopProps.nonNeg-cong
        (BishopProps.+-congʳ abs (BishopProps.neg-involutive x))
        negx-abs-nonneg

    diffSq :
      (abs BishopReal.- x) BishopReal.* (abs BishopReal.+ x)
        BishopReal.≃
      (abs BishopReal.* abs) BishopReal.- (x BishopReal.* x)
    diffSq = begin
      (abs BishopReal.- x) BishopReal.* (abs BishopReal.+ x)
        ≃⟨ BishopProps.*-distribʳ-+ (abs BishopReal.+ x) abs (BishopReal.- x) ⟩
      abs BishopReal.* (abs BishopReal.+ x)
        BishopReal.+ (BishopReal.- x) BishopReal.* (abs BishopReal.+ x)
        ≃⟨ BishopProps.+-cong
             (BishopProps.*-distribˡ-+ abs abs x)
             (BishopProps.*-distribˡ-+ (BishopReal.- x) abs x) ⟩
      (abs BishopReal.* abs BishopReal.+ abs BishopReal.* x)
        BishopReal.+ ((BishopReal.- x) BishopReal.* abs
          BishopReal.+ (BishopReal.- x) BishopReal.* x)
        ≃⟨ BishopProps.+-congʳ
             (abs BishopReal.* abs BishopReal.+ abs BishopReal.* x) bStep ⟩
      (abs BishopReal.* abs BishopReal.+ abs BishopReal.* x)
        BishopReal.+ (BishopReal.- (abs BishopReal.* x)
          BishopReal.+ BishopReal.- (x BishopReal.* x))
        ≃⟨ BishopProps.+-assoc (abs BishopReal.* abs) (abs BishopReal.* x)
             (BishopReal.- (abs BishopReal.* x)
               BishopReal.+ BishopReal.- (x BishopReal.* x)) ⟩
      abs BishopReal.* abs
        BishopReal.+ (abs BishopReal.* x
          BishopReal.+ (BishopReal.- (abs BishopReal.* x)
            BishopReal.+ BishopReal.- (x BishopReal.* x)))
        ≃⟨ BishopProps.+-congʳ (abs BishopReal.* abs) cStep ⟩
      abs BishopReal.* abs BishopReal.+ BishopReal.- (x BishopReal.* x)
        ∎
      where
        open BishopProps.≃-Reasoning

        bStep :
          ((BishopReal.- x) BishopReal.* abs
            BishopReal.+ (BishopReal.- x) BishopReal.* x)
            BishopReal.≃
          (BishopReal.- (abs BishopReal.* x)
            BishopReal.+ BishopReal.- (x BishopReal.* x))
        bStep = BishopProps.≃-trans
          (BishopProps.+-cong
            (BishopProps.≃-symm (BishopProps.neg-distribˡ-* x abs))
            (BishopProps.≃-symm (BishopProps.neg-distribˡ-* x x)))
          (BishopProps.+-cong
            (BishopProps.≃-symm
              (BishopProps.-‿cong (BishopProps.*-comm abs x)))
            BishopProps.≃-refl)

        cStep :
          (abs BishopReal.* x
            BishopReal.+ (BishopReal.- (abs BishopReal.* x)
              BishopReal.+ BishopReal.- (x BishopReal.* x)))
            BishopReal.≃
          BishopReal.- (x BishopReal.* x)
        cStep = BishopProps.≃-trans
          (BishopProps.≃-symm
            (BishopProps.+-assoc (abs BishopReal.* x)
              (BishopReal.- (abs BishopReal.* x))
              (BishopReal.- (x BishopReal.* x))))
          (BishopProps.≃-trans
            (BishopProps.+-congˡ (BishopReal.- (x BishopReal.* x))
              (BishopProps.+-inverseʳ (abs BishopReal.* x)))
            (BishopProps.+-identityˡ (BishopReal.- (x BishopReal.* x))))

    absabs-minus-xx-nonneg :
      BishopReal.NonNegative
        ((abs BishopReal.* abs) BishopReal.- (x BishopReal.* x))
    absabs-minus-xx-nonneg =
      BishopProps.nonNeg-cong
        diffSq
        (BishopProps.nonNegx,y⇒nonNegx*y abs-x-nonneg abs+x-nonneg)

    xx≤absabs : square x BishopReal.≤ abs BishopReal.* abs
    xx≤absabs = absabs-minus-xx-nonneg

    absabs≤halfhalf :
      (abs BishopReal.* abs)
        BishopReal.≤ (half BishopReal.⋆) BishopReal.* (half BishopReal.⋆)
    absabs≤halfhalf =
      BishopProps.*-mono-≤
        {x = abs} {y = half BishopReal.⋆} {z = abs} {w = half BishopReal.⋆}
        (BishopProps.nonNeg∣x∣ x) (BishopProps.nonNeg∣x∣ x)
        halfBall halfBall

    halfHalf≃quarter :
      (half BishopReal.⋆) BishopReal.* (half BishopReal.⋆)
        BishopReal.≃
      quarter BishopReal.⋆
    halfHalf≃quarter =
      BishopProps.≃-symm (BishopProps.⋆-distrib-* half half)

sineCoefficientRecurrence : Set
sineCoefficientRecurrence =
  ∀ {x : BishopReal.ℝ} (k : Nat) →
  BishopReal.∣ x ∣ BishopReal.≤ half BishopReal.⋆ →
  BishopReal._⋆ (inverseFactorialRational (oddExponent (suc k)))
    BishopReal.* BishopReal.∣ BishopReal.pow x (oddExponent (suc k)) ∣
    BishopReal.≤
    (oneTwentyFourth BishopReal.⋆)
    BishopReal.*
    (BishopReal._⋆ (inverseFactorialRational (oddExponent k))
      BishopReal.* BishopReal.∣ BishopReal.pow x (oddExponent k) ∣)

cosineCoefficientRecurrence : Set
cosineCoefficientRecurrence =
  ∀ {x : BishopReal.ℝ} (k : Nat) →
  BishopReal.∣ x ∣ BishopReal.≤ half BishopReal.⋆ →
  BishopReal._⋆ (inverseFactorialRational (evenExponent (suc k)))
    BishopReal.* BishopReal.∣ BishopReal.pow x (evenExponent (suc k)) ∣
    BishopReal.≤
    (oneEighth BishopReal.⋆)
    BishopReal.*
    (BishopReal._⋆ (inverseFactorialRational (evenExponent k))
      BishopReal.* BishopReal.∣ BishopReal.pow x (evenExponent k) ∣)

bishopHalfRadiusRealEstimatesLevel : ProofLevel
bishopHalfRadiusRealEstimatesLevel = conditional
