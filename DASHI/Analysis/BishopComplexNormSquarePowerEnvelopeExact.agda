module DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact where

------------------------------------------------------------------------
-- BISHOP COMPLEX NORM-SQUARE -> POWER-COMPONENT ENVELOPE
--
-- DASHI CONTRIBUTION
--
-- Pure complex-ring algebra proves normSq multiplicativity.  Consequently one
-- same-object radius certificate
--
--   normSq(q) ~= r*r
--
-- propagates to every natural power.  Turning the resulting squared component
-- inequalities into |component| <= r^n requires only one ordered-real
-- capability: reflection of square order on the nonnegative cone.
--
-- This removes an infinite family of q-power estimates from downstream
-- Eisenstein callers.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_,_)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Foundations.BishopSquareNonnegativeExact as SquareNN

open Algebra public using (_*C_)

square : BishopReal.ℝ → BishopReal.ℝ
square x = BishopReal._*_ x x

normSqC : Complex.BishopComplex → BishopReal.ℝ
normSqC (Complex.complex a b) =
  BishopReal._+_ (square a) (square b)

normSqOne : BishopReal._≃_ (normSqC Algebra.oneC) BishopReal.1ℝ
normSqOne =
  let open BishopP.ℝ-Solver
  in solve 0
    ((Κ (+ 1 / 1) ⊗ Κ (+ 1 / 1)) ⊕
     (Κ (+ 0 / 1) ⊗ Κ (+ 0 / 1))
     ⊜ Κ (+ 1 / 1))
    BishopP.≃-refl

normSqMultiply :
  ∀ left right →
  BishopReal._≃_
    (normSqC (Algebra._*C_ left right))
    (BishopReal._*_ (normSqC left) (normSqC right))
normSqMultiply
  (Complex.complex a b)
  (Complex.complex c d) =
  let open BishopP.ℝ-Solver
  in solve 4
    (λ a' b' c' d' →
      (((a' ⊗ c') ⊕ (⊝ (b' ⊗ d'))) ⊗
       ((a' ⊗ c') ⊕ (⊝ (b' ⊗ d'))))
      ⊕
      (((a' ⊗ d') ⊕ (b' ⊗ c')) ⊗
       ((a' ⊗ d') ⊕ (b' ⊗ c')))
      ⊜
      ((a' ⊗ a') ⊕ (b' ⊗ b')) ⊗
      ((c' ⊗ c') ⊕ (d' ⊗ d')))
    BishopP.≃-refl a b c d

normSqPower :
  ∀ q n →
  BishopReal._≃_
    (normSqC (Algebra.powC q n))
    (BishopReal.pow (normSqC q) n)
normSqPower q zero = normSqOne
normSqPower q (suc n) =
  BishopP.≃-trans
    (normSqMultiply q (Algebra.powC q n))
    (BishopP.≃-trans
      (BishopP.*-congˡ (normSqPower q n))
      (BishopP.*-comm
        (normSqC q)
        (BishopReal.pow (normSqC q) n)))

record BishopNonnegativeSquareReflection : Set₁ where
  field
    squareReflects :
      ∀ {left right} →
      BishopReal.NonNegative left →
      BishopReal.NonNegative right →
      BishopReal._≤_ (square left) (square right) →
      BishopReal._≤_ left right

open BishopNonnegativeSquareReflection public

record BishopQNormSquareRadius
    (q : Complex.BishopComplex)
    (ratio : BishopReal.ℝ) : Set₁ where
  field
    ratioNonnegative : BishopReal.NonNegative ratio
    normSquareAgreement :
      BishopReal._≃_
        (normSqC q)
        (square ratio)

open BishopQNormSquareRadius public

normSqPowerFromRadius :
  ∀ {q ratio} →
  BishopQNormSquareRadius q ratio →
  ∀ n →
  BishopReal._≃_
    (normSqC (Algebra.powC q n))
    (square (BishopReal.pow ratio n))
normSqPowerFromRadius {q} {ratio} radius zero =
  BishopP.≃-trans
    (normSqPower q zero)
    (let open BishopP.ℝ-Solver
     in solve 0
       (Κ (+ 1 / 1) ⊜ Κ (+ 1 / 1) ⊗ Κ (+ 1 / 1))
       BishopP.≃-refl)
normSqPowerFromRadius {q} {ratio} radius (suc n) =
  let
    previous = normSqPowerFromRadius radius n
    ratioN = BishopReal.pow ratio n
    ratioNN =
      BishopSequence.nonNegx⇒nonNegxⁿ n
        (ratioNonnegative radius)
  in
  BishopP.≃-trans
    (normSqMultiply q (Algebra.powC q n))
    (BishopP.≃-trans
      (BishopP.*-cong
        (normSquareAgreement radius)
        previous)
      (let open BishopP.ℝ-Solver
       in solve 2
         (λ r rn →
           (r ⊗ r) ⊗ (rn ⊗ rn)
           ⊜ (rn ⊗ r) ⊗ (rn ⊗ r))
         BishopP.≃-refl ratio ratioN))

componentSquareBelowNormSqReal :
  ∀ z →
  BishopReal._≤_
    (square (Complex.re z))
    (normSqC z)
componentSquareBelowNormSqReal (Complex.complex a b) =
  BishopP.≤-respˡ-≃
    (BishopP.+-identityʳ (square a))
    (BishopP.+-monoʳ-≤
      (square a)
      (BishopP.nonNegx⇒0≤x
        (SquareNN.bishopSquareNonnegative b)))

componentSquareBelowNormSqImag :
  ∀ z →
  BishopReal._≤_
    (square (Complex.im z))
    (normSqC z)
componentSquareBelowNormSqImag (Complex.complex a b) =
  BishopP.≤-respˡ-≃
    (BishopP.+-identityˡ (square b))
    (BishopP.+-monoˡ-≤
      (square b)
      (BishopP.nonNegx⇒0≤x
        (SquareNN.bishopSquareNonnegative a)))

absoluteSquare :
  ∀ x →
  BishopReal._≃_
    (square (BishopReal.∣ x ∣))
    (square x)
absoluteSquare x =
  BishopP.≃-trans
    (BishopP.≃-symm
      (BishopP.∣x*y∣≃∣x∣*∣y∣ x x))
    (BishopP.nonNegx⇒∣x∣≃x
      (SquareNN.bishopSquareNonnegative x))

powerEnvelopeFromNormSquare :
  ∀ (q : Complex.BishopComplex) {ratio} →
  BishopNonnegativeSquareReflection →
  BishopReal.NonNegative ratio →
  BishopReal._≃_
    (normSqC q)
    (square ratio) →
  let
    radius : BishopQNormSquareRadius q ratio
    radius = record
      { ratioNonnegative = _
      ; normSquareAgreement = _
      }
  in
  Set
powerEnvelopeFromNormSquare q reflection ratioNN normAgreement =
  let
    radius : BishopQNormSquareRadius q _
    radius = record
      { ratioNonnegative = ratioNN
      ; normSquareAgreement = normAgreement
      }

    componentBound :
      ∀ n component →
      (Complex.BishopComplex → BishopReal.ℝ) →
      BishopReal._≤_ (square component) (normSqC (Algebra.powC q (suc n))) →
      BishopReal._≤_
        (BishopReal.∣ component ∣)
        (BishopReal.pow _ (suc n))
    componentBound n component projection squaredBelow =
      let
        ratioPower = BishopReal.pow _ (suc n)
        ratioPowerNN =
          BishopSequence.nonNegx⇒nonNegxⁿ (suc n) ratioNN
        squaredTarget :
          BishopReal._≤_
            (square (BishopReal.∣ component ∣))
            (square ratioPower)
        squaredTarget =
          BishopP.≤-respʳ-≃
            (normSqPowerFromRadius radius (suc n))
            (BishopP.≤-respˡ-≃
              (absoluteSquare component)
              squaredBelow)
      in
      squareReflects reflection
        (BishopP.nonNeg∣x∣ component)
        ratioPowerNN
        squaredTarget
  in
  record
    { realPowerBound = λ n →
        componentBound n
          (Complex.re (Algebra.powC q (suc n)))
          Complex.re
          (componentSquareBelowNormSqReal
            (Algebra.powC q (suc n)))
    ; imagPowerBound = λ n →
        componentBound n
          (Complex.im (Algebra.powC q (suc n)))
          Complex.im
          (componentSquareBelowNormSqImag
            (Algebra.powC q (suc n)))
    }
