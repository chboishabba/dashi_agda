module DASHI.Analysis.BishopComplexNonzeroFromComponentExact where

------------------------------------------------------------------------
-- COMPONENT APARTNESS -> POSITIVE COMPLEX NORM SQUARE
------------------------------------------------------------------------

open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Rational.Unnormalised using (0ℚᵘ)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexReciprocalExact as Reciprocal
import DASHI.Foundations.BishopSquareNonnegativeExact as SquareNN

negativeNegatesPositive :
  ∀ {x : BishopReal.ℝ} →
  BishopReal._<_ x BishopReal.0ℝ →
  BishopReal._<_ BishopReal.0ℝ (BishopReal.- x)
negativeNegatesPositive {x} xNegative =
  let
    shifted =
      BishopP.+-monoʳ-< (BishopReal.- x) xNegative

    leftZero :
      BishopReal._≃_
        (BishopReal._+_ x (BishopReal.- x))
        BishopReal.0ℝ
    leftZero =
      let open BishopP.ℝ-Solver in
      solve 1
        (λ x′ → x′ ⊕ (⊝ x′) ⊜ Κ 0ℚᵘ)
        BishopP.≃-refl x

    rightNeg :
      BishopReal._≃_
        (BishopReal._+_ BishopReal.0ℝ (BishopReal.- x))
        (BishopReal.- x)
    rightNeg = BishopP.+-identityˡ (BishopReal.- x)
  in
  BishopP.<-respʳ-≃ rightNeg
    (BishopP.<-respˡ-≃ leftZero shifted)

apartCongruent :
  ∀ {left right : BishopReal.ℝ} →
  BishopReal._≃_ left right →
  BishopReal._≄0 left →
  BishopReal._≄0 right
apartCongruent equivalent (inj₁ leftNegative) =
  inj₁
    (BishopP.<-respˡ-≃
      (BishopP.≃-symm equivalent)
      leftNegative)
apartCongruent equivalent (inj₂ leftPositive) =
  inj₂
    (BishopP.<-respʳ-≃
      equivalent
      leftPositive)

positiveNegatesNegative :
  ∀ {x : BishopReal.ℝ} →
  BishopReal._<_ BishopReal.0ℝ x →
  BishopReal._<_ (BishopReal.- x) BishopReal.0ℝ
positiveNegatesNegative {x} xPositive =
  let
    shifted =
      BishopP.+-monoʳ-< (BishopReal.- x) xPositive

    leftNeg :
      BishopReal._≃_
        (BishopReal._+_ (BishopReal.- x) BishopReal.0ℝ)
        (BishopReal.- x)
    leftNeg = BishopP.+-identityʳ (BishopReal.- x)

    rightZero :
      BishopReal._≃_
        (BishopReal._+_ (BishopReal.- x) x)
        BishopReal.0ℝ
    rightZero =
      let open BishopP.ℝ-Solver in
      solve 1
        (λ x′ → (⊝ x′) ⊕ x′ ⊜ Κ 0ℚᵘ)
        BishopP.≃-refl x
  in
  BishopP.<-respʳ-≃ rightZero
    (BishopP.<-respˡ-≃
      (BishopP.≃-symm leftNeg)
      shifted)

squarePositiveFromApart :
  ∀ {x : BishopReal.ℝ} →
  BishopReal._≄0 x →
  BishopReal._<_ BishopReal.0ℝ (Norm.square x)
squarePositiveFromApart {x} (inj₂ xPositive) =
  BishopP.posx⇒0<x
    (BishopP.posx,y⇒posx*y
      (BishopP.0<x⇒posx xPositive)
      (BishopP.0<x⇒posx xPositive))
squarePositiveFromApart {x} (inj₁ xNegative) =
  let
    negPositive = negativeNegatesPositive xNegative
    negSquarePositive =
      BishopP.posx⇒0<x
        (BishopP.posx,y⇒posx*y
          (BishopP.0<x⇒posx negPositive)
          (BishopP.0<x⇒posx negPositive))

    sameSquare :
      BishopReal._≃_
        (Norm.square (BishopReal.- x))
        (Norm.square x)
    sameSquare =
      let open BishopP.ℝ-Solver in
      solve 1
        (λ x′ → (⊝ x′) ⊗ (⊝ x′) ⊜ x′ ⊗ x′)
        BishopP.≃-refl x
  in
  BishopP.<-respʳ-≃ sameSquare negSquarePositive

normSquarePositiveFromImagApart :
  ∀ {z : Complex.BishopComplex} →
  BishopReal._≄0 (Complex.im z) →
  BishopReal._<_ BishopReal.0ℝ (Norm.normSqC z)
normSquarePositiveFromImagApart {Complex.complex a b} bApart =
  let
    realSquareNN =
      BishopP.nonNegx⇒0≤x
        (SquareNN.bishopSquareNonnegative a)

    imagSquarePositive = squarePositiveFromApart bApart

    strictFromRealSquare =
      BishopP.+-monoʳ-< (Norm.square a) imagSquarePositive

    leftNormalize :
      BishopReal._≃_
        (BishopReal._+_ (Norm.square a) BishopReal.0ℝ)
        (Norm.square a)
    leftNormalize = BishopP.+-identityʳ (Norm.square a)

    realSquareBelowNorm :
      BishopReal._<_
        (Norm.square a)
        (BishopReal._+_ (Norm.square a) (Norm.square b))
    realSquareBelowNorm =
      BishopP.<-respˡ-≃ leftNormalize strictFromRealSquare
  in
  BishopP.≤-<-trans realSquareNN realSquareBelowNorm

normSquarePositiveFromRealApart :
  ∀ {z : Complex.BishopComplex} →
  BishopReal._≄0 (Complex.re z) →
  BishopReal._<_ BishopReal.0ℝ (Norm.normSqC z)
normSquarePositiveFromRealApart {Complex.complex a b} aApart =
  let
    imagSquareNN =
      BishopP.nonNegx⇒0≤x
        (SquareNN.bishopSquareNonnegative b)

    realSquarePositive = squarePositiveFromApart aApart

    strict =
      BishopP.+-monoˡ-< (Norm.square b) realSquarePositive

    rightNormalize :
      BishopReal._≃_
        (BishopReal._+_ BishopReal.0ℝ (Norm.square b))
        (Norm.square b)
    rightNormalize = BishopP.+-identityˡ (Norm.square b)

    imagSquareBelowNorm :
      BishopReal._<_
        (Norm.square b)
        (BishopReal._+_ (Norm.square a) (Norm.square b))
    imagSquareBelowNorm =
      BishopP.<-respˡ-≃ rightNormalize strict
  in
  BishopP.≤-<-trans imagSquareNN imagSquareBelowNorm

complexNonzeroFromImagApart :
  ∀ {z : Complex.BishopComplex} →
  BishopReal._≄0 (Complex.im z) →
  Reciprocal.BishopComplexNonzero z
complexNonzeroFromImagApart apart = record
  { Reciprocal.normSquarePositive =
      normSquarePositiveFromImagApart apart
  }

complexNonzeroFromRealApart :
  ∀ {z : Complex.BishopComplex} →
  BishopReal._≄0 (Complex.re z) →
  Reciprocal.BishopComplexNonzero z
complexNonzeroFromRealApart apart = record
  { Reciprocal.normSquarePositive =
      normSquarePositiveFromRealApart apart
  }
