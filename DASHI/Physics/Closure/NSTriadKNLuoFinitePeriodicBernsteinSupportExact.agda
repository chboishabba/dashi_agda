module DASHI.Physics.Closure.NSTriadKNLuoFinitePeriodicBernsteinSupportExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Harmonic-analysis reference:
-- Author: Loukas Grafakos.
-- Title: "Classical Fourier Analysis".
-- DOI: 10.1007/978-1-4939-1194-3.
--
-- PURPOSE
-- Prove the exact finite-support square form of the periodic Bernstein step.
-- If every Fourier coefficient of Delta_q F is bounded in square by
-- ||F||_1^2 and the number/weight of active modes is at most lambda_q^3,
-- then
--
--   ||Delta_q F||_2^2 <= lambda_q^3 ||F||_1^2.
--
-- The Fourier inversion coefficient estimate and the lattice support count
-- remain explicit producer fields.  The finite summation and scale transport
-- are proved here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

record PeriodicOutputMode : Set where
  constructor periodic-output-mode
  field
    coefficientSquared : ℚ

open PeriodicOutputMode public

supportMass : List PeriodicOutputMode → ℚ
supportMass [] = 0ℚ
supportMass (_ ∷ modes) = 1ℚ + supportMass modes

outputL2Squared : List PeriodicOutputMode → ℚ
outputL2Squared [] = 0ℚ
outputL2Squared (mode ∷ modes) =
  coefficientSquared mode + outputL2Squared modes

record FinitePeriodicBernsteinData : Set₁ where
  constructor finite-periodic-bernstein-data
  field
    modes : List PeriodicOutputMode
    inputL1Squared outputScaleCubed : ℚ

    inputL1SquaredNonnegative :
      0ℚ ≤ inputL1Squared

    fourierCoefficientBound :
      (mode : PeriodicOutputMode) →
      coefficientSquared mode ≤ inputL1Squared

    supportCountBound :
      supportMass modes ≤ outputScaleCubed

open FinitePeriodicBernsteinData public

outputL2SquareBoundBySupport :
  (dataSet : FinitePeriodicBernsteinData) →
  outputL2Squared (modes dataSet)
  ≤ supportMass (modes dataSet) * inputL1Squared dataSet
outputL2SquareBoundBySupport dataSet = go (modes dataSet)
  where
  go :
    (remaining : List PeriodicOutputMode) →
    outputL2Squared remaining
    ≤ supportMass remaining * inputL1Squared dataSet
  go [] = ℚₚ.≤-refl
  go (mode ∷ remaining) =
    let
      summed :
        coefficientSquared mode + outputL2Squared remaining
        ≤ inputL1Squared dataSet
          + supportMass remaining * inputL1Squared dataSet
      summed =
        ℚₚ.+-mono-≤
          (fourierCoefficientBound dataSet mode)
          (go remaining)

      targetMeaning :
        inputL1Squared dataSet
          + supportMass remaining * inputL1Squared dataSet
        ≡ (1ℚ + supportMass remaining) * inputL1Squared dataSet
      targetMeaning =
        solve
          ( inputL1Squared dataSet
          ∷ supportMass remaining
          ∷ [])
    in
    subst
      (λ upper →
        coefficientSquared mode + outputL2Squared remaining ≤ upper)
      targetMeaning
      summed

supportScaleTransport :
  (dataSet : FinitePeriodicBernsteinData) →
  supportMass (modes dataSet) * inputL1Squared dataSet
  ≤ outputScaleCubed dataSet * inputL1Squared dataSet
supportScaleTransport dataSet =
  let
    raw :
      inputL1Squared dataSet * supportMass (modes dataSet)
      ≤ inputL1Squared dataSet * outputScaleCubed dataSet
    raw =
      let
        instance
          inputSquareIsNonnegative =
            nonNegative (inputL1SquaredNonnegative dataSet)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (inputL1Squared dataSet)
        (supportCountBound dataSet)

    lowerMeaning :
      inputL1Squared dataSet * supportMass (modes dataSet)
      ≡ supportMass (modes dataSet) * inputL1Squared dataSet
    lowerMeaning =
      solve
        ( inputL1Squared dataSet
        ∷ supportMass (modes dataSet)
        ∷ [])

    upperMeaning :
      inputL1Squared dataSet * outputScaleCubed dataSet
      ≡ outputScaleCubed dataSet * inputL1Squared dataSet
    upperMeaning =
      solve
        ( inputL1Squared dataSet
        ∷ outputScaleCubed dataSet
        ∷ [])
  in
  subst
    (λ lower →
      lower ≤ outputScaleCubed dataSet * inputL1Squared dataSet)
    lowerMeaning
    (subst
      (λ upper →
        inputL1Squared dataSet * supportMass (modes dataSet) ≤ upper)
      upperMeaning
      raw)

finitePeriodicBernsteinSquare :
  (dataSet : FinitePeriodicBernsteinData) →
  outputL2Squared (modes dataSet)
  ≤ outputScaleCubed dataSet * inputL1Squared dataSet
finitePeriodicBernsteinSquare dataSet =
  ℚₚ.≤-trans
    (outputL2SquareBoundBySupport dataSet)
    (supportScaleTransport dataSet)
