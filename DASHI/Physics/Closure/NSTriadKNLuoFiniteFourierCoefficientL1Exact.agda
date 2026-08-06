module DASHI.Physics.Closure.NSTriadKNLuoFiniteFourierCoefficientL1Exact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Loukas Grafakos.
-- Title: "Classical Fourier Analysis".
-- DOI: 10.1007/978-1-4939-1194-3.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Prove the finite ordered core of the Fourier coefficient L1 estimate.
-- Each quadrature/sample contribution c_i carries a nonnegative pointwise
-- magnitude m_i and the unit-phase certificate
--
--   -m_i <= c_i <= m_i.
--
-- Finite summation gives
--
--   -sum m_i <= sum c_i <= sum m_i,
--
-- and hence, without introducing square roots,
--
--   (sum c_i)^2 <= (sum m_i)^2.
--
-- This is the radical-free finite form of |Fhat(k)| <= ||F||_1.  The only
-- remaining analytic identification is that multiplication by the torus
-- phase exp(-ik.x) supplies the pointwise interval certificate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; -_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

record FourierL1Sample : Set where
  constructor fourier-l1-sample
  field
    contribution magnitude : ℚ
    magnitudeNonnegative : 0ℚ ≤ magnitude
    lowerPhaseBound : - magnitude ≤ contribution
    upperPhaseBound : contribution ≤ magnitude

open FourierL1Sample public

coefficientSum : List FourierL1Sample → ℚ
coefficientSum [] = 0ℚ
coefficientSum (sample ∷ samples) =
  contribution sample + coefficientSum samples

l1Mass : List FourierL1Sample → ℚ
l1Mass [] = 0ℚ
l1Mass (sample ∷ samples) =
  magnitude sample + l1Mass samples

l1MassNonnegative :
  (samples : List FourierL1Sample) →
  0ℚ ≤ l1Mass samples
l1MassNonnegative [] = ℚₚ.≤-refl
l1MassNonnegative (sample ∷ samples) =
  L2.addNonnegative
    (magnitudeNonnegative sample)
    (l1MassNonnegative samples)

coefficientUpperBound :
  (samples : List FourierL1Sample) →
  coefficientSum samples ≤ l1Mass samples
coefficientUpperBound [] = ℚₚ.≤-refl
coefficientUpperBound (sample ∷ samples) =
  ℚₚ.+-mono-≤
    (upperPhaseBound sample)
    (coefficientUpperBound samples)

coefficientLowerBound :
  (samples : List FourierL1Sample) →
  - l1Mass samples ≤ coefficientSum samples
coefficientLowerBound [] = ℚₚ.≤-refl
coefficientLowerBound (sample ∷ samples) =
  let
    summed :
      - magnitude sample + (- l1Mass samples)
      ≤ contribution sample + coefficientSum samples
    summed =
      ℚₚ.+-mono-≤
        (lowerPhaseBound sample)
        (coefficientLowerBound samples)

    lowerMeaning :
      - (magnitude sample + l1Mass samples)
      ≡ - magnitude sample + (- l1Mass samples)
    lowerMeaning =
      solve (magnitude sample ∷ l1Mass samples ∷ [])
  in
  subst
    (λ lower → lower ≤ contribution sample + coefficientSum samples)
    (sym lowerMeaning)
    summed

subtractNonnegative :
  ∀ {left right : ℚ} →
  left ≤ right →
  0ℚ ≤ right - left
subtractNonnegative {left} {right} left≤right =
  let
    translated :
      (- left) + left ≤ (- left) + right
    translated = ℚₚ.+-monoʳ-≤ (- left) left≤right

    lowerMeaning : (- left) + left ≡ 0ℚ
    lowerMeaning = solve (left ∷ [])

    upperMeaning : (- left) + right ≡ right - left
    upperMeaning = solve (left ∷ right ∷ [])
  in
  subst
    (λ lower → lower ≤ right - left)
    lowerMeaning
    (subst
      (λ upper → (- left) + left ≤ upper)
      upperMeaning
      translated)

addNonnegativeFromNegativeLower :
  ∀ {value radius : ℚ} →
  - radius ≤ value →
  0ℚ ≤ radius + value
addNonnegativeFromNegativeLower {value} {radius} lower =
  let
    translated :
      radius + (- radius) ≤ radius + value
    translated = ℚₚ.+-monoʳ-≤ radius lower

    lowerMeaning : radius + (- radius) ≡ 0ℚ
    lowerMeaning = solve (radius ∷ [])
  in
  subst
    (λ lowerValue → lowerValue ≤ radius + value)
    lowerMeaning
    translated

intervalSquareBound :
  ∀ value radius →
  0ℚ ≤ radius →
  - radius ≤ value →
  value ≤ radius →
  L2.square value ≤ L2.square radius
intervalSquareBound value radius radiusNonnegative lower upper =
  let
    rightMinusValueNonnegative : 0ℚ ≤ radius - value
    rightMinusValueNonnegative = subtractNonnegative upper

    rightPlusValueNonnegative : 0ℚ ≤ radius + value
    rightPlusValueNonnegative = addNonnegativeFromNegativeLower lower

    productNonnegative :
      0ℚ ≤ (radius - value) * (radius + value)
    productNonnegative =
      let
        instance
          firstIsNonnegative =
            nonNegative rightMinusValueNonnegative
          secondIsNonnegative =
            nonNegative rightPlusValueNonnegative
          productIsNonnegative =
            ℚₚ.nonNeg*nonNeg⇒nonNeg
              (radius - value)
              (radius + value)
      in
      ℚₚ.nonNegative⁻¹
        ((radius - value) * (radius + value))

    addProduct :
      L2.square value + 0ℚ
      ≤ L2.square value
        + (radius - value) * (radius + value)
    addProduct =
      ℚₚ.+-mono-≤ ℚₚ.≤-refl productNonnegative

    lowerMeaning :
      L2.square value + 0ℚ ≡ L2.square value
    lowerMeaning = ℚₚ.+-identityʳ (L2.square value)

    upperMeaning :
      L2.square value
        + (radius - value) * (radius + value)
      ≡ L2.square radius
    upperMeaning = solve (value ∷ radius ∷ [])
  in
  subst
    (λ lowerValue → lowerValue ≤ L2.square radius)
    lowerMeaning
    (subst
      (λ upperValue → L2.square value + 0ℚ ≤ upperValue)
      upperMeaning
      addProduct)

finiteFourierCoefficientL1Square :
  (samples : List FourierL1Sample) →
  L2.square (coefficientSum samples)
  ≤ L2.square (l1Mass samples)
finiteFourierCoefficientL1Square samples =
  intervalSquareBound
    (coefficientSum samples)
    (l1Mass samples)
    (l1MassNonnegative samples)
    (coefficientLowerBound samples)
    (coefficientUpperBound samples)

record FiniteFourierCoefficientData : Set where
  constructor finite-fourier-coefficient-data
  field
    samples : List FourierL1Sample
    coefficientSquared inputL1Squared : ℚ
    coefficientMeaning :
      coefficientSquared ≡ L2.square (coefficientSum samples)
    inputL1Meaning :
      inputL1Squared ≡ L2.square (l1Mass samples)

open FiniteFourierCoefficientData public

finiteFourierCoefficientBound :
  (dataSet : FiniteFourierCoefficientData) →
  coefficientSquared dataSet ≤ inputL1Squared dataSet
finiteFourierCoefficientBound dataSet =
  subst
    (λ lower → lower ≤ inputL1Squared dataSet)
    (sym (coefficientMeaning dataSet))
    (subst
      (λ upper →
        L2.square (coefficientSum (samples dataSet)) ≤ upper)
      (sym (inputL1Meaning dataSet))
      (finiteFourierCoefficientL1Square (samples dataSet)))
