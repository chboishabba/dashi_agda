module DASHI.Physics.Closure.NSTriadKNLuoFiniteParsevalExtractionExact where

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
-- Formalise finite Parseval as a recursive orthogonal-extraction theorem.
-- Each extraction step splits the current physical energy exactly into one
-- Fourier coefficient square plus the orthogonal remainder.  Iterating gives
--
--   initialEnergy = sum coefficientSquares + finalResidual.
--
-- In the complete finite Fourier basis the residual is zero, yielding exact
-- Parseval.  This module proves the entire telescoping argument; the torus
-- realization must construct the extraction steps from character
-- orthogonality for its chosen normalization.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; _/_; _+_; _*_; _-_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

data ParsevalExtraction : ℚ → ℚ → Set where
  exhausted :
    (residual : ℚ) →
    ParsevalExtraction residual residual

  extract :
    (current coefficientSquared remainder finalResidual : ℚ) →
    current ≡ coefficientSquared + remainder →
    ParsevalExtraction remainder finalResidual →
    ParsevalExtraction current finalResidual

coefficientSquareMass :
  ∀ {initial residual} →
  ParsevalExtraction initial residual →
  ℚ
coefficientSquareMass (exhausted residual) = 0ℚ
coefficientSquareMass
  (extract current coefficientSquared remainder finalResidual split rest) =
  coefficientSquared + coefficientSquareMass rest

finiteParsevalWithResidual :
  ∀ {initial residual}
    (extraction : ParsevalExtraction initial residual) →
  initial ≡ coefficientSquareMass extraction + residual
finiteParsevalWithResidual (exhausted residual) =
  sym (ℚₚ.+-identityˡ residual)
finiteParsevalWithResidual
  (extract current coefficientSquared remainder finalResidual split rest) =
  trans
    split
    (trans
      (cong
        (coefficientSquared +_)
        (finiteParsevalWithResidual rest))
      (sym
        (ℚₚ.+-assoc
          coefficientSquared
          (coefficientSquareMass rest)
          finalResidual)))

record CompleteFiniteParsevalData : Set where
  constructor complete-finite-parseval-data
  field
    physicalL2Squared : ℚ
    extraction : ParsevalExtraction physicalL2Squared 0ℚ

open CompleteFiniteParsevalData public

fourierCoefficientSquareSum : CompleteFiniteParsevalData → ℚ
fourierCoefficientSquareSum dataSet =
  coefficientSquareMass (extraction dataSet)

completeFiniteParseval :
  (dataSet : CompleteFiniteParsevalData) →
  physicalL2Squared dataSet ≡ fourierCoefficientSquareSum dataSet
completeFiniteParseval dataSet =
  trans
    (finiteParsevalWithResidual (extraction dataSet))
    (ℚₚ.+-identityʳ
      (fourierCoefficientSquareSum dataSet))

-- Exact two-point periodic Fourier calibration.  This is the elementary
-- orthogonality step from which a dyadic finite transform can be built.
twoPointHalf : ℚ
twoPointHalf = Int.+ 1 / 2

twoPointFourierParseval :
  (left right : ℚ) →
  twoPointHalf
    * ( (left + right) * (left + right)
      + (left - right)
        * (left - right))
  ≡ left * left + right * right
twoPointFourierParseval left right =
  solve (left ∷ right ∷ [])
