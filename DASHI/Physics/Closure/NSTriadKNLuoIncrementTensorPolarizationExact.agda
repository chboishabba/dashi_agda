module DASHI.Physics.Closure.NSTriadKNLuoIncrementTensorPolarizationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions
-- of Euler's Equation".
-- Communications in Mathematical Physics 165 (1994), 207--209.
-- DOI: 10.1007/BF02099744.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Close the coefficient algebra behind the finite-difference increment
-- tensor.  This is the exact polarization identity used when the literal
-- spatial kernel
--
--   (u(x-y)-u(x)) tensor (u(x-y)-u(x))
--
-- is expanded into Fourier coefficients.  The theorem is deliberately only
-- the algebraic coefficient step: translation phases, integration and the
-- identification with the official full-shell pair list remain separate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)

incrementProduct : ℚ → ℚ → ℚ → ℚ → ℚ
incrementProduct translatedLeft baseLeft translatedRight baseRight =
  (translatedLeft - baseLeft) * (translatedRight - baseRight)

expandedIncrementProduct : ℚ → ℚ → ℚ → ℚ → ℚ
expandedIncrementProduct translatedLeft baseLeft translatedRight baseRight =
  translatedLeft * translatedRight
  - translatedLeft * baseRight
  - baseLeft * translatedRight
  + baseLeft * baseRight

incrementProductExpansion :
  ∀ translatedLeft baseLeft translatedRight baseRight →
  incrementProduct translatedLeft baseLeft translatedRight baseRight
  ≡ expandedIncrementProduct
      translatedLeft baseLeft translatedRight baseRight
incrementProductExpansion
  translatedLeft baseLeft translatedRight baseRight =
  solve
    ( translatedLeft
    ∷ baseLeft
    ∷ translatedRight
    ∷ baseRight
    ∷ [] )

incrementSquare : ℚ → ℚ → ℚ
incrementSquare translated base = incrementProduct translated base translated base

expandedIncrementSquare : ℚ → ℚ → ℚ
expandedIncrementSquare translated base =
  translated * translated
  - translated * base
  - base * translated
  + base * base

incrementSquareExpansion :
  ∀ translated base →
  incrementSquare translated base
  ≡ expandedIncrementSquare translated base
incrementSquareExpansion translated base =
  incrementProductExpansion translated base translated base

constantLeftIncrementVanishes :
  ∀ base translatedRight baseRight →
  incrementProduct base base translatedRight baseRight ≡ 0ℚ
constantLeftIncrementVanishes base translatedRight baseRight =
  solve (base ∷ translatedRight ∷ baseRight ∷ [])

constantRightIncrementVanishes :
  ∀ translatedLeft baseLeft base →
  incrementProduct translatedLeft baseLeft base base ≡ 0ℚ
constantRightIncrementVanishes translatedLeft baseLeft base =
  solve (translatedLeft ∷ baseLeft ∷ base ∷ [])

constantIncrementSquareVanishes :
  ∀ base → incrementSquare base base ≡ 0ℚ
constantIncrementSquareVanishes base =
  solve (base ∷ [])

incrementProductSwap :
  ∀ translatedLeft baseLeft translatedRight baseRight →
  incrementProduct translatedLeft baseLeft translatedRight baseRight
  ≡ incrementProduct translatedRight baseRight translatedLeft baseLeft
incrementProductSwap translatedLeft baseLeft translatedRight baseRight =
  solve
    ( translatedLeft
    ∷ baseLeft
    ∷ translatedRight
    ∷ baseRight
    ∷ [] )

incrementTensorPolarizationAlgebraClosed : Bool
incrementTensorPolarizationAlgebraClosed = true

constantModeCancellationClosed : Bool
constantModeCancellationClosed = true

incrementTensorPolarizationAlgebraClosedIsTrue :
  incrementTensorPolarizationAlgebraClosed ≡ true
incrementTensorPolarizationAlgebraClosedIsTrue = refl

constantModeCancellationClosedIsTrue :
  constantModeCancellationClosed ≡ true
constantModeCancellationClosedIsTrue = refl
