module DASHI.Physics.Closure.NSTriadKNLuoFiniteJensenSquareExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Result: finite Cauchy--Schwarz inequality and its equal-weight Jensen
-- corollary.
-- DOI: not applicable to the classical nineteenth-century results.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Prove the finite equal-weight Jensen/Cauchy estimate actually used by the
-- source-faithful time-window route:
--
--   (sum_i a_i)^2 <= (# i) sum_i a_i^2.
--
-- The proof does not accept Jensen as a field.  It maps the scalar list to
-- pairs (a_i,1), applies the repository's exact Gram-defect Cauchy--Schwarz
-- theorem, and proves all three fold-identification equations by induction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product.Base using (_,_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst₂)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteWeightedIncrementFubiniExact as Finite

onePairs : List ℚ → List L2.Pair
onePairs [] = []
onePairs (value ∷ values) = (value , 1ℚ) ∷ onePairs values

sumValues : List ℚ → ℚ
sumValues values = Finite.sumList values (λ value → value)

sumSquares : List ℚ → ℚ
sumSquares values = Finite.sumList values L2.square

rationalLength : List ℚ → ℚ
rationalLength [] = 0ℚ
rationalLength (_ ∷ values) = 1ℚ + rationalLength values

pairDotOnePairs :
  (values : List ℚ) →
  L2.pairDot (onePairs values) ≡ sumValues values
pairDotOnePairs [] = refl
pairDotOnePairs (value ∷ values)
  rewrite pairDotOnePairs values =
  solve (value ∷ sumValues values ∷ [])

leftNormOnePairs :
  (values : List ℚ) →
  L2.leftNormSquared (onePairs values) ≡ sumSquares values
leftNormOnePairs [] = refl
leftNormOnePairs (value ∷ values)
  rewrite leftNormOnePairs values = refl

rightNormOnePairs :
  (values : List ℚ) →
  L2.rightNormSquared (onePairs values) ≡ rationalLength values
rightNormOnePairs [] = refl
rightNormOnePairs (value ∷ values)
  rewrite rightNormOnePairs values =
  solve (rationalLength values ∷ [])

finiteJensenSquare :
  (values : List ℚ) →
  L2.square (sumValues values)
  ≤ sumSquares values * rationalLength values
finiteJensenSquare values =
  let
    cauchy = L2.finiteCauchySchwarzSquared (onePairs values)

    leftMeaning :
      L2.square (L2.pairDot (onePairs values))
      ≡ L2.square (sumValues values)
    leftMeaning = cong L2.square (pairDotOnePairs values)

    rightMeaning :
      L2.leftNormSquared (onePairs values)
        * L2.rightNormSquared (onePairs values)
      ≡ sumSquares values * rationalLength values
    rightMeaning
      rewrite leftNormOnePairs values
            | rightNormOnePairs values = refl
  in
  subst₂ _≤_ leftMeaning rightMeaning cauchy

finiteJensenSquareClosed : Bool
finiteJensenSquareClosed = true

finiteJensenSquareClosedIsTrue :
  finiteJensenSquareClosed ≡ true
finiteJensenSquareClosedIsTrue = refl
