module DASHI.Physics.Closure.NSTriadKNLuoFiniteWeightedJensenExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Johan Jensen.
-- Result: finite weighted Jensen inequality for the convex square function.
-- DOI: not applicable to this classical inequality.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Prove the weighted finite analogue of the time-integral Jensen step without
-- square roots or division.  For nonnegative rational weights,
--
--   (sum_i w_i a_i)^2
--     <= (sum_i w_i) (sum_i w_i a_i^2).
--
-- The proof establishes the exact nonnegative defect identity
--
--   M Q = S^2 + sum_{i<j} w_i w_j (a_i-a_j)^2.
--
-- Thus the inequality is derived from a concrete finite variance defect and
-- not accepted as an analytic authority field.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

record WeightedValue : Set where
  constructor weighted
  field
    weight value : ℚ
    weightNonnegative : 0ℚ ≤ weight

open WeightedValue public

mass : List WeightedValue → ℚ
mass [] = 0ℚ
mass (sample ∷ samples) = weight sample + mass samples

firstMoment : List WeightedValue → ℚ
firstMoment [] = 0ℚ
firstMoment (sample ∷ samples) =
  weight sample * value sample + firstMoment samples

secondMoment : List WeightedValue → ℚ
secondMoment [] = 0ℚ
secondMoment (sample ∷ samples) =
  weight sample * L2.square (value sample) + secondMoment samples

crossDefect : WeightedValue → List WeightedValue → ℚ
crossDefect sample [] = 0ℚ
crossDefect sample (other ∷ samples) =
  weight sample * weight other
    * L2.square (value sample - value other)
  + crossDefect sample samples

jensenDefect : List WeightedValue → ℚ
jensenDefect [] = 0ℚ
jensenDefect (sample ∷ samples) =
  crossDefect sample samples + jensenDefect samples

crossDefectExpansion :
  (sample : WeightedValue) →
  (samples : List WeightedValue) →
  crossDefect sample samples
  ≡ weight sample * secondMoment samples
    + weight sample * L2.square (value sample) * mass samples
    - ( weight sample * value sample * firstMoment samples
      + weight sample * value sample * firstMoment samples)
crossDefectExpansion sample [] =
  solve (weight sample ∷ value sample ∷ [])
crossDefectExpansion sample (other ∷ samples)
  rewrite crossDefectExpansion sample samples =
  solve
    ( weight sample
    ∷ value sample
    ∷ weight other
    ∷ value other
    ∷ mass samples
    ∷ firstMoment samples
    ∷ secondMoment samples
    ∷ []
    )

weightedGramIdentity :
  (samples : List WeightedValue) →
  mass samples * secondMoment samples
  ≡ L2.square (firstMoment samples) + jensenDefect samples
weightedGramIdentity [] = solve []
weightedGramIdentity (sample ∷ samples)
  rewrite crossDefectExpansion sample samples
        | weightedGramIdentity samples =
  solve
    ( weight sample
    ∷ value sample
    ∷ mass samples
    ∷ firstMoment samples
    ∷ secondMoment samples
    ∷ jensenDefect samples
    ∷ []
    )

nonnegativeProduct :
  ∀ {left right : ℚ} →
  0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right
nonnegativeProduct {left} {right} leftNonnegative rightNonnegative =
  let
    instance
      leftIsNonnegative = nonNegative leftNonnegative
      rightIsNonnegative = nonNegative rightNonnegative
      productIsNonnegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg left right
  in
  ℚₚ.nonNegative⁻¹ (left * right)

crossDefectNonnegative :
  (sample : WeightedValue) →
  (samples : List WeightedValue) →
  0ℚ ≤ crossDefect sample samples
crossDefectNonnegative sample [] = ℚₚ.≤-refl
crossDefectNonnegative sample (other ∷ samples) =
  L2.addNonnegative
    (nonnegativeProduct
      (nonnegativeProduct
        (weightNonnegative sample)
        (weightNonnegative other))
      (L2.squareNonnegative (value sample - value other)))
    (crossDefectNonnegative sample samples)

jensenDefectNonnegative :
  (samples : List WeightedValue) →
  0ℚ ≤ jensenDefect samples
jensenDefectNonnegative [] = ℚₚ.≤-refl
jensenDefectNonnegative (sample ∷ samples) =
  L2.addNonnegative
    (crossDefectNonnegative sample samples)
    (jensenDefectNonnegative samples)

finiteWeightedJensenSquare :
  (samples : List WeightedValue) →
  L2.square (firstMoment samples)
  ≤ mass samples * secondMoment samples
finiteWeightedJensenSquare samples =
  let
    addDefect :
      L2.square (firstMoment samples)
      ≤ L2.square (firstMoment samples) + jensenDefect samples
    addDefect =
      subst
        (λ lower →
          lower
          ≤ L2.square (firstMoment samples) + jensenDefect samples)
        (ℚₚ.+-identityʳ (L2.square (firstMoment samples)))
        (ℚₚ.+-monoʳ-≤
          (L2.square (firstMoment samples))
          (jensenDefectNonnegative samples))
  in
  subst
    (λ upper → L2.square (firstMoment samples) ≤ upper)
    (sym (weightedGramIdentity samples))
    addDefect

finiteWeightedJensenClosed : Bool
finiteWeightedJensenClosed = true

finiteWeightedVarianceDefectClosed : Bool
finiteWeightedVarianceDefectClosed = true

finiteWeightedJensenClosedIsTrue :
  finiteWeightedJensenClosed ≡ true
finiteWeightedJensenClosedIsTrue = refl

finiteWeightedVarianceDefectClosedIsTrue :
  finiteWeightedVarianceDefectClosed ≡ true
finiteWeightedVarianceDefectClosedIsTrue = refl
