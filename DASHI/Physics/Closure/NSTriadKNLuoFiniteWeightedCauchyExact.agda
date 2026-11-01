module DASHI.Physics.Closure.NSTriadKNLuoFiniteWeightedCauchyExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Result: finite weighted Cauchy--Schwarz inequality.
-- DOI: not applicable to the classical inequality.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Prove the exact finite weighted time-window Cauchy step used in Luo's
-- J1 <= J11 J12 estimate.  For nonnegative rational weights,
--
--   (sum_i w_i a_i b_i)^2
--     <= (sum_i w_i a_i^2) (sum_i w_i b_i^2).
--
-- The proof derives the weighted Gram-defect identity
--
--   L R = P^2 + sum_{i<j} w_i w_j (a_i b_j-a_j b_i)^2,
--
-- so the inequality is not accepted as an authority field.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

record WeightedPair : Set where
  constructor weighted-pair
  field
    weight left right : ℚ
    weightNonnegative : 0ℚ ≤ weight

open WeightedPair public

weightedPairing : List WeightedPair → ℚ
weightedPairing [] = 0ℚ
weightedPairing (sample ∷ samples) =
  weight sample * left sample * right sample
    + weightedPairing samples

leftEnergy : List WeightedPair → ℚ
leftEnergy [] = 0ℚ
leftEnergy (sample ∷ samples) =
  weight sample * L2.square (left sample) + leftEnergy samples

rightEnergy : List WeightedPair → ℚ
rightEnergy [] = 0ℚ
rightEnergy (sample ∷ samples) =
  weight sample * L2.square (right sample) + rightEnergy samples

crossDefect : WeightedPair → List WeightedPair → ℚ
crossDefect sample [] = 0ℚ
crossDefect sample (other ∷ samples) =
  weight sample * weight other
    * L2.square
        (left sample * right other - left other * right sample)
  + crossDefect sample samples

gramDefect : List WeightedPair → ℚ
gramDefect [] = 0ℚ
gramDefect (sample ∷ samples) =
  crossDefect sample samples + gramDefect samples

crossDefectExpansion :
  (sample : WeightedPair) →
  (samples : List WeightedPair) →
  crossDefect sample samples
  ≡ weight sample * L2.square (left sample) * rightEnergy samples
    + weight sample * L2.square (right sample) * leftEnergy samples
    - ( weight sample * left sample * right sample
          * weightedPairing samples
      + weight sample * left sample * right sample
          * weightedPairing samples)
crossDefectExpansion sample [] =
  solve (weight sample ∷ left sample ∷ right sample ∷ [])
crossDefectExpansion sample (other ∷ samples)
  rewrite crossDefectExpansion sample samples =
  solve
    ( weight sample
    ∷ left sample
    ∷ right sample
    ∷ weight other
    ∷ left other
    ∷ right other
    ∷ leftEnergy samples
    ∷ rightEnergy samples
    ∷ weightedPairing samples
    ∷ []
    )

weightedGramIdentity :
  (samples : List WeightedPair) →
  leftEnergy samples * rightEnergy samples
  ≡ L2.square (weightedPairing samples) + gramDefect samples
weightedGramIdentity [] = solve []
weightedGramIdentity (sample ∷ samples)
  rewrite crossDefectExpansion sample samples
        | weightedGramIdentity samples =
  solve
    ( weight sample
    ∷ left sample
    ∷ right sample
    ∷ leftEnergy samples
    ∷ rightEnergy samples
    ∷ weightedPairing samples
    ∷ gramDefect samples
    ∷ []
    )

nonnegativeProduct :
  ∀ {a b : ℚ} → 0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ a * b
nonnegativeProduct {a} {b} aNonnegative bNonnegative =
  let
    instance
      aIsNonnegative = nonNegative aNonnegative
      bIsNonnegative = nonNegative bNonnegative
      productIsNonnegative = ℚₚ.nonNeg*nonNeg⇒nonNeg a b
  in
  ℚₚ.nonNegative⁻¹ (a * b)

crossDefectNonnegative :
  (sample : WeightedPair) →
  (samples : List WeightedPair) →
  0ℚ ≤ crossDefect sample samples
crossDefectNonnegative sample [] = ℚₚ.≤-refl
crossDefectNonnegative sample (other ∷ samples) =
  L2.addNonnegative
    (nonnegativeProduct
      (nonnegativeProduct
        (weightNonnegative sample)
        (weightNonnegative other))
      (L2.squareNonnegative
        (left sample * right other - left other * right sample)))
    (crossDefectNonnegative sample samples)

gramDefectNonnegative :
  (samples : List WeightedPair) →
  0ℚ ≤ gramDefect samples
gramDefectNonnegative [] = ℚₚ.≤-refl
gramDefectNonnegative (sample ∷ samples) =
  L2.addNonnegative
    (crossDefectNonnegative sample samples)
    (gramDefectNonnegative samples)

finiteWeightedCauchy :
  (samples : List WeightedPair) →
  L2.square (weightedPairing samples)
  ≤ leftEnergy samples * rightEnergy samples
finiteWeightedCauchy samples =
  let
    addDefect :
      L2.square (weightedPairing samples)
      ≤ L2.square (weightedPairing samples) + gramDefect samples
    addDefect =
      subst
        (λ lower →
          lower ≤ L2.square (weightedPairing samples) + gramDefect samples)
        (ℚₚ.+-identityʳ (L2.square (weightedPairing samples)))
        (ℚₚ.+-monoʳ-≤
          (L2.square (weightedPairing samples))
          (gramDefectNonnegative samples))
  in
  subst
    (λ upper → L2.square (weightedPairing samples) ≤ upper)
    (sym (weightedGramIdentity samples))
    addDefect
