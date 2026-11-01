module DASHI.Physics.Closure.NSTriadKNFiniteWeightedGramFluxAggregationRound385Exact where

------------------------------------------------------------------------
-- ROUND385 / FINITE AGGREGATION OF THE R290 PAIR FLUX IDENTITY
--
-- R383 expands the literal R180 Gram debt into a finite sum of pair Gram
-- scalars.  R384 compiles every positive physical R291 pair into an exact R290
-- DampedGramPair.  This module removes the next purely finite-algebra seam:
-- the R290 identity is stable under an arbitrary finite list of such pairs.
--
-- For a list P_i,
--
--   sum gram(P_i)
--     = - sum weightedFluxTangent(P_i)
--       + sum weightedNonlinearRemainder(P_i).
--
-- No sign, positivity, integration, endpoint estimate, or PDE estimate is
-- introduced here.  Positivity is used only upstream to construct each R290
-- pair via R384.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290

sumGram : List R290.DampedGramPair → ℚ
sumGram [] = 0ℚ
sumGram (pair ∷ rest) = R290.gram pair + sumGram rest

sumWeightedFlux : List R290.DampedGramPair → ℚ
sumWeightedFlux [] = 0ℚ
sumWeightedFlux (pair ∷ rest) = R290.weightedGramFlux pair + sumWeightedFlux rest

sumWeightedFluxTangent : List R290.DampedGramPair → ℚ
sumWeightedFluxTangent [] = 0ℚ
sumWeightedFluxTangent (pair ∷ rest) =
  R290.weightedGramFluxTangent pair + sumWeightedFluxTangent rest

sumWeightedRemainder : List R290.DampedGramPair → ℚ
sumWeightedRemainder [] = 0ℚ
sumWeightedRemainder (pair ∷ rest) =
  R290.weightedNonlinearRemainder pair + sumWeightedRemainder rest

finiteGramAsNegativeFluxDerivativePlusRemainder :
  (pairs : List R290.DampedGramPair) →
  sumGram pairs
  ≡ (0ℚ - sumWeightedFluxTangent pairs) + sumWeightedRemainder pairs
finiteGramAsNegativeFluxDerivativePlusRemainder [] = refl
finiteGramAsNegativeFluxDerivativePlusRemainder (pair ∷ rest) =
  let
    head = R290.gramAsNegativeFluxDerivativePlusRemainder pair
    tail = finiteGramAsNegativeFluxDerivativePlusRemainder rest
  in
  trans
    (cong₂ _+_ head tail)
    (solve
      (R290.weightedGramFluxTangent pair
        ∷ sumWeightedFluxTangent rest
        ∷ R290.weightedNonlinearRemainder pair
        ∷ sumWeightedRemainder rest
        ∷ []))

round385FiniteR290AggregationClosed : Bool
round385FiniteR290AggregationClosed = true

round385IntroducesAnySignAssumption : Bool
round385IntroducesAnySignAssumption = false

round385IntroducesAnyIntegrationAssumption : Bool
round385IntroducesAnyIntegrationAssumption = false

round385RemainingSameObjectPairEnumerationWeld : Bool
round385RemainingSameObjectPairEnumerationWeld = true

round385FiniteR290AggregationClosedIsTrue :
  round385FiniteR290AggregationClosed ≡ true
round385FiniteR290AggregationClosedIsTrue = refl

round385IntroducesAnySignAssumptionIsFalse :
  round385IntroducesAnySignAssumption ≡ false
round385IntroducesAnySignAssumptionIsFalse = refl
