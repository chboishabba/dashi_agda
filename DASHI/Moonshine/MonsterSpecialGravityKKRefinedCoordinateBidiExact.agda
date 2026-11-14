module DASHI.Moonshine.MonsterSpecialGravityKKRefinedCoordinateBidiExact where

------------------------------------------------------------------------
-- PHASE-0 EXACT TWO-SIDED COORDINATE TRANSPORT.
--
-- This refines the original MonsterSpecialGravityKKWeightTwoCrosswalkExact
-- by giving an explicit inverse between the proposed gravity *labels*
-- (dilaton, traceless metric, p-form, twisted) and the FLM weight-two
-- sector *coordinate chart* (Sym^2 h, norm-four pairs, twisted).
--
-- Deliberately no assertion about the source metric, Griess product,
-- vertex modes, physical inner product, Monster action or dynamics.
-- They require the separate proof-relevant Phase-1 to Phase-5 gates.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

import DASHI.Moonshine.MoonshineOrbifoldWeightTwoDecompositionExact as FLM
import DASHI.Moonshine.MonsterSpecialGravityKKWeightTwoCrosswalkExact as Gravity

-- FLM's actual sourced 300 + 98280 + 98304 sector counts, rather
-- than the unrelated coordinate subtotal 196608 + 276.
RefinedFLMWeightTwoCoordinate : Set
RefinedFLMWeightTwoCoordinate =
  (Fin FLM.symmetricSquareDimension
   ⊎ Fin FLM.pairedNormFourOrbitCount)
  ⊎ FLM.TwistedInvariantWeightTwoCoordinate

gravityToRefinedFLM :
  Gravity.GravityCandidateCoordinate → RefinedFLMWeightTwoCoordinate
gravityToRefinedFLM (inj₁ (inj₁ (inj₁ zero))) =
  inj₁ (inj₁ zero)
gravityToRefinedFLM (inj₁ (inj₁ (inj₂ n))) =
  inj₁ (inj₁ (suc n))
gravityToRefinedFLM (inj₁ (inj₂ n)) =
  inj₁ (inj₂ n)
gravityToRefinedFLM (inj₂ n) =
  inj₂ n

refinedFLMToGravity :
  RefinedFLMWeightTwoCoordinate → Gravity.GravityCandidateCoordinate
refinedFLMToGravity (inj₁ (inj₁ zero)) =
  inj₁ (inj₁ (inj₁ zero))
refinedFLMToGravity (inj₁ (inj₁ (suc n))) =
  inj₁ (inj₁ (inj₂ n))
refinedFLMToGravity (inj₁ (inj₂ n)) =
  inj₁ (inj₂ n)
refinedFLMToGravity (inj₂ n) =
  inj₂ n

gravityToFLMToGravity :
  (x : Gravity.GravityCandidateCoordinate) →
  refinedFLMToGravity (gravityToRefinedFLM x) ≡ x
gravityToFLMToGravity (inj₁ (inj₁ (inj₁ zero))) = refl
gravityToFLMToGravity (inj₁ (inj₁ (inj₂ n))) = refl
gravityToFLMToGravity (inj₁ (inj₂ n)) = refl
gravityToFLMToGravity (inj₂ n) = refl

flmToGravityToFLM :
  (y : RefinedFLMWeightTwoCoordinate) →
  gravityToRefinedFLM (refinedFLMToGravity y) ≡ y
flmToGravityToFLM (inj₁ (inj₁ zero)) = refl
flmToGravityToFLM (inj₁ (inj₁ (suc n))) = refl
flmToGravityToFLM (inj₁ (inj₂ n)) = refl
flmToGravityToFLM (inj₂ n) = refl

gravityDilatonMapsToFLMScalar :
  gravityToRefinedFLM Gravity.gravityDilatonCoordinate ≡
  inj₁ (inj₁ zero)
gravityDilatonMapsToFLMScalar = refl

gravityMetricMapsToFLMSymmetricSquare :
  (n : Gravity.GravityTracelessMetric) →
  gravityToRefinedFLM (Gravity.gravityMetricCoordinate n) ≡
  inj₁ (inj₁ (suc n))
gravityMetricMapsToFLMSymmetricSquare n = refl

gravityPFormMapsToFLMNormFourPair :
  (n : Gravity.GravityLeechComparison) →
  gravityToRefinedFLM (Gravity.gravityLeechCoordinate n) ≡
  inj₁ (inj₂ n)
gravityPFormMapsToFLMNormFourPair n = refl

gravityTwistedMapsToFLMTwisted :
  (n : Gravity.GravityTwistedComparison) →
  gravityToRefinedFLM (Gravity.gravityTwistedCoordinate n) ≡
  inj₂ n
gravityTwistedMapsToFLMTwisted n = refl
