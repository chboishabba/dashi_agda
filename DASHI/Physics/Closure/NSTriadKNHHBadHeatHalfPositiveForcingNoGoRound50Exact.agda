module DASHI.Physics.Closure.NSTriadKNHHBadHeatHalfPositiveForcingNoGoRound50Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- DASHI CONTRIBUTION
--
-- One exact heat-half gives alpha=1 after dyadic normalization.  The standard
-- invariant-ceiling condition for constant forcing is
--
--   beta <= (1-alpha) M.
--
-- At alpha=1 this becomes beta<=0.  Hence any strictly positive constant
-- forcing is incompatible with that closure mechanism, for every proposed M.
-- This proves precisely that the bare heat-half is scale compensation only;
-- it is not the missing normalized depletion margin.
--
-- The result does NOT rule out the Round-50 fallback: beta_q may instead have
-- bounded finite prefixes (summable creation/leakage).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _-_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary.Negation using (¬_)

heatHalfNormalizedAlpha : ℚ
heatHalfNormalizedAlpha = 1ℚ

heatHalfForcingCapacity : ℚ → ℚ
heatHalfForcingCapacity ceiling =
  (1ℚ - heatHalfNormalizedAlpha) * ceiling

heatHalfForcingCapacityIsZero :
  ∀ ceiling → heatHalfForcingCapacity ceiling ≡ 0ℚ
heatHalfForcingCapacityIsZero ceiling = solve (ceiling ∷ [])

positiveConstantForcingCannotFitHeatHalfCeiling :
  ∀ {beta ceiling} →
  0ℚ < beta →
  ¬ (beta ≤ heatHalfForcingCapacity ceiling)
positiveConstantForcingCannotFitHeatHalfCeiling {beta} {ceiling} betaPositive forcingFits =
  let
    beta≤zero : beta ≤ 0ℚ
    beta≤zero =
      subst
        (beta ≤_)
        (heatHalfForcingCapacityIsZero ceiling)
        forcingFits

    zero<zero : 0ℚ < 0ℚ
    zero<zero = ℚP.<-≤-trans betaPositive beta≤zero
  in
  (ℚP.<-irrefl refl) zero<zero

heatHalfAloneCannotClosePositiveConstantForcing : Bool
heatHalfAloneCannotClosePositiveConstantForcing = true

summableForcingFallbackRemainsOpen : Bool
summableForcingFallbackRemainsOpen = true

heatHalfAloneCannotClosePositiveConstantForcingIsTrue :
  heatHalfAloneCannotClosePositiveConstantForcing ≡ true
heatHalfAloneCannotClosePositiveConstantForcingIsTrue = refl
