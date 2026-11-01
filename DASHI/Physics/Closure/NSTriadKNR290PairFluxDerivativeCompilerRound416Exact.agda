module DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact where

------------------------------------------------------------------------
-- ROUND416 / LOCAL R290 PAIR-FLUX DERIVATIVE COMPILER
--
-- R412 removed finite-sum differentiation.  The next local seam is smaller:
-- for one time-indexed R290 pair, the resolvent weight is constant when the
-- physical modes and viscosity are fixed, so differentiating
--
--   weightedGramFlux = w * gram
--
-- requires only the actual Gram product-rule derivative plus constant-scalar
-- closure.  This module proves that reduction without introducing a second
-- flux or a second tangent.
--
-- Upstream R291 already owns the exact algebraic Gram tangent
--   2 Re <dA,B> + 2 Re <A,dB>.
-- Hence the sole local analytic content after this compiler is to identify that
-- R291 expression with the actual scalar derivative of the real-Hermitian Gram
-- curve.  The resolvent step itself is routine.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _*_)

import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290

record ScalarConstantDerivativeCalculus
    (Time : Set)
    (ScalarDerivativeOf : (Time → ℚ) → (Time → ℚ) → Set) : Set₁ where
  field
    constantScaleDerivative :
      (c : ℚ) →
      ∀ {f df} →
      ScalarDerivativeOf f df →
      ScalarDerivativeOf
        (λ time → c * f time)
        (λ time → c * df time)

    transportDerivative :
      ∀ {f g df dg} →
      ((time : Time) → f time ≡ g time) →
      ((time : Time) → df time ≡ dg time) →
      ScalarDerivativeOf f df →
      ScalarDerivativeOf g dg

open ScalarConstantDerivativeCalculus public

record FixedResolventPairCurve
    (Time : Set) : Set where
  field
    pairAt : Time → R290.DampedGramPair
    fixedWeight : ℚ
    resolventWeightFixed :
      (time : Time) → R290.resolventWeight (pairAt time) ≡ fixedWeight

open FixedResolventPairCurve public

gramCurve : ∀ {Time} → FixedResolventPairCurve Time → Time → ℚ
gramCurve P time = R290.gram (pairAt P time)

gramTangentCurve : ∀ {Time} → FixedResolventPairCurve Time → Time → ℚ
gramTangentCurve P time = R290.gramTangent (pairAt P time)

weightedFluxCurve : ∀ {Time} → FixedResolventPairCurve Time → Time → ℚ
weightedFluxCurve P time = R290.weightedGramFlux (pairAt P time)

weightedFluxTangentCurve : ∀ {Time} → FixedResolventPairCurve Time → Time → ℚ
weightedFluxTangentCurve P time = R290.weightedGramFluxTangent (pairAt P time)

module PairDerivative
    (Time : Set)
    (ScalarDerivativeOf : (Time → ℚ) → (Time → ℚ) → Set)
    (C : ScalarConstantDerivativeCalculus Time ScalarDerivativeOf) where

  fixedWeightTimesGramIsWeightedFlux :
    (P : FixedResolventPairCurve Time) →
    (time : Time) →
    fixedWeight P * gramCurve P time ≡ weightedFluxCurve P time
  fixedWeightTimesGramIsWeightedFlux P time
    rewrite resolventWeightFixed P time = refl

  fixedWeightTimesTangentIsWeightedFluxTangent :
    (P : FixedResolventPairCurve Time) →
    (time : Time) →
    fixedWeight P * gramTangentCurve P time
    ≡ weightedFluxTangentCurve P time
  fixedWeightTimesTangentIsWeightedFluxTangent P time
    rewrite resolventWeightFixed P time = refl

  gramDerivativeBuildsWeightedFluxDerivative :
    (P : FixedResolventPairCurve Time) →
    ScalarDerivativeOf (gramCurve P) (gramTangentCurve P) →
    ScalarDerivativeOf
      (weightedFluxCurve P)
      (weightedFluxTangentCurve P)
  gramDerivativeBuildsWeightedFluxDerivative P gramDerivative =
    transportDerivative C
      (fixedWeightTimesGramIsWeightedFlux P)
      (fixedWeightTimesTangentIsWeightedFluxTangent P)
      (constantScaleDerivative C (fixedWeight P) gramDerivative)

round416ResolventWeightDifferentiationReducedToConstantScale : Bool
round416ResolventWeightDifferentiationReducedToConstantScale = true

round416RemainingLocalAnalyticLeafIsActualGramProductRule : Bool
round416RemainingLocalAnalyticLeafIsActualGramProductRule = true

round416NoNewNSNonlinearEstimateIntroduced : Bool
round416NoNewNSNonlinearEstimateIntroduced = true

round416ResolventWeightDifferentiationReducedToConstantScaleIsTrue :
  round416ResolventWeightDifferentiationReducedToConstantScale ≡ true
round416ResolventWeightDifferentiationReducedToConstantScaleIsTrue = refl
