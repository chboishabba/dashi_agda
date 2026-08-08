module DASHI.Physics.Closure.NSTriadKNLuoCamlinTemporalLiftNoGoExact where

------------------------------------------------------------------------
-- SOURCE UNDER AUDIT
--
-- Author: Jeffrey Camlin.
-- Title: "Global Regularity for Navier-Stokes on T3 via Bounded
-- Vorticity-Response Functionals".
-- DOI: 10.63968/post-bio-ai-epistemics.v1n2.012.
-- Status: independent publication; not used as proof authority.
--
-- AUDITED STEPS
--
-- (1) A family of bounds C(T), one for each finite horizon T, does not supply
--     one constant uniform for all horizons.
--
-- (2) An exact positive time reparameterization preserves any property that
--     depends only on the value of the transformed BKM integral.  Equality of
--     integrals cannot turn divergence into finiteness.
--
-- (3) The scalar superlinear drift used in the proposed Galerkin estimate is
--     not globally dissipative.  On square amplitudes y=s^2, the term
--
--       y^(3/2) - a y = s^3 - a s^2
--
--     is positive at s=a+1 by the already checked exact scaling identity.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ; _,_)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)
open import Relation.Nullary.Negation using (¬_)

import DASHI.Physics.Closure.NSTriadKNLuoBadAmplitudeBernsteinScalingNoGoExact as Scaling

infix 4 _≤ⁿ_

data _≤ⁿ_ : Nat → Nat → Set where
  zero≤ : ∀ {n} → zero ≤ⁿ n
  suc≤suc : ∀ {m n} → m ≤ⁿ n → suc m ≤ⁿ suc n

≤ⁿ-refl : ∀ n → n ≤ⁿ n
≤ⁿ-refl zero = zero≤
≤ⁿ-refl (suc n) = suc≤suc (≤ⁿ-refl n)

notSucLeSelf : ∀ n → ¬ (suc n ≤ⁿ n)
notSucLeSelf zero ()
notSucLeSelf (suc n) (suc≤suc proof) =
  notSucLeSelf n proof

FiniteHorizonBoundFamily : Set
FiniteHorizonBoundFamily =
  (horizon : Nat) → Σ Nat (λ bound → horizon ≤ⁿ bound)

finiteHorizonBoundsExist : FiniteHorizonBoundFamily
finiteHorizonBoundsExist horizon =
  horizon , ≤ⁿ-refl horizon

GlobalUniformHorizonBound : Set
GlobalUniformHorizonBound =
  Σ Nat (λ bound → (horizon : Nat) → horizon ≤ⁿ bound)

finiteHorizonFamilyDoesNotYieldGlobalUniformBound :
  ¬ GlobalUniformHorizonBound
finiteHorizonFamilyDoesNotYieldGlobalUniformBound
  (bound , dominatesEveryHorizon) =
  notSucLeSelf bound (dominatesEveryHorizon (suc bound))

record ExactIntegralChangeOfVariables : Set₁ where
  field
    IntegralValue : Set
    originalIntegral : IntegralValue
    transformedIntegral : IntegralValue
    transformedEqualsOriginal :
      transformedIntegral ≡ originalIntegral

open ExactIntegralChangeOfVariables public

integralPropertyPreservedBackward :
  (change : ExactIntegralChangeOfVariables) →
  (Property : IntegralValue change → Set) →
  Property (transformedIntegral change) →
  Property (originalIntegral change)
integralPropertyPreservedBackward change Property transformedProperty =
  subst Property
    (transformedEqualsOriginal change)
    transformedProperty

integralPropertyPreservedForward :
  (change : ExactIntegralChangeOfVariables) →
  (Property : IntegralValue change → Set) →
  Property (originalIntegral change) →
  Property (transformedIntegral change)
integralPropertyPreservedForward change Property originalProperty =
  subst Property
    (sym (transformedEqualsOriginal change))
    originalProperty

bkmDivergenceCannotBeRemovedByExactTimeChange :
  (change : ExactIntegralChangeOfVariables) →
  (Diverges : IntegralValue change → Set) →
  Diverges (originalIntegral change) →
  Diverges (transformedIntegral change)
bkmDivergenceCannotBeRemovedByExactTimeChange =
  integralPropertyPreservedForward

bkmFinitenessCannotBeCreatedByExactTimeChange :
  (change : ExactIntegralChangeOfVariables) →
  (Finite : IntegralValue change → Set) →
  Finite (transformedIntegral change) →
  Finite (originalIntegral change)
bkmFinitenessCannotBeCreatedByExactTimeChange =
  integralPropertyPreservedBackward

superlinearDriftGapAtCoefficientPlusOne :
  (coefficient : ℚ) →
  Scaling.bernsteinAmplitudeGap coefficient
  ≡ Scaling.shellDiffusionSquared (Scaling.counterScale coefficient)
superlinearDriftGapAtCoefficientPlusOne =
  Scaling.bernsteinSupercriticalGapIdentity

record CamlinAuditBoundary : Set where
  constructor camlinAuditBoundary
  field
    finiteHorizonQuantifierGapProved : Set
    exactTimeChangePreservesIntegralProperties : Set
    superlinearDriftGapReused : Set
    uniformGlobalVorticityBoundProduced : Set
    unconditionalClayConclusionProduced : Set

canonicalCamlinAuditBoundary : CamlinAuditBoundary
canonicalCamlinAuditBoundary =
  camlinAuditBoundary ⊤ ⊤ ⊤ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
