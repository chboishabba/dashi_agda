module DASHI.Physics.Closure.NSTriadKNLuoThreeCycleTorusCrossPollinationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications".
-- DOI: 10.1017/CBO9780511626265.
--
-- Hajer Bahouri, Jean-Yves Chemin and Raphael Danchin,
-- "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
-- Instantiate the common finite 3x3 torus as a translation carrier for a
-- scalar velocity prototype.  Coordinate pullbacks commute and each has order
-- three.  The distinguished completion channel is kept separate from the nine
-- ordinary torus sites.
--
-- This does not identify the carrier with the growing Fourier grids of Round
-- Sixteen or with the physical torus T^3; it supplies a finite regression and
-- an exact translation-action interface only.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Common.FiniteThreeCycleTorusExact as Torus

VelocityPrototype : Set
VelocityPrototype = Torus.Field ℚ

translateVelocityFirst : VelocityPrototype → VelocityPrototype
translateVelocityFirst = Torus.pullbackFirst

translateVelocitySecond : VelocityPrototype → VelocityPrototype
translateVelocitySecond = Torus.pullbackSecond

firstTranslationHasOrderThreeAt :
  ∀ velocity channel →
  translateVelocityFirst
    (translateVelocityFirst (translateVelocityFirst velocity)) channel
  ≡ velocity channel
firstTranslationHasOrderThreeAt = Torus.pullbackFirstCubedAt

secondTranslationHasOrderThreeAt :
  ∀ velocity channel →
  translateVelocitySecond
    (translateVelocitySecond (translateVelocitySecond velocity)) channel
  ≡ velocity channel
secondTranslationHasOrderThreeAt = Torus.pullbackSecondCubedAt

velocityTranslationsCommuteAt :
  ∀ velocity channel →
  translateVelocityFirst (translateVelocitySecond velocity) channel
  ≡ translateVelocitySecond (translateVelocityFirst velocity) channel
velocityTranslationsCommuteAt = Torus.pullbacksCommuteAt

completionValue : VelocityPrototype → ℚ
completionValue velocity = velocity Torus.completionChannel

record ThreeCycleTorusNSBoundary : Set where
  constructor threeCycleTorusNSBoundary
  field
    finiteThreeByThreeCarrierIsPhysicalThreeTorus : Set
    finiteThreeByThreeCarrierIsNotPhysicalThreeTorus :
      finiteThreeByThreeCarrierIsPhysicalThreeTorus → Set

    translationAlgebraSuppliesCenteredKernelEstimate : Set
    translationAlgebraDoesNotSupplyCenteredKernelEstimate :
      translationAlgebraSuppliesCenteredKernelEstimate → Set

canonicalThreeCycleTorusNSBoundary : ThreeCycleTorusNSBoundary
canonicalThreeCycleTorusNSBoundary =
  threeCycleTorusNSBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)
