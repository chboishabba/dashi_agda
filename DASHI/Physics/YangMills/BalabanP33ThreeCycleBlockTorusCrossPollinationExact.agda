module DASHI.Physics.YangMills.BalabanP33ThreeCycleBlockTorusCrossPollinationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications".
-- DOI: 10.1017/CBO9780511626265.
--
-- Tadeusz Balaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. II".
-- DOI: 10.1007/BF01240221.
--
-- John D. Dixon and Brian Mortimer,
-- "Permutation Groups".
-- DOI: 10.1007/978-1-4612-0731-3.
--
-- DASHI CONTRIBUTION
-- Instantiate the common completed 3x3 torus as an exact block-index
-- translation prototype.  The two block translations commute and each has
-- order three on fields.  The completion channel is fixed by these finite
-- translations.
--
-- This is an index-action regression only.  It is not the physical side-four
-- lattice, the actual gauge action, the selected-background constructor or the
-- Balaban block transformation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Common.FiniteThreeCycleTorusExact as Torus

BlockScalarField : Set
BlockScalarField = Torus.Field ℚ

translateBlockFirst : BlockScalarField → BlockScalarField
translateBlockFirst = Torus.pullbackFirst

translateBlockSecond : BlockScalarField → BlockScalarField
translateBlockSecond = Torus.pullbackSecond

blockFirstTranslationOrderThreeAt :
  ∀ field channel →
  translateBlockFirst
    (translateBlockFirst (translateBlockFirst field)) channel
  ≡ field channel
blockFirstTranslationOrderThreeAt = Torus.pullbackFirstCubedAt

blockSecondTranslationOrderThreeAt :
  ∀ field channel →
  translateBlockSecond
    (translateBlockSecond (translateBlockSecond field)) channel
  ≡ field channel
blockSecondTranslationOrderThreeAt = Torus.pullbackSecondCubedAt

blockTranslationsCommuteAt :
  ∀ field channel →
  translateBlockFirst (translateBlockSecond field) channel
  ≡ translateBlockSecond (translateBlockFirst field) channel
blockTranslationsCommuteAt = Torus.pullbacksCommuteAt

completionBlockValue : BlockScalarField → ℚ
completionBlockValue field = field Torus.completionChannel

record ThreeCycleBlockTorusBoundary : Set where
  constructor threeCycleBlockTorusBoundary
  field
    prototypeIsPhysicalP33Lattice : Set
    prototypeIsNotPhysicalP33Lattice :
      prototypeIsPhysicalP33Lattice → Set

    prototypeTranslationsAreGaugeTransformations : Set
    prototypeTranslationsAreNotGaugeTransformations :
      prototypeTranslationsAreGaugeTransformations → Set

    prototypeSuppliesWilsonLocalEstimate : Set
    prototypeDoesNotSupplyWilsonLocalEstimate :
      prototypeSuppliesWilsonLocalEstimate → Set

canonicalThreeCycleBlockTorusBoundary : ThreeCycleBlockTorusBoundary
canonicalThreeCycleBlockTorusBoundary =
  threeCycleBlockTorusBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)
