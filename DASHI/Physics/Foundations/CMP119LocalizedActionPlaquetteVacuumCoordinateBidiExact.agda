{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119LocalizedActionPlaquetteVacuumCoordinateBidiExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; subst; sym)

import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4

------------------------------------------------------------------------
-- LOCALIZED ACTION = PLAQUETTE COORDINATE x CONSTANT/REMAINDER COORDINATE
--
-- This is a literal bidi theorem for the existing two-field carrier:
--
--   LocalizedAction = localizedAction c r.
--
-- The beta/coupling lane observes c through plaquetteCoefficientProjector.
-- The vacuum-normalization lane must retain r when the vacuum term is encoded
-- as an additive constant.  Neither projection alone is injective, while the
-- pair reconstructs the action definitionally.
------------------------------------------------------------------------

localizedActionCoordinates : T4.LocalizedAction → ℚ × ℚ
localizedActionCoordinates action =
  T4.plaquetteCoefficientField action , T4.irrelevantCoefficientField action

rebuildLocalizedAction : ℚ × ℚ → T4.LocalizedAction
rebuildLocalizedAction (coefficient , remainder) =
  T4.localizedAction coefficient remainder

localizedActionCoordinateRoundTrip :
  ∀ action →
  rebuildLocalizedAction (localizedActionCoordinates action) ≡ action
localizedActionCoordinateRoundTrip (T4.localizedAction coefficient remainder) = refl

localizedActionCoordinatePairRoundTrip :
  ∀ coordinates →
  localizedActionCoordinates (rebuildLocalizedAction coordinates) ≡ coordinates
localizedActionCoordinatePairRoundTrip (coefficient , remainder) = refl

zeroBelowOne : 0ℚ < 1ℚ
zeroBelowOne = ℚP.positive⁻¹ 1ℚ

zeroNotOne : 0ℚ ≢ 1ℚ
zeroNotOne equality =
  ℚP.<-irrefl refl
    (subst (λ value → 0ℚ < value) (sym equality) zeroBelowOne)

record ProjectionCollision (project : T4.LocalizedAction → ℚ) : Set where
  constructor projection-collision
  field
    left right : T4.LocalizedAction
    sameProjection : project left ≡ project right
    distinctActions : left ≢ right

open ProjectionCollision public

plaquetteProjectionCollision :
  ProjectionCollision T4.plaquetteCoefficientProjector
plaquetteProjectionCollision = record
  { ProjectionCollision.left = T4.irrelevantAction 0ℚ
  ; ProjectionCollision.right = T4.irrelevantAction 1ℚ
  ; ProjectionCollision.sameProjection = refl
  ; ProjectionCollision.distinctActions = λ actionsEqual →
      zeroNotOne (cong T4.irrelevantCoefficientField actionsEqual)
  }

constantProjectionCollision :
  ProjectionCollision T4.irrelevantCoefficientField
constantProjectionCollision = record
  { ProjectionCollision.left = T4.plaquetteRelevantAction 0ℚ
  ; ProjectionCollision.right = T4.plaquetteRelevantAction 1ℚ
  ; ProjectionCollision.sameProjection = refl
  ; ProjectionCollision.distinctActions = λ actionsEqual →
      zeroNotOne (cong T4.plaquetteCoefficientField actionsEqual)
  }

plaquetteProjectionAloneNotInjective : Bool
plaquetteProjectionAloneNotInjective = true

constantProjectionAloneNotInjective : Bool
constantProjectionAloneNotInjective = true

plaquetteAndConstantCoordinatesJointlyComplete : Bool
plaquetteAndConstantCoordinatesJointlyComplete = true

betaAndNormalizationCoordinatesAreComplementary : Bool
betaAndNormalizationCoordinatesAreComplementary = true

record LocalizedActionCoordinateBoundary : Set where
  constructor localized-action-coordinate-boundary
  field
    plaquetteCoordinateOwned : Bool
    constantRemainderCoordinateOwned : Bool
    plaquetteProjectionInjective : Bool
    constantProjectionInjective : Bool
    pairedCoordinatesReconstructExactly : Bool
    betaAndNormalizationCoordinatesComplementary : Bool

canonicalLocalizedActionCoordinateBoundary : LocalizedActionCoordinateBoundary
canonicalLocalizedActionCoordinateBoundary =
  localized-action-coordinate-boundary
    true true false false true true
