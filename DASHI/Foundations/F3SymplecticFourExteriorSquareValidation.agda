module DASHI.Foundations.F3SymplecticFourExteriorSquareValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.F3SymplecticFourExteriorSquareExact as Exterior

primitiveExteriorSquareConstructed :
  Exterior.primitiveExteriorSquareConstructed Exterior.canonicalExteriorSquareBoundary ≡ true
primitiveExteriorSquareConstructed = refl

rawPuncturedT4KeptDistinct :
  Exterior.rawPuncturedT4IdentifiedWithDerivedLag80 Exterior.canonicalExteriorSquareBoundary ≡ false
rawPuncturedT4KeptDistinct = refl

pluckerNullQuadraticRecorded :
  Exterior.pluckerNullQuadraticRecorded Exterior.canonicalExteriorSquareBoundary ≡ true
pluckerNullQuadraticRecorded = refl

orientedLagrangianRecognitionTyped :
  Exterior.orientedLagrangianRecognitionTyped Exterior.canonicalExteriorSquareBoundary ≡ true
orientedLagrangianRecognitionTyped = refl

projectiveIncidenceDualityTyped :
  Exterior.projectiveIncidenceDualityTyped Exterior.canonicalExteriorSquareBoundary ≡ true
projectiveIncidenceDualityTyped = refl

cardinalityAlonePromotesRecognition :
  Exterior.cardinalityAlonePromotesRecognition Exterior.canonicalExteriorSquareBoundary ≡ false
cardinalityAlonePromotesRecognition = refl
