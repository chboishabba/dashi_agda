{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLiteralWilsonS2CanonicalProductPresentationValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.YangMills.YMClayLiteralWilsonS2CanonicalProductPresentationExact as S2

decodeProductEqualityIsDefinitional :
  S2.independentDecodeToWilsonProductEqualityRequired ≡ false
decodeProductEqualityIsDefinitional =
  S2.independentDecodeToWilsonProductEqualityRequiredIsFalse

translatedProductEqualityIsDefinitional :
  S2.independentTranslatedWilsonProductEqualityRequired ≡ false
translatedProductEqualityIsDefinitional =
  S2.independentTranslatedWilsonProductEqualityRequiredIsFalse

canonicalCarrierPaysRepresentation :
  S2.canonicalFiniteWilsonListCarrierPaysRepresentation ≡ true
canonicalCarrierPaysRepresentation =
  S2.canonicalFiniteWilsonListCarrierPaysRepresentationIsTrue

supportDistanceStillPhysical :
  S2.supportDistanceTimeStillPhysical ≡ true
supportDistanceStillPhysical =
  S2.supportDistanceTimeStillPhysicalIsTrue

multiplicationWeldStillPhysical :
  S2.wilsonT5MultiplicationWeldStillPhysical ≡ true
multiplicationWeldStillPhysical =
  S2.wilsonT5MultiplicationWeldStillPhysicalIsTrue

boundPredicateWeldStillPhysical :
  S2.wilsonBoundPredicateWeldStillPhysical ≡ true
boundPredicateWeldStillPhysical =
  S2.wilsonBoundPredicateWeldStillPhysicalIsTrue
