module DASHI.Foundations.F3FourSymplecticExteriorSquareRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.F3FourSymplecticExteriorSquareExact as E

primitiveRelationIsSymplecticPaid :
  E.primitiveRelationIsSymplecticWedge E.canonicalExteriorSquareBoundary ≡ true
primitiveRelationIsSymplecticPaid = refl

rawPuncturedT4NotPromoted :
  E.rawPuncturedT4IdentifiedWithNullCone E.canonicalExteriorSquareBoundary ≡ false
rawPuncturedT4NotPromoted = refl

orientedLagrangianCarrierDistinguished :
  E.orientedLagrangianDerivedCarrierRecorded E.canonicalExteriorSquareBoundary ≡ true
orientedLagrangianCarrierDistinguished = refl

sameActionRecognitionRequired :
  E.sameActionRecognitionRequired E.canonicalExteriorSquareBoundary ≡ true
sameActionRecognitionRequired = refl

pgspWeylEqualityNotInferredFromOrder :
  E.orderEqualityPromotesGroupRecognition E.canonicalExteriorSquareBoundary ≡ false
pgspWeylEqualityNotInferredFromOrder = refl
