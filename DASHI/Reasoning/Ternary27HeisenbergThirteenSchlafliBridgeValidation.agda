module DASHI.Reasoning.Ternary27HeisenbergThirteenSchlafliBridgeValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.Ternary27HeisenbergThirteenSchlafliBridgeExact as Bridge

quotientIsTwelve : Bridge.symplecticQuotientCoordinateCount ≡ 12
quotientIsTwelve = Bridge.symplecticQuotientCoordinateCountIs12

extraspecialCoordinatesAreThirteen : Bridge.extraspecialCoordinateCount ≡ 13
extraspecialCoordinatesAreThirteen = Bridge.extraspecialCoordinateCountIs13

schlafliCarrierIsSixFifteenSix : Bridge.sixPlusFifteenPlusSix ≡ 27
schlafliCarrierIsSixFifteenSix = Bridge.sixPlusFifteenPlusSixIs27

carrierWeldPaid :
  Bridge.rawTernaryToHeisenbergSixFifteenSixTwoSided
    Bridge.canonicalThirteenSchlafliBoundary ≡ true
carrierWeldPaid = refl

heisenbergRolesPaid :
  Bridge.extraspecialOnePlusSixPlusSixTyped
    Bridge.canonicalThirteenSchlafliBoundary ≡ true
heisenbergRolesPaid = refl

centralPhaseNotVertex :
  Bridge.centralPhaseKeptSeparateFrom27Vertices
    Bridge.canonicalThirteenSchlafliBoundary ≡ true
centralPhaseNotVertex = refl

normalizerConjugationStillOpen :
  Bridge.actualNormalizerSixAxisConjugationPaidHere
    Bridge.canonicalThirteenSchlafliBoundary ≡ false
normalizerConjugationStillOpen = refl

a5SameActionStillOpen :
  Bridge.a5FiveTranspositionsSameActionPaidHere
    Bridge.canonicalThirteenSchlafliBoundary ≡ false
a5SameActionStillOpen = refl

albertProductStillOpen :
  Bridge.albertJordanProductPaidHere
    Bridge.canonicalThirteenSchlafliBoundary ≡ false
albertProductStillOpen = refl
