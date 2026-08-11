module DASHI.Biology.PsychogeographicFilteredScaleExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Cross-pollination from the filtered/mixed-carrier distinction developed in
-- the Monster branch: a displayed scale decomposition is a coordinate system,
-- not automatically an invariant direct sum under total urban dynamics.
------------------------------------------------------------------------

data ScaleCoordinate : Set where
  bodyCoordinate : ScaleCoordinate
  intimateCoordinate : ScaleCoordinate
  streetCoordinate : ScaleCoordinate
  civicCoordinate : ScaleCoordinate
  districtCoordinate : ScaleCoordinate
  horizonCoordinate : ScaleCoordinate

scaleRank : ScaleCoordinate → Nat
scaleRank bodyCoordinate = 1
scaleRank intimateCoordinate = 2
scaleRank streetCoordinate = 3
scaleRank civicCoordinate = 4
scaleRank districtCoordinate = 5
scaleRank horizonCoordinate = 6

mixCoordinate : ScaleCoordinate → ScaleCoordinate
mixCoordinate bodyCoordinate = horizonCoordinate
mixCoordinate horizonCoordinate = bodyCoordinate
mixCoordinate intimateCoordinate = civicCoordinate
mixCoordinate civicCoordinate = intimateCoordinate
mixCoordinate streetCoordinate = districtCoordinate
mixCoordinate districtCoordinate = streetCoordinate

mixCoordinateInvolutive :
  (coordinate : ScaleCoordinate) →
  mixCoordinate (mixCoordinate coordinate) ≡ coordinate
mixCoordinateInvolutive bodyCoordinate = refl
mixCoordinateInvolutive intimateCoordinate = refl
mixCoordinateInvolutive streetCoordinate = refl
mixCoordinateInvolutive civicCoordinate = refl
mixCoordinateInvolutive districtCoordinate = refl
mixCoordinateInvolutive horizonCoordinate = refl

isLowerTrigramCoordinate : ScaleCoordinate → Bool
isLowerTrigramCoordinate bodyCoordinate = true
isLowerTrigramCoordinate intimateCoordinate = true
isLowerTrigramCoordinate streetCoordinate = true
isLowerTrigramCoordinate civicCoordinate = false
isLowerTrigramCoordinate districtCoordinate = false
isLowerTrigramCoordinate horizonCoordinate = false

wholeCarrierMixCrossesLowerUpperBoundary :
  isLowerTrigramCoordinate bodyCoordinate ≡ true
  × isLowerTrigramCoordinate (mixCoordinate bodyCoordinate) ≡ false
wholeCarrierMixCrossesLowerUpperBoundary = refl , refl

record ScaleProfile : Set where
  constructor scaleProfile
  field
    body intimate street civic district horizon : Nat

open ScaleProfile public

canonicalProfile : ScaleProfile
canonicalProfile = scaleProfile 1 2 3 4 5 6

mixProfile : ScaleProfile → ScaleProfile
mixProfile profile =
  scaleProfile
    (horizon profile)
    (civic profile)
    (district profile)
    (intimate profile)
    (street profile)
    (body profile)

profileTotal : ScaleProfile → Nat
profileTotal profile =
  body profile + intimate profile + street profile
  + civic profile + district profile + horizon profile

canonicalProfileTotalIsTwentyOne : profileTotal canonicalProfile ≡ 21
canonicalProfileTotalIsTwentyOne = refl

canonicalMixedProfileTotalIsTwentyOne :
  profileTotal (mixProfile canonicalProfile) ≡ 21
canonicalMixedProfileTotalIsTwentyOne = refl

canonicalMixActuallyChangesBodyCoordinate :
  ¬ (body canonicalProfile ≡ body (mixProfile canonicalProfile))
canonicalMixActuallyChangesBodyCoordinate ()

record FilteredScaleBoundary : Set where
  constructor filteredScaleBoundary
  field
    sixCoordinatesAreSixIndependentSubsystems : Bool
    sixCoordinatesAreSixIndependentSubsystemsIsFalse :
      sixCoordinatesAreSixIndependentSubsystems ≡ false
    lowerAndUpperTrigramsAreInvariantUnderAllDynamics : Bool
    lowerAndUpperTrigramsAreInvariantUnderAllDynamicsIsFalse :
      lowerAndUpperTrigramsAreInvariantUnderAllDynamics ≡ false
    totalPreservationForOneWitnessProvesUniversalConservation : Bool
    totalPreservationForOneWitnessProvesUniversalConservationIsFalse :
      totalPreservationForOneWitnessProvesUniversalConservation ≡ false

canonicalFilteredScaleBoundary : FilteredScaleBoundary
canonicalFilteredScaleBoundary =
  filteredScaleBoundary false refl false refl false refl
