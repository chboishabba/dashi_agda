module DASHI.Law.AustralianDisabilityJusticeObserverFixtureRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.AustralianDisabilityJusticeObserverFixtureExact as Fixture

ahrcSourceBoundRegression :
  Fixture.ahrcSourceBound
    Fixture.canonicalAustralianDisabilityJusticeObserverBoundary
  ≡ true
ahrcSourceBoundRegression = refl

credibilityBarrierLocatedRegression :
  Fixture.negativeAssumptionsCanAffectCredibilityAssessment
    Fixture.canonicalAustralianDisabilityJusticeObserverBoundary
  ≡ true
credibilityBarrierLocatedRegression = refl

communicationAdjustmentLocatedRegression :
  Fixture.communicationSupportAndAdjustmentCoordinateLocated
    Fixture.canonicalAustralianDisabilityJusticeObserverBoundary
  ≡ true
communicationAdjustmentLocatedRegression = refl

-- Scope firewalls: the AHRC report is disability/criminal-justice evidence,
-- not an autism-specific or family-court universalisation.
autismSpecificClaimAutomaticallyPaidRegression :
  Fixture.disabilitySourceAutomaticallyPaysAutismSpecificClaim
    Fixture.canonicalAustralianDisabilityJusticeObserverBoundary
  ≡ false
autismSpecificClaimAutomaticallyPaidRegression = refl

familyCourtClaimAutomaticallyPaidRegression :
  Fixture.criminalJusticeSourceAutomaticallyPaysFamilyCourtClaim
    Fixture.canonicalAustralianDisabilityJusticeObserverBoundary
  ≡ false
familyCourtClaimAutomaticallyPaidRegression = refl

communicationDifferenceAutomaticallyUnreliableRegression :
  Fixture.communicationDifferenceAutomaticallyUnreliable
    Fixture.canonicalAustralianDisabilityJusticeObserverBoundary
  ≡ false
communicationDifferenceAutomaticallyUnreliableRegression = refl

adjustmentAutomaticallyTruthRegression :
  Fixture.adjustmentAutomaticallyEstablishesTruth
    Fixture.canonicalAustralianDisabilityJusticeObserverBoundary
  ≡ false
adjustmentAutomaticallyTruthRegression = refl
