module DASHI.Core.InstitutionalProximityInfluenceAdequacyRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.InstitutionalProximityInfluenceAdequacyExact as Proximity

influenceDefectRegression : Proximity.InfluenceQueryAdequacyDefect
influenceDefectRegression = Proximity.influenceQueryAdequacyDefect

proximityNotInfluenceRegression :
  Proximity.proximityAutomaticallyInfluence
    Proximity.canonicalInstitutionalProximityBoundary
  ≡ false
proximityNotInfluenceRegression = refl

accessNotDecisionControlRegression :
  Proximity.accessAutomaticallyDecisionControl
    Proximity.canonicalInstitutionalProximityBoundary
  ≡ false
accessNotDecisionControlRegression = refl

membershipNotMoralReliabilityRegression :
  Proximity.networkMembershipAutomaticallyMoralReliability
    Proximity.canonicalInstitutionalProximityBoundary
  ≡ false
membershipNotMoralReliabilityRegression = refl

proximityRelevantAcquisitionCoordinateRegression :
  Proximity.proximityMayRemainRelevantAcquisitionCoordinate
    Proximity.canonicalInstitutionalProximityBoundary
  ≡ true
proximityRelevantAcquisitionCoordinateRegression = refl
