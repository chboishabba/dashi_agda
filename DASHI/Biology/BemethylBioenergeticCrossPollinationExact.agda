module DASHI.Biology.BemethylBioenergeticCrossPollinationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.BemethylActoprotectorClaimAtlasExact as Claims
import DASHI.Biology.BemethylMetabolicMechanismBoundaryExact as Mechanism
import DASHI.Biology.Levin.MitochondrialBioenergeticAdapter as Mito
import DASHI.Biology.Levin.ATPDependentCytoplasmicOrganisation as ATP

record BemethylBioenergeticWeld : Set where
  field
    claimAtlas : Claims.BemethylClaimAtlas
    mitochondrialRoute : Mechanism.MechanismBoundary
    existingATPAdapter : Mito.MitochondrialBioenergeticAdapter
    existingATPOrganisation : ATP.ATPOrganisationWitness

    reportedMitochondrialRouteFeedsATPQuestion : Bool
    reportedGluconeogenicRouteFeedsFuelRecoveryQuestion : Bool

    sameObjectHumanValidationPaid : Bool
    exactDoseExposureCalibrationPaid : Bool
    molecularTargetIdentityPaid : Bool
    transcriptMechanismEqualsExistingATPMechanism : Bool

    reading : String

open BemethylBioenergeticWeld public

canonicalBemethylBioenergeticWeld : BemethylBioenergeticWeld
canonicalBemethylBioenergeticWeld = record
  { claimAtlas = Claims.canonicalBemethylClaimAtlas
  ; mitochondrialRoute = Mechanism.mitochondrialBoundary
  ; existingATPAdapter = Mito.canonicalMitochondrialBioenergeticAdapter
  ; existingATPOrganisation = ATP.canonicalATPOrganisationWitness
  ; reportedMitochondrialRouteFeedsATPQuestion = true
  ; reportedGluconeogenicRouteFeedsFuelRecoveryQuestion = true
  ; sameObjectHumanValidationPaid = false
  ; exactDoseExposureCalibrationPaid = false
  ; molecularTargetIdentityPaid = false
  ; transcriptMechanismEqualsExistingATPMechanism = false
  ; reading = "Bemethyl's reported metabolic routes can be attached upstream of the existing ATP/bioenergetic carrier only as candidate biological inputs; they are not identified with the existing ATP organisation theorem or a validated human mechanism"
  }

mechanismHypothesisDoesNotUpgradeExistingATPTheorem :
  transcriptMechanismEqualsExistingATPMechanism canonicalBemethylBioenergeticWeld ≡ false
mechanismHypothesisDoesNotUpgradeExistingATPTheorem = refl

humanSameObjectStillOpen :
  sameObjectHumanValidationPaid canonicalBemethylBioenergeticWeld ≡ false
humanSameObjectStillOpen = refl
