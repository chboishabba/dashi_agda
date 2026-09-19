module DASHI.Biology.Levin.MitochondrialBioenergeticAdapter where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.ATPDependentCytoplasmicOrganisation as ATP
import DASHI.Biology.Levin.CellPhysicalOrganisationCore as Physical

------------------------------------------------------------------------
-- Adapter from the mitochondrial candidate model into the existing physical
-- organisation lane.  Mitochondrial ATP production is an upstream energetic
-- carrier; it is not identified with the whole-cell organisation state.

record MitochondrialBioenergeticAdapter : Set where
  field
    atpOrganisationWitness : ATP.ATPOrganisationWitness
    atpOrganisationWitnessIsCanonical :
      atpOrganisationWitness ≡ ATP.canonicalATPOrganisationWitness

    physicalOrganisationCore : Physical.CellPhysicalOrganisationCore
    physicalOrganisationCoreIsCanonical :
      physicalOrganisationCore ≡ Physical.canonicalCellPhysicalOrganisationCore

    mitochondrialOutputFeedsATPAvailability : Bool
    mitochondrialOutputFeedsATPAvailabilityIsTrue :
      mitochondrialOutputFeedsATPAvailability ≡ true

    ATPFluxIsNotWholeCellState : Bool
    ATPFluxIsNotWholeCellStateIsFalse : ATPFluxIsNotWholeCellState ≡ false

    oscillatorModelIsNotRequiredByExistingLane : Bool
    oscillatorModelIsNotRequiredByExistingLaneIsFalse :
      oscillatorModelIsNotRequiredByExistingLane ≡ false

    reading : String

open MitochondrialBioenergeticAdapter public

canonicalMitochondrialBioenergeticAdapter : MitochondrialBioenergeticAdapter
canonicalMitochondrialBioenergeticAdapter = record
  { atpOrganisationWitness = ATP.canonicalATPOrganisationWitness
  ; atpOrganisationWitnessIsCanonical = refl
  ; physicalOrganisationCore = Physical.canonicalCellPhysicalOrganisationCore
  ; physicalOrganisationCoreIsCanonical = refl
  ; mitochondrialOutputFeedsATPAvailability = true
  ; mitochondrialOutputFeedsATPAvailabilityIsTrue = refl
  ; ATPFluxIsNotWholeCellState = false
  ; ATPFluxIsNotWholeCellStateIsFalse = refl
  ; oscillatorModelIsNotRequiredByExistingLane = false
  ; oscillatorModelIsNotRequiredByExistingLaneIsFalse = refl
  ; reading = "Mitochondrial bioenergetics supplies an upstream ATP/gradient carrier to the existing cell-organisation lane without making the speculative oscillator model a prerequisite"
  }
