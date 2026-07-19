module DASHI.Biology.Levin.ATPDependentCytoplasmicOrganisation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Candidate bridge for ATP-supported cytoplasmic organisation.
--
-- ATP availability, cytoskeletal competence, phase organisation, and
-- cell-like division are kept separate.  This does not deny membrane pumps
-- or identify ATP energy solely with hydration-shell organisation.

record CytoplasmicOrganisationState : Set where
  field
    ATPAvailable             : Bool
    cytoskeletonCompetent    : Bool
    spontaneousCompartment   : Bool
    divisionLikeTransition   : Bool
    membraneRequired         : Bool

open CytoplasmicOrganisationState public

record ATPOrganisationWitness : Set where
  field
    state : CytoplasmicOrganisationState

    ATPIsPresent : ATPAvailable state ≡ true
    cytoskeletonIsCompetent : cytoskeletonCompetent state ≡ true
    compartmentEmerges : spontaneousCompartment state ≡ true

    ATPNotSufficientAlone : Bool
    ATPNotSufficientAloneIsFalse : ATPNotSufficientAlone ≡ false

    hydrationEnergyNotExclusive : Bool
    hydrationEnergyNotExclusiveIsFalse :
      hydrationEnergyNotExclusive ≡ false

    sodiumPotassiumPumpNotRejected : Bool
    sodiumPotassiumPumpNotRejectedIsFalse :
      sodiumPotassiumPumpNotRejected ≡ false

    reading : String

open ATPOrganisationWitness public

canonicalCytoplasmicOrganisationState : CytoplasmicOrganisationState
canonicalCytoplasmicOrganisationState = record
  { ATPAvailable = true
  ; cytoskeletonCompetent = true
  ; spontaneousCompartment = true
  ; divisionLikeTransition = true
  ; membraneRequired = false
  }

canonicalATPOrganisationWitness : ATPOrganisationWitness
canonicalATPOrganisationWitness = record
  { state = canonicalCytoplasmicOrganisationState
  ; ATPIsPresent = refl
  ; cytoskeletonIsCompetent = refl
  ; compartmentEmerges = refl
  ; ATPNotSufficientAlone = false
  ; ATPNotSufficientAloneIsFalse = refl
  ; hydrationEnergyNotExclusive = false
  ; hydrationEnergyNotExclusiveIsFalse = refl
  ; sodiumPotassiumPumpNotRejected = false
  ; sodiumPotassiumPumpNotRejectedIsFalse = refl
  ; reading =
      "ATP-supported cytoplasmic self-organisation is typed with cytoskeletal and phase prerequisites and does not promote an exclusive hydration-energy or pump-denial theory"
  }
