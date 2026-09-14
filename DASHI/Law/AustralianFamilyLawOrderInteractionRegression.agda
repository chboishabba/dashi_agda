module DASHI.Law.AustralianFamilyLawOrderInteractionRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.AustralianFamilyLawOrderInteractionExact as Interaction

------------------------------------------------------------------------
-- RED contract: operational interaction of federal family-law orders,
-- State/Territory family-violence orders, information sharing and child-welfare
-- jurisdiction must not collapse into a bare supremacy slogan.
------------------------------------------------------------------------

section68QInvalidityIsExtentLimited :
  Interaction.section68QInvalidityIsToExtentOfInconsistency ≡ true
section68QInvalidityIsExtentLimited = refl

section68RPowerIsDistinct :
  Interaction.section68RStateTerritoryVariationPowerLocated ≡ true
section68RPowerIsDistinct = refl

informationSharingSubdivisionDALocated :
  Interaction.subdivisionDAInformationSharingLocated ≡ true
informationSharingSubdivisionDALocated = refl

commonwealthSupremacyDoesNotReplaceStatutoryMechanism :
  Interaction.CommonwealthSupremacyAutomaticallyCompleteOperationalRule → ⊥
commonwealthSupremacyDoesNotReplaceStatutoryMechanism =
  Interaction.commonwealthSupremacyDoesNotAutomaticallyCompleteOperationalRule

inconsistencyDoesNotInvalidateWholeFVO :
  Interaction.InconsistencyAutomaticallyInvalidatesWholeFamilyViolenceOrder → ⊥
inconsistencyDoesNotInvalidateWholeFVO =
  Interaction.inconsistencyDoesNotAutomaticallyInvalidateWholeFamilyViolenceOrder

section68RPowerDoesNotMeanExercise :
  Interaction.Section68RPowerAutomaticallyExercised → ⊥
section68RPowerDoesNotMeanExercise =
  Interaction.section68RPowerDoesNotAutomaticallyExerciseItself

informationExistenceDoesNotMeanCourtReceipt :
  Interaction.InformationExistsAutomaticallyReceivedByCourt → ⊥
informationExistenceDoesNotMeanCourtReceipt =
  Interaction.informationExistenceDoesNotAutomaticallyMeanCourtReceipt

courtReceiptDoesNotMeanCorrectWeight :
  Interaction.CourtReceiptAutomaticallyCorrectWeight → ⊥
courtReceiptDoesNotMeanCorrectWeight =
  Interaction.courtReceiptDoesNotAutomaticallyMeanCorrectWeight

familyProceedingDoesNotEraseChildProtectionJurisdiction :
  Interaction.FamilyProceedingAutomaticallyDisplacesChildProtectionJurisdiction → ⊥
familyProceedingDoesNotEraseChildProtectionJurisdiction =
  Interaction.familyProceedingDoesNotAutomaticallyDisplaceChildProtectionJurisdiction

canonicalBoundaryExists : Interaction.AustralianFamilyLawOrderInteractionBoundary
canonicalBoundaryExists = Interaction.canonicalAustralianFamilyLawOrderInteractionBoundary
