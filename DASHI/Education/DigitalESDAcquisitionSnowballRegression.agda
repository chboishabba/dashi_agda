module DASHI.Education.DigitalESDAcquisitionSnowballRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDAcquisitionSnowballParetoExact as Acquisition

participatoryESDContextRegression :
  Acquisition.DigitalESDAcquisitionAtlas.participatoryESDResearchContextPaid
    Acquisition.canonicalDigitalESDAcquisitionAtlas
  ≡ true
participatoryESDContextRegression = refl

longitudinalESDBenchmarkRegression :
  Acquisition.DigitalESDAcquisitionAtlas.longitudinalESDBenchmarkPaid
    Acquisition.canonicalDigitalESDAcquisitionAtlas
  ≡ true
longitudinalESDBenchmarkRegression = refl

oerSustainabilityReviewRegression :
  Acquisition.DigitalESDAcquisitionAtlas.oerOrganisationalSustainabilityReviewPaid
    Acquisition.canonicalDigitalESDAcquisitionAtlas
  ≡ true
oerSustainabilityReviewRegression = refl

oerESDStudentProducerRegression :
  Acquisition.DigitalESDAcquisitionAtlas.oerESDStudentProducerEvidencePaid
    Acquisition.canonicalDigitalESDAcquisitionAtlas
  ≡ true
oerESDStudentProducerRegression = refl

publicPlatformInteroperabilityCharterRegression :
  Acquisition.DigitalESDAcquisitionAtlas.publicPlatformInteroperabilityCharterPaid
    Acquisition.canonicalDigitalESDAcquisitionAtlas
  ≡ true
publicPlatformInteroperabilityCharterRegression = refl

rightToRepairEducationRegression :
  Acquisition.DigitalESDAcquisitionAtlas.rightToRepairEducationSourcePaid
    Acquisition.canonicalDigitalESDAcquisitionAtlas
  ≡ true
rightToRepairEducationRegression = refl

participationDoesNotPromoteAuthorityRegression :
  Acquisition.ParticipatoryESDPromotesConstitutiveEpistemicAuthority → ⊥
participationDoesNotPromoteAuthorityRegression =
  Acquisition.participatoryESDDoesNotPromoteConstitutiveEpistemicAuthority

longitudinalBenchmarkDoesNotCloseDigitalESDRegression :
  Acquisition.OneYearESDResultPaysDigitalESDLongHorizonImpact → ⊥
longitudinalBenchmarkDoesNotCloseDigitalESDRegression =
  Acquisition.oneYearESDResultDoesNotPayDigitalESDLongHorizonImpact

oerSustainabilityDoesNotPayMaterialDurabilityRegression :
  Acquisition.OEROrganisationalSustainabilityPaysMaterialRepairability → ⊥
oerSustainabilityDoesNotPayMaterialDurabilityRegression =
  Acquisition.oerOrganisationalSustainabilityDoesNotPayMaterialRepairability

charterDoesNotProvePlatformDurabilityRegression :
  Acquisition.OpenStandardsCharterProvesPlatformDurability → ⊥
charterDoesNotProvePlatformDurabilityRegression =
  Acquisition.openStandardsCharterDoesNotProvePlatformDurability

repairEducationDoesNotProveRepairabilityRegression :
  Acquisition.RightToRepairEducationProvesDeployedHardwareRepairability → ⊥
repairEducationDoesNotProveRepairabilityRegression =
  Acquisition.rightToRepairEducationDoesNotProveDeployedHardwareRepairability

participantGovernanceResidualRegression :
  Acquisition.paymentState Acquisition.esdParticipantGovernanceTransfer
  ≡ Acquisition.unpaid
participantGovernanceResidualRegression = refl

longitudinalResidualRegression :
  Acquisition.paymentState Acquisition.longitudinalInterventionImpact
  ≡ Acquisition.unpaid
longitudinalResidualRegression = refl

openDurabilityResidualRegression :
  Acquisition.paymentState Acquisition.openInteroperabilityDurability
  ≡ Acquisition.unpaid
openDurabilityResidualRegression = refl

frontierStillRetainsResidualsRegression :
  Acquisition.currentAcquisitionFrontier
  ≡ Acquisition.educationSpecificLifecycleMeasurement
  ∷ Acquisition.longitudinalInterventionImpact
  ∷ Acquisition.esdParticipantGovernanceTransfer
  ∷ Acquisition.openInteroperabilityDurability
  ∷ []
frontierStillRetainsResidualsRegression = refl
