module DASHI.Education.DigitalESDStudyClaimPilotRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Education.DigitalESDStudyClaimPilotExact as Pilot
import DASHI.Education.DigitalESDStudyClaimCeilingExact as Ceiling
import DASHI.Education.DigitalESDCurrentScholarlySnowballExact as Sources
import DASHI.Education.DigitalESDAcquisitionSnowballParetoExact as Acquisition
import DASHI.Education.DigitalESDSourceAttributionCorrectionExact as Correction
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone

ardilaSourceIdentityRegression :
  Ceiling.StudyClaimProfile.source Pilot.ardilaPilotProfile
  ≡ Sources.ardilaDigitalFuturesSource
ardilaSourceIdentityRegression = refl

gousetiSourceIdentityRegression :
  Ceiling.StudyClaimProfile.source Pilot.gousetiPilotProfile
  ≡ Sources.gousetiPlatformisationSource
gousetiSourceIdentityRegression = refl

martinezSourceIdentityRegression :
  Ceiling.StudyClaimProfile.source Pilot.martinezPilotProfile
  ≡ Sources.martinezDigitalEducationSystematicReviewSource
martinezSourceIdentityRegression = refl

boehmeSourceIdentityRegression :
  Ceiling.StudyClaimProfile.source Pilot.boehmePilotProfile
  ≡ Sources.boehmeDigitainabilitySource
boehmeSourceIdentityRegression = refl

descampsSourceIdentityRegression :
  Ceiling.StudyClaimProfile.source Pilot.descampsPilotProfile
  ≡ Acquisition.descampsDigitalSobrietySource
descampsSourceIdentityRegression = refl

pinzoneCorrectedSourceIdentityRegression :
  Ceiling.StudyClaimProfile.source Pilot.pinzonePilotProfile
  ≡ Correction.pinzoneEducationLCACorrectedSource
pinzoneCorrectedSourceIdentityRegression = refl

ardilaClaimKindRegression :
  Ceiling.StudyClaimProfile.strongestSupportedClaim Pilot.ardilaPilotProfile
  ≡ Ceiling.implementationContextClaim
ardilaClaimKindRegression = refl

gousetiClaimKindRegression :
  Ceiling.StudyClaimProfile.strongestSupportedClaim Pilot.gousetiPilotProfile
  ≡ Ceiling.livedExperienceClaim
gousetiClaimKindRegression = refl

martinezClaimKindRegression :
  Ceiling.StudyClaimProfile.strongestSupportedClaim Pilot.martinezPilotProfile
  ≡ Ceiling.reviewSynthesisClaim
martinezClaimKindRegression = refl

boehmeClaimKindRegression :
  Ceiling.StudyClaimProfile.strongestSupportedClaim Pilot.boehmePilotProfile
  ≡ Ceiling.conceptualMechanismClaim
boehmeClaimKindRegression = refl

descampsClaimKindRegression :
  Ceiling.StudyClaimProfile.strongestSupportedClaim Pilot.descampsPilotProfile
  ≡ Ceiling.implicationConeClaim Cone.derivesBoundedContrast
descampsClaimKindRegression = refl

pinzoneClaimKindRegression :
  Ceiling.StudyClaimProfile.strongestSupportedClaim Pilot.pinzonePilotProfile
  ≡ Ceiling.modelBasedEnvironmentalImpactClaim
pinzoneClaimKindRegression = refl

ardilaNRegression :
  Ceiling.StudyClaimProfile.enrolledOrReportedN Pilot.ardilaPilotProfile
  ≡ Ceiling.explicitlyReportedNat 10 "two five-member HE student teams; Methods 3.1"
ardilaNRegression = refl

gousetiNRegression :
  Ceiling.StudyClaimProfile.enrolledOrReportedN Pilot.gousetiPilotProfile
  ≡ Ceiling.explicitlyReportedNat 71 "Table 1 total: 4 senior leaders + 21 teachers + 36 students + 10 parents"
gousetiNRegression = refl

martinezStudyCountRegression :
  Ceiling.StudyClaimProfile.enrolledOrReportedN Pilot.martinezPilotProfile
  ≡ Ceiling.explicitlyReportedNat 33 "final included-study count; PRISMA flow"
martinezStudyCountRegression = refl

boehmeNoInventedNRegression :
  Ceiling.StudyClaimProfile.enrolledOrReportedN Pilot.boehmePilotProfile
  ≡ Ceiling.natNotReported "no empirical enrolled-sample size applies to this conceptual framework source"
boehmeNoInventedNRegression = refl

descampsEnrolledNRegression :
  Ceiling.StudyClaimProfile.enrolledOrReportedN Pilot.descampsPilotProfile
  ≡ Ceiling.explicitlyReportedNat 164 "students participating in the learning session; Sample section"
descampsEnrolledNRegression = refl

descampsAnalysisNRegression :
  Ceiling.StudyClaimProfile.analysisN Pilot.descampsPilotProfile
  ≡ Ceiling.explicitlyReportedNat 107 "students completing both pre-test and post-test and used for analysis"
descampsAnalysisNRegression = refl

pinzoneNoParticipantNRegression :
  Ceiling.StudyClaimProfile.enrolledOrReportedN Pilot.pinzonePilotProfile
  ≡ Ceiling.natNotReported "no participant enrolment n is the estimand carrier for the LCA; one-student functional unit is not a participant sample size"
pinzoneNoParticipantNRegression = refl
