module DASHI.Education.DigitalESDStudyClaimPilotRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Education.DigitalESDStudyClaimPilotExact as Pilot
import DASHI.Education.DigitalESDStudyClaimCeilingExact as Ceiling
import DASHI.Education.DigitalESDCurrentScholarlySnowballExact as Sources

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
