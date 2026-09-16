module DASHI.Education.DigitalESDStudyClaimQuantitativePilotRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Education.DigitalESDStudyClaimQuantitativePilotExact as Quant
import DASHI.Education.DigitalESDStudyClaimCeilingExact as Ceiling
import DASHI.Education.DigitalESDAcquisitionSnowballParetoExact as Acquisition
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone

brasslerSourceRegression :
  Ceiling.StudyClaimProfile.source Quant.brasslerPilotProfile
  ≡ Acquisition.brasslerOERESDStudentProducerSource
brasslerSourceRegression = refl

brasslerEnrolledNRegression :
  Ceiling.StudyClaimProfile.enrolledOrReportedN Quant.brasslerPilotProfile
  ≡ Ceiling.explicitlyReportedNat 409 "study sample: 83 OER-production students + 326 control-group students"
brasslerEnrolledNRegression = refl

brasslerAnalysisNUnresolvedRegression :
  Ceiling.StudyClaimProfile.analysisN Quant.brasslerPilotProfile
  ≡ Ceiling.natNotReported "article reports N=409 but repeated-measures ANOVA F(1,191); visible primary text does not explain the inferential analysis denominator, so analysis n is not reconstructed from degrees of freedom"
brasslerAnalysisNUnresolvedRegression = refl

brasslerClaimRegression :
  Ceiling.StudyClaimProfile.strongestSupportedClaim Quant.brasslerPilotProfile
  ≡ Ceiling.implicationConeClaim Cone.derivesBoundedContrast
brasslerClaimRegression = refl
