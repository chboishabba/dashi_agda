module DASHI.Education.DigitalESDRandomizedCausalAcquisitionRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Education.DigitalESDRandomizedCausalAcquisitionExact as RCT
import DASHI.Education.DigitalESDStudyClaimCeilingExact as Ceiling
import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone

sourceDOIRegression :
  Attr.AttributedSource.doiState RCT.greenMolloyDugganSource
  ≡ Attr.doiRecorded "10.3390/su14010394"
sourceDOIRegression = refl

trialNRegression :
  Ceiling.StudyClaimProfile.enrolledOrReportedN RCT.greenMolloyDugganPilotProfile
  ≡ Ceiling.explicitlyReportedNat 106 "randomised controlled factorial trial total n"
trialNRegression = refl

reportedAnalysisNRegression :
  Ceiling.StudyClaimProfile.analysisN RCT.greenMolloyDugganPilotProfile
  ≡ Ceiling.natNotReported "106 complete randomized datasets exist, but reported inferential contrasts use analysis-local exclusions (e.g. simulation 24 vs control 27 after control outlier removal); no single analysis n represents all reported tests"
reportedAnalysisNRegression = refl

causalPromotionStillUnpaidRegression :
  Ceiling.StudyClaimProfile.strongestSupportedClaim RCT.greenMolloyDugganPilotProfile
  ≡ Ceiling.implicationConeClaim Cone.associatesTreatmentAndOutcome
causalPromotionStillUnpaidRegression = refl
