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

causalCeilingRegression :
  Ceiling.StudyClaimProfile.strongestSupportedClaim RCT.greenMolloyDugganPilotProfile
  ≡ Ceiling.implicationConeClaim Cone.attributesCausalEffect
causalCeilingRegression = refl
