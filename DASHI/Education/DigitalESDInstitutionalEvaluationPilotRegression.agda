module DASHI.Education.DigitalESDInstitutionalEvaluationPilotRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Education.DigitalESDInstitutionalEvaluationPilotExact as Eval
import DASHI.Education.DigitalESDStudyClaimCeilingExact as Ceiling
import DASHI.Education.DigitalESDPrimarySourceMethodologyAtlasExact as Primary

uneceSourceRegression :
  Ceiling.StudyClaimProfile.source Eval.uneceFifthEvaluationPilotProfile
  ≡ Primary.uneceFifthESDEvaluationSource
uneceSourceRegression = refl

uneceReportCorpusRegression :
  Ceiling.StudyClaimProfile.enrolledOrReportedN Eval.uneceFifthEvaluationPilotProfile
  ≡ Ceiling.explicitlyReportedNat 31 "national implementation reports underlying the fifth regional evaluation"
uneceReportCorpusRegression = refl

uneceClaimRegression :
  Ceiling.StudyClaimProfile.strongestSupportedClaim Eval.uneceFifthEvaluationPilotProfile
  ≡ Ceiling.reviewSynthesisClaim
uneceClaimRegression = refl
