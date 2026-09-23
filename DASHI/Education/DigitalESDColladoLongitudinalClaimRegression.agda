module DASHI.Education.DigitalESDColladoLongitudinalClaimRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Education.DigitalESDColladoLongitudinalClaimExact as Collado
import DASHI.Education.DigitalESDStudyClaimCeilingExact as Ceiling
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone

immediateAnalyticNRegression :
  Ceiling.StudyClaimProfile.enrolledOrReportedN Collado.colladoLongitudinalProfile
  ≡ Ceiling.derivedNatWithSameObjectReceipt 257
      "120 experimental + 137 control complete T0/T1 cases"
      "same-object arithmetic from Participants and procedure"
immediateAnalyticNRegression = refl

longitudinalCompleteNRegression :
  Ceiling.StudyClaimProfile.analysisN Collado.colladoLongitudinalProfile
  ≡ Ceiling.explicitlyReportedNat 98
      "49 experimental + 49 control completed T2; final sample with all measures"
longitudinalCompleteNRegression = refl

claimCeilingRegression :
  Ceiling.StudyClaimProfile.strongestSupportedClaim Collado.colladoLongitudinalProfile
  ≡ Ceiling.implicationConeClaim Cone.derivesBoundedContrast
claimCeilingRegression = refl

knowledgeT2CIRegression : Collado.knowledgeT2InteractionCI ≡ "b=0.74; 95% CI [0.35, 1.14]; t=3.72"
knowledgeT2CIRegression = refl

normT2CIRegression : Collado.normT2InteractionCI ≡ "b=0.34; 95% CI [0.02, 0.67]; t=2.06"
normT2CIRegression = refl

behaviourT2CIRegression : Collado.behaviourT2InteractionCI ≡ "b=0.69; 95% CI [0.40, 0.98]; t=4.70"
behaviourT2CIRegression = refl
