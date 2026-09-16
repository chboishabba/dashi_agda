module DASHI.Education.DigitalESDDisabilityStudyPNFRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Education.DigitalESDDisabilityStudyPNFExact as Audit
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone

primaryDisabilityStudyPNFCountRegression : Audit.primaryDisabilityStudyPNFCount ≡ 4
primaryDisabilityStudyPNFCountRegression = refl

haiderCeilingRegression :
  Audit.DisabilityStudyResultAudit.strongestPaidImplication Audit.haiderResultAudit
  ≡ Cone.restatesMeasuredResult
haiderCeilingRegression = refl

zhaoCeilingRegression :
  Audit.DisabilityStudyResultAudit.strongestPaidImplication Audit.zhaoResultAudit
  ≡ Cone.restatesMeasuredResult
zhaoCeilingRegression = refl

yetergeCeilingRegression :
  Audit.DisabilityStudyResultAudit.strongestPaidImplication Audit.yetergeResultAudit
  ≡ Cone.restatesMeasuredResult
yetergeCeilingRegression = refl

noDisabilityStudyPaysUniversalEffectRegression :
  Audit.disabilityPrimaryStudiesPayUniversalDigitalLearningEffect ≡ false
noDisabilityStudyPaysUniversalEffectRegression = refl
