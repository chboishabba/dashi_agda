module DASHI.Education.DigitalESDDisabilityIntersectionalityAuditRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Education.DigitalESDDisabilityIntersectionalityAuditExact as Audit

primaryEmpiricalSourceCountRegression : Audit.primaryEmpiricalSourceCount ≡ 4
primaryEmpiricalSourceCountRegression = refl

atlasSourceCountRegression :
  Attr.sourceCount (Attr.AttributedSourceAtlas.sources Audit.canonicalDisabilityDigitalESDSourceAtlas) ≡ 6
atlasSourceCountRegression = refl

participationAccessibilityDistinctRegression :
  Audit.DisabilityDigitalESDBoundary.participationAndAccessibilityRemainDistinct
    Audit.canonicalDisabilityDigitalESDBoundary ≡ true
participationAccessibilityDistinctRegression = refl

assistiveSustainabilityRetainedRegression :
  Audit.DisabilityDigitalESDBoundary.assistiveTechnologySustainabilityRetained
    Audit.canonicalDisabilityDigitalESDBoundary ≡ true
assistiveSustainabilityRetainedRegression = refl

intersectionalRepairRequiredRegression :
  Audit.DisabilityDigitalESDBoundary.broadEquityLabelIsDisabilityConsumerAdequate
    Audit.canonicalDisabilityDigitalESDBoundary ≡ false
intersectionalRepairRequiredRegression = refl

broadEquityNotEnoughRegression :
  Audit.BroadEquityCreatesDisabilityConsumerAdequacy → ⊥
broadEquityNotEnoughRegression = Audit.broadEquityDoesNotCreateDisabilityConsumerAdequacy

traumaNotDisabilityInferenceRegression :
  Audit.TraumaMemoryCreatesDisabilityInference → ⊥
traumaNotDisabilityInferenceRegression = Audit.traumaMemoryDoesNotCreateDisabilityInference

politicalLaneNotDisabilityEvidenceRegression :
  Audit.PoliticalCaseCreatesDisabilityEvidence → ⊥
politicalLaneNotDisabilityEvidenceRegression = Audit.politicalCaseDoesNotCreateDisabilityEvidence

amalekLaneNotDisabilityEvidenceRegression :
  Audit.AmalekAnalogyCreatesDisabilityEvidence → ⊥
amalekLaneNotDisabilityEvidenceRegression = Audit.amalekAnalogyDoesNotCreateDisabilityEvidence
