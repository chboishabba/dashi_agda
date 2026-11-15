module DASHI.Biology.AutismTranscriptHighAlphaCrossPollinationRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Biology.AutismTranscriptHighAlphaCrossPollinationExact as X

normMediationRetained :
  X.normMediationRepresented X.canonicalHighAlphaBoundary ≡ true
normMediationRetained = refl

engagementOutcomeNoncollapseRetained :
  X.engagementMetricsCollapsedWithBeliefOrSharing X.canonicalHighAlphaBoundary ≡ false
engagementOutcomeNoncollapseRetained = refl

singlePronounDiagnosisBlocked :
  X.singlePronounDiagnosesDepression X.canonicalHighAlphaBoundary ≡ false
singlePronounDiagnosisBlocked = refl

languageModelClinicalAuthorityBlocked :
  X.languageModelCreatesClinicalDiagnosisAuthority X.canonicalHighAlphaBoundary ≡ false
languageModelClinicalAuthorityBlocked = refl

fmtPrimaryNullRetained :
  X.fmtPrimaryClinicalEndpointPaid X.canonicalHighAlphaBoundary ≡ false
fmtPrimaryNullRetained = refl

fmtDiagnosisRemovalBlocked :
  X.fmtRemovesAutismDiagnosis X.canonicalHighAlphaBoundary ≡ false
fmtDiagnosisRemovalBlocked = refl

opioidModulationNotTruthAuthority :
  X.muOpioidModulationDeterminesBeliefTruth X.canonicalHighAlphaBoundary ≡ false
opioidModulationNotTruthAuthority = refl

identitySupportCompatibilityRetained :
  X.identityAndSupportCanCoexist X.canonicalHighAlphaBoundary ≡ true
identitySupportCompatibilityRetained = refl

-- Attribution/source identity does not itself pay an outcome.  A completed
-- trial receipt must carry the family-specific source admission, while the
-- design-only protocol has a distinct admission family.
fmtTrialOutcomeSourceBound :
  X.AdmittedHighAlphaSource X.fmtTrialOutcome X.wan2024FMTSource
fmtTrialOutcomeSourceBound = X.wan2024PaysFMTTrialOutcome

fmtProtocolDesignSourceBound :
  X.AdmittedHighAlphaSource X.fmtProtocolDesignOutcome X.zou2026FMTProtocolSource
fmtProtocolDesignSourceBound = X.zou2026PaysFMTProtocolDesign

protocolCannotPayCompletedFMTOutcome :
  X.AdmittedHighAlphaSource X.fmtTrialOutcome X.zou2026FMTProtocolSource → ⊥
protocolCannotPayCompletedFMTOutcome ()
