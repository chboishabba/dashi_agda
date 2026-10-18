module DASHI.Culture.CohnInstitutionalResidualDiagnosisNegativeExact where

open import DASHI.Core.Prelude

import DASHI.Core.DiscriminatorSynthesisExact as Synthesis
import DASHI.Culture.CohnInstitutionalResidualDiagnosisExact as Diagnosis

provenanceBundleCannotSeparate :
  Synthesis.BundleSeparates
    Diagnosis.provenanceBundle
    Diagnosis.representedAcceptedWorld
    Diagnosis.originatingRefusedWorld → ⊥
provenanceBundleCannotSeparate separator =
  Synthesis.separates separator refl

permissionBundleCannotSeparate :
  Synthesis.BundleSeparates
    Diagnosis.permissionBundle
    Diagnosis.representedAcceptedWorld
    Diagnosis.originatingRefusedWorld → ⊥
permissionBundleCannotSeparate separator =
  Synthesis.separates separator refl

ignoranceProductionBundleCannotSeparate :
  Synthesis.BundleSeparates
    Diagnosis.ignoranceProductionBundle
    Diagnosis.representedAcceptedWorld
    Diagnosis.originatingRefusedWorld → ⊥
ignoranceProductionBundleCannotSeparate separator =
  Synthesis.separates separator refl

criticalUptakeBundleCannotSeparate :
  Synthesis.BundleSeparates
    Diagnosis.criticalUptakeBundle
    Diagnosis.representedAcceptedWorld
    Diagnosis.originatingRefusedWorld → ⊥
criticalUptakeBundleCannotSeparate separator =
  Synthesis.separates separator refl
