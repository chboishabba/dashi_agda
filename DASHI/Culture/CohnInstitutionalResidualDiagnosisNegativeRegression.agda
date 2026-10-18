module DASHI.Culture.CohnInstitutionalResidualDiagnosisNegativeRegression where

open import DASHI.Core.Prelude

import DASHI.Core.DiscriminatorSynthesisExact as Synthesis
import DASHI.Culture.CohnInstitutionalResidualDiagnosisExact as Diagnosis
import DASHI.Culture.CohnInstitutionalResidualDiagnosisNegativeExact as Negative

provenanceReallyCannotSeparate :
  Synthesis.BundleSeparates
    Diagnosis.provenanceBundle
    Diagnosis.representedAcceptedWorld
    Diagnosis.originatingRefusedWorld → ⊥
provenanceReallyCannotSeparate = Negative.provenanceBundleCannotSeparate

permissionReallyCannotSeparate :
  Synthesis.BundleSeparates
    Diagnosis.permissionBundle
    Diagnosis.representedAcceptedWorld
    Diagnosis.originatingRefusedWorld → ⊥
permissionReallyCannotSeparate = Negative.permissionBundleCannotSeparate

ignoranceProductionReallyCannotSeparate :
  Synthesis.BundleSeparates
    Diagnosis.ignoranceProductionBundle
    Diagnosis.representedAcceptedWorld
    Diagnosis.originatingRefusedWorld → ⊥
ignoranceProductionReallyCannotSeparate = Negative.ignoranceProductionBundleCannotSeparate

criticalUptakeReallyCannotSeparate :
  Synthesis.BundleSeparates
    Diagnosis.criticalUptakeBundle
    Diagnosis.representedAcceptedWorld
    Diagnosis.originatingRefusedWorld → ⊥
criticalUptakeReallyCannotSeparate = Negative.criticalUptakeBundleCannotSeparate
