module DASHI.Culture.CohnInstitutionalResidualDiagnosisRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Culture.CohnInstitutionalResidualDiagnosisExact as Diagnosis

subjectPositionCandidateSeparates :
  Diagnosis.subjectPositionSeparates ≡ true
subjectPositionCandidateSeparates = refl

provenanceCandidateDoesNotSeparate :
  Diagnosis.provenanceSeparates ≡ false
provenanceCandidateDoesNotSeparate = refl

permissionCandidateDoesNotSeparate :
  Diagnosis.permissionSeparates ≡ false
permissionCandidateDoesNotSeparate = refl

ignoranceProductionCandidateDoesNotSeparate :
  Diagnosis.ignoranceProductionSeparates ≡ false
ignoranceProductionCandidateDoesNotSeparate = refl

hermeneuticalRefusalCandidateSeparates :
  Diagnosis.hermeneuticalRefusalSeparates ≡ true
hermeneuticalRefusalCandidateSeparates = refl

criticalUptakeCandidateDoesNotSeparate :
  Diagnosis.criticalUptakeSeparates ≡ false
criticalUptakeCandidateDoesNotSeparate = refl

leastDeclaredSeparatorIsHermeneuticalRefusal :
  Diagnosis.selectedResidualIsHermeneuticalRefusal ≡ true
leastDeclaredSeparatorIsHermeneuticalRefusal = refl

sourceLabelDoesNotAutoSelectResidual :
  Diagnosis.sourceLabelAutomaticallySelectsRepair ≡ false
sourceLabelDoesNotAutoSelectResidual = refl

fixtureProvesInstitutionalBadFaith :
  Diagnosis.syntheticFixtureProvesRealInstitutionalBadFaith ≡ false
fixtureProvesInstitutionalBadFaith = refl

existingGenericGrammarReused :
  Diagnosis.genericRepairGrammarReused ≡ true
existingGenericGrammarReused = refl
