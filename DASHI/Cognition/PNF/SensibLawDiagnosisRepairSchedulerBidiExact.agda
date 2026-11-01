module DASHI.Cognition.PNF.SensibLawDiagnosisRepairSchedulerBidiExact where

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.SensibLawPluralEpistemicRepairMethodologyBidiExact as Law
import DASHI.Core.DiagnosisFibreSalienceSchedulerBidiExact as Diagnosis
import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Outcome
import DASHI.Core.SequentialOutcomeBackpropagationBidiExact as Revision

------------------------------------------------------------------------
-- SENSIBLAW / LEGAL-REASONING REPAIR <-> DIAGNOSIS FIBRE
--
-- A legal/epistemic mismatch is not a one-bit 'case failed' state.  Keep live
-- whether the problem is evidence, framing/classification, rule applicability,
-- consumer/remedy scope, provenance, or authority; inspect the discriminating
-- coordinate rather than treating an adverse result as the opposite holding.
------------------------------------------------------------------------

sensibLawDiagnosisFibre : Diagnosis.DiagnosisFibre
sensibLawDiagnosisFibre Outcome.observationConflict = ⊤
sensibLawDiagnosisFibre Outcome.frameConflict = ⊤
sensibLawDiagnosisFibre Outcome.ruleConflict = ⊤
sensibLawDiagnosisFibre Outcome.consumerMismatch = ⊤
sensibLawDiagnosisFibre Outcome.provenanceConflict = ⊤
sensibLawDiagnosisFibre Outcome.authorityMismatch = ⊤
sensibLawDiagnosisFibre _ = ⊥

legalRevision : Outcome.OutcomeDiagnosis → Revision.RevisionAction
legalRevision Outcome.observationConflict = Revision.reacquireObservation
legalRevision Outcome.frameConflict = Revision.rechartRepresentation
legalRevision Outcome.premiseConflict = Revision.inspectPremise
legalRevision Outcome.ruleConflict = Revision.inspectRule
legalRevision Outcome.modelConflict = Revision.reviseModel
legalRevision Outcome.consumerMismatch = Revision.reformulateConsumer
legalRevision Outcome.provenanceConflict = Revision.acquireIndependentProvenance
legalRevision Outcome.authorityMismatch = Revision.seekAuthorityReceipt
legalRevision Outcome.insufficientResolution = Revision.reacquireObservation

ruleConflictRoutesToRuleInspection :
  legalRevision Outcome.ruleConflict ≡ Revision.inspectRule
ruleConflictRoutesToRuleInspection = refl

authorityMismatchRoutesToAuthorityReceipt :
  legalRevision Outcome.authorityMismatch ≡ Revision.seekAuthorityReceipt
authorityMismatchRoutesToAuthorityReceipt = refl

consumerMismatchRoutesToReformulation :
  legalRevision Outcome.consumerMismatch ≡ Revision.reformulateConsumer
consumerMismatchRoutesToReformulation = refl

lawRepairBoundary : Law.SensibLawPluralEpistemicRepairBoundary
lawRepairBoundary = Law.canonicalSensibLawPluralEpistemicRepairBoundary

data AdverseLegalResultIsOppositeHolding : Set where
data RuleFailureCreatesAuthority : Set where

adverseLegalResultIsNotOppositeHolding : AdverseLegalResultIsOppositeHolding → ⊥
adverseLegalResultIsNotOppositeHolding ()

ruleFailureDoesNotCreateAuthority : RuleFailureCreatesAuthority → ⊥
ruleFailureDoesNotCreateAuthority ()

record SensibLawDiagnosisSchedulerBoundary : Set where
  constructor sensiblaw-diagnosis-scheduler-boundary
  field
    legalMismatchMayHaveMultipleDiagnoses : Bool
    ruleConflictMayRequireRuleInspection : Bool
    authorityMismatchRequiresSeparateAuthorityReceipt : Bool
    consumerMismatchMayRequireReformulation : Bool
    adverseResultEqualsOppositeHolding : Bool

canonicalSensibLawDiagnosisSchedulerBoundary : SensibLawDiagnosisSchedulerBoundary
canonicalSensibLawDiagnosisSchedulerBoundary =
  sensiblaw-diagnosis-scheduler-boundary true true true true false
