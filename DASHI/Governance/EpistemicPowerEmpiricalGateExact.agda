module DASHI.Governance.EpistemicPowerEmpiricalGateExact where

-- K2/K3: Parametric empirical admissibility, NOT generated evidence.
-- The caller supplies independent validation predicates and witnesses.
-- No constructors for those externally interpreted predicates live here.
open import DASHI.Core.Prelude
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Education.DigitalESDSourceAuditHyperfabricExact as ESD

record EmpiricalValidators (Case : Set) : Set₁ where
  field
    originalSource : Case → Set
    burdenObserved : Case → Set
    fatigueIndependentlyObserved : Case → Set
    alternativeCausationExamined : Case → Set
    decisionAuthoritySource : Case → Set
    materialOutcomeSource : Case → Set
    participantConsentAndAccess : Case → Set

open EmpiricalValidators public

record AuditedCase {Case : Set}
  (validator : EmpiricalValidators Case)
  (caseId : Case) : Set where
  constructor audited-case
  field
    sourceReceipt : originalSource validator caseId
    workloadReceipt : burdenObserved validator caseId
    fatigueReceipt : fatigueIndependentlyObserved validator caseId
    causalReceipt : alternativeCausationExamined validator caseId
    authorityReceipt : decisionAuthoritySource validator caseId
    materialReceipt : materialOutcomeSource validator caseId
    ethicsReceipt : participantConsentAndAccess validator caseId

open AuditedCase public

-- These projections guarantee that a caller cannot access an admitted
-- case's particular empirical claim without providing its typed evidence.
auditedCaseRequiresIndependentFatigue :
  ∀ {Case : Set} {v : EmpiricalValidators Case} {c : Case} →
  AuditedCase v c → fatigueIndependentlyObserved v c
auditedCaseRequiresIndependentFatigue = fatigueReceipt

auditedCaseRequiresCausalAlternatives :
  ∀ {Case : Set} {v : EmpiricalValidators Case} {c : Case} →
  AuditedCase v c → alternativeCausationExamined v c
auditedCaseRequiresCausalAlternatives = causalReceipt

auditedCaseRequiresDecisionSource :
  ∀ {Case : Set} {v : EmpiricalValidators Case} {c : Case} →
  AuditedCase v c → decisionAuthoritySource v c
auditedCaseRequiresDecisionSource = authorityReceipt

auditedCaseRequiresMaterialSource :
  ∀ {Case : Set} {v : EmpiricalValidators Case} {c : Case} →
  AuditedCase v c → materialOutcomeSource v c
auditedCaseRequiresMaterialSource = materialReceipt

auditedCaseRequiresEthicalStanding :
  ∀ {Case : Set} {v : EmpiricalValidators Case} {c : Case} →
  AuditedCase v c → participantConsentAndAccess v c
auditedCaseRequiresEthicalStanding = ethicsReceipt

-- A deliberately incomplete synthetic case supplies all receipts except
-- independent fatigue. Its full admission is refutable, not fabricated.
data ExampleCase : Set where example : ExampleCase

exampleValidators : EmpiricalValidators ExampleCase
exampleValidators = record
  { originalSource = λ _ → ⊤
  ; burdenObserved = λ _ → ⊤
  ; fatigueIndependentlyObserved = λ _ → ⊥
  ; alternativeCausationExamined = λ _ → ⊤
  ; decisionAuthoritySource = λ _ → ⊤
  ; materialOutcomeSource = λ _ → ⊤
  ; participantConsentAndAccess = λ _ → ⊤
  }

missingFatigueBlocksCaseAdmission :
  AuditedCase exampleValidators example → ⊥
missingFatigueBlocksCaseAdmission caseReceipt =
  fatigueReceipt caseReceipt

-- Existing ESD data demonstrates that the *coarse visibility profile*
-- does not establish a full situated audit state. This does not establish
-- whether any historical ESD sample passes the new admission predicates.
esdScoreCannotReplaceSituatedCase :
  INF.FactorsThrough
    ESD.coarseVisibilityProfile ESD.fullAuditState → ⊥
esdScoreCannotReplaceSituatedCase =
  ESD.coarseVisibilityProfileCannotDetermineFullAuditState
