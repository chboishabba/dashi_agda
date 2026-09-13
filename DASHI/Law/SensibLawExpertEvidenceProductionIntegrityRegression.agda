module DASHI.Law.SensibLawExpertEvidenceProductionIntegrityRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawExpertEvidenceProductionIntegrityExact as Expert

------------------------------------------------------------------------
-- RED contract for the generic expert-evidence production spine.
--
-- This regression deliberately requires the reusable owner before the
-- Australian family-report manifestation is introduced.
------------------------------------------------------------------------

data-inference-opinion-distinct :
  Expert.dataInferenceOpinionCollapsed Expert.canonicalExpertProductionBoundary
  ≡ false
data-inference-opinion-distinct = refl

expert-authority-does-not-promote-truth :
  Expert.expertStatusAutomaticallyTruthAuthority Expert.canonicalExpertProductionBoundary
  ≡ false
expert-authority-does-not-promote-truth = refl

admission-does-not-repair-method :
  Expert.reportAdmissionRepairsUpstreamIntegrity Expert.canonicalExpertProductionBoundary
  ≡ false
admission-does-not-repair-method = refl

cross-examination-does-not-add-missing-input :
  Expert.crossExaminationRetroactivelyAddsUnobservedInput Expert.canonicalExpertProductionBoundary
  ≡ false
cross-examination-does-not-add-missing-input = refl

disputed-risk-is-not-irrelevant-risk :
  Expert.disputedRiskAutomaticallyIrrelevant Expert.canonicalExpertProductionBoundary
  ≡ false
disputed-risk-is-not-irrelevant-risk = refl

insufficient-evidence-allows-abstention :
  Expert.insufficientEvidenceMayRequireAbstention Expert.canonicalExpertProductionBoundary
  ≡ true
insufficient-evidence-allows-abstention = refl

risk-query-has-exact-observer-defect : Expert.RiskQueryAdequacyDefect
risk-query-has-exact-observer-defect = Expert.riskQueryAdequacyDefect

risk-query-cannot-factor-through-erased-source :
  Expert.RiskQueryAdequate → ⊥
risk-query-cannot-factor-through-erased-source =
  Expert.riskQueryNotAdequate

closed-authority-bundle-is-non-promoting :
  Expert.expertProductionPromotesAnyAuthority ≡ false
closed-authority-bundle-is-non-promoting = refl
