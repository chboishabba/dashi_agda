module DASHI.Biology.AutismVaccineCurrentSOTA2026Regression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Biology.AutismVaccineCurrentSOTA2026Exact as S

currentReviewUpdatesEvidenceWindowWithoutScopeCollapse :
  S.reviewExtendsThroughAugust2025 S.canonicalAutismVaccineCurrentSOTABoundary ≡ true
  × S.broaderVaccineASDNoCausalAssociationFindingReported S.canonicalAutismVaccineCurrentSOTABoundary ≡ true
  × S.broaderReviewAutomaticallyPaysExactHbombMMREstimand S.canonicalAutismVaccineCurrentSOTABoundary ≡ false
currentReviewUpdatesEvidenceWindowWithoutScopeCollapse = refl , (refl , refl)

currentInstitutionalReviewDoesNotCreateAuthorityOrUniversalZeroRisk :
  S.sourceCitationCreatesAuthority S.canonicalAutismVaccineCurrentSOTABoundary ≡ false
  × S.reviewCreatesUniversalZeroRiskTheorem S.canonicalAutismVaccineCurrentSOTABoundary ≡ false
currentInstitutionalReviewDoesNotCreateAuthorityOrUniversalZeroRisk = refl , refl
