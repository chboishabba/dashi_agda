module DASHI.Wikimedia.MaboResidualDrivenWorldSessionValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Wikimedia.MaboResidualDrivenWorldSessionExact

_ : admissionIsStagedBeforeReentry canonicalWorldExpansionSessionBoundary ≡ true
_ = admissionIsStagedBeforeReentryTrue

_ : successfulReentryCommitsLedgerFrontierLineageTogether canonicalWorldExpansionSessionBoundary ≡ true
_ = successfulReentryCommitsTogetherTrue

_ : failedReentryMayAdvanceNovelObjectCount canonicalWorldExpansionSessionBoundary ≡ false
_ = failedReentryMayAdvanceNovelObjectCountFalse

_ : failedReentryMayAdvanceFrontier canonicalWorldExpansionSessionBoundary ≡ false
_ = failedReentryMayAdvanceFrontierFalse

_ : failedReentryMayPersistLineage canonicalWorldExpansionSessionBoundary ≡ false
_ = failedReentryMayPersistLineageFalse

_ : sessionCreatesSemanticAuthority canonicalWorldExpansionSessionBoundary ≡ false
_ = sessionCreatesSemanticAuthorityFalse

_ : sessionCreatesClaimTruth canonicalWorldExpansionSessionBoundary ≡ false
_ = sessionCreatesClaimTruthFalse
