module DASHI.Wikimedia.MaboResidualDrivenWorldSessionExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.MaboResidualDrivenWorldExpansionStepExact
import DASHI.Wikimedia.MaboResidualDrivenWorldReentryExact

record WorldExpansionSessionBoundary : Set where
  constructor worldExpansionSessionBoundary
  field
    admissionIsStagedBeforeReentry : Bool
    successfulReentryCommitsLedgerFrontierLineageTogether : Bool
    failedReentryMayAdvanceNovelObjectCount : Bool
    failedReentryMayAdvanceFrontier : Bool
    failedReentryMayPersistLineage : Bool
    sessionCreatesSemanticAuthority : Bool
    sessionCreatesClaimTruth : Bool

open WorldExpansionSessionBoundary public

canonicalWorldExpansionSessionBoundary : WorldExpansionSessionBoundary
canonicalWorldExpansionSessionBoundary =
  worldExpansionSessionBoundary
    true
    true
    false
    false
    false
    false
    false

admissionIsStagedBeforeReentryTrue :
  admissionIsStagedBeforeReentry canonicalWorldExpansionSessionBoundary ≡ true
admissionIsStagedBeforeReentryTrue = refl

successfulReentryCommitsTogetherTrue :
  successfulReentryCommitsLedgerFrontierLineageTogether canonicalWorldExpansionSessionBoundary ≡ true
successfulReentryCommitsTogetherTrue = refl

failedReentryMayAdvanceNovelObjectCountFalse :
  failedReentryMayAdvanceNovelObjectCount canonicalWorldExpansionSessionBoundary ≡ false
failedReentryMayAdvanceNovelObjectCountFalse = refl

failedReentryMayAdvanceFrontierFalse :
  failedReentryMayAdvanceFrontier canonicalWorldExpansionSessionBoundary ≡ false
failedReentryMayAdvanceFrontierFalse = refl

failedReentryMayPersistLineageFalse :
  failedReentryMayPersistLineage canonicalWorldExpansionSessionBoundary ≡ false
failedReentryMayPersistLineageFalse = refl

sessionCreatesSemanticAuthorityFalse :
  sessionCreatesSemanticAuthority canonicalWorldExpansionSessionBoundary ≡ false
sessionCreatesSemanticAuthorityFalse = refl

sessionCreatesClaimTruthFalse :
  sessionCreatesClaimTruth canonicalWorldExpansionSessionBoundary ≡ false
sessionCreatesClaimTruthFalse = refl

data FailedReentryAdvancesNovelCount : Set where
data FailedReentryAdvancesFrontier : Set where
data FailedReentryPersistsLineage : Set where

failedReentryDoesNotAdvanceNovelCount : FailedReentryAdvancesNovelCount → ⊥
failedReentryDoesNotAdvanceNovelCount ()

failedReentryDoesNotAdvanceFrontier : FailedReentryAdvancesFrontier → ⊥
failedReentryDoesNotAdvanceFrontier ()

failedReentryDoesNotPersistLineage : FailedReentryPersistsLineage → ⊥
failedReentryDoesNotPersistLineage ()
