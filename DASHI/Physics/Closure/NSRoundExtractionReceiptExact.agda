{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSRoundExtractionReceiptExact where

------------------------------------------------------------------------
-- NAVIER--STOKES ROUND EXTRACTION AUTHORITY RECEIPT
--
-- Repository-native DASHI bookkeeping.  These values describe extraction and
-- authority policy; they do not prove any Navier--Stokes theorem.
--
-- Task-4 observed counts are the pre-status-pattern full-index evidence gate
-- reported from the 23,257-file local SQLite index.  They are preserved as an
-- audit baseline; the refined receipt must be regenerated after this branch is
-- re-indexed and the status-pattern rules / canonical owners are visible.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

roundsAuthoritativeByDefault : Bool
roundsAuthoritativeByDefault = false

extractionCreatesTheoremTruth : Bool
extractionCreatesTheoremTruth = false

statusCountsAreClayPayments : Bool
statusCountsAreClayPayments = false

negativeResultsPreserved : Bool
negativeResultsPreserved = true

unresolvedPackagesCountAsDischarged : Bool
unresolvedPackagesCountAsDischarged = false

roundFilesArchivedOrDeleted : Bool
roundFilesArchivedOrDeleted = false

clayPromotion : Bool
clayPromotion = false

task4ObservedPackageCount : Nat
task4ObservedPackageCount = 30885

task4ObservedUnresolvedPackageCount : Nat
task4ObservedUnresolvedPackageCount = 19312

task4ObservedStatusPatternCandidates : Nat
task4ObservedStatusPatternCandidates = 5508

task4ObservedTheoremLikeCandidates : Nat
task4ObservedTheoremLikeCandidates = 582

roundsAuthoritativeByDefaultIsFalse : roundsAuthoritativeByDefault ≡ false
roundsAuthoritativeByDefaultIsFalse = refl

extractionCreatesTheoremTruthIsFalse : extractionCreatesTheoremTruth ≡ false
extractionCreatesTheoremTruthIsFalse = refl

statusCountsAreClayPaymentsIsFalse : statusCountsAreClayPayments ≡ false
statusCountsAreClayPaymentsIsFalse = refl

negativeResultsPreservedIsTrue : negativeResultsPreserved ≡ true
negativeResultsPreservedIsTrue = refl

unresolvedPackagesCountAsDischargedIsFalse :
  unresolvedPackagesCountAsDischarged ≡ false
unresolvedPackagesCountAsDischargedIsFalse = refl

roundFilesArchivedOrDeletedIsFalse : roundFilesArchivedOrDeleted ≡ false
roundFilesArchivedOrDeletedIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
