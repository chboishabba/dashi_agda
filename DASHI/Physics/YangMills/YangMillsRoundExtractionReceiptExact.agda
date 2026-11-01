{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsRoundExtractionReceiptExact where

open import Agda.Builtin.Bool using (Bool; true; false)

------------------------------------------------------------------------
-- Formal extraction/provenance firewall.
--
-- These booleans record the authority policy of the extraction tranche.  They
-- are not substitutes for the source mathematics and do not promote any Clay
-- theorem.  Historical negative/no-go results remain part of the receipt even
-- when a later positive route exists.
------------------------------------------------------------------------

roundsAuthoritativeByDefault : Bool
roundsAuthoritativeByDefault = false

extractionCreatesTheoremTruth : Bool
extractionCreatesTheoremTruth = false

supersessionCreatesTheoremTruth : Bool
supersessionCreatesTheoremTruth = false

statusCountsAreClayPayments : Bool
statusCountsAreClayPayments = false

sourceCitationCreatesAgdaProof : Bool
sourceCitationCreatesAgdaProof = false

executionReceiptCreatesAgdaProof : Bool
executionReceiptCreatesAgdaProof = false

negativeResultsPreserved : Bool
negativeResultsPreserved = true

roundFilesArchivedOrDeleted : Bool
roundFilesArchivedOrDeleted = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

clayPromotion : Bool
clayPromotion = false
