module DASHI.Governance.OccupyFilesCorpusReceiptExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- MATERIALISED OCCUPYFILES CORPUS RECEIPT.
--
-- Provenance classes remain separate:
--   * user supplied origin points to UK Data Service ReShare SN 853247;
--   * Kinna/Prichard archive metadata and README describe curation/selection;
--   * the minute text is underlying Occupy archival material downloaded from
--     camp websites according to the corpus README;
--   * DASHI hashing, parsing, segmentation and coding are derived processing.
------------------------------------------------------------------------

record OccupyFilesCorpusReceipt : Set where
  constructor occupyFilesCorpusReceipt
  field
    suppliedOrigin : String
    localFilename : String
    packageBytes : Nat
    packageSha256 : String
    nonDirectoryMemberCount : Nat

    readmeMemberSha256 : String
    owsContainerMemberSha256 : String
    oaklandContainerMemberSha256 : String

    readmeReportedOWSGAMinuteSets : Nat
    readmeReportedLondonGAMinuteSets : Nat
    readmeReportedOaklandGAMinuteSets : Nat

    parserDetectedOWSRecords : Nat
    parserDetectedLondonFiles : Nat

open OccupyFilesCorpusReceipt public

canonicalOccupyFilesCorpusReceipt : OccupyFilesCorpusReceipt
canonicalOccupyFilesCorpusReceipt =
  occupyFilesCorpusReceipt
    "https://reshare.ukdataservice.ac.uk/853247/"
    "OccupyFiles.zip"
    1396637
    "b8a2e36ae46328dfec375ab3b3a859c45e5bf626d92d130db43855f19c8c75fb"
    49
    "086271fcad7cab14bb569099ffaf8c939cb24600947afdd8647566aae258196b"
    "d6b4eff1541b93a033d8de4021ae86a2e7f6aa2bfbaa7e58d04108140e400f00"
    "1dafbe698b0fcbd816d9b0f369ae709d1f9f4768bc2ac9fcf8face47aba7e2dd"
    45
    46
    44
    45
    46

record OccupyFilesCorpusBoundary : Set where
  constructor occupyFilesCorpusBoundary
  field
    reShareRecordIsUnderlyingMinuteAuthor : Bool
    curatorsAuthoredUnderlyingMinutes : Bool
    dashiParserAuthoredUnderlyingMinutes : Bool
    readmeCountsAreDashiMeasurements : Bool
    parserCountsRewriteCuratorMetadata : Bool
    readmeOaklandCountParserVerified : Bool

    packageMaterialisedAndHashed : Bool
    owsRecordCountParserVerified : Bool
    londonFileCountParserVerified : Bool

open OccupyFilesCorpusBoundary public

canonicalOccupyFilesCorpusBoundary : OccupyFilesCorpusBoundary
canonicalOccupyFilesCorpusBoundary =
  occupyFilesCorpusBoundary
    false
    false
    false
    false
    false
    false
    true
    true
    true

canonicalOccupyFilesCorpusReceiptProof : GenericReceipt.GenericReceipt
canonicalOccupyFilesCorpusReceiptProof =
  GenericReceipt.mkNonPromotingReceipt
    "materialised OccupyFiles corpus provenance receipt"
    "DASHI.Governance.OccupyFilesCorpusReceiptExact"
    "canonicalOccupyFilesCorpusBoundary"
    "pins the user-supplied UK Data Service origin, uploaded ZIP byte count and SHA-256, member count, selected internal member hashes, README-reported camp minute-set counts, and independently parser-detected OWS/London counts"
    "curation, underlying archival authorship and DASHI parsing remain distinct; the README's Oakland count remains curator-reported metadata until separately reproduced by a parser-level segmentation receipt"
    "agda -i . DASHI/Governance/OccupyFilesCorpusReceiptRegression.agda"
