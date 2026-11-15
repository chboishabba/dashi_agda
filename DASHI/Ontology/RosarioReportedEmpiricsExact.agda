module DASHI.Ontology.RosarioReportedEmpiricsExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Ontology.RosarioConceptualDiagnosticsExact

------------------------------------------------------------------------
-- SOURCE-REPORTED EMPIRICAL RECEIPTS
--
-- These values transcribe reported ACL 2025 benchmark statistics.  They are
-- not promoted to population parameters, universal LLM laws, Wikidata truth,
-- or independent DASHI empirical results.
------------------------------------------------------------------------

domainClusterCount : BenchmarkDomain → Nat
domainClusterCount academicDisciplines = 443
domainClusterCount dishes = 1220
domainClusterCount financeProducts = 725
domainClusterCount homeAppliances = 421
domainClusterCount medicalOccupations = 740
domainClusterCount musicGenres = 1990
domainClusterCount naturalDisasters = 357
domainClusterCount software = 249

domainQuestionsPerClusterHundredths : BenchmarkDomain → Nat
domainQuestionsPerClusterHundredths academicDisciplines = 420
domainQuestionsPerClusterHundredths dishes = 515
domainQuestionsPerClusterHundredths financeProducts = 457
domainQuestionsPerClusterHundredths homeAppliances = 567
domainQuestionsPerClusterHundredths medicalOccupations = 494
domainQuestionsPerClusterHundredths musicGenres = 609
domainQuestionsPerClusterHundredths naturalDisasters = 452
domainQuestionsPerClusterHundredths software = 449

reportedClusterTotal : Nat
reportedClusterTotal = 6145

reportedConsistentCorrectPercent : Nat
reportedConsistentCorrectPercent = 90

reportedInconsistentPercent : Nat
reportedInconsistentPercent = 10

reportedConsistentDisagreementPercent : Nat
reportedConsistentDisagreementPercent = 2

reportedFalsePositiveShareOfDisagreementPercent : Nat
reportedFalsePositiveShareOfDisagreementPercent = 15

record RosarioEmpiricalReceiptStatus : Set where
  constructor rosarioEmpiricalReceiptStatus
  field
    tableOneCountsTranscribed : Bool
    approximateRatesRemainSourceReports : Bool
    noUniversalPerformanceLawClaimed : Bool

    tableOneCountsTranscribedIsTrue : tableOneCountsTranscribed ≡ true
    approximateRatesRemainSourceReportsIsTrue :
      approximateRatesRemainSourceReports ≡ true
    noUniversalPerformanceLawClaimedIsTrue :
      noUniversalPerformanceLawClaimed ≡ true

open RosarioEmpiricalReceiptStatus public

canonicalRosarioEmpiricalReceiptStatus : RosarioEmpiricalReceiptStatus
canonicalRosarioEmpiricalReceiptStatus =
  rosarioEmpiricalReceiptStatus true true true refl refl refl
