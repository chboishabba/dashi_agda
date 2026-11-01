module Ontology.DNA.PublishedChemistryAssayReceipts where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Published aggregate evidence.  These receipts preserve external authority;
-- they are not presented as an internal reanalysis of unavailable raw records.

record PublishedAggregateReceipt : Set where
  constructor publishedAggregate
  field
    citation : String
    doi : String
    sampleCount : Nat
    reportedPerfectRecovery : Bool
    reportedConstraintValidation : Bool
    authorityNote : String

santaLuciaUnifiedReceipt : PublishedAggregateReceipt
santaLuciaUnifiedReceipt = publishedAggregate
  "SantaLucia J Jr., PNAS 95:1460-1465 (1998)"
  "10.1073/pnas.95.4.1460"
  108
  false
  true
  "Unified nearest-neighbour parameters derived from 108 oligonucleotide duplexes; aggregate literature authority, not a DASHI assay replay."

allawiGTMismatchReceipt : PublishedAggregateReceipt
allawiGTMismatchReceipt = publishedAggregate
  "Allawi HT and SantaLucia J Jr., Biochemistry 36:10581-10594 (1997)"
  "10.1021/bi962590c"
  45
  false
  true
  "39 measured oligonucleotides plus six literature sequences support context-dependent G.T mismatch parameters."

dnaFountainReceipt : PublishedAggregateReceipt
dnaFountainReceipt = publishedAggregate
  "Erlich Y and Zielinski D, Science 355:950-954 (2017)"
  "10.1126/science.aaj2038"
  2146816
  true
  true
  "Reported perfect recovery of 2.14 million encoded bytes; this is an end-to-end storage receipt, not proof of the DASHI operational quotient."

dnaAeonReceipt : PublishedAggregateReceipt
dnaAeonReceipt = publishedAggregate
  "Welzel M et al., Nature Communications 14 (2023)"
  "10.1038/s41467-023-36297-3"
  1
  false
  true
  "Published in-vitro validation of GC, homopolymer, motif and error-correction machinery; sampleCount is a study-level receipt because raw strand rows are not vendored here."

record AssayRelativeQuotientWitness : Set₁ where
  field
    Feature : Set
    Outcome : Set
    DatasetRow : Set
    feature : DatasetRow → Feature
    outcome : DatasetRow → Outcome
    sameFeatureImpliesCloseOutcome : Set
    source : PublishedAggregateReceipt
    rawRowsVendored : Bool

record ExternalEvidenceBoundary : Set where
  field
    aggregateReceiptsPresent : Bool
    sequenceLevelSufficiencyReanalysed : Bool

externalEvidenceBoundary : ExternalEvidenceBoundary
externalEvidenceBoundary = record
  { aggregateReceiptsPresent = true
  ; sequenceLevelSufficiencyReanalysed = false
  }
