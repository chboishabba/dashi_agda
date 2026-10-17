module DASHI.Biology.BH4ExecutedSIFTSReceiptExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- Executed bounded PDBe/SIFTS acquisition receipt, 2026-10-17.
------------------------------------------------------------------------

executedProteinsRequested : Nat
executedProteinsRequested = 16

executedStructuresExamined : Nat
executedStructuresExamined = 38

executedMatchingSIFTSSegmentCount : Nat
executedMatchingSIFTSSegmentCount = 526

executedProteinsWithUniProtPDBLinks : Nat
executedProteinsWithUniProtPDBLinks = 14

executedProteinsWithMatchingSegments : Nat
executedProteinsWithMatchingSegments = 13

executedProteinsWithoutUniProtPDBLinks : Nat
executedProteinsWithoutUniProtPDBLinks = 2

executedProteinsWithoutMatchingSegments : Nat
executedProteinsWithoutMatchingSegments = 3

executedSIFTSErrorCount : Nat
executedSIFTSErrorCount = 0

record ExecutedSIFTSReceipt : Set where
  constructor executed-sifts-receipt
  field
    proteinsRequested : Nat
    structuresExamined : Nat
    matchingSIFTSSegmentCount : Nat
    proteinsWithUniProtPDBLinks : Nat
    proteinsWithMatchingSegments : Nat
    proteinsWithoutUniProtPDBLinks : Nat
    proteinsWithoutMatchingSegments : Nat
    errorCount : Nat
    proteinsWithoutPDBLinkIds : List String
    proteinsWithoutMatchingSegmentIds : List String
    boundedAcquisitionExecuted : Bool

open ExecutedSIFTSReceipt public

canonicalExecutedSIFTSReceipt : ExecutedSIFTSReceipt
canonicalExecutedSIFTSReceipt =
  executed-sifts-receipt
    executedProteinsRequested
    executedStructuresExamined
    executedMatchingSIFTSSegmentCount
    executedProteinsWithUniProtPDBLinks
    executedProteinsWithMatchingSegments
    executedProteinsWithoutUniProtPDBLinks
    executedProteinsWithoutMatchingSegments
    executedSIFTSErrorCount
    ("PCBD1:P61457" ∷ "AGMO:Q6ZNB7" ∷ [])
    ("PCBD1:P61457" ∷ "AGMO:Q6ZNB7" ∷ "PAH:P00439" ∷ [])
    true

structuresExaminedExact : structuresExamined canonicalExecutedSIFTSReceipt ≡ 38
structuresExaminedExact = refl

matchingSegmentsExact : matchingSIFTSSegmentCount canonicalExecutedSIFTSReceipt ≡ 526
matchingSegmentsExact = refl

record ExecutedSIFTSBoundary : Set where
  constructor executed-sifts-boundary
  field
    mappingCreatesCatalyticFunction : Bool
    mappingCreatesCatalyticFunctionIsFalse : mappingCreatesCatalyticFunction ≡ false
    mappingCreatesRegulatoryFunction : Bool
    mappingCreatesRegulatoryFunctionIsFalse : mappingCreatesRegulatoryFunction ≡ false
    missingBoundedMappingMeansProteinHasNoStructure : Bool
    missingBoundedMappingMeansProteinHasNoStructureIsFalse :
      missingBoundedMappingMeansProteinHasNoStructure ≡ false
    threePDBBoundedSampleMeansExhaustiveCoverage : Bool
    threePDBBoundedSampleMeansExhaustiveCoverageIsFalse :
      threePDBBoundedSampleMeansExhaustiveCoverage ≡ false
    structuralCoverageCreatesSameCellState : Bool
    structuralCoverageCreatesSameCellStateIsFalse : structuralCoverageCreatesSameCellState ≡ false

open ExecutedSIFTSBoundary public

canonicalExecutedSIFTSBoundary : ExecutedSIFTSBoundary
canonicalExecutedSIFTSBoundary =
  executed-sifts-boundary false refl false refl false refl false refl false refl

canonicalExecutedSIFTSGenericReceipt : Receipt.GenericReceipt
canonicalExecutedSIFTSGenericReceipt =
  Receipt.mkNonPromotingReceipt
    "executed bounded BH4 PDBe/SIFTS receipt"
    "DASHI.Biology.BH4ExecutedSIFTSReceiptExact"
    "16 proteins -> 38 examined PDB structures -> 526 exact UniProt/PDB SIFTS segment mappings; 14 proteins have panel PDB links and 13 have >=1 matching segment; zero acquisition errors"
    "closes generic bounded structural-mapping acquisition for the first-three-PDB sample and moves the live residual to residue/site functional adjudication"
    "mapping is not catalytic/regulatory function; a bounded no-match is not structural absence; first-three-PDB sampling is not exhaustive; structural coverage is not same-cell biochemical state"
    "python3 scripts/run_bh4_phase4_maxcut.py"
