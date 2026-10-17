module DASHI.Biology.BH4ExecutedSIFTSReceiptExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- Executed bounded PDBe/SIFTS acquisition receipt, 2026-10-17.
--
-- The live schema-v2 artifact machine-computed its own totals rather than
-- relying on manually summed console output:
--   16 proteins requested
--   38 structures examined (max three UniProt-linked PDBs per protein)
--   526 exact _pdbx_sifts_unp_segments rows matching the panel accession
--   14 proteins with UniProt PDB links
--   13 proteins with >=1 matching SIFTS segment
--   2 proteins without panel PDB links: PCBD1, AGMO
--   3 proteins without matching segments in this bounded run: PCBD1, AGMO, PAH
--   0 HTTP/parse errors
--
-- This receipt pays structural identity/mapping coverage only. It does not
-- identify a catalytic residue, regulatory site, perturbational effect or
-- same-cell biochemical state.
------------------------------------------------------------------------

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
    16
    38
    526
    14
    13
    2
    3
    0
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
