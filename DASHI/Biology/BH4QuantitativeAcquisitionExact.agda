module DASHI.Biology.BH4QuantitativeAcquisitionExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- Public quantitative/structural acquisition lanes for Phase 4.
--
-- SABIO-RK is used as a candidate source for curated biochemical kinetic-law
-- parameters. PDBe/SIFTS is used for UniProt<->PDB sequence/residue mappings.
-- Neither source is permitted to manufacture in-vivo flux, same-compartment
-- state, catalytic mechanism, or disease causation.
------------------------------------------------------------------------

data QuantitativeExternalSource : Set where
  SABIO-RK : QuantitativeExternalSource
  PDBe : QuantitativeExternalSource
  SIFTS : QuantitativeExternalSource

data QuantitativeEvidenceKind : Set where
  kineticLawEntry : QuantitativeEvidenceKind
  kineticParameter : QuantitativeEvidenceKind
  structureMapping : QuantitativeEvidenceKind
  residueMapping : QuantitativeEvidenceKind

record QuantitativeAcquisitionBoundary : Set where
  constructor quantitative-acquisition-boundary
  field
    kineticConstantCreatesFluxBound : Bool
    kineticConstantCreatesFluxBoundIsFalse : kineticConstantCreatesFluxBound ≡ false
    inVitroKineticsCreatesInVivoState : Bool
    inVitroKineticsCreatesInVivoStateIsFalse : inVitroKineticsCreatesInVivoState ≡ false
    structureMappingCreatesCatalyticMechanism : Bool
    structureMappingCreatesCatalyticMechanismIsFalse :
      structureMappingCreatesCatalyticMechanism ≡ false
    residueMappingCreatesFunctionalPerturbation : Bool
    residueMappingCreatesFunctionalPerturbationIsFalse :
      residueMappingCreatesFunctionalPerturbation ≡ false
    sourceSpecificEvidenceRequired : Bool
    sourceSpecificEvidenceRequiredIsTrue : sourceSpecificEvidenceRequired ≡ true

open QuantitativeAcquisitionBoundary public

canonicalQuantitativeAcquisitionBoundary : QuantitativeAcquisitionBoundary
canonicalQuantitativeAcquisitionBoundary =
  quantitative-acquisition-boundary false refl false refl false refl false refl true refl

canonicalBH4QuantitativeAcquisitionReceipt : Receipt.GenericReceipt
canonicalBH4QuantitativeAcquisitionReceipt =
  Receipt.mkNonPromotingReceipt
    "BH4 Phase-4 quantitative acquisition"
    "DASHI.Biology.BH4QuantitativeAcquisitionExact"
    "SABIO-RK kinetic-law candidates + PDBe/SIFTS UniProt/PDB structural mappings"
    "adds reproducible public evidence acquisition for kinetic and structural coordinates while preserving source/same-object/compartment boundaries"
    "kinetic constants are not in-vivo flux bounds; structure/residue mapping is not catalytic mechanism; neither source creates disease causation"
    "python3 scripts/acquire_bh4_sabio_kinetics.py --help && python3 scripts/acquire_bh4_pdbe_sifts.py --help"
