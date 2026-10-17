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

data SABIOProtocolStatus : Set where
  protocolPayload : SABIOProtocolStatus
  browserShellPayload : SABIOProtocolStatus
  protocolError : SABIOProtocolStatus
  migratedExportAPI : SABIOProtocolStatus

-- Historical first attempt: the retired sabioRestWebServices surface rewrote
-- requests to the browser SPA/404 shell. This was correctly treated as a
-- protocol-shape failure rather than evidence of zero kinetic entries.
firstSABIOAttemptStatus : SABIOProtocolStatus
firstSABIOAttemptStatus = browserShellPayload

firstSABIOAttemptMayConcludeZeroEntries : Bool
firstSABIOAttemptMayConcludeZeroEntries = false

-- Current adapter targets the 2026 export API:
-- https://sabio.h-its.org/export-api/sabio/kinlaw-entry/json
currentSABIOProtocolStatus : SABIOProtocolStatus
currentSABIOProtocolStatus = migratedExportAPI

sabioExportEnvelopeRequired : Bool
sabioExportEnvelopeRequired = true

-- Bounded PDBe/SIFTS acquisition is now machine-recounted and promoted by the
-- dedicated BH4ExecutedSIFTSReceiptExact owner: 38 structures / 526 segments.
pdbeSiftsBoundedAcquisitionExecuted : Bool
pdbeSiftsBoundedAcquisitionExecuted = true

pdbeSiftsFatalErrorsReported : Nat
pdbeSiftsFatalErrorsReported = 0

pdbeSiftsCanonicalCoverageCountsRequireArtifactRecount : Bool
pdbeSiftsCanonicalCoverageCountsRequireArtifactRecount = false

record QuantitativeAcquisitionBoundary : Set where
  constructor quantitative-acquisition-boundary
  field
    kineticConstantCreatesFluxBound : Bool
    kineticConstantCreatesFluxBoundIsFalse : kineticConstantCreatesFluxBound ≡ false
    inVitroKineticsCreatesInVivoState : Bool
    inVitroKineticsCreatesInVivoStateIsFalse : inVitroKineticsCreatesInVivoState ≡ false
    htmlShellCreatesNoEntryConclusion : Bool
    htmlShellCreatesNoEntryConclusionIsFalse : htmlShellCreatesNoEntryConclusion ≡ false
    structureMappingCreatesCatalyticMechanism : Bool
    structureMappingCreatesCatalyticMechanismIsFalse :
      structureMappingCreatesCatalyticMechanism ≡ false
    residueMappingCreatesFunctionalPerturbation : Bool
    residueMappingCreatesFunctionalPerturbationIsFalse :
      residueMappingCreatesFunctionalPerturbation ≡ false
    boundedSIFTSAcquisitionCreatesSiteFunction : Bool
    boundedSIFTSAcquisitionCreatesSiteFunctionIsFalse :
      boundedSIFTSAcquisitionCreatesSiteFunction ≡ false
    sourceSpecificEvidenceRequired : Bool
    sourceSpecificEvidenceRequiredIsTrue : sourceSpecificEvidenceRequired ≡ true

open QuantitativeAcquisitionBoundary public

canonicalQuantitativeAcquisitionBoundary : QuantitativeAcquisitionBoundary
canonicalQuantitativeAcquisitionBoundary =
  quantitative-acquisition-boundary
    false refl false refl false refl false refl false refl false refl true refl

canonicalBH4QuantitativeAcquisitionReceipt : Receipt.GenericReceipt
canonicalBH4QuantitativeAcquisitionReceipt =
  Receipt.mkNonPromotingReceipt
    "BH4 Phase-4 quantitative acquisition"
    "DASHI.Biology.BH4QuantitativeAcquisitionExact"
    "SABIO-RK export-API kinetic candidates + executed bounded PDBe/SIFTS UniProt/PDB structural mappings"
    "records the retired REST/SPA failure as protocol failure, promotes migration to the validated meta+data export envelope, and delegates canonical SIFTS coverage totals to BH4ExecutedSIFTSReceiptExact"
    "kinetic constants are not in-vivo flux bounds; HTML is not a no-entry receipt; structure/residue mapping is not catalytic mechanism; neither source creates disease causation"
    "python3 scripts/run_bh4_phase4_maxcut.py"
