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

-- The 2026-10-17 first SABIO attempt reached the documented endpoint but the
-- entry-ID GET returned an HTTP-200 browser SPA shell.  That result is a
-- protocol-shape failure, not evidence that SABIO contains zero entries.
firstSABIOAttemptStatus : SABIOProtocolStatus
firstSABIOAttemptStatus = browserShellPayload

firstSABIOAttemptMayConcludeZeroEntries : Bool
firstSABIOAttemptMayConcludeZeroEntries = false

-- The bounded PDBe/SIFTS acquisition did execute successfully against the
-- exact panel and recovered exact UniProt/PDB segment mappings.  The pasted
-- diagnostic contained inconsistent hand-summed headline/per-protein totals,
-- so the formal owner promotes execution/zero-fatal-error status only; schema
-- v2 now computes canonical totals directly from the artifact on rerun.
pdbeSiftsBoundedAcquisitionExecuted : Bool
pdbeSiftsBoundedAcquisitionExecuted = true

pdbeSiftsFatalErrorsReported : Nat
pdbeSiftsFatalErrorsReported = 0

pdbeSiftsCanonicalCoverageCountsRequireArtifactRecount : Bool
pdbeSiftsCanonicalCoverageCountsRequireArtifactRecount = true

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
    "SABIO-RK kinetic-law candidates + executed bounded PDBe/SIFTS UniProt/PDB structural mapping acquisition"
    "records the SABIO HTTP-200 SPA-shell failure as protocol failure rather than zero data, promotes successful bounded SIFTS acquisition execution, and keeps canonical coverage totals delegated to the machine-generated v2 artifact"
    "kinetic constants are not in-vivo flux bounds; HTML is not a no-entry receipt; structure/residue mapping is not catalytic mechanism; neither source creates disease causation"
    "python3 scripts/run_bh4_phase4_maxcut.py"
