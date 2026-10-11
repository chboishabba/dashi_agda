#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

EXPECTED = {
    "DASHI/Culture/PowersPlantationParadiseSourceAtlasExact.agda": [
        "powersBookSource",
        "mondelliReviewSource",
        "canonicalPowersSourceBoundary",
        "chapter3ColonialSocietyAtTheTheatrePages",
        "chapter6EscapeFromRealityPages",
        "chapter7FinalePages",
    ],
    "DASHI/Culture/PowersPlantationParadiseHistoricalClaimReceiptsExact.agda": [
        "colonialHierarchyClaimReceipt",
        "colonialSocietyAtTheTheatreClaimReceipt",
        "escapeFromRealityClaimReceipt",
        "finaleRevolutionClaimReceipt",
        "pageRangeDoesNotPromoteUninspectedPassage",
    ],
    "DASHI/Culture/ColonialPerformanceStatusNonfactorabilityExact.agda": [
        "performedRoleCannotRecoverSocialOccupancy",
        "performanceCannotRecoverEndorsement",
    ],
    "DASHI/Culture/HistoricalArchiveAbsenceNonfactorabilityExact.agda": [
        "absenceInArchiveCannotRecoverAbsenceInWorld",
        "archiveCompletenessRequiresWitness",
    ],
    "DASHI/Culture/ColonialTheatreAccessAdapterExact.agda": [
        "sameProductionCannotRecoverVenueAccess",
        "historyQualifiedTheatreAccess",
    ],
    "DASHI/Culture/PowersPlantationParadiseSynthesisExact.agda": [
        "paradiseObserverCannotRecoverMaterialAffordance",
        "recognitionCannotRecoverDistribution",
        "localExpansionDoesNotProveGlobalEmancipation",
        "sourceClaimDoesNotBecomeDASHITheorem",
        "historicalClaimBoundary",
    ],
    "DASHI/Culture/PowersPlantationParadiseValidation.agda": [
        "_paradise-material-gap-paid",
        "_performance-status-gap-paid",
        "_archive-absence-gap-paid",
    ],
}

errors = []
for rel, markers in EXPECTED.items():
    path = ROOT / rel
    if not path.exists():
        errors.append(f"missing file: {rel}")
        continue
    text = path.read_text(encoding="utf-8")
    for marker in markers:
        if marker not in text:
            errors.append(f"{rel}: missing marker {marker}")

rollup = ROOT / "DASHI/Culture/Everything.agda"
if not rollup.exists():
    errors.append("missing Culture/Everything.agda")
else:
    text = rollup.read_text(encoding="utf-8")
    for module in [
        "PowersPlantationParadiseSourceAtlasExact",
        "PowersPlantationParadiseHistoricalClaimReceiptsExact",
        "ColonialPerformanceStatusNonfactorabilityExact",
        "HistoricalArchiveAbsenceNonfactorabilityExact",
        "ColonialTheatreAccessAdapterExact",
        "PowersPlantationParadiseSynthesisExact",
        "PowersPlantationParadiseValidation",
    ]:
        if module not in text:
            errors.append(f"Culture/Everything.agda missing import {module}")

workflow = ROOT / ".github/workflows/plantation-paradise-agda.yml"
if not workflow.exists():
    errors.append("missing focused Plantation-to-Paradise Agda workflow")

if errors:
    raise SystemExit("\n".join(errors))

print("Plantation to Paradise max-cut static contract: OK")
