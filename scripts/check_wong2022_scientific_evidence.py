#!/usr/bin/env python3
"""Focused, fail-closed Wong 2022 source/formalisation integrity audit.

This checks exact source/code invariants and optionally invokes Agda.
A successful static audit is NOT kernel acceptance, experimental validation,
an authenticated source data binary, or proof of a metabolic mechanism.

Original experimental authors: Wong, Lim, Tan, Go, Bell, Freemont, Yew.
Nature Communications 13:712 (2022), DOI 10.1038/s41467-022-28386-6.
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
from pathlib import Path
from typing import Mapping

ROOT = Path(__file__).resolve().parents[1]
CORE = "DASHI/Biology/Wong2022LysergicAcidFiniteCore.agda"
SOURCE = "DASHI/Biology/Wong2022LysergicAcidEvidenceExact.agda"
LEDGER = "DASHI/Biology/Wong2022EvidenceLedgerExact.agda"
SCIENTIFIC = "DASHI/Biology/Wong2022ScientificMetabolicBridgeExact.agda"
AGGREGATE = "DASHI/Biology/Everything.agda"
DOC = "docs/biology/Wong2022LysergicAcidEvidenceCrosswalk.md"
BYTES = "scripts/audit_wong2022_source_bytes.py"
BYTE_TEST = "tests/test_wong2022_source_bytes.py"
PATHS = (CORE, SOURCE, LEDGER, SCIENTIFIC, AGGREGATE, DOC, BYTES, BYTE_TEST)
AGDA_PATHS = (CORE, SOURCE, LEDGER, SCIENTIFIC, AGGREGATE)

MARKERS: dict[str, tuple[str, ...]] = {
    CORE: (
        "{-# OPTIONS --safe #-}",
        "data EvidenceReviewTier",
        "authorReportCannotCertifyIndependentValidation",
        "sourceDataReviewCannotCertifyIndependentValidation",
        "registryTagCannotCertifyAssaySample",
        "assaySampleTagCannotCertifyReceptorIdentity",
        "experimentNotAuthorProjection",
    ),
    SOURCE: (
        "10.1038/s41467-022-28386-6",
        "import DASHI.Biology.Wong2022LysergicAcidFiniteCore as Core",
        "Kluver.lsdIdentity",
        "Monoamine.tryptophan",
        "PubChem Compound CID 6717",
        '"1.7"',
        '"1.4"',
        "Chemistry.ChemistryTransitionKernel",
        "Metabolic.OpenMetabolicNetwork",
        "wongCitationImportsNoProof = refl",
    ),
    LEDGER: (
        "Wong.oneLitreEndpoint",
        "Wong.fourLitreEndpoint",
        "supplementaryTableTwelve",
        "supplementaryDataNotInspected",
        "reportedUnit",
        "replicateCountReportedInFigureCaption",
        '"CHEBI:6604"',
        "rawMeasurementTableReviewedIsFalse",
    ),
    SCIENTIFIC: (
        "import DASHI.Core.ScientificMechanismEvidenceBidiExact as Science",
        "import DASHI.Biology.Cell.MetabolicStoichiometricConservation as Stoich",
        "Science.scientific-mechanism-receipt",
        "Science.experimentalObservation",
        "Science.sourceInterpretation",
        "Science.independentReplicationReceipt",
        "Stoich.certifyMetabolicStoichiometry bridge",
        "currentUnpaidEmpiricalTransport",
    ),
    AGGREGATE: (
        "import DASHI.Biology.Wong2022LysergicAcidEvidenceExact",
        "import DASHI.Biology.Wong2022EvidenceLedgerExact",
        "import DASHI.Biology.Wong2022ScientificMetabolicBridgeExact",
    ),
    DOC: (
        "W22-01",
        "W22-07",
        "10.1038/s41467-022-28386-6",
    ),
    BYTES: (
        "def file_digest_receipt(",
        "publisher_file_identity_authenticated",
        "independent_experiment_verification",
        "source_data_xlsx",
        "supplementary_pdf",
    ),
    BYTE_TEST: (
        "test_local_workbook_digest_is_not_publisher_authentication",
        "test_missing_workbook_structure_fails_closed",
        "test_bad_expected_hash_rejected",
    ),
}

# These forbidden escape hatches are checked only in newly added Agda owners.
UNTRUSTED_AGDA = (
    re.compile(r"^\s*postulate\b", re.MULTILINE),
    re.compile(r"\{\-#\s*(?:NON_TERMINATING|TERMINATING)\b"),
    re.compile(r"\{\![\s\S]*?\!\}"),
    re.compile(r"--allow-unsolved-metas|--type-in-type|--no-positivity-check"),
)


def inspect_source_bundle(contents: Mapping[str, str]) -> list[str]:
    """Report static contract failures; never return a kernel or data proof."""
    failures: list[str] = []
    for path in PATHS:
        source = contents.get(path)
        if source is None:
            failures.append(f"missing file: {path}")
            continue
        for marker in MARKERS[path]:
            if marker not in source:
                failures.append(f"missing marker in {path}: {marker}")
        if path in (CORE, SOURCE, LEDGER, SCIENTIFIC):
            for pattern in UNTRUSTED_AGDA:
                if pattern.search(source):
                    failures.append(f"trust escape/hole in {path}: {pattern.pattern}")
    if CORE in contents and not contents[CORE].startswith("{-# OPTIONS --safe #-}"):
        failures.append("Golden core must start with safe option")
    if SOURCE in contents and contents[SOURCE].startswith("{-# OPTIONS --safe #-}"):
        failures.append("legacy source adapter is not asserted Golden safe")
    if LEDGER in contents:
        ledger = contents[LEDGER]
        for symbol in ("oneLitreIndexed", "fourLitreIndexed"):
            if symbol not in ledger:
                failures.append(f"missing reported endpoint: {symbol}")
        if "originalWorkbookDigestVerifiedIsFalse" not in ledger:
            failures.append("source workbook verification must remain explicit")
    if SCIENTIFIC in contents:
        scientific = contents[SCIENTIFIC]
        if "sameCompartmentAndTimePaidIsFalse" not in scientific:
            failures.append("missing same-context transport firewall")
        if "physicalFluxUnitsPaidIsFalse" not in scientific:
            failures.append("missing physical flux unit firewall")
    for path in (CORE, SOURCE, LEDGER, SCIENTIFIC):
        if path in contents and re.search(r"^\s*import\s+DASHI\.Wikimedia\.SensibLaw", contents[path], re.M):
            failures.append(f"deferred SLR/SensibLaw import in {path}")
    return failures


def load_source_bundle(root: Path = ROOT) -> dict[str, str]:
    return {
        path: (root / path).read_text(encoding="utf-8")
        for path in PATHS
        if (root / path).is_file()
    }


def check_agda(root: Path, *, required: bool) -> dict:
    executable = shutil.which("agda")
    if executable is None:
        return {
            "state": "unavailable",
            "success": False,
            "details": "Agda executable not installed on this runner",
            "required": required,
        }
    checks = []
    for path in AGDA_PATHS:
        command = [executable, "-i", ".", path]
        try:
            run = subprocess.run(
                command, cwd=root, capture_output=True, text=True, timeout=240
            )
            checks.append({
                "file": path,
                "passed": run.returncode == 0,
                "returncode": run.returncode,
                "output_tail": (run.stdout + "\n" + run.stderr)[-1500:],
            })
            if run.returncode != 0:
                break
        except subprocess.TimeoutExpired:
            checks.append({"file": path, "passed": False, "error": "timeout"})
            break
    return {
        "state": "executed",
        "success": len(checks) == len(AGDA_PATHS) and all(
            row["passed"] for row in checks
        ),
        "checks": checks,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--agda",
        action="store_true",
        help="Run focused Agda checks (fails if checker absent)",
    )
    args = parser.parse_args()
    failures = inspect_source_bundle(load_source_bundle(ROOT))
    receipt: dict = {
        "schema_version": "dashi.wong2022.source-integrity.v1",
        "scope": "DASHI-only; static checks are not kernel verification",
        "source_doi": "10.1038/s41467-022-28386-6",
        "static_passed": not failures,
        "failures": failures,
        "external_experiment_independently_reanalysed": False,
        "supplementary_file_sha256_verified": False,
        "same_object_flux_bridge_paid": False,
        "agda": {"state": "not_requested", "success": False},
    }
    if args.agda and not failures:
        receipt["agda"] = check_agda(ROOT, required=True)
    print(json.dumps(receipt, sort_keys=True, indent=2))
    return 0 if not failures and (not args.agda or receipt["agda"]["success"]) else 1


if __name__ == "__main__":
    raise SystemExit(main())
