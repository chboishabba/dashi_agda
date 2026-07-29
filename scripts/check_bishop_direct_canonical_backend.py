#!/usr/bin/env python3
"""
Independent audit: Murray--Bishop direct-canonical backend.

This is a structural and exact-arithmetic audit, not an Agda typecheck.
It verifies:

1. the superproject gitlink and checked-out submodule both name the patched
   Bishop compatibility commit;
2. the pinned upstream base and local compatibility commit remain explicitly
   distinguished;
3. the Agda 2.9 wrapper copies and includes vendor/bishop;
4. all proof-critical backend modules are present;
5. s = 11/4 and its decay arithmetic are exact;
6. the quarter/thirty-second recurrences and 128/93 mass are exact;
7. the Stage-3 ledger remains fail-closed at the literal NS coefficient bridge
   and does not reintroduce global exp/log as an output-relocation dependency.
"""

from __future__ import annotations

import subprocess
import sys
from fractions import Fraction
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
BISHOP_PATH = REPO_ROOT / "vendor/bishop"

UPSTREAM_BASE = "582c6afcdf805d06730c8c0aa970f4a6e033b611"
PATCHED_GITLINK = "d6b24f905ec6596c2a63a1dcdfe4dda4ffe4a6a2"


def fail(message: str) -> bool:
    print(f"  FAIL: {message}")
    return False


def run_git(*args: str, cwd: Path = REPO_ROOT) -> str:
    result = subprocess.run(
        ["git", *args],
        cwd=cwd,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(result.stderr.strip() or "git command failed")
    return result.stdout.strip()


def check_gitlink() -> bool:
    print("[1/7] Checking patched vendor/bishop gitlink...")
    try:
        index_line = run_git("ls-files", "-s", "vendor/bishop")
    except RuntimeError as error:
        return fail(str(error))

    fields = index_line.split()
    if len(fields) < 4 or fields[0] != "160000":
        return fail(f"vendor/bishop is not a gitlink: {index_line!r}")
    index_commit = fields[1]
    if index_commit != PATCHED_GITLINK:
        return fail(
            f"superproject expects {PATCHED_GITLINK}, got {index_commit}"
        )

    if not BISHOP_PATH.is_dir():
        return fail("vendor/bishop is not initialized")
    try:
        checkout_commit = run_git("rev-parse", "HEAD", cwd=BISHOP_PATH)
    except RuntimeError as error:
        return fail(str(error))
    if checkout_commit != PATCHED_GITLINK:
        return fail(
            f"checked-out submodule is {checkout_commit}, expected {PATCHED_GITLINK}"
        )

    print(f"  OK: superproject and checkout use {PATCHED_GITLINK}")
    return True


def check_source_provenance() -> bool:
    print("[2/7] Checking upstream-base/local-patch provenance...")
    scope = (
        REPO_ROOT
        / "DASHI/Physics/Closure/NSTriadKNMurrayBishopBackendScopeAudit.agda"
    )
    if not scope.is_file():
        return fail(f"missing {scope.relative_to(REPO_ROOT)}")
    text = scope.read_text(encoding="utf-8")
    if UPSTREAM_BASE not in text:
        return fail("scope audit no longer records the upstream Bishop base")

    try:
        parent = run_git("rev-parse", f"{PATCHED_GITLINK}^", cwd=BISHOP_PATH)
    except RuntimeError as error:
        return fail(str(error))
    if parent != UPSTREAM_BASE:
        return fail(
            f"compatibility commit parent is {parent}, expected upstream {UPSTREAM_BASE}"
        )

    print("  OK: patched commit is a direct child of the recorded upstream base")
    return True


def check_wiring() -> bool:
    print("[3/7] Checking Agda wrapper source-root wiring...")
    wrapper = REPO_ROOT / "scripts/run_agda29_parallel_check.sh"
    if not wrapper.is_file():
        return fail("scripts/run_agda29_parallel_check.sh is missing")
    content = wrapper.read_text(encoding="utf-8")

    required_fragments = (
        "rsync -a --delete --prune-empty-dirs",
        "--include='*.agda'",
        "-i vendor/bishop",
    )
    missing = [fragment for fragment in required_fragments if fragment not in content]
    if missing:
        return fail(f"wrapper is missing required wiring: {missing}")

    print("  OK: shadow copy includes Agda sources and Agda receives -i vendor/bishop")
    return True


def check_modules() -> bool:
    print("[4/7] Checking proof-critical module inventory...")
    required = (
        "DASHI/Analysis/SetoidConstructiveRealSpine.agda",
        "DASHI/Analysis/MurrayBishopSetoidBackend.agda",
        "DASHI/Physics/Closure/NSTriadKNSetoidDirectCanonicalEnvelopeClosure.agda",
        "DASHI/Physics/Closure/NSTriadKNMurrayBishopDirectCanonicalCarrier.agda",
        "DASHI/Physics/Closure/NSTriadKNMurrayBishopCanonicalDyadicAnchors.agda",
        "DASHI/Physics/Closure/NSTriadKNMurrayBishopSobolevElevenFourths.agda",
        "DASHI/Physics/Closure/NSTriadKNMurrayBishopBackendScopeAudit.agda",
        "DASHI/Physics/Closure/NSTriadKNStage3MurrayBishopConcreteBackendIntegration.agda",
    )
    missing = [path for path in required if not (REPO_ROOT / path).is_file()]
    if missing:
        return fail(f"missing modules: {missing}")
    print(f"  OK: all {len(required)} backend modules are present")
    return True


def check_exact_arithmetic() -> bool:
    print("[5/7] Verifying s = 11/4 and exact decay arithmetic...")
    s = Fraction(11, 4)
    five_halves = Fraction(5, 2)
    assert five_halves < s < 3
    assert 2 * s - five_halves == 3
    assert 2 * s == Fraction(11, 2)
    print("  OK: 5/2 < 11/4 < 3, low decay = 3, gap decay = 11/2")
    return True


def check_dyadic_envelope() -> bool:
    print("[6/7] Verifying dyadic recurrences and 128/93 mass...")
    quarter = Fraction(1, 4)
    thirty_second = Fraction(1, 32)

    low = [quarter**index for index in range(12)]
    gap = [thirty_second**index for index in range(12)]
    assert low[0] == gap[0] == 1
    assert all(low[index + 1] == quarter * low[index] for index in range(11))
    assert all(
        gap[index + 1] == thirty_second * gap[index] for index in range(11)
    )

    assert Fraction(1, 1 - quarter) == Fraction(4, 3)
    assert Fraction(1, 1 - thirty_second) == Fraction(32, 31)
    assert Fraction(4, 3) * Fraction(32, 31) == Fraction(128, 93)
    print("  OK: exact anchor recurrences and canonical mass agree")
    return True


def require_assignments(text: str, required: dict[str, str]) -> list[str]:
    missing: list[str] = []
    for name, value in required.items():
        declaration = f"{name} = {value}"
        if declaration not in text:
            missing.append(declaration)
    return missing


def check_fail_closed_statuses() -> bool:
    print("[7/7] Auditing Stage-3 fail-closed statuses...")
    integration = (
        REPO_ROOT
        / "DASHI/Physics/Closure/"
        "NSTriadKNStage3MurrayBishopConcreteBackendIntegration.agda"
    )
    scope = (
        REPO_ROOT
        / "DASHI/Physics/Closure/NSTriadKNMurrayBishopBackendScopeAudit.agda"
    )
    if not integration.is_file() or not scope.is_file():
        return fail("backend integration or scope audit is missing")

    integration_text = integration.read_text(encoding="utf-8")
    scope_text = scope.read_text(encoding="utf-8")

    integration_required = {
        "outputRelocationGenericBackendComplete": "true",
        "outputRelocationConcreteSobolevChoiceComplete": "true",
        "outputRelocationGlobalExpLogDependencyRetired": "true",
        "outputRelocationLiteralPhysicalCoefficientBridgeComplete": "false",
    }
    scope_required = {
        "arbitraryLiteralQuotientSequenceCompletenessClaimed": "false",
        "setoidCompletenessAvoidsRepresentativeChoice": "true",
        "globalRealExpLogPackageInhabited": "false",
        "globalRealExpLogRequiredForThisArchetype": "false",
        "exactCanonicalDyadicAnchorsInhabited": "true",
        "concreteSobolevElevenFourthsInhabited": "true",
        "setoidDirectCanonical128Over93Closed": "true",
        "literalNavierStokesDirectCanonicalCoefficientBridgeClosed": "false",
    }

    missing = require_assignments(integration_text, integration_required)
    missing.extend(require_assignments(scope_text, scope_required))
    if missing:
        return fail(f"missing or changed status assignments: {missing}")

    forbidden_promotions = (
        "outputRelocationLiteralPhysicalCoefficientBridgeComplete = true",
        "literalNavierStokesDirectCanonicalCoefficientBridgeClosed = true",
        "arbitraryLiteralQuotientSequenceCompletenessClaimed = true",
        "globalRealExpLogPackageInhabited = true",
    )
    present = [
        statement
        for statement in forbidden_promotions
        if statement in integration_text or statement in scope_text
    ]
    if present:
        return fail(f"forbidden proof promotions detected: {present}")

    print("  OK: generic backend is closed and physical/choice seams remain false")
    return True


def main() -> int:
    print("=== Bishop Direct-Canonical Backend Audit ===")
    checks = (
        check_gitlink,
        check_source_provenance,
        check_wiring,
        check_modules,
        check_exact_arithmetic,
        check_dyadic_envelope,
        check_fail_closed_statuses,
    )

    results: list[bool] = []
    for check in checks:
        try:
            results.append(check())
        except (AssertionError, OSError, RuntimeError) as error:
            print(f"  FAIL: {error}")
            results.append(False)

    if all(results):
        print("\nALL STRUCTURAL AUDIT CHECKS PASSED.")
        print("NOTE: this does not replace Agda typechecking.")
        return 0

    print("\nSOME STRUCTURAL AUDIT CHECKS FAILED.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
