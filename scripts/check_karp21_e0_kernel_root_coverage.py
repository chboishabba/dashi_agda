#!/usr/bin/env python3
"""Fail-closed E0 coverage check for the *actual* focused Agda kernel runner.

Checks explicitly invoked original theorem owners, not mere imports, filenames,
preflight booleans or prior source-audit receipts. This is a static coverage
check only; it does NOT certify typechecking or prove the Karp-21 endpoint.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys

# The canonical 15-gate ledger's E0 scope, grouped by original proof seam.
# Roots include both B6 objects, both E1 trace owners, and
# distinct partial physical F2 and original G3 evidence owners.
REQUIRED: dict[str, tuple[str, ...]] = {
    "B1 strict original": ("Karp21NativeBinaryStrictAfterOriginalExact.agda",),
    "B2 valid raw edges": ("Karp21NativeBinaryValidRawEdgesOriginalExact.agda",),
    "B3 graph header": ("Karp21NativeBinaryHeaderBudgetExact.agda",),
    "B4 count budget": ("Karp21NativeBinaryCountBudgetExact.agda",),
    "B5 endpoint history": ("Karp21NativeBinaryEndpointHistoryOriginalExact.agda",),
    "B6 whole graph and verifier": (
        "Karp21NativeWholeBinaryGraphOriginalExact.agda",
        "Karp21NativeWholeBinaryVerifierOriginalExact.agda",
    ),
    "D1 initial source step": ("Karp21NativeWholeBinaryPriorityMachineExact.agda",),
    "D2 first enabled original step": (
        "Karp21NativeBinaryToOriginalRawMachineStepExact.agda",
    ),
    "E1 selected events and trace": (
        "Karp21NativeWholeBinarySelectedEventTraceExact.agda",
        "Karp21NativeWholeBinaryTraceRebuildExact.agda",
    ),
    "E2 typed acceptance": ("Karp21NativeWholeBinaryTypedAcceptanceExact.agda",),
    "F2 partial live allocation": (
        "Karp21NativeLivePayloadPotentialExact.agda",
        "Karp21NativeFirstEnabledLedgerWordBoundExact.agda",
    ),
    "G3 original certificate bits": (
        "Karp21NativeOriginalSparseCertificateBoundExact.agda",
        "Karp21NativeOriginalSparseCertificateTightBoundExact.agda",
    ),
}

PREFIX = "DASHI/Mathematics/Complexity/"
START = "# Focused direct kernel adjudication"
STOP = 'if [[ "$mode" == "golden"'
CHECK = re.compile(r"^\s*check_agda\s+(DASHI/Mathematics/Complexity/[\w]+\.agda)\s*$", re.M)


def root_checks(script: str) -> list[str]:
    if script.count(START) != 1:
        raise ValueError("missing or ambiguous focused kernel-cut section")
    segment = script.split(START, 1)[1]
    if STOP not in segment:
        raise ValueError("missing kernel-cut end boundary")
    segment = segment.split(STOP, 1)[0]
    if 'if [[ "$mode" == "kernel-cut" ]]' not in segment:
        raise ValueError("kernel-cut guard missing")
    return CHECK.findall(segment)


def assess(script: str, root: Path | None = None) -> tuple[list[str], list[str]]:
    checked = root_checks(script)
    missing = [f"{phase}: {name}" for phase, names in REQUIRED.items()
               for name in names if PREFIX + name not in checked]
    duplicates = sorted({path for path in checked if checked.count(path) > 1})
    if root is not None:
        missing += [f"source missing: {path}" for path in checked
                    if not (root / path).is_file()]
    return missing, duplicates


def self_test() -> None:
    roots = [PREFIX + name for names in REQUIRED.values() for name in names]
    fixture = START + '\nif [[ "$mode" == "kernel-cut" ]]; then\n' + ''.join(
        f"  check_agda {path}\n" for path in roots
    ) + 'fi\n' + STOP + '\n'
    assert assess(fixture) == ([], [])
    removed = fixture.replace(f"  check_agda {roots[0]}\n", "", 1)
    assert any("B1" in msg for msg in assess(removed)[0])
    doubled = fixture.replace(f"  check_agda {roots[0]}\n",
                              f"  check_agda {roots[0]}\n  check_agda {roots[0]}\n", 1)
    assert assess(doubled)[1] == [roots[0]]
    assert len(roots) == len(set(roots)) == 16


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()
    if args.self_test:
        self_test()
    try:
        script = (args.root / "scripts/referee_karp21_maxcut.sh").read_text()
        missing, duplicates = assess(script, args.root)
    except (ValueError, OSError) as exc:
        print(f"BLOCKED E0 root-coverage reader: {exc}", file=sys.stderr)
        return 2
    for msg in missing:
        print(f"MISSING E0 root: {msg}", file=sys.stderr)
    for msg in duplicates:
        print(f"DUPLICATE E0 root: {msg}", file=sys.stderr)
    if missing or duplicates:
        return 1
    print("E0 STATIC COVERAGE PASS: 16 original B1-B6/D1-D2/E1-E2/F2/G3 owners "+
          "are explicitly in kernel-cut; source paths exist. AGDA NOT RUN.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
