#!/usr/bin/env python3
"""Verify exact coverage of the attached Luo completion lemma inventory."""

from __future__ import annotations

import hashlib
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EXPECTED_COUNTS = {0: 38, 1: 47, 2: 53, 3: 45, 4: 57, 5: 52, 6: 59, 7: 46, 8: 59, 9: 39, 10: 53, 11: 26, 12: 36, 13: 36, 14: 15}
STAGE_FILES = {
    0: "DASHI/Physics/Closure/NSTriadKNLuoCompletionLemmaInventoryAExact.agda",
    1: "DASHI/Physics/Closure/NSTriadKNLuoCompletionLemmaInventoryAExact.agda",
    2: "DASHI/Physics/Closure/NSTriadKNLuoCompletionLemmaInventoryAExact.agda",
    3: "DASHI/Physics/Closure/NSTriadKNLuoCompletionLemmaInventoryAExact.agda",
    4: "DASHI/Physics/Closure/NSTriadKNLuoCompletionLemmaInventoryAExact.agda",
    5: "DASHI/Physics/Closure/NSTriadKNLuoCompletionLemmaInventoryBExact.agda",
    6: "DASHI/Physics/Closure/NSTriadKNLuoCompletionLemmaInventoryBExact.agda",
    7: "DASHI/Physics/Closure/NSTriadKNLuoCompletionLemmaInventoryBExact.agda",
    8: "DASHI/Physics/Closure/NSTriadKNLuoCompletionLemmaInventoryBExact.agda",
    9: "DASHI/Physics/Closure/NSTriadKNLuoCompletionLemmaInventoryBExact.agda",
    10: "DASHI/Physics/Closure/NSTriadKNLuoCompletionLemmaInventoryCExact.agda",
    11: "DASHI/Physics/Closure/NSTriadKNLuoCompletionLemmaInventoryCExact.agda",
    12: "DASHI/Physics/Closure/NSTriadKNLuoCompletionLemmaInventoryCExact.agda",
    13: "DASHI/Physics/Closure/NSTriadKNLuoCompletionLemmaInventoryCExact.agda",
    14: "DASHI/Physics/Closure/NSTriadKNLuoCompletionLemmaInventoryCExact.agda",
}
EXPECTED_TOTAL = 661
EXPECTED_UNIQUE = 659
EXPECTED_DIGEST = "9f6bcf08a4acbb12009f74531fb0ba9919e6a788acf230d541d4efffa8484ecf"


def parse_stages(path: Path) -> dict[int, list[str]]:
    stages: dict[int, list[str]] = {}
    current_stage: int | None = None
    inside_data = False

    for raw in path.read_text(encoding="utf-8").splitlines():
        stripped = raw.strip()
        module_match = re.fullmatch(r"module Stage(\d+) where", stripped)
        if module_match:
            current_stage = int(module_match.group(1))
            stages[current_stage] = []
            inside_data = False
            continue

        if current_stage is None:
            continue
        if stripped == "data Lemma : Set where":
            inside_data = True
            continue
        if not inside_data:
            continue
        if stripped == ": Lemma":
            inside_data = False
            continue
        if not stripped or stripped.startswith("--"):
            continue
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_′₀-₉-]*", stripped):
            raise SystemExit(
                f"invalid lemma constructor in {path} Stage{current_stage}: "
                f"{stripped!r}"
            )
        stages[current_stage].append(stripped)

    return stages


def main() -> int:
    parsed_by_file: dict[str, dict[int, list[str]]] = {}
    for relative in sorted(set(STAGE_FILES.values())):
        path = ROOT / relative
        if not path.exists():
            raise SystemExit(f"missing inventory module: {relative}")
        parsed_by_file[relative] = parse_stages(path)

    stage_lines: list[str] = []
    all_names: list[str] = []

    for stage in sorted(EXPECTED_COUNTS):
        relative = STAGE_FILES[stage]
        names = parsed_by_file[relative].get(stage)
        if names is None:
            raise SystemExit(f"Stage{stage} missing from {relative}")
        expected = EXPECTED_COUNTS[stage]
        if len(names) != expected:
            raise SystemExit(
                f"Stage{stage} count mismatch: "
                f"expected {expected}, found {len(names)}"
            )
        stage_lines.extend(f"{stage}:{name}" for name in names)
        all_names.extend(names)

    digest = hashlib.sha256(
        ("\n".join(stage_lines) + "\n").encode("utf-8")
    ).hexdigest()

    if len(stage_lines) != EXPECTED_TOTAL:
        raise SystemExit(
            f"occurrence mismatch: expected {EXPECTED_TOTAL}, "
            f"found {len(stage_lines)}"
        )
    if len(set(all_names)) != EXPECTED_UNIQUE:
        raise SystemExit(
            f"unique-name mismatch: expected {EXPECTED_UNIQUE}, "
            f"found {len(set(all_names))}"
        )
    if digest != EXPECTED_DIGEST:
        raise SystemExit(
            f"digest mismatch: expected {EXPECTED_DIGEST}, found {digest}"
        )

    full = ROOT / "DASHI/Physics/Closure/NSTriadKNLuoFullCompletionLemmaInventoryExact.agda"
    full_text = full.read_text(encoding="utf-8")
    required_fail_closed = (
        "fullCompletionLemmaInventoryInhabited = false",
        "canonicalAnalyticPhysicalLeavesInhabited = false",
        "periodicNavierStokesGlobalRegularityProved = false",
        "submissionPackageComplete = false",
    )
    missing = [entry for entry in required_fail_closed if entry not in full_text]
    if missing:
        raise SystemExit(
            "full inventory is not fail-closed; missing: " + ", ".join(missing)
        )

    print(
        "Luo completion inventory verified: "
        f"{len(stage_lines)} stage-qualified occurrences, "
        f"{len(set(all_names))} unique names, sha256={digest}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
