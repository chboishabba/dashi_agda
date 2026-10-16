#!/usr/bin/env python3
"""Regenerate numerical receipts and verify producer/evidence integrity.

For each registered producer this checker verifies:
1. the evidence `script_sha256` matches the current producer bytes when present;
2. the producer exits successfully and emits JSON;
3. every generated field equals the corresponding evidence field.
"""

from __future__ import annotations
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
PAIRS = [
    ("scripts/matbg_bm_plane_wave_replay.py", "Docs/evidence/matbg_bm_plane_wave_replay_2026-10-16.json"),
    ("scripts/matbg_bm_quantum_geometry.py", "Docs/evidence/matbg_bm_quantum_geometry_2026-10-16.json"),
    ("scripts/matbg_qtm_matrix_element_observer.py", "Docs/evidence/matbg_qtm_matrix_element_observer_2026-10-16.json"),
    ("scripts/matbg_geometry_caloric_upper_bound.py", "Docs/evidence/matbg_geometry_caloric_upper_bound_2026-10-16.json"),
    ("scripts/matbg_thf_hubbard_i_atomic_reference.py", "Docs/evidence/matbg_thf_hubbard_i_atomic_reference_2026-10-16.json"),
    ("scripts/matbg_thf_coupled_green_reference.py", "Docs/evidence/matbg_thf_coupled_green_reference_2026-10-16.json"),
    ("scripts/matbg_thf_self_consistency_obstruction.py", "Docs/evidence/matbg_thf_self_consistency_obstruction_2026-10-16.json"),
    ("scripts/matbg_entropy_combinatorial_replay.py", "Docs/evidence/matbg_entropy_combinatorial_replay_2026-10-16.json"),
    ("scripts/casimir_finite_disk_gravity_proxy.py", "Docs/evidence/casimir_finite_disk_gravity_proxy_2026-10-16.json"),
]

def assert_generated_matches_evidence(generated: Any, evidence: Any, path: str = "$") -> None:
    if isinstance(generated, dict):
        if not isinstance(evidence, dict):
            raise AssertionError(f"{path}: generated object but evidence has {type(evidence).__name__}")
        for key, value in generated.items():
            if key not in evidence:
                raise AssertionError(f"{path}: generated key {key!r} missing from evidence")
            assert_generated_matches_evidence(value, evidence[key], f"{path}.{key}")
        return
    if isinstance(generated, list):
        if not isinstance(evidence, list) or len(generated) != len(evidence):
            raise AssertionError(f"{path}: list shape mismatch")
        for index, (g_value, e_value) in enumerate(zip(generated, evidence)):
            assert_generated_matches_evidence(g_value, e_value, f"{path}[{index}]")
        return
    if generated != evidence:
        raise AssertionError(f"{path}: generated {generated!r} != evidence {evidence!r}")

def check_pair(script_rel: str, evidence_rel: str) -> None:
    script = ROOT / script_rel
    evidence_path = ROOT / evidence_rel
    evidence = json.loads(evidence_path.read_text())
    actual_sha = hashlib.sha256(script.read_bytes()).hexdigest()
    recorded_sha = evidence.get("script_sha256")
    if recorded_sha is not None and actual_sha != recorded_sha:
        raise AssertionError(f"{script_rel}: sha256 {actual_sha} != evidence script_sha256 {recorded_sha}")
    completed = subprocess.run([sys.executable, str(script)], cwd=ROOT, check=True, capture_output=True, text=True)
    generated = json.loads(completed.stdout)
    assert_generated_matches_evidence(generated, evidence)
    print(f"evidence OK: {script_rel} -> {evidence_rel}")

def main() -> None:
    for script_rel, evidence_rel in PAIRS:
        check_pair(script_rel, evidence_rel)

if __name__ == "__main__":
    main()
