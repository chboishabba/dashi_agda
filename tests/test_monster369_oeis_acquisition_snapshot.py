from __future__ import annotations

import importlib.util
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "monster369_oeis_acquisition_snapshot.py"


def load_runtime():
    spec = importlib.util.spec_from_file_location("monster369_oeis_acquisition", SCRIPT)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_a005052_ladder_snapshot_retains_90_65610_196830():
    runtime = load_runtime()
    node = runtime.SEQUENCES["A005052"]

    assert node["formula"] == "10*3^n"
    assert node["selected_terms"] == {2: 90, 8: 65610, 9: 196830}
    assert node["authority"] == "numerical-navigation"


def test_6b_normalization_family_retains_q6_32772_across_three_manifests():
    runtime = load_runtime()

    family = [runtime.SEQUENCES[key] for key in ("A007255", "A045485", "A121665")]
    assert {node["class_label"] for node in family} == {"6B"}
    assert {node["q0"] for node in family} == {0, 7, 12}
    assert {node["positive_coefficients"][6] for node in family} == {32772}
    assert all(node["positive_coefficients"][1] == 78 for node in family)
    assert runtime.RELATIONS["6b-normalization-positive-degree-agreement"]["paid"] is True


def test_power_family_trace_nodes_are_acquired_but_not_action_authority():
    runtime = load_runtime()

    assert runtime.SEQUENCES["A007244"]["positive_coefficients"][1] == 54
    assert runtime.SEQUENCES["A007246"]["positive_coefficients"][1] == 276
    assert runtime.SEQUENCES["A014708"]["positive_coefficients"][1] == 196884
    assert all(
        runtime.SEQUENCES[key]["authority"] == "source-navigation"
        for key in ("A007244", "A007246", "A014708")
    )


def test_snapshot_keeps_positive_bridge_signal_separate_from_proof_authority():
    runtime = load_runtime()
    report = runtime.build_report()

    assert report["positive_bridge_candidates"]["a005052-heisenberg-ladder"] is True
    assert report["positive_bridge_candidates"]["6b-q6-to-c6-spectrum-32772"] is True
    assert report["authority"]["oeis_snapshot_creates_same_object"] is False
    assert report["authority"]["oeis_snapshot_creates_monster_action"] is False
    assert report["authority"]["positive_bridge_signal_creates_theorem"] is False
