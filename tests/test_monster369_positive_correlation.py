from __future__ import annotations

import importlib.util
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "monster369_positive_correlation.py"


def load_runtime():
    spec = importlib.util.spec_from_file_location("monster369_positive_correlation", SCRIPT)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_17496_is_positive_cross_context_numerical_echo_not_same_object():
    runtime = load_runtime()
    receipt = runtime.CORRELATIONS[17496]

    assert receipt.same_integer_paid
    assert receipt.independent_derivations
    assert receipt.monster_context_shared
    assert receipt.positive_bridge_signal
    assert receipt.strength == "crossContextNumericalEcho"
    assert not receipt.same_object_paid
    assert not receipt.same_representation_paid
    assert not receipt.same_character_role_paid


def test_32772_is_stronger_same_class_cross_role_positive_signal():
    runtime = load_runtime()
    receipt = runtime.CORRELATIONS[32772]

    assert receipt.same_integer_paid
    assert receipt.independent_derivations
    assert receipt.monster_context_shared
    assert receipt.same_monster_class
    assert receipt.same_source_family
    assert receipt.positive_bridge_signal
    assert receipt.strength == "sameClassCrossRoleEcho"
    assert not receipt.same_object_paid
    assert not receipt.same_representation_paid
    assert not receipt.same_character_role_paid


def test_bridge_search_priority_keeps_32772_ahead_of_17496_without_proof_promotion():
    runtime = load_runtime()

    ordered = runtime.bridge_search_priority()

    assert [item.observed_integer for item in ordered] == [32772, 17496]
    assert all(item.positive_bridge_signal for item in ordered)
    assert all(not item.theorem_authority_paid for item in ordered)


def test_report_separates_positive_signal_from_theorem_authority():
    runtime = load_runtime()
    report = runtime.build_report()

    assert report["positive_correlations"]["17496"]["positive_bridge_signal"] is True
    assert report["positive_correlations"]["32772"]["positive_bridge_signal"] is True
    assert report["positive_correlations"]["32772"]["same_monster_class"] is True
    assert report["authority"]["positive_correlation_creates_same_object"] is False
    assert report["authority"]["positive_correlation_creates_representation_theorem"] is False
