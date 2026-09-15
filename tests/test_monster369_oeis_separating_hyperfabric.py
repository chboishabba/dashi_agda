from __future__ import annotations

import importlib.util
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "monster369_oeis_separating_hyperfabric.py"


def load_runtime():
    spec = importlib.util.spec_from_file_location("monster369_oeis_hyperfabric", SCRIPT)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_current_monster369_portfolio_has_expected_shape_and_negative_control():
    runtime = load_runtime()

    assert len(runtime.COORDINATES) == 23
    assert len(runtime.EDGES) == 5
    assert runtime.hits_every_edge(runtime.CANONICAL_TYPED_SELECTION)
    assert not runtime.hits_every_edge(runtime.OEIS_ONLY_SELECTION)


def test_exhaustive_finite_search_finds_unique_size_two_transversal():
    runtime = load_runtime()

    result = runtime.minimum_transversals()

    assert result.minimum_size == 2
    assert result.transversals == (
        ("actualWeylActionCoordinate", "monster3B65610Character"),
    )


def test_runtime_receipt_keeps_discovery_separate_from_proof_authority():
    runtime = load_runtime()

    report = runtime.build_report()

    assert report["portfolio"]["coordinate_count"] == 23
    assert report["portfolio"]["edge_count"] == 5
    assert report["negative_controls"]["oeis_only_hits_every_edge"] is False
    assert report["minimum_transversal_search"]["minimum_size"] == 2
    assert report["minimum_transversal_search"]["kernel_proved_minimum"] is False
    assert report["authority"]["python_runtime_creates_monster_theorem"] is False
    assert report["authority"]["oeis_identity_creates_monster_action"] is False
