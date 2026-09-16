from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "rsa260_mksol_action_chunk_receipt.py"


def load_module():
    spec = importlib.util.spec_from_file_location("rsa260_mksol_action_chunk_receipt", SCRIPT)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def row(world_id: int) -> dict[str, object]:
    return {
        "world_id": world_id,
        "action_digest": f"action-{world_id}",
        "rank_r2": world_id + 2,
        "rank_r10": world_id + 10,
        "all_ranks": [world_id + i for i in range(14)],
    }


def test_complete_first_chunk_is_verified():
    m = load_module()
    payload = m.build_verified_chunk_receipt("worlds00to07", [row(i) for i in range(8)])
    assert payload["chunk"] == "worlds00to07"
    assert payload["expected_world_count"] == 8
    assert payload["completed_world_count"] == 8
    assert payload["complete"] is True
    assert payload["action_outputs_retained"] is True
    assert payload["rank_r2_retained"] is True
    assert payload["rank_r10_retained"] is True
    assert payload["all_universally_available_rank_coordinates_retained"] is True


def test_partial_chunk_is_rejected():
    m = load_module()
    with pytest.raises(ValueError, match="expected 8 worlds"):
        m.build_verified_chunk_receipt("worlds00to07", [row(i) for i in range(7)])


def test_missing_full_rank_vector_is_rejected():
    m = load_module()
    rows = [row(i) for i in range(8)]
    rows[3]["all_ranks"] = [1, 2]
    with pytest.raises(ValueError, match="14 rank coordinates"):
        m.build_verified_chunk_receipt("worlds00to07", rows)


def test_wrong_world_ids_are_rejected():
    m = load_module()
    rows = [row(i) for i in range(1, 9)]
    with pytest.raises(ValueError, match="world ids"):
        m.build_verified_chunk_receipt("worlds00to07", rows)
