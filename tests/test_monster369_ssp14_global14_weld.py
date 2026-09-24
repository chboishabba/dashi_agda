from __future__ import annotations

import importlib.util
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "monster369_ssp14_global14_weld.py"


def load_runtime():
    spec = importlib.util.spec_from_file_location("monster369_ssp14_global14_weld", SCRIPT)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_ssp14_global14_weld_is_bijective_but_not_canonical_lift_induced():
    runtime = load_runtime()
    probe = runtime.build_probe()

    assert probe["raw_state_count"] == 27
    assert probe["residual_lane_count"] == 14
    assert probe["global_inversion_orbit_count"] == 14
    assert probe["canonical_lift_image_count"] == 13
    assert probe["canonical_lift_duplicate_orbit"] == (-1, 0, 0)
    assert probe["canonical_lift_missing_orbit"] == (0, 0, 0)
    assert probe["explicit_weld_image_count"] == 14
    assert probe["explicit_weld_is_bijection"] is True
    assert probe["explicit_weld_is_canonical_lift_induced"] is False
    assert probe["exceptional_lane"] == ("mode09", 1)
    assert probe["exceptional_lane_natural_target"] == (-1, 0, 0)
    assert probe["exceptional_lane_weld_target"] == (0, 0, 0)
    assert probe["weld_creates_monster_action"] is False


def test_global_inversion_quotient_is_invariant_and_has_one_fixed_orbit():
    runtime = load_runtime()
    probe = runtime.build_probe()

    assert probe["global_inversion_invariant_for_all_27_states"] is True
    assert probe["fixed_orbits"] == {(0, 0, 0)}
    assert probe["nonfixed_orbit_count"] == 13
