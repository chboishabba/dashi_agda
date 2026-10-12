from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PLANNER = ROOT / "scripts/plan_waller_diffusercam_claim_scale.py"


def load_planner():
    spec = spec_from_file_location("waller_claim_scale", PLANNER)
    assert spec is not None and spec.loader is not None
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_dense_working_set_estimate_counts_columns_and_gram():
    planner = load_planner()
    est = planner.estimate_dense_working_set(6, 8, 5, lateral_radius=1, lateral_step=1)
    assert est["sensor_pixels"] == 48
    assert est["lateral_positions"] == 9
    assert est["selected_columns"] == 45
    assert est["selected_h_bytes"] == 48 * 45 * 8
    assert est["gram_bytes"] == 45 * 45 * 8
    assert est["resident_lower_bound_bytes"] == 2 * est["selected_h_bytes"] + est["gram_bytes"]
    assert est["conservative_peak_bytes"] == 3 * est["selected_h_bytes"] + est["gram_bytes"]


def test_recommendation_rejects_unsafe_radius_and_keeps_safe_scales():
    planner = load_planner()
    plan = planner.plan_claim_scales(
        100,
        100,
        20,
        budget_bytes=200_000_000,
        radii=(0, 1, 2, 3),
        steps=(1,),
    )
    assert plan["budget_bytes"] == 200_000_000
    assert any(item["safe"] for item in plan["candidates"])
    assert any(not item["safe"] for item in plan["candidates"])
    assert plan["largest_safe_candidate"] is not None
    assert plan["planner_is_numerical_certificate"] is False
    assert plan["planner_is_physical_receipt"] is False
