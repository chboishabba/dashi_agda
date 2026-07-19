from __future__ import annotations

import importlib
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
sys.path.insert(0, str(SCRIPTS))
MODULE = importlib.import_module("materialize_dashi_phase_visualisations")
CONFIG = ROOT / "config" / "dashi-euler-phase-visualisations.json"


def build():
    return MODULE.build_ir(ROOT, CONFIG)


def test_scene_descriptors_are_parsed_from_agda_source() -> None:
    ir = build()
    names = [scene["name"] for scene in ir["scenes"]]
    assert names == [
        "eulerComplex2D",
        "eulerHelix3D",
        "eulerAmbient4D",
        "eulerAmbient5D",
        "eulerAmbient12D",
        "eulerAmbient32D",
    ]
    assert all(scene["source"]["path"].endswith("PhaseResidualProjection.agda") for scene in ir["scenes"])
    assert all(scene["source"]["line"] > 0 for scene in ir["scenes"])
    assert ir["invariants"]["configuration_names_scenes_not_coordinates"] is True


def test_full_turn_closure_and_projection_zero_are_preserved() -> None:
    ir = build()
    MODULE.validate_ir(ir)
    for scene in ir["scenes"]:
        invariants = scene["invariants"]
        assert invariants["full_turn_phase_closes"] is True
        assert invariants["full_turn_residual_norm"] < 1e-9
        assert invariants["screen_projection_preserves_zero"] is True
        assert invariants["ambient_coordinates_above_one_are_zero"] is True


def test_higher_dimensional_scenes_do_not_invent_extra_phase_coordinates() -> None:
    ir = build()
    for scene in ir["scenes"]:
        assert scene["phase_embedding"]["active_coordinates"] == [0, 1]
        for sample in scene["samples"]:
            assert all(abs(value) < 1e-12 for value in sample["phase"][2:])


def test_visualisation_battery_covers_curated_and_diagnostic_views() -> None:
    ir = build()
    views = {view for scene in ir["scenes"] for view in scene["views"]}
    assert {
        "phase-plane",
        "residual-shadow",
        "helix",
        "axis-fan",
        "waveform",
        "mosaic",
        "spiral",
    } <= views


def test_svg_carries_source_and_authority_boundaries() -> None:
    ir = build()
    svg = MODULE.render_svg(ir)
    assert "DASHI Euler phase visualisation battery" in svg
    assert "PhaseResidualProjection.agda" in svg
    assert "semantic exact" in svg
    assert "render illustrative" in svg
    assert "animateMotion" in svg
    assert "projection matrix mosaic" in svg
    assert "only Re/Im carry phase" in svg
    assert "only the reconstructed Agda proof can promote it" in svg
