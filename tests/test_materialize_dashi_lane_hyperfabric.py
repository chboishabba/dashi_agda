import importlib.util
import json
import sys
from pathlib import Path

SCRIPT = Path(__file__).parents[1] / "scripts/materialize_dashi_lane_hyperfabric.py"
SPEC = importlib.util.spec_from_file_location("lane_hf", SCRIPT)
LANE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = LANE
SPEC.loader.exec_module(LANE)


def write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def test_degree_generates_split_and_merge(tmp_path: Path) -> None:
    write(tmp_path / "DASHI/Test/Lane.agda", """module DASHI.Test.Lane where
source : Set
source = Set
left : Set
left = source
right : Set
right = source
merge : Set
merge = left
""")
    config = {
        "schema": LANE.SCHEMA,
        "title": "fixture",
        "slug": "fixture",
        "carriers": [
            {"id": "source", "declaration": "DASHI.Test.Lane.source"},
            {"id": "left", "declaration": "DASHI.Test.Lane.left", "dependencies": ["source"]},
            {"id": "right", "declaration": "DASHI.Test.Lane.right", "dependencies": ["source"]},
            {"id": "merge", "declaration": "DASHI.Test.Lane.merge", "dependencies": ["left", "right"]}
        ]
    }
    config_path = tmp_path / "config.json"
    config_path.write_text(json.dumps(config))
    ir = LANE.build_ir(tmp_path, config_path)
    edges = {(e["source"], e["target"]): e["kind"] for e in ir["transports"]}
    assert edges[("source", "left")] == "split"
    assert edges[("source", "right")] == "split"
    assert edges[("left", "merge")] == "merge"
    assert edges[("right", "merge")] == "merge"


def test_open_endpoint_is_derived_from_declaration_name(tmp_path: Path) -> None:
    write(tmp_path / "DASHI/Test/Open.agda", """module DASHI.Test.Open where
analyticCondition : Set
analyticCondition = Set
""")
    config = {
        "schema": LANE.SCHEMA,
        "title": "fixture",
        "slug": "fixture",
        "authority_rules": {"open_declaration_patterns": ["Condition$"]},
        "carriers": [{"id": "open", "declaration": "DASHI.Test.Open.analyticCondition"}]
    }
    path = tmp_path / "config.json"
    path.write_text(json.dumps(config))
    ir = LANE.build_ir(tmp_path, path)
    assert ir["carriers"][0]["state"] == "open_analytic"
    assert "open" in LANE.render_svg(ir)


def test_external_leaf_requires_qualified_source_reference(tmp_path: Path) -> None:
    write(tmp_path / "DASHI/Test/Import.agda", """module DASHI.Test.Import where
import Source as S
anchor : Set
anchor = S.actualTheorem
""")
    config = {
        "schema": LANE.SCHEMA,
        "title": "fixture",
        "slug": "fixture",
        "external_reference_labels": {"S.actualTheorem": "source theorem"},
        "carriers": [{"id": "anchor", "declaration": "DASHI.Test.Import.anchor"}]
    }
    path = tmp_path / "config.json"
    path.write_text(json.dumps(config))
    ir = LANE.build_ir(tmp_path, path)
    assert any(c["id"].startswith("external-") for c in ir["carriers"])
    assert any(e["evidence"] == "qualified-reference" for e in ir["transports"])
