from __future__ import annotations

import importlib
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
sys.path.insert(0, str(SCRIPTS))
MODULE = importlib.import_module("dashi_visualize_agda")


def write_fixture(tmp_path: Path) -> Path:
    dashi = tmp_path / "DASHI" / "Fixture"
    dashi.mkdir(parents=True)
    (dashi / "Flow.agda").write_text(
        """module DASHI.Fixture.Flow where

open import Agda.Builtin.Nat using (Nat)

addOne : Nat → Nat
addOne n = n

record PairBox : Set where
  constructor pairBox
  field
    left : Nat
    right : Nat

assemble : (x : Nat) → (y : Nat) → PairBox
assemble x y =
  record
    { left = addOne x
    ; right = addOne y
    }
""",
        encoding="utf-8",
    )
    config = {
        "schema": MODULE.SCHEMA,
        "title": "Fixture term flow",
        "slug": "fixture-term-flow",
        "scan_root": "DASHI",
        "roots": ["DASHI.Fixture.Flow.assemble"],
        "max_declarations": 8,
        "max_term_nodes_per_declaration": 16,
        "output_json": "artifacts/fixture.json",
        "output_svg": "artifacts/fixture.svg",
    }
    path = tmp_path / "config.json"
    path.write_text(json.dumps(config), encoding="utf-8")
    return path


def test_config_is_root_only_and_references_are_discovered(tmp_path: Path) -> None:
    config_path = write_fixture(tmp_path)
    config = json.loads(config_path.read_text())
    assert "carriers" not in config
    assert "dependencies" not in config
    ir = MODULE.build_ir(tmp_path, config_path)
    declarations = {row["fqname"] for row in ir["declarations"]}
    assert "DASHI.Fixture.Flow.assemble" in declarations
    assert "DASHI.Fixture.Flow.addOne" in declarations
    assert ir["invariants"]["configuration_contains_roots_not_edges"] is True


def test_binders_and_actual_math_expressions_become_fibres(tmp_path: Path) -> None:
    config_path = write_fixture(tmp_path)
    ir = MODULE.build_ir(tmp_path, config_path)
    binder_names = {row["name"] for row in ir["binders"]}
    assert {"x", "y"} <= binder_names
    expressions = [row["expression"] for row in ir["terms"]]
    assert any("addOne x" in expression for expression in expressions)
    assert any("addOne y" in expression for expression in expressions)
    assert any(fibre["kind"] == "function-application" and fibre["label"] == "addOne" for fibre in ir["fibres"])
    assert any(fibre["kind"] == "variable-use" and fibre["label"] == "x" for fibre in ir["fibres"])


def test_svg_prints_type_and_source_expressions(tmp_path: Path) -> None:
    config_path = write_fixture(tmp_path)
    ir = MODULE.build_ir(tmp_path, config_path)
    svg = MODULE.render_svg(ir)
    assert "TYPE / MATHEMATICAL MAP" in svg
    assert "addOne x" in svg
    assert "Variables are fibres" in svg
    assert "animateMotion" in svg
