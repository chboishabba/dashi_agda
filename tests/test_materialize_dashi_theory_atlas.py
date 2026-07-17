from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

SCRIPT = Path(__file__).parents[1] / "scripts/materialize_dashi_theory_atlas.py"
SPEC = importlib.util.spec_from_file_location("dashi_theory_atlas", SCRIPT)
ATLAS = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = ATLAS
assert SPEC.loader is not None
SPEC.loader.exec_module(ATLAS)


def write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def test_postulate_block_yields_separate_open_declarations(tmp_path: Path) -> None:
    write(
        tmp_path / "DASHI/Test/Open.agda",
        """module DASHI.Test.Open where
postulate
  shellEstimate : Set
  interactionEstimate : Set
""",
    )
    declarations = ATLAS.scan_repo(tmp_path / "DASHI")
    assert set(declarations) == {
        "DASHI.Test.Open.shellEstimate",
        "DASHI.Test.Open.interactionEstimate",
    }
    assert all(declaration.postulated for declaration in declarations.values())


def test_open_dependency_makes_composition_conditional(tmp_path: Path) -> None:
    write(
        tmp_path / "DASHI/Test/Open.agda",
        """module DASHI.Test.Open where
postulate
  shellEstimate : Set
""",
    )
    write(
        tmp_path / "DASHI/Test/Compose.agda",
        """module DASHI.Test.Compose where
compose : Set
compose = Set
""",
    )
    declarations = ATLAS.scan_repo(tmp_path / "DASHI")
    spec = {
        "schema": ATLAS.SCHEMA,
        "cards": [
            {"id": "open", "declaration": "DASHI.Test.Open.shellEstimate"},
            {"id": "compose", "declaration": "DASHI.Test.Compose.compose", "dependencies": ["open"]},
        ],
    }
    cards = ATLAS.build_cards(spec, declarations)
    ATLAS.derive_graph(cards, spec)
    assert {card.id: card.state for card in cards} == {
        "open": "open_analytic",
        "compose": "proved_conditional",
    }
    assert cards[1].open_inputs == ["open"]


def test_conditional_input_type_is_derived_not_asserted(tmp_path: Path) -> None:
    write(
        tmp_path / "DASHI/Test/Bridge.agda",
        """module DASHI.Test.Bridge where
bridge : AnalyticInput → Set
bridge input = Set
""",
    )
    declarations = ATLAS.scan_repo(tmp_path / "DASHI")
    spec = {
        "schema": ATLAS.SCHEMA,
        "authority_rules": {"conditional_input_type_patterns": ["AnalyticInput"]},
        "cards": [{"id": "bridge", "declaration": "DASHI.Test.Bridge.bridge"}],
    }
    cards = ATLAS.build_cards(spec, declarations)
    ATLAS.derive_graph(cards, spec)
    assert cards[0].state == "proved_conditional"
    assert cards[0].open_inputs == ["AnalyticInput"]


def test_svg_carries_non_promotion_footer(tmp_path: Path) -> None:
    write(
        tmp_path / "DASHI/Test/Closed.agda",
        """module DASHI.Test.Closed where
closed : Set
closed = Set
""",
    )
    declarations = ATLAS.scan_repo(tmp_path / "DASHI")
    spec = {
        "schema": ATLAS.SCHEMA,
        "title": "Fixture Atlas",
        "cards": [{"id": "closed", "declaration": "DASHI.Test.Closed.closed"}],
    }
    cards = ATLAS.build_cards(spec, declarations)
    ATLAS.derive_graph(cards, spec)
    payload = ATLAS.make_payload(spec, cards, tmp_path, "2026-07-17T00:00:00+00:00")
    svg = ATLAS.render_svg(payload)
    assert "Compilation certifies type-correct assembly only" in svg
    assert "proved" in svg
