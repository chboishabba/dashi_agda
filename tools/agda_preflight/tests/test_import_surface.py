from __future__ import annotations

from pathlib import Path

from agda_preflight.ast_index import build_import_surface
from agda_preflight.checker import Checker


def write_module(root: Path, module: str, body: str = "") -> Path:
    path = root.joinpath(*module.split(".")).with_suffix(".agda")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        f"module {module} where\n{body}",
        encoding="utf-8",
    )
    return path


def test_lightweight_import_surface_matches_full_ast_index(tmp_path):
    write_module(tmp_path, "Lib.One")
    write_module(tmp_path, "Lib.Two")
    path = write_module(
        tmp_path,
        "Use",
        """
import Lib.One as One
open import Lib.Two public using ()
""",
    )

    checker = Checker(tmp_path)
    source = path.read_text(encoding="utf-8")
    surface = build_import_surface(
        checker.parser,
        path,
        tmp_path,
        source,
    )
    full = checker.parse_summary(path).ast

    assert surface.module_name == full.module_name
    assert {
        (item.module, item.alias, item.opened, item.public)
        for item in surface.imports
    } == {
        (item.module, item.alias, item.opened, item.public)
        for item in full.imports
    }
    assert {
        (item.target, item.public)
        for item in surface.opens
    } == {
        (item.target, item.public)
        for item in full.opens
    }
