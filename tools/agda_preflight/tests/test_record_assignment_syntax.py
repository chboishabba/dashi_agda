from pathlib import Path

from agda_preflight.checker import Checker


def write_module(root: Path, module: str, source: str) -> Path:
    path = root.joinpath(*module.split(".")).with_suffix(".agda")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(source, encoding="utf-8")
    return path


def test_qualified_record_construction_field_is_reported(tmp_path):
    path = write_module(
        tmp_path,
        "QualifiedRecordField",
        """module QualifiedRecordField where

record Tower : Set₁ where
  field
    reflectPoint : Set

mkTower : Tower
mkTower = record
  { Tower.reflectPoint = Set
  }
""",
    )

    diagnostics = Checker(tmp_path).check(path)
    hits = [d for d in diagnostics if d.code == "TSAGDA090"]

    assert len(hits) == 1
    assert hits[0].severity == "error"
    assert "Tower.reflectPoint" in hits[0].message


def test_unqualified_record_construction_field_is_not_reported(tmp_path):
    path = write_module(
        tmp_path,
        "UnqualifiedRecordField",
        """module UnqualifiedRecordField where

record Tower : Set₁ where
  field
    reflectPoint : Set

mkTower : Tower
mkTower = record
  { reflectPoint = Set
  }
""",
    )

    diagnostics = Checker(tmp_path).check(path)

    assert not any(d.code == "TSAGDA090" for d in diagnostics)
