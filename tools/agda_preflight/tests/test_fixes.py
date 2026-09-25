from __future__ import annotations

from pathlib import Path

from agda_preflight.checker import Checker
from agda_preflight.source_index import SourceIndex
from agda_preflight.timing import Profiler


def write_module(root: Path, module: str, body: str) -> Path:
    path = root.joinpath(*module.split(".")).with_suffix(".agda")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(f"module {module} where\n{body}", encoding="utf-8")
    return path


def test_unknown_record_field_gets_unique_close_name_fix(tmp_path):
    path = write_module(
        tmp_path,
        "FixRecord",
        """
record R : Set₁ where
  field
    carrier : Set
    witness : carrier

mk : R
mk =
  record
    { carrier = Set
    ; witnes = Set
    }
""",
    )

    diagnostic = next(
        item for item in Checker(tmp_path).check(path)
        if item.code == "TSAGDA060"
    )

    assert diagnostic.root_cause == "unknown-record-field"
    assert diagnostic.found == "witnes"
    assert "witness" in (diagnostic.expected or "")
    assert diagnostic.fixes
    assert diagnostic.fixes[0].applicability == "likely"
    assert "witness" in diagnostic.fixes[0].title
    assert diagnostic.fixes[0].validation == "typecheck"
    assert diagnostic.fixes[0].edits
    edit = diagnostic.fixes[0].edits[0]
    assert edit.start_byte is not None
    assert edit.end_byte is not None
    assert edit.replacement == "witness"


def test_unapplied_projection_gets_receiver_fix_explanation(tmp_path):
    path = write_module(
        tmp_path,
        "ProjectionFix",
        """
record Model : Set₁ where
  field
    Parameter : Set
    Scalar : Set

open Model public

Series : Model → Parameter → Scalar
Series M x = x
""",
    )

    diagnostic = next(
        item for item in Checker(tmp_path).check(path)
        if item.code == "TSAGDA001" and "Parameter" in item.message
    )

    assert diagnostic.root_cause == "unapplied-dependent-projection"
    assert diagnostic.fixes
    assert diagnostic.fixes[0].applicability == "likely"
    assert diagnostic.fixes[0].validation == "typecheck"


def test_fix_metadata_survives_persistent_cache_roundtrip(tmp_path):
    path = write_module(
        tmp_path,
        "CachedFix",
        """
record R : Set₁ where
  field
    witness : Set

mk : R
mk = record { witnes = Set }
""",
    )
    database = tmp_path / ".cache" / "source-index.sqlite3"

    with SourceIndex(tmp_path, database, profiler=Profiler()) as index:
        first = index.diagnose(path)
    original = next(item for item in first.diagnostics if item.code == "TSAGDA060")
    assert original.fixes

    profiler = Profiler()
    with SourceIndex(tmp_path, database, profiler=profiler) as index:
        second = index.diagnose(path)
    cached = next(item for item in second.diagnostics if item.code == "TSAGDA060")

    assert cached.fixes == original.fixes
    assert cached.explanation == original.explanation
    assert profiler.snapshot().counts.get("files_parsed", 0) == 0
