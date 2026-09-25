from __future__ import annotations

from pathlib import Path

from agda_preflight.source_index import SourceIndex
from agda_preflight.timing import Profiler


def write_module(root: Path, module: str, body: str = "") -> Path:
    path = root.joinpath(*module.split(".")).with_suffix(".agda")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        f"module {module} where\n{body}",
        encoding="utf-8",
    )
    return path


def fixture_closure(tmp_path: Path) -> Path:
    write_module(
        tmp_path,
        "A.Leaf",
        """
x : Set
x = Set
""",
    )
    write_module(
        tmp_path,
        "A.Middle",
        """
import A.Leaf

y : Set
y = A.Leaf.x
""",
    )
    return write_module(
        tmp_path,
        "A.Top",
        """
import A.Middle

z : Set
z = A.Middle.y
""",
    )


def test_warm_unchanged_rollup_parses_zero_files(tmp_path):
    top = fixture_closure(tmp_path)
    database = tmp_path / ".cache" / "source-index.sqlite3"

    cold_profiler = Profiler()
    with SourceIndex(tmp_path, database, profiler=cold_profiler) as index:
        cold = index.diagnose(top)

    cold_counts = cold_profiler.snapshot().counts
    assert set(cold.modules) == {"A.Leaf", "A.Middle", "A.Top"}
    assert cold_counts["files_parsed"] == 3
    assert cold_counts["checker_instances"] == 1

    warm_profiler = Profiler()
    with SourceIndex(tmp_path, database, profiler=warm_profiler) as index:
        warm = index.diagnose(top)

    warm_counts = warm_profiler.snapshot().counts
    assert warm.cache_hit is True
    assert set(warm.modules) == {"A.Leaf", "A.Middle", "A.Top"}
    assert warm_counts.get("files_parsed", 0) == 0
    assert warm_counts.get("checker_instances", 0) == 0
    assert warm_counts["modules_cached"] == 3
    assert warm_counts["closure_cache_hit"] == 1


def test_changed_dependency_invalidates_cached_importers(tmp_path):
    top = fixture_closure(tmp_path)
    leaf = tmp_path / "A" / "Leaf.agda"
    database = tmp_path / ".cache" / "source-index.sqlite3"

    with SourceIndex(tmp_path, database, profiler=Profiler()) as index:
        index.diagnose(top)

    # Change both size and hash so the freshness transition is deterministic
    # even on filesystems with coarse timestamp resolution.
    leaf.write_text(
        """module A.Leaf where

x : Set
x = Set

extra : Set
extra = Set
""",
        encoding="utf-8",
    )

    profiler = Profiler()
    with SourceIndex(tmp_path, database, profiler=profiler) as index:
        result = index.diagnose(top)

    counts = profiler.snapshot().counts
    assert result.cache_hit is False
    assert counts["dirty_modules"] >= 1
    # The source-changed leaf plus importers are conservatively recomputed.
    # Public-API fingerprints can narrow this further in a later tranche.
    assert counts["diagnostics_recomputed"] == 3
    assert counts["files_parsed"] == 3


def test_cached_rollup_diagnostics_survive_process_boundary(tmp_path):
    broken = write_module(
        tmp_path,
        "Broken",
        """
record R : Set where
  field
    A : Set

mk : R
mk = record { bogus = Set }
""",
    )
    database = tmp_path / ".cache" / "source-index.sqlite3"

    with SourceIndex(tmp_path, database, profiler=Profiler()) as index:
        first = index.diagnose(broken)
    first_codes = [diagnostic.code for diagnostic in first.diagnostics]
    assert "TSAGDA060" in first_codes

    profiler = Profiler()
    with SourceIndex(tmp_path, database, profiler=profiler) as index:
        second = index.diagnose(broken)

    assert [diagnostic.code for diagnostic in second.diagnostics] == first_codes
    assert profiler.snapshot().counts.get("files_parsed", 0) == 0
