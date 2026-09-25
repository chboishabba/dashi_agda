from __future__ import annotations

from pathlib import Path
import sqlite3

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


def test_parallel_cold_bootstrap_populates_one_persistent_closure(tmp_path):
    write_module(
        tmp_path,
        "P.Leaf",
        """
x : Set
x = Set
""",
    )
    write_module(
        tmp_path,
        "P.Middle",
        """
import P.Leaf

y : Set
y = Set
""",
    )
    top = write_module(
        tmp_path,
        "P.Top",
        """
import P.Middle

z : Set
z = Set
""",
    )
    database = tmp_path / ".cache" / "source-index.sqlite3"

    cold_profiler = Profiler()
    with SourceIndex(
        tmp_path,
        database,
        profiler=cold_profiler,
        jobs=2,
    ) as index:
        cold = index.diagnose(top)

    counts = cold_profiler.snapshot().counts
    assert cold.cache_hit is False
    assert set(cold.modules) == {"P.Leaf", "P.Middle", "P.Top"}
    assert counts["cold_workers"] == 2
    assert counts["cold_modules_discovered"] == 3
    assert counts["files_parsed"] >= 3

    connection = sqlite3.connect(database)
    try:
        assert connection.execute(
            "SELECT count(*) FROM modules"
        ).fetchone()[0] == 3
        assert connection.execute(
            "SELECT count(*) FROM imports"
        ).fetchone()[0] == 2
    finally:
        connection.close()

    warm_profiler = Profiler()
    with SourceIndex(
        tmp_path,
        database,
        profiler=warm_profiler,
        jobs=2,
    ) as index:
        warm = index.diagnose(top)

    warm_counts = warm_profiler.snapshot().counts
    assert warm.cache_hit is True
    assert warm_counts.get("files_parsed", 0) == 0
    assert warm_counts.get("checker_instances", 0) == 0
    assert warm_counts["closure_cache_hit"] == 1


def test_parallel_and_sequential_cold_diagnostics_agree(tmp_path):
    broken = write_module(
        tmp_path,
        "P.Broken",
        """
record R : Set₁ where
  field
    witness : Set

mk : R
mk = record { witnes = Set }
""",
    )

    sequential_db = tmp_path / ".cache" / "sequential.sqlite3"
    parallel_db = tmp_path / ".cache" / "parallel.sqlite3"

    with SourceIndex(
        tmp_path,
        sequential_db,
        profiler=Profiler(),
        jobs=1,
    ) as index:
        sequential = index.diagnose(broken)

    with SourceIndex(
        tmp_path,
        parallel_db,
        profiler=Profiler(),
        jobs=2,
    ) as index:
        parallel = index.diagnose(broken)

    sequential_view = [
        (item.code, item.line, item.column, item.message)
        for item in sequential.diagnostics
    ]
    parallel_view = [
        (item.code, item.line, item.column, item.message)
        for item in parallel.diagnostics
    ]
    assert parallel_view == sequential_view
