from __future__ import annotations

from pathlib import Path
import sqlite3

from agda_preflight.source_index import SourceIndex
from agda_preflight.cold_bootstrap import ImportReceipt, dependency_affinity_batches
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



def test_dependency_affinity_batches_cluster_shared_foundations():
    receipts = (
        ImportReceipt("/tmp/A.Root.agda", "A.Root", ("A.Left", "A.Right")),
        ImportReceipt("/tmp/A.Left.agda", "A.Left", ("Shared.A",)),
        ImportReceipt("/tmp/A.Right.agda", "A.Right", ("Shared.A",)),
        ImportReceipt("/tmp/B.Root.agda", "B.Root", ("B.Left", "B.Right")),
        ImportReceipt("/tmp/B.Left.agda", "B.Left", ("Shared.B",)),
        ImportReceipt("/tmp/B.Right.agda", "B.Right", ("Shared.B",)),
        ImportReceipt("/tmp/Shared.A.agda", "Shared.A", ()),
        ImportReceipt("/tmp/Shared.B.agda", "Shared.B", ()),
    )

    batches = dependency_affinity_batches(receipts, jobs=2)
    assert len(batches) == 2
    assert sorted(len(batch) for batch in batches) == [4, 4]

    module_batches = [
        {item.module_name for item in batch}
        for batch in batches
    ]

    a_family = {"A.Root", "A.Left", "A.Right", "Shared.A"}
    b_family = {"B.Root", "B.Left", "B.Right", "Shared.B"}

    assert any(a_family <= batch for batch in module_batches)
    assert any(b_family <= batch for batch in module_batches)


def test_affinity_parallel_bootstrap_reports_parse_amplification(tmp_path):
    write_module(tmp_path, "Shared.Base", "base : Set\nbase = Set\n")
    write_module(
        tmp_path,
        "Q.Left",
        "import Shared.Base\nleft : Set\nleft = Set\n",
    )
    write_module(
        tmp_path,
        "Q.Right",
        "import Shared.Base\nright : Set\nright = Set\n",
    )
    top = write_module(
        tmp_path,
        "Q.Top",
        "import Q.Left\nimport Q.Right\ntop : Set\ntop = Set\n",
    )
    database = tmp_path / ".cache" / "source-index.sqlite3"
    profiler = Profiler()

    with SourceIndex(
        tmp_path,
        database,
        profiler=profiler,
        jobs=2,
    ) as index:
        result = index.diagnose(top)

    counts = profiler.snapshot().counts
    assert set(result.modules) == {
        "Q.Left",
        "Q.Right",
        "Q.Top",
        "Shared.Base",
    }
    assert counts["cold_batches"] == 2
    assert counts["cold_modules_discovered"] == 4
    assert counts["cold_worker_files_parsed"] >= 4
    assert counts["cold_parse_amplification_milli"] >= 1000
