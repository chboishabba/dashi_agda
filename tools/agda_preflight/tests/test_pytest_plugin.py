from __future__ import annotations

from pathlib import Path

pytest_plugins = ["pytester"]


def write_agda(root: Path, module: str, body: str = "") -> Path:
    path = root.joinpath(*module.split(".")).with_suffix(".agda")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(f"module {module} where\n{body}", encoding="utf-8")
    return path


def test_pytest_collects_passing_agda_module(pytester):
    good = write_agda(pytester.path, "Good")

    result = pytester.runpytest(
        "-p",
        "dashi_agda_preflight",
        "--agda-preflight",
        "--agda-root",
        str(pytester.path),
        str(good),
        "-q",
    )

    result.assert_outcomes(passed=1)
    result.stdout.fnmatch_lines(
        [
            "*Agda preflight*",
            "*modules passed: 1*",
            "*modules failed: 0*",
        ]
    )


def test_pytest_renders_structural_preflight_failure(pytester):
    broken = write_agda(
        pytester.path,
        "Broken",
        """
record Model : Set₁ where
  field
    Parameter : Set
    Scalar : Set

open Model public

Series :
  Model → Parameter → Scalar
Series M x = x
""",
    )

    result = pytester.runpytest(
        "-p",
        "dashi_agda_preflight",
        "--agda-preflight",
        "--agda-root",
        str(pytester.path),
        str(broken),
        "-q",
    )

    result.assert_outcomes(failed=1)
    result.stdout.fnmatch_lines(
        [
            "*Agda preflight failed for Broken*",
            "*TSAGDA001*",
            "*modules failed: 1*",
        ]
    )


def test_pytest_reverse_closure_collects_consumers(pytester):
    leaf = write_agda(pytester.path, "A.Leaf")
    write_agda(
        pytester.path,
        "A.Middle",
        """
import A.Leaf
""",
    )
    write_agda(
        pytester.path,
        "A.Top",
        """
import A.Middle
""",
    )

    result = pytester.runpytest(
        "-p",
        "dashi_agda_preflight",
        "--agda-preflight",
        "--agda-closure",
        "--agda-root",
        str(pytester.path),
        str(leaf),
        "-q",
    )

    result.assert_outcomes(passed=3)
    result.stdout.fnmatch_lines(
        [
            "*modules passed: 3*",
            "*modules failed: 0*",
        ]
    )


def test_pytest_errors_only_suppresses_warning_text_on_failure(pytester):
    path = write_agda(
        pytester.path,
        "Mixed",
        """
record Model : Set₁ where
  field
    Parameter : Set
    Scalar : Set

open Model public

broken :
  Model → Parameter → Scalar
broken M x = x
""",
    )

    result = pytester.runpytest(
        "-p",
        "dashi_agda_preflight",
        "--agda-preflight",
        "--agda-errors-only",
        "--agda-root",
        str(pytester.path),
        str(path),
        "-q",
    )

    result.assert_outcomes(failed=1)
    result.stdout.fnmatch_lines(["*TSAGDA001*"])


def test_pytest_module_item_nodeid_supports_k_filter(pytester):
    first = write_agda(pytester.path, "First")
    second = write_agda(pytester.path, "Second")

    result = pytester.runpytest(
        "-p",
        "dashi_agda_preflight",
        "--agda-preflight",
        "--agda-root",
        str(pytester.path),
        str(first),
        str(second),
        "-k",
        "Second",
        "-q",
    )

    result.assert_outcomes(passed=1, deselected=1)


def test_pytest_dependency_closure_collects_imports_dependency_first(pytester):
    write_agda(pytester.path, "A.Leaf")
    write_agda(
        pytester.path,
        "A.Middle",
        """
import A.Leaf
""",
    )
    top = write_agda(
        pytester.path,
        "A.Top",
        """
import A.Middle
""",
    )

    result = pytester.runpytest(
        "-p",
        "dashi_agda_preflight",
        "--agda-preflight",
        "--agda-deps",
        "--agda-root",
        str(pytester.path),
        str(top),
        "-vv",
    )

    result.assert_outcomes(passed=3)
    output = "\n".join(result.outlines)
    leaf = output.find("A.Leaf")
    middle = output.find("A.Middle")
    top_index = output.find("A.Top")
    assert -1 not in (leaf, middle, top_index)
    assert leaf < middle < top_index



def test_pytest_compact_mode_writes_structured_report(pytester):
    broken = write_agda(
        pytester.path,
        "CompactBroken",
        """
record Model : Set₁ where
  field
    Parameter : Set
    Scalar : Set

open Model public

Series :
  Model → Parameter → Scalar
Series M x = x
""",
    )
    report = pytester.path / "agda-report.json"

    result = pytester.runpytest(
        "-p",
        "dashi_agda_preflight",
        "--agda-preflight",
        "--agda-compact",
        "--agda-report-json",
        str(report),
        "--agda-root",
        str(pytester.path),
        str(broken),
        "-q",
    )

    result.assert_outcomes(failed=1)
    assert report.exists()

    import json
    payload = json.loads(report.read_text(encoding="utf-8"))
    assert payload["summary"]["modules_failed"] == 1
    assert payload["summary"]["errors"] >= 1
    assert "TSAGDA001" in payload["summary"]["diagnostics_by_code"]
    assert payload["modules"]


def test_pytest_compact_summary_ranks_diagnostic_codes(pytester):
    broken = write_agda(
        pytester.path,
        "CompactSummary",
        """
record Model : Set₁ where
  field
    Parameter : Set
    Scalar : Set

open Model public

Series :
  Model → Parameter → Scalar
Series M x = x
""",
    )

    result = pytester.runpytest(
        "-p",
        "dashi_agda_preflight",
        "--agda-preflight",
        "--agda-compact",
        "--agda-root",
        str(pytester.path),
        str(broken),
        "-q",
    )

    result.assert_outcomes(failed=1)
    result.stdout.fnmatch_lines(
        [
            "*top diagnostics:*",
            "*TSAGDA001:*",
        ]
    )
