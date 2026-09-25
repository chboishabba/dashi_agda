from __future__ import annotations

from pathlib import Path

from agda_preflight.checker import Checker
from agda_preflight.interfaces import interface_from_summary, resolve_interface_exports
from agda_preflight.timing import Profiler


def write_module(root: Path, module: str, body: str = "") -> Path:
    path = root.joinpath(*module.split(".")).with_suffix(".agda")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        f"module {module} where\n{body}",
        encoding="utf-8",
    )
    return path


def diagnostic_view(items):
    return [
        (
            item.code,
            item.line,
            item.column,
            item.message,
            item.severity,
            item.minimum_evidence,
        )
        for item in items
    ]


def test_preloaded_interfaces_preserve_cross_module_diagnostics(tmp_path):
    lib = write_module(
        tmp_path,
        "Lib",
        """
record R : Set₁ where
  field
    carrier : Set
    witness : carrier

open R public
""",
    )
    use = write_module(
        tmp_path,
        "Use",
        """
import Lib

badProjection : Set
badProjection = Lib.witness

mk : Lib.R
mk =
  record
    { carrier = Set
    ; witnes = Set
    }
""",
    )

    baseline = Checker(tmp_path).structural_check(use)

    interface_checker = Checker(tmp_path)
    lib_summary = interface_checker.parse_summary(lib)
    interfaces = resolve_interface_exports(
        {
            "Lib": interface_from_summary(tmp_path, lib_summary),
        }
    )

    profiler = Profiler()
    preloaded = Checker(
        tmp_path,
        profiler=profiler,
        interfaces=interfaces,
    ).structural_check(use)

    assert diagnostic_view(preloaded) == diagnostic_view(baseline)
    assert profiler.snapshot().counts["files_parsed"] == 1


def test_interface_export_surface_matches_checker_public_reexports(tmp_path):
    base = write_module(
        tmp_path,
        "Base",
        """
x : Set
x = Set
""",
    )
    middle = write_module(
        tmp_path,
        "Middle",
        """
open import Base public
""",
    )

    checker = Checker(tmp_path)
    base_summary = checker.parse_summary(base)
    middle_summary = checker.parse_summary(middle)

    resolved = resolve_interface_exports(
        {
            "Base": interface_from_summary(tmp_path, base_summary),
            "Middle": interface_from_summary(tmp_path, middle_summary),
        }
    )

    assert resolved["Middle"].exports == checker.exported_names(middle_summary)



def test_preloaded_interface_resolves_qualified_record_field_result(tmp_path):
    b = write_module(
        tmp_path,
        "B",
        """
record S : Set₁ where
  field
    value : Set
""",
    )
    a = write_module(
        tmp_path,
        "A",
        """
import B

record R : Set₁ where
  field
    child : B.S
""",
    )
    use = write_module(
        tmp_path,
        "UseQualified",
        """
import A

mk : A.R
mk =
  record
    { child =
        record
          { value = Set
          }
    }
""",
    )

    builder = Checker(tmp_path)
    summaries = {
        "A": builder.parse_summary(a),
        "B": builder.parse_summary(b),
    }
    interfaces = resolve_interface_exports(
        {
            module: interface_from_summary(tmp_path, summary)
            for module, summary in summaries.items()
        }
    )

    baseline = Checker(tmp_path).structural_check(use)

    profiler = Profiler()
    preloaded = Checker(
        tmp_path,
        profiler=profiler,
        interfaces=interfaces,
    ).structural_check(use)

    assert diagnostic_view(preloaded) == diagnostic_view(baseline)
    assert profiler.snapshot().counts["files_parsed"] == 1
