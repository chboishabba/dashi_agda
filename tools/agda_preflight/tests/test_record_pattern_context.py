from __future__ import annotations

from pathlib import Path

from agda_preflight.checker import Checker


def write_module(root: Path, module: str, body: str) -> Path:
    path = root.joinpath(*module.split(".")).with_suffix(".agda")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        f"module {module} where\n{body}",
        encoding="utf-8",
    )
    return path


def test_record_pattern_fields_are_not_validated_as_result_record_fields(tmp_path):
    path = write_module(
        tmp_path,
        "PatternCopy",
        """
record Source : Set₁ where
  field
    clock : Set
    shift : Set

record Target : Set₁ where
  field
    m3Clock : Set
    m3Shift : Set

copy : Source → Target
copy record
  { clock = c
  ; shift = s
  } =
  record
    { m3Clock = c
    ; m3Shift = s
    }
""",
    )

    checker = Checker(tmp_path)
    summary = checker.parse_summary(path)

    contexts = [
        (
            item.context,
            tuple(assignment.name for assignment in item.assignments),
        )
        for item in summary.ast.record_expressions
    ]

    assert ("pattern", ("clock", "shift")) in contexts
    assert ("expression", ("m3Clock", "m3Shift")) in contexts

    diagnostics = checker.structural_check(path)
    bogus = [
        item
        for item in diagnostics
        if item.code == "TSAGDA060"
        and ("clock is not a field" in item.message or "shift is not a field" in item.message)
    ]
    assert bogus == []


def test_record_pattern_never_receives_machine_field_edit(tmp_path):
    path = write_module(
        tmp_path,
        "PatternNoFix",
        """
record Source : Set₁ where
  field
    clock : Set

record Target : Set₁ where
  field
    m3Clock : Set

copy : Source → Target
copy record { clock = c } =
  record { m3Clock = c }
""",
    )

    diagnostics = Checker(tmp_path).structural_check(path)
    pattern_fixes = [
        fix
        for diagnostic in diagnostics
        for fix in diagnostic.fixes
        if any(
            edit.start_line == 11 and edit.replacement == "m3Clock"
            for edit in fix.edits
        )
    ]
    assert pattern_fixes == []
