from __future__ import annotations

from dataclasses import replace
from difflib import get_close_matches
from typing import Iterable, List

from .fixes import SuggestedFix


def _find_record(checker, summary, name):
    record = summary.ast.records.get(name)
    if record is not None:
        return record
    for imported in checker.imported_summaries(summary).values():
        record = imported.ast.records.get(name)
        if record is not None:
            return record
    return None


def _record_field_fix(checker, summary, diagnostic):
    marker = " is not a field of record "
    if marker not in diagnostic.message:
        return diagnostic
    original, record_name = diagnostic.message.split(marker, 1)
    original = original.strip()
    record_name = record_name.strip().rstrip(".")
    record = _find_record(checker, summary, record_name)
    if record is None or not record.field_surface_complete:
        return diagnostic

    field_names = sorted(record.fields)
    if not field_names:
        return replace(
            diagnostic,
            root_cause="unknown-record-field",
            explanation=(
                f"{record_name} is structurally known to have no fields, "
                f"but the record expression assigns {original}."
            ),
            expected="no field assignments",
            found=original,
            fixes=(
                SuggestedFix(
                    title=f"Remove or retarget field {original}",
                    applicability="speculative",
                    rationale=(
                        "The indexed target record has no fields; the expression "
                        "may target the wrong record or contain a stray assignment."
                    ),
                    validation="typecheck",
                ),
            ),
        )

    short = original.rsplit(".", 1)[-1]
    matches = get_close_matches(short, field_names, n=3, cutoff=0.6)
    if len(matches) == 1:
        candidate = matches[0]
        fixes = (
            SuggestedFix(
                title=f"Replace {original} with {candidate}",
                applicability="likely",
                rationale=(
                    f"{candidate} is the unique close field name in "
                    f"record {record_name}."
                ),
                validation="typecheck",
            ),
        )
    else:
        preview = ", ".join(field_names[:12])
        suffix = "" if len(field_names) <= 12 else ", …"
        fixes = (
            SuggestedFix(
                title=f"Choose a field declared by {record_name}",
                applicability="speculative",
                rationale=f"Known fields: {preview}{suffix}",
                validation="typecheck",
            ),
        )

    return replace(
        diagnostic,
        root_cause="unknown-record-field",
        explanation=(
            f"The record expression is resolved to {record_name}, whose indexed "
            "field surface does not contain this assignment name."
        ),
        expected=", ".join(field_names),
        found=original,
        fixes=fixes,
    )


def _missing_record_fields_fix(diagnostic):
    marker = " is missing fields: "
    if marker not in diagnostic.message:
        return diagnostic
    prefix, missing = diagnostic.message.split(marker, 1)
    record_name = prefix.removeprefix("record ").strip()
    missing_names = [name.strip() for name in missing.split(",") if name.strip()]
    if not missing_names:
        return diagnostic
    return replace(
        diagnostic,
        root_cause="missing-record-fields",
        explanation=(
            f"The record expression targets {record_name} but omits required "
            "assignments from its complete indexed field surface."
        ),
        expected=", ".join(missing_names),
        found="missing assignments",
        fixes=(
            SuggestedFix(
                title="Add the missing record assignments",
                applicability="likely",
                rationale="Missing fields: " + ", ".join(missing_names),
                validation="typecheck",
            ),
        ),
    )


def _projection_type_fix(diagnostic):
    marker = " is a projection of "
    if marker not in diagnostic.message:
        return diagnostic
    projection, rest = diagnostic.message.split(marker, 1)
    record_name = rest.split(",", 1)[0].strip()
    return replace(
        diagnostic,
        root_cause="unapplied-dependent-projection",
        explanation=(
            f"{projection} is a dependent projection of {record_name}; using it "
            "as a terminal type atom leaves its record receiver unapplied."
        ),
        expected=f"{projection} <{record_name} receiver>",
        found=projection,
        fixes=(
            SuggestedFix(
                title=f"Apply {projection} to its {record_name} receiver",
                applicability="likely",
                rationale=diagnostic.hint or "Pass the record/model value explicitly.",
                validation="typecheck",
            ),
        ),
    )


def _projection_receiver_fix(diagnostic):
    if "uses '_' for its" not in diagnostic.message:
        return diagnostic
    return replace(
        diagnostic,
        root_cause="implicit-projection-receiver",
        explanation=(
            "A projection receiver metavariable is used even though the source "
            "index found a matching record binder in scope."
        ),
        found="_",
        fixes=(
            SuggestedFix(
                title="Pass the projection receiver explicitly",
                applicability="likely",
                rationale=diagnostic.hint or diagnostic.message,
                validation="typecheck",
            ),
        ),
    )


def enrich_diagnostics(checker, summary, diagnostics: Iterable):
    enriched: List = []
    for diagnostic in diagnostics:
        if diagnostic.code == "TSAGDA060":
            diagnostic = _record_field_fix(checker, summary, diagnostic)
        elif diagnostic.code == "TSAGDA062":
            diagnostic = _missing_record_fields_fix(diagnostic)
        elif diagnostic.code == "TSAGDA001":
            diagnostic = _projection_type_fix(diagnostic)
        elif diagnostic.code in {"TSAGDA002", "TSAGDA171"}:
            diagnostic = _projection_receiver_fix(diagnostic)
        enriched.append(diagnostic)
    return enriched
