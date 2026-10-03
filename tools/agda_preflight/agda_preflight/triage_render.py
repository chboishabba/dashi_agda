from __future__ import annotations

from collections import Counter, defaultdict
from dataclasses import dataclass
import hashlib
from pathlib import Path
import re
from typing import Iterable, Sequence


_SIBLING_FAMILIES = {
    "TSAGDA049": "receiver",
    "TSAGDA052": "receiver",
    "TSAGDA120": "type-value",
    "TSAGDA123": "type-value",
}
_KIND_BY_CODE = {
    "TSAGDA049": "receiver",
    "TSAGDA052": "receiver",
    "TSAGDA053": "arity",
    "TSAGDA090": "parser",
    "TSAGDA104": "type-value",
    "TSAGDA120": "type-value",
    "TSAGDA123": "type-value",
    "TSAGDA204": "placeholder",
    "TSAGDA300": "shadowing",
    "TSAGDA301": "rewrite",
    "TSAGDA302": "deprecated-api",
    "TSAGDA390": "parser",
    "TSAGDA398": "agda-error",
    "TSAGDA399": "agda-warning",
}

_SYMBOL_PATTERNS = (
    re.compile(r"^projection\s+([^\s]+)\s+is\s+under-applied"),
    re.compile(r"^([^\s]+)\s+is\s+used\s+without\s+a\s+visible\s+.+\s+receiver"),
    re.compile(r"^([^\s]+)\s+is\s+visibly\s+over-applied"),
    re.compile(r"^(?:field|projection)\s+([^\s]+)\s+has\s+known\s+term"),
)
_RECEIVER = re.compile(r"without a visible\s+(.+?)\s+receiver")
_ARITY = re.compile(r"over-applied\s*\((\d+)>(\d+)\)")
_KNOWN_TERM = re.compile(r"known term\s+([^\s]+)\s+in type")
_EQUALITY_VALUE = re.compile(
    r"equality proof\s+([^\s]+)\s+is used as the value of non-equality result\s+([^\s]+)"
)


@dataclass(frozen=True)
class LogicalDiagnostic:
    path: Path
    display_path: str
    line: int
    column: int
    severity: str
    kind: str
    subject: str
    codes: tuple[str, ...]
    message: str
    evidence: str
    minimum_evidence: str
    diagnostics: tuple[object, ...]
    cause_key: tuple[str, ...]

    @property
    def code_label(self) -> str:
        numbers = [code.removeprefix("TSAGDA") for code in self.codes]
        if len(numbers) == 1:
            return f"TSAGDA{numbers[0]}"
        return "TSAGDA" + "/".join(numbers)

    @property
    def compact_code_label(self) -> str:
        return "/".join(code.removeprefix("TSAGDA") for code in self.codes)


@dataclass(frozen=True)
class TriageReport:
    root: Path
    diagnostics: tuple[object, ...]
    logical: tuple[LogicalDiagnostic, ...]
    fingerprint: str
    absolute_paths: bool = False



def _display_path(path: Path, root: Path, absolute: bool) -> str:
    if absolute:
        return str(path)
    try:
        return str(path.resolve().relative_to(root.resolve()))
    except (ValueError, OSError):
        return str(path)


def _kind(code: str) -> str:
    return _KIND_BY_CODE.get(code, "diagnostic")


def _subject(message: str, code: str) -> str:
    for pattern in _SYMBOL_PATTERNS:
        match = pattern.search(message)
        if match:
            return match.group(1)
    equality = _EQUALITY_VALUE.search(message)
    if equality:
        return equality.group(2)
    if code == "TSAGDA204":
        return "_"
    if code.startswith("TSAGDA3"):
        return "Agda"
    return ""


def _family(code: str) -> str:
    return _SIBLING_FAMILIES.get(code, code)


def _logical_message(diagnostics: Sequence[object], kind: str, subject: str) -> str:
    messages = [diag.message for diag in diagnostics]
    if kind == "receiver":
        receiver = next(
            (match.group(1) for message in messages if (match := _RECEIVER.search(message))),
            None,
        )
        if receiver:
            return f"projection under-applied; missing {receiver} receiver"
        return "projection receiver/application mismatch"
    if kind == "arity":
        match = next(
            (match for message in messages if (match := _ARITY.search(message))),
            None,
        )
        if match:
            return f"visibly over-applied: got {match.group(1)} arguments, expected {match.group(2)}"
    if kind == "placeholder":
        return "unresolved proof placeholder"
    if kind == "type-value":
        term = next(
            (match.group(1) for message in messages if (match := _KNOWN_TERM.search(message))),
            None,
        )
        if term:
            return f"term `{term}` appears in type position"
        equality = next(
            (match for message in messages if (match := _EQUALITY_VALUE.search(message))),
            None,
        )
        if equality:
            return (
                f"equality proof `{equality.group(1)}` used where non-equality value "
                f"`{equality.group(2)}` is required"
            )
    return messages[0]


def _cause_key(diagnostics: Sequence[object], kind: str, subject: str, message: str) -> tuple[str, ...]:
    if kind == "type-value":
        term = next(
            (match.group(1) for diag in diagnostics if (match := _KNOWN_TERM.search(diag.message))),
            None,
        )
        if term:
            return (kind, term, "type-position")
    return (kind, subject, message)


def _fingerprint(logical: Iterable[LogicalDiagnostic]) -> str:
    rows = sorted(
        (
            item.display_path,
            str(item.line),
            str(item.column),
            item.severity,
            item.kind,
            item.subject,
            ",".join(item.codes),
            item.message,
        )
        for item in logical
    )
    payload = "\n".join("\0".join(row) for row in rows).encode("utf-8")
    return "preflight:" + hashlib.sha256(payload).hexdigest()[:12]


def build_triage(
    diagnostics: Sequence[object],
    root: Path,
    *,
    absolute_paths: bool = False,
    only_kind: str | None = None,
) -> TriageReport:
    grouped: dict[tuple, list[object]] = defaultdict(list)
    for diagnostic in diagnostics:
        kind = _kind(diagnostic.code)
        if only_kind and kind != only_kind:
            continue
        subject = _subject(diagnostic.message, diagnostic.code)
        key = (
            Path(diagnostic.path),
            diagnostic.line,
            diagnostic.column,
            diagnostic.severity,
            _family(diagnostic.code),
            subject,
        )
        grouped[key].append(diagnostic)

    logical = []
    for key, members in grouped.items():
        path, line, column, severity, _, subject = key
        codes = tuple(sorted({member.code for member in members}))
        kinds = {_kind(code) for code in codes}
        kind = next(iter(kinds)) if len(kinds) == 1 else "diagnostic"
        message = _logical_message(members, kind, subject)
        evidence_values = {member.evidence for member in members}
        minimum_values = {member.minimum_evidence for member in members}
        evidence = next(iter(evidence_values)) if len(evidence_values) == 1 else "+".join(sorted(evidence_values))
        minimum = next(iter(minimum_values)) if len(minimum_values) == 1 else "+".join(sorted(minimum_values))
        logical.append(
            LogicalDiagnostic(
                path=path,
                display_path=_display_path(path, root, absolute_paths),
                line=line,
                column=column,
                severity=severity,
                kind=kind,
                subject=subject,
                codes=codes,
                message=message,
                evidence=evidence,
                minimum_evidence=minimum,
                diagnostics=tuple(sorted(members, key=lambda d: d.code)),
                cause_key=_cause_key(members, kind, subject, message),
            )
        )

    logical.sort(key=lambda item: (item.display_path, item.line, item.column, item.codes))
    return TriageReport(
        root=root,
        diagnostics=tuple(diagnostics),
        logical=tuple(logical),
        fingerprint=_fingerprint(logical),
        absolute_paths=absolute_paths,
    )


def _counts(items: Sequence[LogicalDiagnostic]) -> tuple[int, int]:
    errors = sum(item.severity == "error" for item in items)
    warnings = sum(item.severity == "warning" for item in items)
    return errors, warnings


def _cause_groups(items: Sequence[LogicalDiagnostic]):
    groups: dict[tuple, list[LogicalDiagnostic]] = defaultdict(list)
    for item in items:
        groups[(item.display_path, *item.cause_key)].append(item)
    return sorted(
        groups.values(),
        key=lambda group: (
            group[0].display_path,
            -len(group),
            group[0].line,
            group[0].column,
        ),
    )


def _cause_label(group: Sequence[LogicalDiagnostic]) -> str:
    first = group[0]
    if first.kind == "receiver":
        return f"{first.subject} receiver/application mismatch"
    if first.kind == "arity":
        return f"{first.subject} over-application"
    if first.kind == "placeholder":
        return "unresolved proof placeholder"
    if first.kind == "type-value":
        match = _KNOWN_TERM.search(first.diagnostics[0].message)
        if match:
            return f"{match.group(1)} used in type position"
        return first.message
    return first.message.splitlines()[0]


def _evidence_line(item: LogicalDiagnostic) -> str | None:
    if item.evidence != item.minimum_evidence:
        return f"evidence: {item.evidence} → requires {item.minimum_evidence}"
    return None


def _render_file_header(path: str, items: Sequence[LogicalDiagnostic], cause_count: int) -> list[str]:
    errors, warnings = _counts(items)
    lines = [path, "─" * min(max(len(path), 12), 78)]
    locations = [item.line for item in items]
    span = f" · lines {min(locations)}–{max(locations)}" if locations else ""
    lines.append(f"{errors} errors · {warnings} warnings · {cause_count} root causes{span}")
    return lines


def render_grouped(report: TriageReport) -> str:
    if not report.logical:
        return "agda-preflight: no high-confidence issues found"

    by_file: dict[str, list[LogicalDiagnostic]] = defaultdict(list)
    for item in report.logical:
        by_file[item.display_path].append(item)

    output: list[str] = []
    all_cause_groups = _cause_groups(report.logical)
    for path in sorted(by_file):
        items = by_file[path]
        file_causes = [group for group in all_cause_groups if group[0].display_path == path]
        output.extend(_render_file_header(path, items, len(file_causes)))
        output.append("")
        for item in items:
            subject = f"  {item.subject}" if item.subject else ""
            sev = "E" if item.severity == "error" else "W"
            output.append(
                f"{item.line}:{item.column:<3} {sev} {item.code_label:<15}{subject}"
            )
            output.append(f"        {item.message}")
            evidence = _evidence_line(item)
            if evidence:
                output.append(f"        {evidence}")
            output.append("")

        output.extend(["Root causes", "───────────"])
        for group in file_causes:
            codes = sorted({code for item in group for code in item.codes})
            code_label = "TSAGDA" + "/".join(code.removeprefix("TSAGDA") for code in codes)
            output.append(f"{len(group):>2} × {_cause_label(group):<52} {code_label}")
        output.append("")

    errors, warnings = _counts(report.logical)
    output.append(f"{errors} errors · {warnings} warnings · {len(all_cause_groups)} root causes")
    output.append(f"fingerprint: {report.fingerprint}")
    return "\n".join(output).rstrip()


def render_location(report: TriageReport) -> str:
    if not report.logical:
        return "agda-preflight: no high-confidence issues found"
    output = []
    current_path = None
    for item in sorted(report.logical, key=lambda item: (item.display_path, item.line, item.column, item.codes)):
        if item.display_path != current_path:
            if output:
                output.append("")
            output.append(item.display_path)
            current_path = item.display_path
        sev = "E" if item.severity == "error" else "W"
        subject = f" {item.subject}" if item.subject else ""
        output.append(f"  {item.line}:{item.column}  {sev} {item.code_label}{subject}")
        output.append(f"      {item.message}")
        evidence = _evidence_line(item)
        if evidence:
            output.append(f"      {evidence}")
    output.append("")
    output.append(f"fingerprint: {report.fingerprint}")
    return "\n".join(output)


def render_compact(report: TriageReport) -> str:
    if not report.logical:
        return "agda-preflight: no high-confidence issues found"
    output = []
    for item in sorted(report.logical, key=lambda item: (item.display_path, item.line, item.column, item.codes)):
        sev = "E" if item.severity == "error" else "W"
        subject = f" {item.subject}:" if item.subject else ""
        output.append(
            f"{item.display_path}:{item.line}:{item.column}  {sev} "
            f"{item.compact_code_label:<9} {item.kind:<14}{subject} {item.message}"
        )
    groups = _cause_groups(report.logical)
    errors, warnings = _counts(report.logical)
    output.append(f"{errors} errors · {warnings} warnings · {len(groups)} root causes · {report.fingerprint}")
    return "\n".join(output)


def render_verbose(report: TriageReport) -> str:
    output = []
    selected_ids = {
        id(diagnostic)
        for item in report.logical
        for diagnostic in item.diagnostics
    }
    for diagnostic in report.diagnostics:
        if selected_ids and id(diagnostic) not in selected_ids:
            continue
        display_path = _display_path(Path(diagnostic.path), report.root, report.absolute_paths)
        head = (
            f"{display_path}:{diagnostic.line}:{diagnostic.column}: {diagnostic.severity}: "
            f"{diagnostic.code}: {diagnostic.message} "
            f"[evidence={diagnostic.evidence}; requires={diagnostic.minimum_evidence}]"
        )
        output.append(head)
        if diagnostic.hint:
            output.append(f"  hint: {diagnostic.hint}")
    if not output:
        return "agda-preflight: no high-confidence issues found"
    return "\n".join(output)
