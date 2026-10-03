from __future__ import annotations

from pathlib import Path
import re

from .ast_index import application_view, typed_binders
from .checker import Diagnostic


_QUALIFIED_RECEIVER = re.compile(
    r"^(?P<head>[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_']*)+)"
    r"\s+(?P<receiver>[A-Za-z_][A-Za-z0-9_']*)"
)
_RECORD = re.compile(r"^\s*record\b")
_CONSTRUCTOR = re.compile(r"^\s*constructor\b")
_FIELD = re.compile(r"^\s*field\b")
_LEAN_REWRITE = re.compile(r"\brewrite\s*<-\s*")
_REWRITE_CALL = re.compile(r"\brewrite\b[^\n]*\(\s*([A-Za-z_][A-Za-z0-9_']*)\b([^)]*)\)")
_NAMED_IMPLICIT = re.compile(r"^\{\s*([A-Za-z_][A-Za-z0-9_']*)\s*=")
_KNOWN_TERM_IN_TYPE = re.compile(r"known term\s+([^\s]+)\s+in type")
_WORD = r"[A-Za-z_][A-Za-z0-9_']*"
_SET_TOKEN = re.compile(r"(?<![A-Za-z0-9_'₀-₉])Set(?![A-Za-z0-9_'₀-₉])")


def _line_text(source: str, line: int) -> str:
    """Return one 1-based source line, or an empty string out of range."""

    lines = source.splitlines()
    if 1 <= line <= len(lines):
        return lines[line - 1]
    return ""


def _is_constructor_field_transition_gap(source: str, line: int) -> bool:
    """Recognize the narrow valid-record layout tree-sitter-agda misparses."""

    lines = source.splitlines()
    if not lines or line < 1:
        return False
    index = min(line - 1, len(lines) - 1)
    window_start = max(0, index - 3)
    window_end = min(len(lines), index + 4)
    window = lines[window_start:window_end]

    constructor_index = next(
        (i for i, text in enumerate(window) if _CONSTRUCTOR.match(text)),
        None,
    )
    field_index = next(
        (i for i, text in enumerate(window) if _FIELD.match(text)),
        None,
    )
    if constructor_index is None or field_index is None or constructor_index >= field_index:
        return False

    context_start = max(0, window_start - 12)
    context = lines[context_start : window_start + field_index + 1]
    if not any(_RECORD.match(text) for text in context):
        return False

    interesting = range(
        max(0, window_start + constructor_index - 1),
        min(len(lines), window_start + field_index + 2),
    )
    return index in interesting


def _visible_qualified_receiver(summary, diagnostic) -> bool:
    """Return true when source text visibly supplies the reported receiver."""

    if diagnostic.code not in {"TSAGDA049", "TSAGDA052"}:
        return False
    line = _line_text(summary.source, diagnostic.line)
    if not line or diagnostic.column < 1:
        return False
    tail = line[diagnostic.column - 1 :].strip()
    match = _QUALIFIED_RECEIVER.match(tail)
    if not match:
        return False
    if match.group("head") not in diagnostic.message:
        return False
    return match.group("receiver") not in {
        "where", "with", "rewrite", "in", "using", "hiding", "renaming",
    }


def _term_is_equality_operand(summary, diagnostic) -> bool:
    """Reject TSAGDA120/123 when the known term is merely an operand of ≡."""

    if diagnostic.code not in {"TSAGDA120", "TSAGDA123"}:
        return False
    match = _KNOWN_TERM_IN_TYPE.search(diagnostic.message)
    if match is None:
        return False
    term = match.group(1)

    for record in summary.ast.records.values():
        for field in record.field_occurrences:
            if field.line == diagnostic.line and term in field.type_text and "≡" in field.type_text:
                return True
    for signature in summary.ast.signatures.values():
        if signature.line == diagnostic.line and term in signature.type_text and "≡" in signature.type_text:
            return True
    return False


def _lean_reverse_rewrite_diagnostics(summary) -> list[Diagnostic]:
    """Catch Lean-style `rewrite <-` before Agda's parser does."""

    out = []
    for line, text in enumerate(summary.source.splitlines(), 1):
        match = _LEAN_REWRITE.search(text)
        if match is None:
            continue
        out.append(
            Diagnostic(
                "TSAGDA091",
                "Lean-style reverse rewrite `<-` is not Agda rewrite syntax",
                summary.path,
                line,
                match.start() + 1,
                "Use `rewrite sym (...)` (and import `sym`) for a reversed equality.",
                severity="error",
                confidence="high",
                evidence="tree-sitter",
                minimum_evidence="tree-sitter",
                evidence_sufficient=True,
                root_cause="Lean-style reverse rewrite syntax",
            )
        )
    return out


def _fragile_rewrite_diagnostics(summary) -> list[Diagnostic]:
    """Warn when rewrite matching is driven by a known non-constructor call."""

    local_terms = set(summary.ast.signatures) | set(summary.ast.clauses)
    constructors = {
        name
        for data in summary.ast.data.values()
        for name in data.constructors
    }
    constructors.update(
        record.constructor
        for record in summary.ast.records.values()
        if record.constructor
    )
    candidate_heads = local_terms - constructors
    if not candidate_heads:
        return []

    out = []
    for line, text in enumerate(summary.source.splitlines(), 1):
        if "rewrite" not in text or "<-" in text:
            continue
        for match in _REWRITE_CALL.finditer(text):
            head = match.group(1)
            if head not in candidate_heads:
                continue
            expression = f"{head}{match.group(2)}".strip()
            out.append(
                Diagnostic(
                    "TSAGDA303",
                    f"rewrite matcher depends on non-constructor term `{expression}`",
                    summary.path,
                    line,
                    match.start(1) + 1,
                    "Prefer an explicit `trans`/`cong` proof when the equality is not constructor-pattern driven.",
                    severity="warning",
                    confidence="medium",
                    evidence="dashi-index",
                    minimum_evidence="dashi-index",
                    evidence_sufficient=True,
                    root_cause=f"fragile rewrite target {head}",
                )
            )
    return out


def _record_header_text(summary, record) -> str:
    lines = summary.source.splitlines()
    start = max(0, record.line - 1)
    chunk = []
    for text in lines[start : min(len(lines), start + 8)]:
        chunk.append(text)
        if "where" in text:
            break
    return "\n".join(chunk)


def _record_universe_diagnostics(summary) -> list[Diagnostic]:
    """Catch the rigid lower bound `field : Set` => record cannot live in Set."""

    out = []
    for record in summary.ast.records.values():
        header = _record_header_text(summary, record)
        if not re.search(r":\s*Set\s+where\b", header):
            continue
        field = next(
            (field for field in record.field_occurrences if _SET_TOKEN.search(field.type_text)),
            None,
        )
        if field is None:
            continue
        out.append(
            Diagnostic(
                "TSAGDA304",
                (
                    f"record {record.name} is declared in Set but field {field.name} "
                    "has a Set-valued type, requiring at least Set₁"
                ),
                summary.path,
                record.line,
                1,
                f"Declare `{record.name}` in `Set₁` (or a higher universe if other fields require it).",
                severity="error",
                confidence="high",
                evidence="dashi-index",
                minimum_evidence="dashi-index",
                evidence_sufficient=True,
                root_cause=f"record universe lower bound for {record.name}",
            )
        )
    return out


def _wrong_hiding_diagnostics(summary) -> list[Diagnostic]:
    """Warn when a named implicit appears before required explicit LHS binders."""

    out = []
    for name, clauses in summary.ast.clauses.items():
        signature = summary.ast.signatures.get(name)
        if signature is None or signature.type_node is None:
            continue
        binders = typed_binders(summary.ast.source_bytes, signature.type_node)
        binder_index = {binder.name: index for index, binder in enumerate(binders)}
        for clause in clauses:
            view = application_view(summary.ast.source_bytes, clause.lhs_node)
            if view is None:
                continue
            explicit_seen = 0
            for arg in view.args:
                if arg.visibility == "explicit":
                    explicit_seen += 1
                    continue
                match = _NAMED_IMPLICIT.match(arg.text.strip())
                if match is None:
                    continue
                binder_name = match.group(1)
                index = binder_index.get(binder_name)
                if index is None:
                    continue
                required_explicit = sum(
                    binder.visibility == "explicit"
                    for binder in binders[:index]
                )
                if explicit_seen >= required_explicit:
                    continue
                out.append(
                    Diagnostic(
                        "TSAGDA305",
                        (
                            f"named implicit {{{binder_name} = …}} appears before "
                            f"{required_explicit} preceding explicit binder(s) are matched"
                        ),
                        summary.path,
                        clause.line,
                        1,
                        "Move the named implicit to the LHS position dictated by the signature telescope.",
                        severity="warning",
                        confidence="high",
                    )
                )
    return out


def _imported_qualified_constructors(checker, summary) -> dict[str, set[str]]:
    """Map constructor basenames to non-open import aliases that own them."""

    opened_aliases = {item.alias for item in summary.ast.imports if item.opened}
    result: dict[str, set[str]] = {}
    for alias, interface in checker.imported_interfaces(summary).items():
        if alias in opened_aliases:
            continue
        constructors = set()
        for _datatype, names in interface.data_constructors:
            constructors.update(names)
        for record in interface.records:
            if record.constructor:
                constructors.add(record.constructor)
        for name in constructors:
            result.setdefault(name, set()).add(alias)
    return result


def _shadow_diagnostics(checker, summary) -> list[Diagnostic]:
    """Predict Agda PatternShadowsConstructor at user-authored binder clauses."""

    owners = _imported_qualified_constructors(checker, summary)
    if not owners:
        return []

    out: list[Diagnostic] = []
    seen: set[tuple[int, str]] = set()
    for clauses in summary.ast.clauses.values():
        for clause in clauses:
            lhs = clause.lhs_text
            if not lhs:
                continue
            head_match = re.match(rf"\s*{_WORD}", lhs)
            if head_match is None:
                continue
            tail_start = head_match.end()
            tail = lhs[tail_start:]
            for basename, aliases in owners.items():
                pattern = re.compile(
                    rf"(?<![A-Za-z0-9_'.]){re.escape(basename)}(?![A-Za-z0-9_'])"
                )
                match = pattern.search(tail)
                if match is None:
                    continue
                key = (clause.line, basename)
                if key in seen:
                    continue
                seen.add(key)
                alias = sorted(aliases)[0]
                prefix = lhs[: tail_start + match.start()]
                line_offset = prefix.count("\n")
                line = clause.line + line_offset
                last_newline = prefix.rfind("\n")
                column = (
                    tail_start + match.start() + 1
                    if last_newline < 0
                    else len(prefix) - last_newline
                )
                out.append(
                    Diagnostic(
                        "TSAGDA300",
                        f"pattern variable {basename} shadows constructor {alias}.{basename}",
                        summary.path,
                        line,
                        column,
                        "Rename the pattern binder to avoid constructor shadowing.",
                        severity="warning",
                        confidence="high",
                        evidence="dashi-index",
                        minimum_evidence="dashi-index",
                        evidence_sufficient=True,
                        root_cause=f"pattern binder shadows {alias}.{basename}",
                    )
                )
    return out


def install_checker_boundary_rules(Checker) -> None:
    """Install narrow compatibility rules around the tree-sitter/Agda boundary."""

    if getattr(Checker, "_dashi_boundary_rules_installed", False):
        return

    original_syntax = Checker._syntax_diagnostics
    original_structural = Checker.structural_check

    def syntax_with_known_gaps(self, summary):
        diagnostics = original_syntax(self, summary)
        diagnostics = [
            diagnostic
            for diagnostic in diagnostics
            if not (
                diagnostic.code == "TSAGDA000"
                and _is_constructor_field_transition_gap(summary.source, diagnostic.line)
            )
        ]
        diagnostics.extend(_lean_reverse_rewrite_diagnostics(summary))
        return diagnostics

    def structural_with_boundary_rules(self, path: Path):
        diagnostics = list(original_structural(self, path))
        summary = self.parse_summary(path)

        diagnostics = [
            diagnostic
            for diagnostic in diagnostics
            if not _visible_qualified_receiver(summary, diagnostic)
            and not _term_is_equality_operand(summary, diagnostic)
        ]

        additions = []
        additions.extend(_fragile_rewrite_diagnostics(summary))
        additions.extend(_record_universe_diagnostics(summary))
        additions.extend(_wrong_hiding_diagnostics(summary))
        additions.extend(_shadow_diagnostics(self, summary))

        existing = {(d.code, d.line, d.column, d.message) for d in diagnostics}
        for diagnostic in additions:
            key = (
                diagnostic.code,
                diagnostic.line,
                diagnostic.column,
                diagnostic.message,
            )
            if key not in existing:
                diagnostics.append(diagnostic)
                existing.add(key)

        diagnostics.sort(key=lambda d: (d.line, d.column, d.code, d.message))
        return diagnostics

    Checker._syntax_diagnostics = syntax_with_known_gaps
    Checker.structural_check = structural_with_boundary_rules
    Checker._dashi_boundary_rules_installed = True
