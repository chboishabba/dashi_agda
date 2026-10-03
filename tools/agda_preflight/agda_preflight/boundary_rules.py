from __future__ import annotations

from pathlib import Path
import re

from .checker import Diagnostic


_QUALIFIED_RECEIVER = re.compile(
    r"^(?P<head>[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_']*)+)"
    r"\s+(?P<receiver>[A-Za-z_][A-Za-z0-9_']*)"
)
_RECORD = re.compile(r"^\s*record\b")
_CONSTRUCTOR = re.compile(r"^\s*constructor\b")
_FIELD = re.compile(r"^\s*field\b")
_WORD = r"[A-Za-z_][A-Za-z0-9_']*"


def _line_text(source: str, line: int) -> str:
    """Return one 1-based source line, or an empty string out of range."""

    lines = source.splitlines()
    if 1 <= line <= len(lines):
        return lines[line - 1]
    return ""


def _is_constructor_field_transition_gap(source: str, line: int) -> bool:
    """Recognize the narrow valid-record layout tree-sitter-agda misparses.

    The grammar gap appears at/near a `constructor` immediately followed by
    `field` inside a record body. Suppression is deliberately local so a real
    syntax error elsewhere in the record is not hidden.
    """

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
    if constructor_index is None or field_index is None:
        return False
    if constructor_index >= field_index:
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
    """Return true when source text visibly supplies the reported receiver.

    TSAGDA049/052 historically trusted application_view for qualified
    projections. tree-sitter-agda can split `Render.klein R` such that the
    qualified head is indexed but its receiver is not attached to the same
    application node. A literal same-line receiver is enough to suppress that
    specific structural false positive; ambiguous layouts remain deferred to
    Agda scope evidence by policy.
    """

    if diagnostic.code not in {"TSAGDA049", "TSAGDA052"}:
        return False
    line = _line_text(summary.source, diagnostic.line)
    if not line or diagnostic.column < 1:
        return False
    tail = line[diagnostic.column - 1 :].strip()
    match = _QUALIFIED_RECEIVER.match(tail)
    if not match:
        return False
    head = match.group("head")
    if head not in diagnostic.message:
        return False
    receiver = match.group("receiver")
    return receiver not in {
        "where", "with", "rewrite", "in", "using", "hiding", "renaming",
    }


def _imported_qualified_constructors(checker, summary) -> dict[str, set[str]]:
    """Map constructor basenames to non-open import aliases that own them.

    Open imports are deliberately excluded: in that case an unqualified name
    can itself denote the constructor, so syntax/index evidence cannot safely
    classify the token as a shadowing variable.
    """

    opened_aliases = {
        item.alias
        for item in summary.ast.imports
        if item.opened
    }
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
    """Predict Agda PatternShadowsConstructor at user-authored binder clauses.

    Only constructors reachable through a non-open imported alias are used.
    Therefore an unqualified same-basename token on a recognized clause LHS
    cannot be that imported constructor. Generated with-clauses are not
    predicted: preflight reports the source binder that causes them instead.
    """

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
                # Operators/mixfix/otherwise unfamiliar clause heads stay on
                # the false-negative side until the AST exposes binders rigidly.
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
                        (
                            f"pattern variable {basename} shadows constructor "
                            f"{alias}.{basename}"
                        ),
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
    """Install narrow compatibility rules around the tree-sitter/Agda boundary.

    These wrappers deliberately leave the raw Diagnostic model unchanged. They
    suppress two known tree grammar/application false positives and add the
    conservative index-backed TSAGDA300 producer before optional Agda refinement.
    """

    if getattr(Checker, "_dashi_boundary_rules_installed", False):
        return

    original_syntax = Checker._syntax_diagnostics
    original_structural = Checker.structural_check

    def syntax_with_known_gaps(self, summary):
        """Filter only the bounded constructor→field grammar-gap TSAGDA000."""

        diagnostics = original_syntax(self, summary)
        return [
            diagnostic
            for diagnostic in diagnostics
            if not (
                diagnostic.code == "TSAGDA000"
                and _is_constructor_field_transition_gap(
                    summary.source,
                    diagnostic.line,
                )
            )
        ]

    def structural_with_boundary_rules(self, path: Path):
        """Refine structural false positives and append sound shadow warnings."""

        diagnostics = list(original_structural(self, path))
        summary = self.parse_summary(path)

        diagnostics = [
            diagnostic
            for diagnostic in diagnostics
            if not _visible_qualified_receiver(summary, diagnostic)
        ]

        existing = {
            (d.code, d.line, d.column, d.message)
            for d in diagnostics
        }
        for diagnostic in _shadow_diagnostics(self, summary):
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
