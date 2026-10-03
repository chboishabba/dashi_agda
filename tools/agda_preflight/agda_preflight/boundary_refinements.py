from __future__ import annotations

from .ast_index import significant_tokens
from .checker import Diagnostic
from . import boundary_rules


def _shadow_diagnostics(checker, summary) -> list[Diagnostic]:
    """Predict constructor shadowing conservatively from whole Agda tokens.

    Exact token equality avoids partial matches inside names such as `pair-x`
    and `pair₁`. Named implicit labels (`{pair = ...}`) are not binders for this
    warning. The prediction remains advisory until Agda scope confirms it.
    """

    owners = boundary_rules._imported_qualified_constructors(checker, summary)
    if not owners:
        return []

    out: list[Diagnostic] = []
    seen: set[tuple[int, int, str]] = set()
    for clauses in summary.ast.clauses.values():
        for clause in clauses:
            tokens = significant_tokens(summary.ast.source_bytes, clause.lhs_node)
            if len(tokens) <= 1:
                continue
            # The first significant token is the defining function head. Every
            # later candidate must be one complete unqualified token.
            for index, token in enumerate(tokens[1:], 1):
                basename = token.text
                aliases = owners.get(basename)
                if not aliases or "." in basename:
                    continue
                next_text = tokens[index + 1].text if index + 1 < len(tokens) else None
                prev_text = tokens[index - 1].text if index > 0 else None
                if next_text == "=" or prev_text == ".":
                    continue
                key = (token.line, token.column, basename)
                if key in seen:
                    continue
                seen.add(key)
                alias = sorted(aliases)[0]
                out.append(
                    Diagnostic(
                        "TSAGDA300",
                        f"pattern variable {basename} may shadow constructor {alias}.{basename}",
                        summary.path,
                        token.line,
                        token.column,
                        "Agda scope checking can confirm this constructor-shadowing warning.",
                        severity="warning",
                        confidence="insufficient-evidence",
                        evidence="dashi-index",
                        minimum_evidence="agda-scope",
                        evidence_sufficient=False,
                        root_cause=f"possible pattern binder shadow of {alias}.{basename}",
                    )
                )
    return out


def install_boundary_refinements() -> None:
    """Install conservative post-review refinements for boundary diagnostics."""

    boundary_rules._shadow_diagnostics = _shadow_diagnostics
