from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

from .agda import FileExtraction, build_semantic_graph
from .model import SemanticGraph


@dataclass(frozen=True)
class IncrementalImpactPlan:
    changed_paths: tuple[str, ...]
    changed_modules: tuple[str, ...]
    affected_modules: tuple[str, ...]
    reasons: tuple[tuple[str, str], ...]

    @property
    def is_empty(self) -> bool:
        return not self.affected_modules


def _qualified_module_hint(reference: str) -> str | None:
    if "." not in reference:
        return None
    pieces = reference.split(".")
    if len(pieces) < 2:
        return None
    return ".".join(pieces[:-1])


def plan_incremental_impact(
    before: Iterable[FileExtraction],
    after: Iterable[FileExtraction],
    changed_paths: Iterable[str],
) -> IncrementalImpactPlan:
    """Conservatively bound semantic re-resolution to affected modules.

    A changed module invalidates itself plus modules whose resolution evidence
    explicitly mentions it through import/open scope or a qualified reference.
    This intentionally does *not* use repository-wide bare-name uniqueness.
    """

    before = list(before)
    after = list(after)
    changed_paths = tuple(sorted(set(changed_paths)))

    before_by_path = {file.path: file for file in before}
    after_by_path = {file.path: file for file in after}

    changed_modules: set[str] = set()
    for path in changed_paths:
        old = before_by_path.get(path)
        new = after_by_path.get(path)
        if old is not None:
            changed_modules.add(old.module)
        if new is not None:
            changed_modules.add(new.module)

    affected = set(changed_modules)
    reasons: set[tuple[str, str]] = {
        (module, "changed-module")
        for module in changed_modules
    }

    # Resolve against the post-change source set, while retaining deleted-module
    # names from changed_modules above.
    for file in after:
        if file.module in changed_modules:
            continue

        imported = set(file.imports)
        opened = {scope.module for scope in file.open_scopes}
        touched = changed_modules & (imported | opened)
        for module in touched:
            affected.add(file.module)
            relation = (
                "opens-changed-module"
                if module in opened
                else "imports-changed-module"
            )
            reasons.add((file.module, f"{relation}:{module}"))

        qualified_hints: set[str] = set()
        for declaration in file.declarations:
            for reference in declaration.references:
                hint = _qualified_module_hint(reference.value)
                if hint is not None:
                    qualified_hints.add(hint)
                if reference.application_head:
                    head_hint = _qualified_module_hint(
                        reference.application_head
                    )
                    if head_hint is not None:
                        qualified_hints.add(head_hint)

        for module in changed_modules & qualified_hints:
            affected.add(file.module)
            reasons.add(
                (
                    file.module,
                    f"qualified-reference-to-changed-module:{module}",
                )
            )

    return IncrementalImpactPlan(
        changed_paths=changed_paths,
        changed_modules=tuple(sorted(changed_modules)),
        affected_modules=tuple(sorted(affected)),
        reasons=tuple(sorted(reasons)),
    )


@dataclass(frozen=True)
class IncrementalPatchReceipt:
    affected_modules: tuple[str, ...]
    removed_nodes: int
    added_nodes: int
    removed_edges: int
    added_edges: int
    unresolved_before: int
    unresolved_after: int
    parse_errors_before: int
    parse_errors_after: int


def patch_semantic_graph(
    previous: SemanticGraph,
    before: Iterable[FileExtraction],
    after: Iterable[FileExtraction],
    plan: IncrementalImpactPlan,
) -> tuple[SemanticGraph, IncrementalPatchReceipt]:
    """Replace only the affected semantic fragment.

    The fragment resolver still sees the full current source set, so qualified
    and open-scope resolution remains global where needed. Only owners in the
    affected module set emit replacement nodes/relations.
    """

    before = list(before)
    after = list(after)
    affected = set(plan.affected_modules)

    if not affected:
        clone = SemanticGraph(
            nodes=dict(previous.nodes),
            edges=dict(previous.edges),
            unresolved_references=list(previous.unresolved_references),
            parse_error_files=list(previous.parse_error_files),
        )
        return clone, IncrementalPatchReceipt(
            affected_modules=(),
            removed_nodes=0,
            added_nodes=0,
            removed_edges=0,
            added_edges=0,
            unresolved_before=len(previous.unresolved_references),
            unresolved_after=len(previous.unresolved_references),
            parse_errors_before=len(previous.parse_error_files),
            parse_errors_after=len(previous.parse_error_files),
        )

    fragment = build_semantic_graph(
        after,
        include_modules=affected,
    )

    removed_node_ids = {
        symbol_id
        for symbol_id, symbol in previous.nodes.items()
        if symbol.module in affected
    }
    kept_nodes = {
        symbol_id: symbol
        for symbol_id, symbol in previous.nodes.items()
        if symbol_id not in removed_node_ids
    }
    kept_edges = {
        relation_id: relation
        for relation_id, relation in previous.edges.items()
        if relation.source not in removed_node_ids
        and relation.target not in removed_node_ids
    }

    before_paths = {
        file.path
        for file in before
        if file.module in affected
    }
    after_paths = {
        file.path
        for file in after
        if file.module in affected
    }
    affected_paths = before_paths | after_paths

    kept_unresolved = [
        observation
        for observation in previous.unresolved_references
        if observation.get("owner") not in removed_node_ids
    ]
    kept_parse_errors = [
        path
        for path in previous.parse_error_files
        if path not in affected_paths
    ]

    result = SemanticGraph(
        nodes={**kept_nodes, **fragment.nodes},
        edges={**kept_edges, **fragment.edges},
        unresolved_references=(
            kept_unresolved
            + list(fragment.unresolved_references)
        ),
        parse_error_files=sorted(
            set(kept_parse_errors)
            | set(fragment.parse_error_files)
        ),
    )

    added_node_ids = set(fragment.nodes)
    added_edge_ids = set(fragment.edges)

    receipt = IncrementalPatchReceipt(
        affected_modules=tuple(sorted(affected)),
        removed_nodes=len(removed_node_ids),
        added_nodes=len(added_node_ids),
        removed_edges=len(previous.edges) - len(kept_edges),
        added_edges=len(added_edge_ids),
        unresolved_before=len(previous.unresolved_references),
        unresolved_after=len(result.unresolved_references),
        parse_errors_before=len(previous.parse_error_files),
        parse_errors_after=len(result.parse_error_files),
    )
    return result, receipt
