from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

from .agda import FileExtraction, build_semantic_graph
from .model import SemanticGraph


@dataclass(frozen=True)
class FileResolutionDeps:
    path: str
    module: str
    imports: frozenset[str]
    opens: frozenset[str]
    qualified_hints: frozenset[str]


def _file_resolution_deps(file: FileExtraction) -> FileResolutionDeps:
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

    return FileResolutionDeps(
        path=file.path,
        module=file.module,
        imports=frozenset(file.imports),
        opens=frozenset(
            scope.module
            for scope in file.open_scopes
        ),
        qualified_hints=frozenset(qualified_hints),
    )


@dataclass(frozen=True)
class ResolutionImpactIndex:
    by_path: dict[str, FileResolutionDeps]
    importers_by_target: dict[str, frozenset[str]]
    openers_by_target: dict[str, frozenset[str]]
    qualified_users_by_target: dict[str, frozenset[str]]

    @classmethod
    def from_files(
        cls,
        files: Iterable[FileExtraction],
    ) -> "ResolutionImpactIndex":
        by_path = {
            file.path: _file_resolution_deps(file)
            for file in files
        }
        return cls._from_path_map(by_path)

    @classmethod
    def _from_path_map(
        cls,
        by_path: dict[str, FileResolutionDeps],
    ) -> "ResolutionImpactIndex":
        importers: dict[str, set[str]] = {}
        openers: dict[str, set[str]] = {}
        qualified: dict[str, set[str]] = {}

        for deps in by_path.values():
            for target in deps.imports:
                importers.setdefault(target, set()).add(deps.module)
            for target in deps.opens:
                openers.setdefault(target, set()).add(deps.module)
            for target in deps.qualified_hints:
                qualified.setdefault(target, set()).add(deps.module)

        return cls(
            by_path=dict(by_path),
            importers_by_target={
                target: frozenset(users)
                for target, users in importers.items()
            },
            openers_by_target={
                target: frozenset(users)
                for target, users in openers.items()
            },
            qualified_users_by_target={
                target: frozenset(users)
                for target, users in qualified.items()
            },
        )

    def fork_apply(
        self,
        after_files_by_path: dict[str, FileExtraction],
        changed_paths: Iterable[str],
    ) -> "ResolutionImpactIndex":
        """Copy-on-write update of resolution evidence for changed files only."""

        changed_paths = tuple(sorted(set(changed_paths)))
        by_path = dict(self.by_path)

        importers = dict(self.importers_by_target)
        openers = dict(self.openers_by_target)
        qualified = dict(self.qualified_users_by_target)

        def remove_user(
            table: dict[str, frozenset[str]],
            target: str,
            module: str,
        ) -> None:
            current = table.get(target, frozenset())
            if module not in current:
                return
            updated = current - {module}
            if updated:
                table[target] = frozenset(updated)
            else:
                table.pop(target, None)

        def add_user(
            table: dict[str, frozenset[str]],
            target: str,
            module: str,
        ) -> None:
            current = table.get(target, frozenset())
            if module in current:
                return
            table[target] = frozenset((*current, module))

        for path in changed_paths:
            old = by_path.pop(path, None)
            if old is not None:
                for target in old.imports:
                    remove_user(importers, target, old.module)
                for target in old.opens:
                    remove_user(openers, target, old.module)
                for target in old.qualified_hints:
                    remove_user(qualified, target, old.module)

            new_file = after_files_by_path.get(path)
            if new_file is None:
                continue

            new = _file_resolution_deps(new_file)
            by_path[path] = new
            for target in new.imports:
                add_user(importers, target, new.module)
            for target in new.opens:
                add_user(openers, target, new.module)
            for target in new.qualified_hints:
                add_user(qualified, target, new.module)

        return ResolutionImpactIndex(
            by_path=by_path,
            importers_by_target=importers,
            openers_by_target=openers,
            qualified_users_by_target=qualified,
        )


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


def plan_incremental_impact_indexed(
    before_index: ResolutionImpactIndex,
    after_index: ResolutionImpactIndex,
    changed_paths: Iterable[str],
) -> IncrementalImpactPlan:
    changed_paths = tuple(sorted(set(changed_paths)))
    changed_modules: set[str] = set()

    for path in changed_paths:
        old = before_index.by_path.get(path)
        new = after_index.by_path.get(path)
        if old is not None:
            changed_modules.add(old.module)
        if new is not None:
            changed_modules.add(new.module)

    affected = set(changed_modules)
    reasons: set[tuple[str, str]] = {
        (module, "changed-module")
        for module in changed_modules
    }

    for changed_module in sorted(changed_modules):
        for consumer in after_index.importers_by_target.get(
            changed_module,
            frozenset(),
        ):
            affected.add(consumer)
            reasons.add(
                (
                    consumer,
                    f"imports-changed-module:{changed_module}",
                )
            )

        for consumer in after_index.openers_by_target.get(
            changed_module,
            frozenset(),
        ):
            affected.add(consumer)
            reasons.add(
                (
                    consumer,
                    f"opens-changed-module:{changed_module}",
                )
            )

        for consumer in after_index.qualified_users_by_target.get(
            changed_module,
            frozenset(),
        ):
            affected.add(consumer)
            reasons.add(
                (
                    consumer,
                    "qualified-reference-to-changed-module:"
                    f"{changed_module}",
                )
            )

    return IncrementalImpactPlan(
        changed_paths=changed_paths,
        changed_modules=tuple(sorted(changed_modules)),
        affected_modules=tuple(sorted(affected)),
        reasons=tuple(sorted(reasons)),
    )


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
    updated_nodes: int
    removed_edges: int
    added_edges: int
    updated_edges: int
    recomputed_nodes: int
    recomputed_edges: int
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
            updated_nodes=0,
            removed_edges=0,
            added_edges=0,
            updated_edges=0,
            recomputed_nodes=0,
            recomputed_edges=0,
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

    old_affected_nodes = {
        symbol_id: symbol
        for symbol_id, symbol in previous.nodes.items()
        if symbol.module in affected
    }
    old_affected_node_ids = set(old_affected_nodes)
    new_affected_node_ids = set(fragment.nodes)

    old_touching_edges = {
        relation_id: relation
        for relation_id, relation in previous.edges.items()
        if relation.source in old_affected_node_ids
        or relation.target in old_affected_node_ids
    }
    new_touching_edges = dict(fragment.edges)

    semantic_removed_nodes = (
        old_affected_node_ids - new_affected_node_ids
    )
    semantic_added_nodes = (
        new_affected_node_ids - old_affected_node_ids
    )
    semantic_updated_nodes = {
        node_id
        for node_id in old_affected_node_ids & new_affected_node_ids
        if old_affected_nodes[node_id] != fragment.nodes[node_id]
    }

    old_edge_ids = set(old_touching_edges)
    new_edge_ids = set(new_touching_edges)
    semantic_removed_edges = old_edge_ids - new_edge_ids
    semantic_added_edges = new_edge_ids - old_edge_ids
    semantic_updated_edges = {
        edge_id
        for edge_id in old_edge_ids & new_edge_ids
        if old_touching_edges[edge_id]
        != new_touching_edges[edge_id]
    }

    receipt = IncrementalPatchReceipt(
        affected_modules=tuple(sorted(affected)),
        removed_nodes=len(semantic_removed_nodes),
        added_nodes=len(semantic_added_nodes),
        updated_nodes=len(semantic_updated_nodes),
        removed_edges=len(semantic_removed_edges),
        added_edges=len(semantic_added_edges),
        updated_edges=len(semantic_updated_edges),
        recomputed_nodes=len(fragment.nodes),
        recomputed_edges=len(fragment.edges),
        unresolved_before=len(previous.unresolved_references),
        unresolved_after=len(result.unresolved_references),
        parse_errors_before=len(previous.parse_error_files),
        parse_errors_after=len(result.parse_error_files),
    )
    return result, receipt
