from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

from .agda import FileExtraction


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
