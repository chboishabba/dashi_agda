from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, Protocol

from .agda import FileExtraction
from .incremental import (
    IncrementalImpactPlan,
    IncrementalPatchReceipt,
    patch_semantic_graph,
    plan_incremental_impact,
)
from .model import SemanticGraph


@dataclass(frozen=True)
class SemanticPatchResult:
    graph: SemanticGraph
    plan: IncrementalImpactPlan
    receipt: IncrementalPatchReceipt


class SemanticPatchBackend(Protocol):
    """Deterministic semantic patch engine.

    Parsing/extraction observations are inputs. The backend may not invent
    source authority and must return the same semantic graph contract as the
    Python reference implementation.
    """

    name: str

    def patch(
        self,
        *,
        previous: SemanticGraph,
        before: Iterable[FileExtraction],
        after: Iterable[FileExtraction],
        changed_paths: Iterable[str],
    ) -> SemanticPatchResult:
        ...


class PythonAffectedModuleBackend:
    name = "python-affected-module-v1"

    def patch(
        self,
        *,
        previous: SemanticGraph,
        before: Iterable[FileExtraction],
        after: Iterable[FileExtraction],
        changed_paths: Iterable[str],
    ) -> SemanticPatchResult:
        before = list(before)
        after = list(after)
        plan = plan_incremental_impact(
            before,
            after,
            changed_paths,
        )
        graph, receipt = patch_semantic_graph(
            previous,
            before,
            after,
            plan,
        )
        return SemanticPatchResult(
            graph=graph,
            plan=plan,
            receipt=receipt,
        )
