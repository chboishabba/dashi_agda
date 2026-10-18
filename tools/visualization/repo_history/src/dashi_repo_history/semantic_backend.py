from __future__ import annotations

from dataclasses import dataclass
import time
from typing import Iterable, Protocol

from .agda import FileExtraction
from .incremental import (
    IncrementalImpactPlan,
    IncrementalPatchReceipt,
    ResolutionImpactIndex,
    patch_semantic_graph,
    plan_incremental_impact,
    plan_incremental_impact_indexed,
)
from .model import SemanticGraph


@dataclass(frozen=True)
class SemanticPatchResult:
    graph: SemanticGraph
    plan: IncrementalImpactPlan
    receipt: IncrementalPatchReceipt
    plan_ns: int
    patch_ns: int


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
        before_index: ResolutionImpactIndex | None = None,
        after_index: ResolutionImpactIndex | None = None,
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
        before_index: ResolutionImpactIndex | None = None,
        after_index: ResolutionImpactIndex | None = None,
    ) -> SemanticPatchResult:
        before = list(before)
        after = list(after)
        plan_start = time.perf_counter_ns()
        if before_index is not None and after_index is not None:
            plan = plan_incremental_impact_indexed(
                before_index,
                after_index,
                changed_paths,
            )
        else:
            plan = plan_incremental_impact(
                before,
                after,
                changed_paths,
            )
        plan_ns = time.perf_counter_ns() - plan_start

        patch_start = time.perf_counter_ns()
        graph, receipt = patch_semantic_graph(
            previous,
            before,
            after,
            plan,
        )
        patch_ns = time.perf_counter_ns() - patch_start

        return SemanticPatchResult(
            graph=graph,
            plan=plan,
            receipt=receipt,
            plan_ns=plan_ns,
            patch_ns=patch_ns,
        )
