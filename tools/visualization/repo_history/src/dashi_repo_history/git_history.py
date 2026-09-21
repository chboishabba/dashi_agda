from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
import subprocess
import time

from .agda import AgdaLanguageAdapter
from .backend_policy import IncrementalStepTiming, decide_backend
from .history_topology import derive_branch_episodes
from .incremental import ResolutionImpactIndex
from .language import LanguageAdapter
from .semantic_backend import (
    PythonAffectedModuleBackend,
    SemanticPatchBackend,
)
from .model import CommitRecord, GraphDelta, SemanticSnapshot, Timeline


def _run_bytes(repo: Path, *args: str) -> bytes:
    return subprocess.check_output(["git", *args], cwd=repo)


def _run_text(repo: Path, *args: str) -> str:
    return _run_bytes(repo, *args).decode("utf-8", "replace")


def read_refs(repo: Path) -> dict[str, str]:
    raw = _run_text(
        repo,
        "for-each-ref",
        "--format=%(refname:short)%00%(objectname)",
        "refs/heads",
        "refs/remotes",
        "refs/tags",
    )
    refs: dict[str, str] = {}
    for line in raw.splitlines():
        if "\x00" not in line:
            continue
        name, sha = line.split("\x00", 1)
        refs[name] = sha
    return refs


def fetch_seed_commits(
    repo: Path,
    seeds: list[str],
    *,
    remote: str = "origin",
) -> None:
    for seed in seeds:
        subprocess.run(
            ["git", "fetch", "--no-tags", remote, seed],
            cwd=repo,
            check=True,
        )


def read_commit_dag(
    repo: Path,
    seeds: list[str] | None = None,
    history_refs: list[str] | None = None,
) -> list[CommitRecord]:
    live_refs = read_refs(repo)
    refs_by_sha: dict[str, list[str]] = {}
    for name, sha in live_refs.items():
        refs_by_sha.setdefault(sha, []).append(name)

    rev_args = [
        "rev-list",
        "--topo-order",
        "--reverse",
        "--parents",
        "--timestamp",
    ]
    if history_refs:
        rev_args.extend(history_refs)
    else:
        rev_args.append("--all")
    rev_args.extend(seeds or [])
    raw = _run_text(repo, *rev_args)
    commits: list[CommitRecord] = []
    for line in raw.splitlines():
        fields = line.split()
        if len(fields) < 2:
            continue
        timestamp = int(fields[0])
        commit = fields[1]
        parents = tuple(fields[2:])
        commits.append(
            CommitRecord(
                commit=commit,
                timestamp=timestamp,
                parents=parents,
                refs=tuple(sorted(refs_by_sha.get(commit, []))),
            )
        )
    return commits


def source_tree(
    repo: Path,
    commit: str,
    *,
    suffixes: tuple[str, ...],
    path_prefix: str | None = None,
) -> list[tuple[str, str]]:
    raw = _run_bytes(repo, "ls-tree", "-r", "-z", commit)
    entries: list[tuple[str, str]] = []
    for record in raw.split(b"\0"):
        if not record:
            continue
        metadata, path_bytes = record.split(b"\t", 1)
        path = path_bytes.decode("utf-8", "replace")
        if not path.endswith(suffixes):
            continue
        if path_prefix and not path.startswith(path_prefix):
            continue
        fields = metadata.decode("ascii", "replace").split()
        if len(fields) != 3:
            continue
        _mode, object_type, blob = fields
        if object_type != "blob":
            continue
        entries.append((path, blob))
    return entries


def read_blob(repo: Path, blob: str) -> bytes:
    return _run_bytes(repo, "cat-file", "-p", blob)


def changed_source_paths(
    repo: Path,
    parent: str,
    commit: str,
    *,
    suffixes: tuple[str, ...],
    path_prefix: str | None = None,
) -> list[str]:
    raw = _run_bytes(
        repo,
        "diff",
        "--name-only",
        "-z",
        parent,
        commit,
    )
    paths: list[str] = []
    for record in raw.split(b"\0"):
        if not record:
            continue
        path = record.decode("utf-8", "replace")
        if not path.endswith(suffixes):
            continue
        if path_prefix and not path.startswith(path_prefix):
            continue
        paths.append(path)
    return sorted(set(paths))


def select_commit_window(
    commits: list[CommitRecord],
    *,
    first_commits: int | None = None,
    max_commits: int | None = None,
    stride: int = 1,
) -> list[CommitRecord]:
    if first_commits is not None and max_commits is not None:
        raise ValueError("first_commits and max_commits are mutually exclusive")
    selected = commits
    if first_commits is not None:
        selected = selected[:first_commits]
    elif max_commits is not None:
        selected = selected[-max_commits:]

    if stride > 1:
        keep = selected[::stride]
        if selected and (not keep or keep[-1].commit != selected[-1].commit):
            keep.append(selected[-1])
        selected = keep
    return selected


def _episode_context_commits(
    all_commits: list[CommitRecord],
    selected: list[CommitRecord],
) -> tuple[list[CommitRecord], list]:
    """Close selected merge commits over their actual fork-to-parent paths."""

    all_episodes = derive_branch_episodes(all_commits)
    selected_ids = {commit.commit for commit in selected}
    relevant = [
        episode
        for episode in all_episodes
        if episode.merge_commit in selected_ids
    ]

    context_ids = set(selected_ids)
    for episode in relevant:
        context_ids.add(episode.fork_base)
        context_ids.add(episode.merge_commit)
        context_ids.update(episode.left_path)
        context_ids.update(episode.right_path)

    expanded = [
        commit
        for commit in all_commits
        if commit.commit in context_ids
    ]
    return expanded, relevant


@dataclass
class HistoryExtractor:
    repo: Path
    path_prefix: str | None = None
    seed_commits: tuple[str, ...] = ()
    history_refs: tuple[str, ...] = ()
    adapter: LanguageAdapter = field(default_factory=AgdaLanguageAdapter)
    patch_backend: SemanticPatchBackend = field(
        default_factory=PythonAffectedModuleBackend
    )
    parity_every: int = 0

    def __post_init__(self) -> None:
        self.repo = self.repo.resolve()
        self._blob_cache: dict[tuple[str, str], object] = {}
        self._extractions_cache: dict[str, list[object]] = {}
        self._graph_cache = {}
        self._impact_index_cache: dict[str, ResolutionImpactIndex] = {}
        self._incremental_receipts: dict[str, object] = {}
        self._incremental_timings: list[IncrementalStepTiming] = []
        self._incremental_step_count = 0
        self._parity_receipts: list[dict[str, object]] = []

    def extractions_at(self, commit: str) -> list[object]:
        cached = self._extractions_cache.get(commit)
        if cached is not None:
            return cached

        extractions: list[object] = []
        for path, blob in source_tree(
            self.repo,
            commit,
            suffixes=self.adapter.suffixes,
            path_prefix=self.path_prefix,
        ):
            key = (path, blob)
            extraction = self._blob_cache.get(key)
            if extraction is None:
                extraction = self.adapter.extract_file(
                    path,
                    read_blob(self.repo, blob),
                )
                self._blob_cache[key] = extraction
            extractions.append(extraction)

        self._extractions_cache[commit] = extractions
        return extractions

    def graph_at(self, commit: str):
        if commit in self._graph_cache:
            return self._graph_cache[commit]

        extractions = self.extractions_at(commit)
        graph = self.adapter.build_graph(extractions)
        self._graph_cache[commit] = graph
        if isinstance(self.adapter, AgdaLanguageAdapter):
            self._impact_index_cache[commit] = (
                ResolutionImpactIndex.from_files(extractions)
            )
        return graph

    def graph_from_parent(
        self,
        parent: str,
        commit: str,
    ):
        cached = self._graph_cache.get(commit)
        if not isinstance(self.adapter, AgdaLanguageAdapter):
            return self.graph_at(commit)
        if cached is not None:
            return cached

        parent_graph = self._graph_cache.get(parent)
        if parent_graph is None:
            return self.graph_at(commit)

        total_start = time.perf_counter_ns()
        before = self.extractions_at(parent)
        after = self.extractions_at(commit)
        changed = changed_source_paths(
            self.repo,
            parent,
            commit,
            suffixes=self.adapter.suffixes,
            path_prefix=self.path_prefix,
        )
        before_index = self._impact_index_cache.get(parent)
        if before_index is None:
            before_index = ResolutionImpactIndex.from_files(before)
            self._impact_index_cache[parent] = before_index

        after_by_path = {
            file.path: file
            for file in after
        }
        after_index = before_index.fork_apply(
            after_by_path,
            changed,
        )

        result = self.patch_backend.patch(
            previous=parent_graph,
            before=before,
            after=after,
            changed_paths=changed,
            before_index=before_index,
            after_index=after_index,
        )
        total_ns = time.perf_counter_ns() - total_start

        timing = IncrementalStepTiming(
            commit=commit,
            parent=parent,
            changed_paths=len(changed),
            affected_modules=len(result.plan.affected_modules),
            plan_ns=result.plan_ns,
            patch_ns=result.patch_ns,
            total_ns=total_ns,
            removed_nodes=result.receipt.removed_nodes,
            added_nodes=result.receipt.added_nodes,
            removed_edges=result.receipt.removed_edges,
            added_edges=result.receipt.added_edges,
            updated_nodes=result.receipt.updated_nodes,
            updated_edges=result.receipt.updated_edges,
            recomputed_nodes=result.receipt.recomputed_nodes,
            recomputed_edges=result.receipt.recomputed_edges,
        )

        graph = result.graph
        self._incremental_step_count += 1
        if (
            self.parity_every > 0
            and self._incremental_step_count % self.parity_every == 0
        ):
            full_start = time.perf_counter_ns()
            full_graph = self.adapter.build_graph(after)
            full_ns = time.perf_counter_ns() - full_start
            passed, details = self._graph_parity(
                graph,
                full_graph,
            )
            parity_receipt = {
                "commit": commit,
                "parent": parent,
                "passed": passed,
                "full_rebuild_ns": full_ns,
                **details,
            }
            self._parity_receipts.append(parity_receipt)
            if not passed:
                raise RuntimeError(
                    "incremental semantic parity failure at "
                    f"{commit}"
                )

        self._graph_cache[commit] = graph
        self._impact_index_cache[commit] = after_index
        self._incremental_receipts[commit] = result.receipt
        self._incremental_timings.append(timing)
        return graph

    @staticmethod
    def _graph_parity(
        left,
        right,
    ) -> tuple[bool, dict[str, int]]:
        left_unresolved = {
            (
                item.get("owner"),
                item.get("reference"),
                item.get("relation_kind"),
                item.get("scope"),
            )
            for item in left.unresolved_references
        }
        right_unresolved = {
            (
                item.get("owner"),
                item.get("reference"),
                item.get("relation_kind"),
                item.get("scope"),
            )
            for item in right.unresolved_references
        }

        details = {
            "left_nodes": len(left.nodes),
            "right_nodes": len(right.nodes),
            "left_edges": len(left.edges),
            "right_edges": len(right.edges),
            "left_unresolved": len(left_unresolved),
            "right_unresolved": len(right_unresolved),
        }
        equal = (
            left.nodes == right.nodes
            and left.edges == right.edges
            and left_unresolved == right_unresolved
            and set(left.parse_error_files)
            == set(right.parse_error_files)
        )
        return equal, details

    def performance_report(self) -> dict[str, object]:
        decision = decide_backend(self._incremental_timings)
        return {
            "schema": "dashi.repo-history-performance.v1",
            "incremental_steps": [
                timing.to_dict()
                for timing in self._incremental_timings
            ],
            "backend_decision": decision.to_dict(),
            "parity_receipts": list(self._parity_receipts),
            "parity_all_passed": all(
                bool(receipt.get("passed"))
                for receipt in self._parity_receipts
            ),
            "backend": getattr(
                self.patch_backend,
                "name",
                type(self.patch_backend).__name__,
            ),
            "notes": {
                "python_is_reference": True,
                "rust_candidate_requires_gate": True,
                "high_fanout_means_fix_invalidation_first": True,
            },
        }

    def timeline(
        self,
        *,
        first_commits: int | None = None,
        max_commits: int | None = None,
        stride: int = 1,
        semantic: bool = True,
        episode_context: bool = False,
    ) -> Timeline:
        refs = read_refs(self.repo)
        all_commits = read_commit_dag(
            self.repo,
            list(self.seed_commits),
            list(self.history_refs),
        )
        commits = select_commit_window(
            all_commits,
            first_commits=first_commits,
            max_commits=max_commits,
            stride=stride,
        )

        all_episodes = derive_branch_episodes(all_commits)
        selected_ids = {commit.commit for commit in commits}
        branch_episodes = [
            episode
            for episode in all_episodes
            if episode.merge_commit in selected_ids
        ]

        if episode_context:
            commits, branch_episodes = _episode_context_commits(
                all_commits,
                commits,
            )

        if not semantic:
            return Timeline(
                commits=commits,
                snapshots=[],
                refs=refs,
                branch_episodes=branch_episodes,
            )

        snapshots: list[SemanticSnapshot] = []

        for record in commits:
            first_parent = (
                record.parents[0]
                if record.parents
                else None
            )
            if (
                first_parent is not None
                and first_parent in self._graph_cache
            ):
                graph = self.graph_from_parent(
                    first_parent,
                    record.commit,
                )
            else:
                graph = self.graph_at(record.commit)

            parent_deltas: dict[str, GraphDelta] = {}
            for parent in record.parents:
                parent_graph = self.graph_at(parent)
                parent_deltas[parent] = GraphDelta.between(parent_graph, graph)

            snapshots.append(
                SemanticSnapshot(
                    commit=record.commit,
                    graph=graph,
                    parent_deltas=parent_deltas,
                )
            )

        return Timeline(
            commits=commits,
            snapshots=snapshots,
            refs=refs,
            branch_episodes=branch_episodes,
        )
