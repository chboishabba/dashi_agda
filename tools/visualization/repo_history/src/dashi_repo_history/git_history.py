from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import subprocess

from .agda import FileExtraction, build_semantic_graph, extract_file
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


def read_commit_dag(repo: Path) -> list[CommitRecord]:
    refs = read_refs(repo)
    refs_by_sha: dict[str, list[str]] = {}
    for name, sha in refs.items():
        refs_by_sha.setdefault(sha, []).append(name)

    raw = _run_text(
        repo,
        "rev-list",
        "--all",
        "--topo-order",
        "--reverse",
        "--parents",
        "--timestamp",
    )
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


def agda_tree(
    repo: Path,
    commit: str,
    path_prefix: str | None = None,
) -> list[tuple[str, str]]:
    raw = _run_bytes(repo, "ls-tree", "-r", "-z", commit)
    entries: list[tuple[str, str]] = []
    for record in raw.split(b"\0"):
        if not record:
            continue
        metadata, path_bytes = record.split(b"\t", 1)
        path = path_bytes.decode("utf-8", "replace")
        if not path.endswith(".agda"):
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


@dataclass
class HistoryExtractor:
    repo: Path
    path_prefix: str | None = None

    def __post_init__(self) -> None:
        self.repo = self.repo.resolve()
        self._blob_cache: dict[tuple[str, str], FileExtraction] = {}
        self._graph_cache = {}

    def graph_at(self, commit: str):
        if commit in self._graph_cache:
            return self._graph_cache[commit]

        extractions: list[FileExtraction] = []
        for path, blob in agda_tree(self.repo, commit, self.path_prefix):
            key = (path, blob)
            extraction = self._blob_cache.get(key)
            if extraction is None:
                extraction = extract_file(path, read_blob(self.repo, blob))
                self._blob_cache[key] = extraction
            extractions.append(extraction)

        graph = build_semantic_graph(extractions)
        self._graph_cache[commit] = graph
        return graph

    def timeline(
        self,
        *,
        first_commits: int | None = None,
        max_commits: int | None = None,
        stride: int = 1,
        semantic: bool = True,
    ) -> Timeline:
        refs = read_refs(self.repo)
        commits = select_commit_window(
            read_commit_dag(self.repo),
            first_commits=first_commits,
            max_commits=max_commits,
            stride=stride,
        )

        if not semantic:
            return Timeline(
                commits=commits,
                snapshots=[],
                refs=refs,
            )

        snapshots: list[SemanticSnapshot] = []

        for record in commits:
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
        )
