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
        max_commits: int | None = None,
        stride: int = 1,
    ) -> Timeline:
        all_commits = read_commit_dag(self.repo)
        refs = read_refs(self.repo)

        commits = all_commits
        if max_commits is not None:
            commits = commits[-max_commits:]
        if stride > 1:
            keep = commits[::stride]
            if commits and (not keep or keep[-1].commit != commits[-1].commit):
                keep.append(commits[-1])
            commits = keep

        snapshots: list[SemanticSnapshot] = []
        previous_commit: str | None = None
        previous_graph = None

        for record in commits:
            graph = self.graph_at(record.commit)
            delta = (
                None
                if previous_graph is None
                else GraphDelta.between(previous_graph, graph)
            )
            snapshots.append(
                SemanticSnapshot(
                    commit=record.commit,
                    graph=graph,
                    base_commit=previous_commit,
                    delta=delta,
                )
            )
            previous_commit = record.commit
            previous_graph = graph

        return Timeline(
            commits=commits,
            snapshots=snapshots,
            refs=refs,
        )
