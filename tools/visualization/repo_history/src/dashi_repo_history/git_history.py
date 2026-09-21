from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
import subprocess

from .agda import AgdaLanguageAdapter
from .history_topology import derive_branch_episodes
from .language import LanguageAdapter
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

    def __post_init__(self) -> None:
        self.repo = self.repo.resolve()
        self._blob_cache: dict[tuple[str, str], object] = {}
        self._graph_cache = {}

    def graph_at(self, commit: str):
        if commit in self._graph_cache:
            return self._graph_cache[commit]

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
                extraction = self.adapter.extract_file(path, read_blob(self.repo, blob))
                self._blob_cache[key] = extraction
            extractions.append(extraction)

        graph = self.adapter.build_graph(extractions)
        self._graph_cache[commit] = graph
        return graph

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
