from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess

from .git_history import HistoryExtractor, fetch_seed_commits
from .merge_attribution import attribute_merge


def _extract(args: argparse.Namespace) -> None:
    repo = Path(args.repo)
    if args.fetch_seeds and args.seed_commit:
        fetch_seed_commits(
            repo,
            list(args.seed_commit),
            remote=args.remote,
        )
    extractor = HistoryExtractor(
        repo,
        path_prefix=args.path_prefix,
        seed_commits=tuple(args.seed_commit or ()),
    )
    timeline = extractor.timeline(
        first_commits=args.first_commits,
        max_commits=args.max_commits,
        stride=args.stride,
        semantic=not args.history_only,
        episode_context=args.episode_context,
    )
    timeline.write_json(args.output)
    print(args.output)


def _render(args: argparse.Namespace) -> None:
    scene_file = Path(__file__).with_name("manim_backend.py")
    env = dict(os.environ)
    env["DASHI_REPO_HISTORY_JSON"] = str(Path(args.input).resolve())
    if args.snapshot_index is not None:
        env["DASHI_REPO_SNAPSHOT_INDEX"] = str(args.snapshot_index)
    if args.episode_index is not None:
        env["DASHI_REPO_EPISODE_INDEX"] = str(args.episode_index)
    if args.target_commit is not None:
        env["DASHI_REPO_TARGET_COMMIT"] = str(args.target_commit)
    if args.symbol is not None:
        env["DASHI_REPO_SYMBOL"] = str(args.symbol)
    env["DASHI_REPO_UPSTREAM_DEPTH"] = str(args.upstream_depth)
    env["DASHI_REPO_DOWNSTREAM_DEPTH"] = str(args.downstream_depth)

    scene_by_mode = {
        "history": "RepositoryHistoryScene",
        "snapshot": "SemanticSnapshotScene",
        "symbol": "SemanticSymbolScene",
        "semantic-history": "SemanticHistoryScene",
        "episode": "SemanticBranchEpisodeScene",
        "merge": "SemanticMergeScene",
    }
    scene = scene_by_mode[args.scene]
    subprocess.run(
        [
            "python",
            "-m",
            "manim",
            args.quality,
            str(scene_file),
            scene,
        ],
        env=env,
        check=True,
    )


def _symbols(args: argparse.Namespace) -> None:
    data = json.loads(Path(args.input).read_text(encoding="utf-8"))
    snapshots = data.get("snapshots", [])
    if not snapshots:
        raise SystemExit("No semantic snapshots in input.")

    snapshot = snapshots[args.snapshot_index]
    query = (args.query or "").lower()
    rows = []
    for node in snapshot["graph"].get("nodes", []):
        qualified = f"{node.get('module')}::{node.get('label')}"
        haystack = " ".join(
            [
                qualified,
                str(node.get("kind", "")),
                str(node.get("scope", "")),
            ]
        ).lower()
        if query and query not in haystack:
            continue
        rows.append(
            {
                "selector": qualified,
                "symbol_id": node["symbol_id"],
                "kind": node.get("kind"),
                "module": node.get("module"),
                "label": node.get("label"),
                "scope": node.get("scope"),
            }
        )

    rows.sort(
        key=lambda row: (
            str(row["module"]),
            str(row["label"]),
            str(row["scope"]),
        )
    )

    if args.json:
        print(json.dumps(rows, indent=2))
        return

    for row in rows[: args.limit]:
        scope = (
            f" scope={str(row['scope'])[:16]}"
            if row["scope"]
            else ""
        )
        print(
            f"{row['selector']} "
            f"[{row['kind']}] "
            f"id={row['symbol_id'][:12]}"
            f"{scope}"
        )


def _episodes(args: argparse.Namespace) -> None:
    data = json.loads(Path(args.input).read_text(encoding="utf-8"))
    commits = {
        commit["commit"]: commit
        for commit in data.get("commits", [])
    }
    snapshots = {
        snapshot["commit"]: snapshot
        for snapshot in data.get("snapshots", [])
    }

    rows = []
    for index, episode in enumerate(data.get("branch_episodes", [])):
        row = {
            "index": index,
            "fork_base": episode["fork_base"],
            "left_tip": episode["left_tip"],
            "right_tip": episode["right_tip"],
            "merge_commit": episode["merge_commit"],
            "left_steps": max(0, len(episode["left_path"]) - 1),
            "right_steps": max(0, len(episode["right_path"]) - 1),
        }

        merge_sha = episode["merge_commit"]
        if (
            merge_sha in commits
            and merge_sha in snapshots
            and episode["left_tip"] in snapshots
            and episode["right_tip"] in snapshots
        ):
            attribution = attribute_merge(
                merge_commit=commits[merge_sha],
                snapshots_by_commit=snapshots,
            )
            row.update(
                {
                    "merge_only_nodes": len(attribution.introduced_nodes),
                    "merge_only_edges": len(attribution.introduced_edges),
                    "left_only_nodes": len(
                        attribution.parent_only_nodes.get(
                            episode["left_tip"],
                            (),
                        )
                    ),
                    "right_only_nodes": len(
                        attribution.parent_only_nodes.get(
                            episode["right_tip"],
                            (),
                        )
                    ),
                }
            )
        rows.append(row)

    if args.json:
        print(json.dumps(rows, indent=2))
        return

    for row in rows:
        print(
            f"[{row['index']}] "
            f"fork={row['fork_base'][:10]} "
            f"left={row['left_tip'][:10]}({row['left_steps']}) "
            f"right={row['right_tip'][:10]}({row['right_steps']}) "
            f"merge={row['merge_commit'][:10]} "
            f"merge-only-nodes={row.get('merge_only_nodes', '?')}"
        )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="dashi-repo-history",
        description="Extract and render temporal Git + Agda semantic graphs.",
    )
    sub = parser.add_subparsers(dest="command", required=True)

    extract = sub.add_parser("extract")
    extract.add_argument("repo")
    extract.add_argument("-o", "--output", default="repo-history.json")
    extract.add_argument("--path-prefix")
    extract.add_argument(
        "--seed-commit",
        action="append",
        help="Include an explicit historical commit root, including commits no longer reachable from live refs.",
    )
    extract.add_argument(
        "--fetch-seeds",
        action="store_true",
        help="Fetch each seed commit from the selected remote before traversal.",
    )
    extract.add_argument("--remote", default="origin")
    window = extract.add_mutually_exclusive_group()
    window.add_argument("--first-commits", type=int)
    window.add_argument("--max-commits", type=int)
    extract.add_argument("--stride", type=int, default=1)
    extract.add_argument(
        "--history-only",
        action="store_true",
        help="Extract only commit/branch/merge topology; skip Tree-sitter semantic snapshots.",
    )
    extract.add_argument(
        "--episode-context",
        action="store_true",
        help="For selected merge commits, include the real fork base and both branch paths in the timeline.",
    )
    extract.set_defaults(func=_extract)

    render = sub.add_parser("render")
    render.add_argument("input")
    render.add_argument(
        "--quality",
        default="-ql",
        choices=["-ql", "-qm", "-qh", "-qk"],
    )
    render.add_argument(
        "--scene",
        choices=["history", "snapshot", "symbol", "semantic-history", "episode", "merge"],
        default="history",
    )
    render.add_argument("--snapshot-index", type=int)
    render.add_argument("--episode-index", type=int)
    render.add_argument(
        "--symbol",
        help="Semantic symbol id or unique label for the rooted symbol scene.",
    )
    render.add_argument("--upstream-depth", type=int, default=2)
    render.add_argument("--downstream-depth", type=int, default=0)
    render.add_argument(
        "--target-commit",
        help="Target commit for the first-parent semantic-history lineage.",
    )
    render.set_defaults(func=_render)

    symbols = sub.add_parser(
        "symbols",
        help="List semantic symbols and stable selectors in one snapshot.",
    )
    symbols.add_argument("input")
    symbols.add_argument("--snapshot-index", type=int, default=-1)
    symbols.add_argument("--query")
    symbols.add_argument("--limit", type=int, default=100)
    symbols.add_argument("--json", action="store_true")
    symbols.set_defaults(func=_symbols)

    episodes = sub.add_parser(
        "episodes",
        help="List derived fork/merge episodes and semantic contribution counts.",
    )
    episodes.add_argument("input")
    episodes.add_argument("--json", action="store_true")
    episodes.set_defaults(func=_episodes)

    return parser


def main() -> None:
    parser = build_parser()
    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
