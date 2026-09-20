from __future__ import annotations

import argparse
import os
from pathlib import Path
import subprocess

from .git_history import HistoryExtractor


def _extract(args: argparse.Namespace) -> None:
    extractor = HistoryExtractor(
        Path(args.repo),
        path_prefix=args.path_prefix,
    )
    timeline = extractor.timeline(
        first_commits=args.first_commits,
        max_commits=args.max_commits,
        stride=args.stride,
        semantic=not args.history_only,
    )
    timeline.write_json(args.output)
    print(args.output)


def _render(args: argparse.Namespace) -> None:
    scene_file = Path(__file__).with_name("manim_backend.py")
    env = dict(os.environ)
    env["DASHI_REPO_HISTORY_JSON"] = str(Path(args.input).resolve())
    if args.snapshot_index is not None:
        env["DASHI_REPO_SNAPSHOT_INDEX"] = str(args.snapshot_index)
    if args.merge_index is not None:
        env["DASHI_REPO_MERGE_INDEX"] = str(args.merge_index)

    scene_by_mode = {
        "history": "RepositoryHistoryScene",
        "snapshot": "SemanticSnapshotScene",
        "semantic-history": "SemanticHistoryScene",
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
    window = extract.add_mutually_exclusive_group()
    window.add_argument("--first-commits", type=int)
    window.add_argument("--max-commits", type=int)
    extract.add_argument("--stride", type=int, default=1)
    extract.add_argument(
        "--history-only",
        action="store_true",
        help="Extract only commit/branch/merge topology; skip Tree-sitter semantic snapshots.",
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
        choices=["history", "snapshot", "semantic-history", "merge"],
        default="history",
    )
    render.add_argument("--snapshot-index", type=int)
    render.add_argument("--merge-index", type=int)
    render.set_defaults(func=_render)

    return parser


def main() -> None:
    parser = build_parser()
    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
