from __future__ import annotations

import argparse
import json
from pathlib import Path

from .repository_store import DEFAULT_REPOSITORY_DB


def _common(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument(
        "--index",
        type=Path,
        default=DEFAULT_REPOSITORY_DB,
    )
    parser.add_argument("--json", action="store_true")


def build_semantic_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="dashi-agda")
    sub = parser.add_subparsers(dest="command", required=True)

    symbol = sub.add_parser("symbol", help="search repo-wide Agda symbols")
    symbol.add_argument("query")
    symbol.add_argument("--include-history", action="store_true")
    symbol.add_argument("--limit", type=int, default=50)
    _common(symbol)

    related = sub.add_parser("related", help="find equivalent/similar declarations")
    related.add_argument("symbol")
    related.add_argument("--include-history", action="store_true")
    related.add_argument("--limit", type=int, default=50)
    _common(related)

    obj = sub.add_parser("object", help="show an indexed object with status, requirements and references")
    obj.add_argument("symbol_id")
    _common(obj)

    archaeology = sub.add_parser("archaeology", help="search PR/commit development narrative")
    archaeology.add_argument("query")
    archaeology.add_argument("--limit", type=int, default=50)
    _common(archaeology)

    discover = sub.add_parser("discover", help="produce a fail-closed repository discovery/absence receipt")
    discover.add_argument("query")
    discover.add_argument("--limit", type=int, default=50)
    _common(discover)

    lineage = sub.add_parser("lineage", help="report RoundNNN lineage and snapshot noise")
    lineage.add_argument("--prefix")
    _common(lineage)
    return parser


def _print_payload(payload: dict, *, as_json: bool) -> None:
    if as_json:
        print(json.dumps(payload, indent=2, sort_keys=True))
        return
    if "results" in payload:
        for item in payload["results"]:
            location = ""
            if item.get("file") and item.get("line_start"):
                location = f" {item['file']}:{item['line_start']}"
            print(f"{item['qualified_name']} [{item['kind']}; {item['surface_role']}]{location}")
        if not payload["results"]:
            print("dashi-agda: no matching symbols")
        return
    # Legacy compatibility command. The canonical dashi-repo CLI uses tabular
    # human output; JSON remains only as this opt-in compatibility renderer.
    print(json.dumps(payload, indent=2, sort_keys=True))


def run_semantic_command(argv) -> int:
    from .service import DashiAgdaService

    args = build_semantic_parser().parse_args(argv)
    with DashiAgdaService(args.root, args.index) as service:
        if args.command == "symbol":
            payload = service.symbol_search(
                args.query,
                include_history=args.include_history,
                limit=args.limit,
            )
        elif args.command == "related":
            payload = service.related_symbols(
                args.symbol,
                include_history=args.include_history,
                limit=args.limit,
            )
        elif args.command == "object":
            payload = service.object_detail(args.symbol_id)
        elif args.command == "archaeology":
            payload = service.narrative_archaeology(args.query, limit=args.limit)
        elif args.command == "discover":
            payload = service.discover(args.query, limit=args.limit)
        elif args.command == "lineage":
            payload = service.round_lineage(prefix=args.prefix)
        else:  # pragma: no cover
            raise AssertionError(args.command)
    _print_payload(payload, as_json=args.json)
    return 0


def install_interactive_cli_semantic_extension(module) -> None:
    if getattr(module, "_semantic_discovery_installed", False):
        return
    original = module.main
    semantic_commands = {"symbol", "related", "object", "archaeology", "discover", "lineage"}

    def main(argv=None) -> int:
        import sys

        actual = list(sys.argv[1:] if argv is None else argv)
        if actual and actual[0] in semantic_commands:
            return run_semantic_command(actual)
        return original(argv)

    module.main = main
    module.build_semantic_parser = build_semantic_parser
    module._semantic_discovery_installed = True
