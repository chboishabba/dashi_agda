from __future__ import annotations

import argparse
import json
from pathlib import Path


def _common(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument(
        "--index",
        type=Path,
        default=Path(".cache/agda_preflight/source-index.sqlite3"),
    )
    parser.add_argument("--json", action="store_true")


def build_semantic_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="dashi-agda")
    sub = parser.add_subparsers(dest="command", required=True)

    symbol = sub.add_parser("symbol", help="search exact indexed Agda symbols")
    symbol.add_argument("query")
    symbol.add_argument("--include-history", action="store_true")
    symbol.add_argument("--limit", type=int, default=50)
    _common(symbol)

    related = sub.add_parser("related", help="find equivalent/similar declarations")
    related.add_argument("symbol")
    related.add_argument("--include-history", action="store_true")
    related.add_argument("--limit", type=int, default=50)
    _common(related)

    discover = sub.add_parser("discover", help="produce a repository discovery/absence receipt")
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
            print(f"{item['qualified_name']} [{item['kind']}; {item['surface_role']}]")
        if not payload["results"]:
            print("dashi-agda: no matching symbols")
        return
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
    semantic_commands = {"symbol", "related", "discover", "lineage"}

    def main(argv=None) -> int:
        import sys

        actual = list(sys.argv[1:] if argv is None else argv)
        if actual and actual[0] in semantic_commands:
            return run_semantic_command(actual)
        return original(argv)

    module.main = main
    module.build_semantic_parser = build_semantic_parser
    module._semantic_discovery_installed = True
