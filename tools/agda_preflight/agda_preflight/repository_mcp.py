from __future__ import annotations

import argparse
from pathlib import Path

from .repository_store import DEFAULT_REPOSITORY_DB
from .service import DashiAgdaService
from .mcp_adapter import DashiAgdaMcpTools
from .mcp_server import create_mcp_server, register_repository_mcp_tools


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        prog="dashi-repo-mcp",
        description="Unified DASHI repository-intelligence MCP server.",
    )
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument(
        "--database",
        type=Path,
        default=DEFAULT_REPOSITORY_DB,
        help="single repository-intelligence SQLite database",
    )
    parser.add_argument("--jobs", type=int, default=0)
    parser.add_argument(
        "--transport",
        choices=("stdio", "streamable-http"),
        default="stdio",
    )
    args = parser.parse_args(argv)
    root = args.root.resolve()
    database = args.database if args.database.is_absolute() else root / args.database
    try:
        with DashiAgdaService(root, database, jobs=args.jobs) as service:
            server = create_mcp_server(service)
            register_repository_mcp_tools(server, DashiAgdaMcpTools(service))
            server.run(transport=args.transport)
    except ImportError as error:
        raise SystemExit(
            "MCP support is not installed. Install the optional mcp extra."
        ) from error
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
