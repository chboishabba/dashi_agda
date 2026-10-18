from __future__ import annotations

import argparse
import asyncio
import json
from pathlib import Path


async def _run(server) -> dict:
    try:
        from mcp import Client
    except ImportError as error:  # pragma: no cover - optional runtime
        raise RuntimeError(
            "MCP support is not installed. Install "
            "tools/agda_preflight[mcp] on Python 3.10+."
        ) from error

    async with Client(server) as client:
        listed = await client.list_tools()
        tool_names = sorted(tool.name for tool in listed.tools)
        ping = await client.call_tool("ping", {})
        return {
            "tools": tool_names,
            "tool_count": len(tool_names),
            "ping_structured_content": ping.structured_content,
        }


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        prog="dashi-agda-mcp-smoke",
        description="In-process smoke test for the optional DASHI Agda MCP adapter",
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path.cwd(),
        help="repository root (default: current directory)",
    )
    parser.add_argument(
        "--index",
        type=Path,
        default=Path(".cache/agda_preflight/source-index.sqlite3"),
        help="persistent source-index database",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=0,
        help="cold-bootstrap workers; 0 = auto",
    )
    args = parser.parse_args(argv)

    from .mcp_server import create_mcp_server
    from .service import DashiAgdaService

    with DashiAgdaService(
        args.root,
        args.index,
        jobs=args.jobs,
    ) as service:
        result = asyncio.run(
            _run(create_mcp_server(service))
        )

    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
