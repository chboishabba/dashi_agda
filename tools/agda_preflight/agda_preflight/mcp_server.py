from __future__ import annotations

import argparse
from pathlib import Path
from typing import Any, Optional

from .mcp_adapter import DashiAgdaMcpTools
from .service import DashiAgdaService


def register_mcp_tools(server: Any, tools: DashiAgdaMcpTools) -> None:
    """Register the stable DASHI Agda tool surface on an MCPServer-like object."""

    @server.tool()
    def diagnose(
        target: str,
        errors_only: bool = False,
    ) -> dict:
        """Diagnose a module/Everything rollup using the persistent source index.

        Read-only. Never invokes Agda. Returns diagnostics, semantic freshness
        when configured, cache-hit state, and per-request profiling metrics.
        """
        return tools.diagnose(
            target,
            errors_only=errors_only,
        )

    @server.tool()
    def next_error(
        target: str,
        require_fix: bool = False,
    ) -> dict:
        """Return the highest-priority current diagnostic for an agent.

        Read-only. Set require_fix=true to restrict results to diagnostics with
        suggested fixes. Never invokes Agda.
        """
        return tools.next_error(
            target,
            require_fix=require_fix,
        )

    @server.tool()
    def apply_fix(
        target: str,
        diagnostic_id: str,
        fix_index: int = 0,
        allow_likely: bool = False,
    ) -> dict:
        """Apply one exact suggested edit and immediately re-diagnose it.

        Mutates source files. Speculative fixes are rejected. Likely fixes
        require allow_likely=true. This tool itself never invokes Agda.
        """
        return tools.apply_fix(
            target,
            diagnostic_id,
            fix_index=fix_index,
            allow_likely=allow_likely,
        )

    @server.tool()
    def affected(target: str) -> dict:
        """Return the indexed reverse-import frontier after changing a module.

        Read-only. The changed module is first, followed by nearest consumers.
        """
        return tools.affected(target)

    @server.tool()
    def cache_status() -> dict:
        """Return persistent source-index/cache statistics. Read-only."""
        return tools.cache_status()

    @server.tool()
    def semantic_status(target: str) -> dict:
        """Report fresh/stale/unknown last-known semantic snapshots.

        Read-only. Never invokes Agda.
        """
        return tools.semantic_status(target)

    @server.tool()
    def promote(target: str) -> dict:
        """Explicitly run the configured fail-closed semantic promoter.

        This tool may invoke the configured external semantic checker. Success
        requires a fresh semantic catalog head matching the post-run source
        hash; process exit code zero alone is not sufficient.
        """
        return tools.promote(target)

    @server.tool()
    def promotion_history(
        module_name: Optional[str] = None,
        limit: int = 20,
    ) -> dict:
        """Return persisted semantic-promotion receipts. Read-only."""
        return tools.promotion_history(
            module_name=module_name,
            limit=limit,
        )

    @server.tool()
    def ping() -> dict:
        """Return a minimal liveness result."""
        return tools.ping()


def create_mcp_server(service: DashiAgdaService):
    """Create the optional SDK-v2 MCPServer around an existing service."""
    try:
        from mcp.server import MCPServer
    except ImportError as error:  # pragma: no cover - depends on optional extra
        raise RuntimeError(
            "MCP support is not installed. Install the optional extra with "
            "pip install -e 'tools/agda_preflight[mcp]' on Python 3.10+."
        ) from error

    server = MCPServer(
        "DASHI Agda",
        instructions=(
            "Fast incremental Agda source diagnostics and repair planning. "
            "diagnose/next_error/affected/cache_status/semantic_status are "
            "read-only and do not invoke Agda. apply_fix edits source only "
            "when an exact suggested edit exists. promote is the explicit "
            "fail-closed semantic-validation boundary."
        ),
    )
    register_mcp_tools(
        server,
        DashiAgdaMcpTools(service),
    )
    return server


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        prog="dashi-agda-mcp",
        description=(
            "MCP server for the long-lived DASHI Agda incremental analysis service"
        ),
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
    parser.add_argument(
        "--semantic-catalog",
        type=Path,
        help="optional agda2lean semantic catalog",
    )
    parser.add_argument(
        "--promoter-command",
        help=(
            "explicit semantic promotion command; supports {file}, {module}, "
            "{root}, {catalog}, and {receipt} placeholders"
        ),
    )
    parser.add_argument(
        "--promoter-timeout",
        type=float,
        default=900.0,
        help="promotion subprocess timeout in seconds (default: 900)",
    )
    parser.add_argument(
        "--transport",
        choices=("stdio", "streamable-http"),
        default="stdio",
        help="MCP transport (default: stdio)",
    )
    args = parser.parse_args(argv)

    with DashiAgdaService(
        args.root,
        args.index,
        jobs=args.jobs,
        semantic_catalog=args.semantic_catalog,
        promoter_command=args.promoter_command,
        promoter_timeout=args.promoter_timeout,
    ) as service:
        server = create_mcp_server(service)
        server.run(transport=args.transport)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
