"""DASHI tree-sitter Agda preflight checker.

The checker core remains generic. Narrow compatibility rules for known
`tree-sitter-agda`/Agda boundary mismatches are installed here once at package
import so every CLI, service, pytest and MCP entrypoint sees the same behavior.
"""

from .checker import Checker, Diagnostic
from .boundary_rules import install_checker_boundary_rules
from .boundary_refinements import install_boundary_refinements
from .integration_refinements import install_scope_refinements
from .source_index import SourceIndex
from .semantic_extension import install_source_index_semantic_extension

install_checker_boundary_rules(Checker)
install_boundary_refinements(Checker)
install_scope_refinements()
install_source_index_semantic_extension(SourceIndex)

from .service import DashiAgdaService
from .service_semantic_extension import install_service_semantic_extension
from .mcp_adapter import DashiAgdaMcpTools
from .mcp_semantic_extension import (
    install_mcp_adapter_semantic_extension,
    install_mcp_server_semantic_extension,
)
from . import mcp_server as _mcp_server
from . import interactive_cli as _interactive_cli
from .interactive_cli_semantic_extension import install_interactive_cli_semantic_extension

install_service_semantic_extension(DashiAgdaService)
install_mcp_adapter_semantic_extension(DashiAgdaMcpTools)
install_mcp_server_semantic_extension(_mcp_server)
install_interactive_cli_semantic_extension(_interactive_cli)

__all__ = ["Checker", "Diagnostic", "SourceIndex", "DashiAgdaService"]
