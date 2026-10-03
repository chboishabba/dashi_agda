"""DASHI tree-sitter Agda preflight checker.

The checker core remains generic. Narrow compatibility rules for known
`tree-sitter-agda`/Agda boundary mismatches are installed here once at package
import so every CLI, service, pytest and MCP entrypoint sees the same behavior.
"""

from .checker import Checker, Diagnostic
from .boundary_rules import install_checker_boundary_rules

install_checker_boundary_rules(Checker)

__all__ = ["Checker", "Diagnostic"]
