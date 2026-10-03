"""DASHI tree-sitter Agda preflight checker."""

from .checker import Checker, Diagnostic
from .boundary_rules import install_checker_boundary_rules

install_checker_boundary_rules(Checker)

__all__ = ["Checker", "Diagnostic"]
