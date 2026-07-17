#!/usr/bin/env python3
"""Public entry point for generic DASHI Agda term-flow visualisation.

This compatibility layer enriches declarations produced by the older shared
source scanner with a derived end line, then exposes the root-driven term-flow
builder and renderer. Configurations still contain roots and limits only.
"""
from __future__ import annotations

import materialize_dashi_agda_termflow as core


_original_scan_repo = core.scan_repo


def _scan_repo_with_ranges(root):
    declarations = _original_scan_repo(root)
    for declaration in declarations.values():
        if not hasattr(declaration, "end_line"):
            body_lines = len(declaration.body.splitlines()) if declaration.body else 0
            declaration.end_line = declaration.line + max(0, body_lines - 1)
    return declarations


core.scan_repo = _scan_repo_with_ranges

SCHEMA = core.SCHEMA
TermFlowError = core.TermFlowError
build_ir = core.build_ir
render_svg = core.render_svg


if __name__ == "__main__":
    raise SystemExit(core.main())
