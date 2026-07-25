#!/usr/bin/env python3
"""Run the legacy physical-progress audit plus the exact C1 frontier audit.

The legacy implementation is preserved verbatim in
``check_ym_physical_progress_legacy.py``.  This wrapper updates the one status
that advanced in PR #335, then executes both fail-closed audits.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path
import runpy

ROOT = Path(__file__).resolve().parents[1]
LEGACY = Path(__file__).with_name("check_ym_physical_progress_legacy.py")


def load_legacy():
    spec = importlib.util.spec_from_file_location("ym_physical_progress_legacy", LEGACY)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load legacy audit from {LEGACY}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main() -> None:
    legacy = load_legacy()

    translated = legacy.YM / "BalabanConfiguredSideTranslatedBlockExact.agda"
    required = tuple(
        item
        for item in legacy.FILES[translated]
        if item != "globalWilsonToLocalTranslatedBlockLevel = conditional"
    )
    legacy.FILES[translated] = required + (
        "arbitraryLatticeOpenBlockWilsonExtractionLevel = machineChecked",
        "repositorySUNWilsonActionHessianAdapterLevel = conditional",
    )

    legacy.main()
    runpy.run_path(
        str(ROOT / "scripts/check_ym_c1_exact_cutset.py"),
        run_name="__main__",
    )


if __name__ == "__main__":
    main()
