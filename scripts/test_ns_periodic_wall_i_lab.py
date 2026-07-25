#!/usr/bin/env python3
"""Fast regression checks for the Wall-I research scripts."""
from fractions import Fraction
import importlib.util
import py_compile
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
TARGET = HERE / "ns_periodic_wall_i_lab.py"
SWEEP = HERE / "ns_periodic_wall_i_sweep.py"
spec = importlib.util.spec_from_file_location("wall_i_lab", TARGET)
assert spec is not None and spec.loader is not None
lab = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = lab
spec.loader.exec_module(lab)


def main() -> int:
    assert len(lab.cube_modes(0)) == 1
    assert len(lab.cube_modes(2)) == 125
    shell = lab.verify_shell_profile(128)
    assert shell["partition_exact"]
    assert shell["worst_overlap"] <= 2
    assert lab.geometric_tail_exact(8, 1) == Fraction(1, 128)
    high = lab.far_high_tail_report(8, 7)
    assert high["two_placements"] == "1/64"
    assert high["fits_one_sixteenth"] is True
    report = lab.triad_geometry_report(1, 0, 2, 1)
    assert report.mode_count == report.expected_mode_count == 27
    assert report.triad_count > 0
    py_compile.compile(str(SWEEP), doraise=True)
    print("[ok] Wall-I laboratory regressions passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
