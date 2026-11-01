#!/usr/bin/env python3
"""Fail-closed executable regression entrypoint for Karp's 21-problem programme.

Runs historical E01-E19 gadget fixtures (including E09/E11/E13/E16) and
the signed E20 Partition -> Max-Cut fixture. This is finite executable
regression only, never an Agda kernel or polynomial machine-time proof.
"""
from pathlib import Path
import subprocess
import sys

SCRIPTS = (
    "check_karp_historical_reductions.py",
    "check_karp_remaining_four_gadgets.py",
    "check_karp_partition_maxcut.py",
)


def main() -> None:
    root = Path(__file__).resolve().parent
    for script in SCRIPTS:
        print("KARP RUN:", script, flush=True)
        subprocess.run([sys.executable, str(root / script)], cwd=root, check=True)
    print("PASS KARP finite controls: 20 historical edges exercised; "
          "zero claims about Agda kernel acceptance or polynomial clocks")


if __name__ == "__main__":
    main()
