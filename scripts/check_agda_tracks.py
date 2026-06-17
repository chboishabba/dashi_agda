#!/usr/bin/env python3
"""Report Agda track configuration for the Dashi/Agda workflow."""

from __future__ import annotations

import os
import re
import shutil
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
WRAPPER = ROOT / "scripts" / "run_agda29_parallel_check.sh"


def _read_wrapper() -> str:
    return WRAPPER.read_text(encoding="utf-8")


def _parse_default_stdlib_ref(wrapper_text: str) -> str | None:
    match = re.search(
        r'^\s*STDLIB_REF="\$\{AGDA_STDLIB_REF:-([^}]+)\}"\s*$',
        wrapper_text,
        re.MULTILINE,
    )
    return match.group(1).strip() if match else None


def _parse_agda_flake_ref(wrapper_text: str) -> str | None:
    match = re.search(
        r'^\s*AGDA_FLAKE="\$\{AGDA_FLAKE:-([^}]+)\}"\s*$',
        wrapper_text,
        re.MULTILINE,
    )
    return match.group(1).strip() if match else None


def _exists(path: Path) -> bool:
    return path.is_file()


def _report_bool(label: str, value: bool) -> str:
    return f"{label}: {'yes' if value else 'no'}"


def _resolve_agda_binary(agda_flake: str | None) -> tuple[bool, str]:
    if not agda_flake:
        return False, "AGDA_FLAKE default could not be parsed from wrapper"

    if shutil.which("nix") is None:
        return False, "nix is not available in PATH"

    cmd = ["nix", "build", "--no-link", "--print-out-paths", agda_flake]
    env = os.environ.copy()
    if "XDG_CACHE_HOME" not in env:
        cache_home = Path("/tmp") / "dashi-nix-cache"
        cache_home.mkdir(parents=True, exist_ok=True)
        env["XDG_CACHE_HOME"] = str(cache_home)
    try:
        completed = subprocess.run(
            cmd,
            cwd=ROOT,
            env=env,
            check=False,
            capture_output=True,
            text=True,
        )
    except OSError as exc:  # pragma: no cover - environment-specific error path
        return False, f"nix build failed to start: {exc}"

    if completed.returncode != 0:
        stderr = (completed.stderr or "").strip()
        return False, f"nix build failed (exit {completed.returncode}): {stderr or 'no output'}"

    lines = [line.strip() for line in completed.stdout.splitlines() if line.strip()]
    if not lines:
        return False, "nix build returned no output"

    agda_bin = f"{lines[0]}/bin/agda"
    if Path(agda_bin).is_file():
        return True, agda_bin
    return False, f"nix build path resolved but binary missing: {agda_bin}"


def _status_line(label: str, value: str, status: str) -> str:
    return f"{label}: {status} ({value})"


def main() -> int:
    if not WRAPPER.is_file():
        print(f"Wrapper missing: {WRAPPER}")
        return 1

    wrapper_text = _read_wrapper()
    stdlib_ref = _parse_default_stdlib_ref(wrapper_text)
    agda_flake = _parse_agda_flake_ref(wrapper_text)

    print("=== Track A (Dashi) ===")
    print(_report_bool("Dashi flake.nix", _exists(ROOT / "flake.nix")))
    print(_report_bool("Dashi flake.lock", _exists(ROOT / "flake.lock")))

    print("\n=== Track B (Agda 2.9 shadow checks) ===")
    sibling_agda = ROOT.parent / "agda"
    print(
        _status_line(
            "Sibling Agda flake path",
            str(sibling_agda),
            "present" if sibling_agda.is_dir() else "missing",
        )
    )
    print(_status_line("Wrapper path", str(WRAPPER), "present" if WRAPPER.is_file() else "missing"))
    print(
        _status_line(
            "Wrapper executable",
            str(WRAPPER),
            "yes" if os.access(WRAPPER, os.X_OK) else "no",
        )
    )
    print(_status_line("Wrapper default STDLIB_REF", stdlib_ref or "<unparsed>", "ok" if stdlib_ref else "warn"))
    print(
        _status_line(
            "Wrapper AGDA_FLAKE",
            agda_flake or "<unparsed>",
            "ok" if agda_flake else "warn",
        )
    )

    resolved_ok, agda_status = _resolve_agda_binary(agda_flake)
    print(
        _status_line(
            "Resolved agda binary",
            agda_status,
            "ok" if resolved_ok else "warn",
        )
    )

    src_29_set = "set" if "AGDA_STDLIB_SRC_29" in os.environ else "unset"
    src_29_value = os.environ.get("AGDA_STDLIB_SRC_29", "")
    ref_set = "set" if "AGDA_STDLIB_REF" in os.environ else "unset"
    ref_value = os.environ.get("AGDA_STDLIB_REF", "")

    print("\n=== Override status ===")
    print(
        f"AGDA_STDLIB_SRC_29: {src_29_set}"
        + (f" ({src_29_value})" if src_29_set == "set" else "")
    )
    print(
        f"AGDA_STDLIB_REF: {ref_set}"
        + (f" ({ref_value})" if ref_set == "set" else "")
    )

    if not all([_exists(ROOT / "flake.nix"), _exists(ROOT / "flake.lock"), WRAPPER.is_file()]):
        return 1

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
