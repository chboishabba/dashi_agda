#!/usr/bin/env python3
"""Fetch/probe CT18NNLO and run the non-promoting W5 luminosity diagnostic.

This script is intentionally narrow.  It verifies that the public CT18NNLO
LHAPDF set is available in this environment, stores it in the repo's existing
``scripts/data/pdf`` cache, and delegates the numeric calculation to
``run_w4w5_ct18_corrected_dy_luminosity.py``.

The output is a checksum-bound diagnostic.  It does not construct W5 closure.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tarfile
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any


CT18NNLO_URL = "https://lhapdfsets.web.cern.ch/lhapdfsets/current/CT18NNLO.tar.gz"
TARGET_T45 = 0.8804486068


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def file_metadata(path: Path) -> dict[str, Any]:
    return {
        "path": str(path),
        "present": path.exists(),
        "size_bytes": path.stat().st_size if path.exists() else None,
        "sha256": sha256_file(path) if path.exists() and path.is_file() else None,
    }


def fetch_if_needed(url: str, archive: Path, *, refetch: bool) -> dict[str, Any]:
    if archive.exists() and not refetch:
        return {
            "url": url,
            "attempted": False,
            "status": "already_present",
            "http_status": None,
            "error": None,
            "archive": file_metadata(archive),
        }

    archive.parent.mkdir(parents=True, exist_ok=True)
    tmp = archive.with_suffix(archive.suffix + ".tmp")
    if tmp.exists():
        tmp.unlink()

    request = urllib.request.Request(url, headers={"User-Agent": "DASHI-W5-CT18NNLO-diagnostic"})
    try:
        with urllib.request.urlopen(request, timeout=300) as response:
            http_status = response.status
            with tmp.open("wb") as handle:
                shutil.copyfileobj(response, handle)
        tmp.replace(archive)
        status = "downloaded"
        error = None
    except urllib.error.HTTPError as exc:
        http_status = exc.code
        status = "http_error"
        error = str(exc)
        if tmp.exists():
            tmp.unlink()
    except (OSError, urllib.error.URLError) as exc:
        http_status = None
        status = "fetch_error"
        error = str(exc)
        if tmp.exists():
            tmp.unlink()

    return {
        "url": url,
        "attempted": True,
        "status": status,
        "http_status": http_status,
        "error": error,
        "archive": file_metadata(archive),
    }


def extract_if_needed(archive: Path, pdf_dir: Path, *, force: bool) -> dict[str, Any]:
    if not archive.exists():
        return {
            "attempted": False,
            "status": "archive_absent",
            "error": None,
            "directory": str(pdf_dir),
            "member_grid_count": 0,
        }
    if pdf_dir.exists() and not force:
        grids = sorted(pdf_dir.glob("CT18NNLO_*.dat"))
        return {
            "attempted": False,
            "status": "already_extracted",
            "error": None,
            "directory": str(pdf_dir),
            "member_grid_count": len(grids),
        }

    try:
        with tarfile.open(archive, "r:gz") as tar:
            names = tar.getnames()
            unsafe = [name for name in names if Path(name).is_absolute() or ".." in Path(name).parts]
            if unsafe:
                raise ValueError(f"unsafe tar entries: {unsafe[:3]}")
            tar.extractall(pdf_dir.parent)
        grids = sorted(pdf_dir.glob("CT18NNLO_*.dat"))
        return {
            "attempted": True,
            "status": "extracted",
            "error": None,
            "directory": str(pdf_dir),
            "member_grid_count": len(grids),
        }
    except (OSError, tarfile.TarError, ValueError) as exc:
        return {
            "attempted": True,
            "status": "extract_error",
            "error": str(exc),
            "directory": str(pdf_dir),
            "member_grid_count": 0,
        }


def run_command(command: list[str], *, env: dict[str, str], timeout: int = 300) -> dict[str, Any]:
    try:
        proc = subprocess.run(
            command,
            check=False,
            capture_output=True,
            text=True,
            env=env,
            timeout=timeout,
        )
        return {
            "command": command,
            "returncode": proc.returncode,
            "stdout": proc.stdout,
            "stderr": proc.stderr,
            "timeout": False,
        }
    except subprocess.TimeoutExpired as exc:
        return {
            "command": command,
            "returncode": None,
            "stdout": exc.stdout or "",
            "stderr": exc.stderr or "",
            "timeout": True,
        }


def parse_json_file(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def build_payload(args: argparse.Namespace) -> dict[str, Any]:
    repo_root = args.repo_root.resolve()
    pdf_cache = repo_root / "scripts" / "data" / "pdf"
    archive = pdf_cache / "CT18NNLO.tar.gz"
    pdf_dir = pdf_cache / "CT18NNLO"
    diagnostic_output = args.diagnostic_output or (
        repo_root / "scripts" / "data" / "outputs" / "w5_ct18nnlo_corrected_dy_luminosity.json"
    )

    fetch = fetch_if_needed(CT18NNLO_URL, archive, refetch=args.refetch)
    extraction = extract_if_needed(archive, pdf_dir, force=args.force_extract)

    data_path = f"/usr/share/lhapdf/LHAPDF:{pdf_cache}"
    env = os.environ.copy()
    env["LHAPDF_DATA_PATH"] = data_path

    lhapdf_show = run_command(["lhapdf", "show", "CT18NNLO"], env=env, timeout=30) if shutil.which("lhapdf") else {
        "command": ["lhapdf", "show", "CT18NNLO"],
        "returncode": None,
        "stdout": "",
        "stderr": "lhapdf command not found",
        "timeout": False,
    }

    runner = run_command(
        [
            sys.executable,
            str(repo_root / "scripts" / "run_w4w5_ct18_corrected_dy_luminosity.py"),
            "--pdf-set",
            "CT18NNLO",
            "--member",
            str(args.member),
            "--n-x",
            str(args.n_x),
            "--n-m",
            str(args.n_m),
            "--output",
            str(diagnostic_output),
        ],
        env=env,
        timeout=args.timeout,
    )

    diagnostic = parse_json_file(diagnostic_output)
    decision = None if diagnostic is None else diagnostic.get("decision")
    correction_factor = None if not isinstance(decision, dict) else decision.get("correction_factor")
    abs_gap = None if not isinstance(decision, dict) else decision.get("abs_gap")
    matches_target = None if not isinstance(decision, dict) else decision.get("matches_target")

    return {
        "artifact_schema": "dashi-w5-ct18nnlo-public-fetch-diagnostic-v1",
        "status": "candidate_diagnostic_non_promoting",
        "promotion": {
            "w5": False,
            "pdf_carrier": False,
            "accepted_dy_convention": False,
        },
        "source": {
            "url": CT18NNLO_URL,
            "pdf_set": "CT18NNLO",
            "member": args.member,
            "target": TARGET_T45,
        },
        "fetch": fetch,
        "extraction": extraction,
        "artifacts": {
            "archive": file_metadata(archive),
            "info": file_metadata(pdf_dir / "CT18NNLO.info"),
            "central_member_grid": file_metadata(pdf_dir / "CT18NNLO_0000.dat"),
            "diagnostic_output": file_metadata(diagnostic_output),
        },
        "environment": {
            "python_executable": sys.executable,
            "lhapdf_command": shutil.which("lhapdf"),
            "lhapdf_config": shutil.which("lhapdf-config"),
            "lhapdf_data_path": data_path,
        },
        "lhapdf_show": {
            "returncode": lhapdf_show["returncode"],
            "stdout": lhapdf_show["stdout"].strip(),
            "stderr": lhapdf_show["stderr"].strip(),
            "timeout": lhapdf_show["timeout"],
        },
        "runner": {
            "returncode": runner["returncode"],
            "stderr": runner["stderr"].strip(),
            "timeout": runner["timeout"],
            "output_path": str(diagnostic_output),
        },
        "numeric_result": {
            "compared_ratio": None if not isinstance(decision, dict) else decision.get("compared_ratio"),
            "correction_factor": correction_factor,
            "target": TARGET_T45,
            "abs_gap": abs_gap,
            "matches_target": matches_target,
        },
        "residual_blocker": (
            "CT18NNLO is publicly fetchable and LHAPDF-runnable here, but the "
            "repo's current local DY luminosity convention remains non-promoting; "
            "the W5 runner still requires an accepted/replacement provider packet "
            "or a typed convention law before W5 can close."
        ),
    }


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--diagnostic-output", type=Path)
    parser.add_argument("--member", type=int, default=0)
    parser.add_argument("--n-x", type=int, default=200)
    parser.add_argument("--n-m", type=int, default=80)
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--refetch", action="store_true")
    parser.add_argument("--force-extract", action="store_true")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    payload = build_payload(args)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
