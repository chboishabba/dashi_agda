#!/usr/bin/env python3
"""Emit a checksum-bound intake for the Aristotle Lean allm evidence."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_LEAN_REPO = Path("/home/c/Documents/code/dashi_lean4")
DEFAULT_ALLM = Path("/home/c/Documents/20260604_070337_allm_20260604_070337.txt")
DEFAULT_OUTPUT_DIR = ROOT / "outputs" / "lean_aristotle_intake"
SCHEMA = "dashi-lean-aristotle-intake-v1"
SCHEMA_VERSION = "1.0.0"

SECTION_RE = re.compile(r"^───── (?P<path>.+?) \((?P<size>[^)]*)\) ─────$")
REQUEST_PROJECT_LEAN_RE = re.compile(r"output-final_aristotle/RequestProject/([^/\s,]+\.lean)")
MAIN_IMPORT_RE = re.compile(r"^import RequestProject\.([A-Za-z0-9_]+)\s*$", re.MULTILINE)


def sha256_file(path: Path, chunk_size: int = 1024 * 1024) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(chunk_size), b""):
            h.update(chunk)
    return h.hexdigest()


def canonical_json_digest(payload: Any) -> str:
    return hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()


def load_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def section_paths(text: str) -> list[str]:
    return [match.group("path") for match in map(SECTION_RE.match, text.splitlines()) if match]


def selected_request_modules(text: str) -> list[str]:
    modules = sorted({match.group(1) for match in REQUEST_PROJECT_LEAN_RE.finditer(text)})
    return modules


def selected_formal_modules(text: str) -> list[str]:
    return [module for module in selected_request_modules(text) if module != "Main.lean"]


def main_import_modules(text: str) -> list[str]:
    main_start = text.find("───── output-final_aristotle/RequestProject/Main.lean")
    if main_start < 0:
        return []
    next_section = text.find("───── ", main_start + 10)
    main_text = text[main_start:] if next_section < 0 else text[main_start:next_section]
    return MAIN_IMPORT_RE.findall(main_text)


def current_repo_lean_files(repo: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for path in sorted(repo.rglob("*.lean")):
        if ".lake" in path.parts:
            continue
        rel = path.relative_to(repo).as_posix()
        text = load_text(path)
        rows.append(
            {
                "path": rel,
                "bytes": path.stat().st_size,
                "sha256": sha256_file(path),
                "sorry_token_count": len(re.findall(r"\bsorry\b", text)),
                "admit_token_count": len(re.findall(r"\badmit\b", text)),
                "axiom_token_count": len(re.findall(r"\baxiom\b", text)),
                "unsafe_token_count": len(re.findall(r"\bunsafe\b", text)),
            }
        )
    return rows


def build_intake(*, lean_repo: Path, allm_path: Path, generated_at: str) -> dict[str, Any]:
    if not lean_repo.exists():
        raise FileNotFoundError(f"Lean repo not found: {lean_repo}")
    if not allm_path.exists():
        raise FileNotFoundError(f"allm file not found: {allm_path}")

    allm_text = load_text(allm_path)
    selected_modules = selected_request_modules(allm_text)
    selected_modules_excluding_main = selected_formal_modules(allm_text)
    imported_modules = main_import_modules(allm_text)
    current_files = current_repo_lean_files(lean_repo)

    summary_claims = {
        "allm_claims_19_modules_compile": "All 19 modules compile with `lake build`" in allm_text,
        "allm_claims_zero_sorry": "Zero `sorry` statements remain" in allm_text,
        "allm_claims_standard_axioms": "Only standard axioms used: `propext`, `Classical.choice`, `Quot.sound`" in allm_text,
        "allm_claims_main_imports_all_19": "Updated to import all 19 modules" in allm_text,
    }
    gates = {
        "archived_request_project_formal_module_count_is_19": len(selected_modules_excluding_main) == 19,
        "archived_request_project_lean_file_count_is_20_including_main": len(selected_modules) == 20,
        "archived_main_import_count_is_19": len(imported_modules) == 19,
        "archived_main_imports_match_selected_modules": sorted(imported_modules)
        == sorted(Path(name).stem for name in selected_modules_excluding_main),
        "current_checkout_inspected": True,
        "current_checkout_is_same_as_archived_request_project": False,
        "lean_build_rerun": False,
        "zero_sorry_claim_rerun": False,
        "authority_promoted": False,
        "unification_promoted": False,
    }
    payload = {
        "schema": SCHEMA,
        "schema_version": SCHEMA_VERSION,
        "generated_at_utc": generated_at,
        "receipt_kind": "lean-aristotle-intake",
        "lean_repo_path": str(lean_repo),
        "allm_path": str(allm_path),
        "lean_repo_exists": lean_repo.exists(),
        "allm_sha256": sha256_file(allm_path),
        "allm_bytes": allm_path.stat().st_size,
        "selected_request_project_modules": selected_modules,
        "selected_request_project_lean_file_count": len(selected_modules),
        "selected_request_project_formal_modules_excluding_main": selected_modules_excluding_main,
        "selected_request_project_formal_module_count": len(selected_modules_excluding_main),
        "main_import_modules": imported_modules,
        "main_import_module_count": len(imported_modules),
        "section_count": len(section_paths(allm_text)),
        "source_archive": "360d39a0-6c5e-49d6-8ff0-8fefe5d8ba01-aristotle.tar.gz",
        "claimed_lake_build_jobs": 8046 if "8046 jobs" in allm_text else None,
        "claimed_standard_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "summary_claims": summary_claims,
        "gates": gates,
        "current_checkout": {
            "lean_file_count": len(current_files),
            "lean_files": current_files,
            "aggregate_sorry_token_count": sum(row["sorry_token_count"] for row in current_files),
            "aggregate_admit_token_count": sum(row["admit_token_count"] for row in current_files),
            "aggregate_axiom_token_count": sum(row["axiom_token_count"] for row in current_files),
            "aggregate_unsafe_token_count": sum(row["unsafe_token_count"] for row in current_files),
        },
        "remaining_obligations": [
            "extract or recover the archived RequestProject Lean source tree if build rerun is required",
            "rerun lake build over the recovered Aristotle project before promoting compile status",
            "run a Lean no-sorry/no-admit audit over recovered source before promoting zero-sorry status",
            "bind the Lean receipt to an Agda promotion surface only after rerun evidence exists",
        ],
    }
    payload["intake_digest"] = canonical_json_digest(payload)
    return payload


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_markdown(output_dir: Path, payload: dict[str, Any]) -> None:
    gates = payload["gates"]
    lines = [
        "# Lean Aristotle Intake",
        "",
        f"- schema: `{payload['schema']}`",
        f"- allm path: `{payload['allm_path']}`",
        f"- allm sha256: `{payload['allm_sha256']}`",
        f"- archived RequestProject Lean files: `{payload['selected_request_project_lean_file_count']}`",
        f"- archived formal modules excluding Main: `{payload['selected_request_project_formal_module_count']}`",
        f"- archived Main imports: `{payload['main_import_module_count']}`",
        f"- current checkout Lean files: `{payload['current_checkout']['lean_file_count']}`",
        f"- archived formal module count is 19: `{str(gates['archived_request_project_formal_module_count_is_19']).lower()}`",
        f"- archived imports match selected modules: `{str(gates['archived_main_imports_match_selected_modules']).lower()}`",
        f"- Lean build rerun: `{str(gates['lean_build_rerun']).lower()}`",
        f"- authority promoted: `{str(gates['authority_promoted']).lower()}`",
        "",
        "This receipt checksums and parses the archived Aristotle allm evidence. It does",
        "not rerun `lake build`; the checked-out Lean repository is inspected separately",
        "and is not treated as the recovered 19-module `RequestProject` archive.",
        "",
        "## Archived Modules",
        "",
    ]
    lines.extend(f"- `{module}`" for module in payload["selected_request_project_formal_modules_excluding_main"])
    lines.extend(["", "## Remaining Obligations", ""])
    lines.extend(f"- {item}" for item in payload["remaining_obligations"])
    (output_dir / "lean_aristotle_intake.md").write_text(
        "\n".join(lines) + "\n", encoding="utf-8"
    )


def write_outputs(payload: dict[str, Any], output_dir: Path) -> None:
    output_dir.mkdir(parents=True, exist_ok=True)
    write_json(output_dir / "lean_aristotle_intake.json", payload)
    write_markdown(output_dir, payload)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Emit a non-promoting checksum/count intake for Aristotle Lean allm evidence."
    )
    parser.add_argument("--lean-repo", type=Path, default=DEFAULT_LEAN_REPO)
    parser.add_argument("--allm", type=Path, default=DEFAULT_ALLM)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    parser.add_argument(
        "--generated-at",
        default=None,
        help="Fixed timestamp for reproducible tests. Defaults to current UTC.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    generated_at = args.generated_at or datetime.now(timezone.utc).isoformat()
    payload = build_intake(
        lean_repo=args.lean_repo,
        allm_path=args.allm,
        generated_at=generated_at,
    )
    write_outputs(payload, args.output_dir)
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
