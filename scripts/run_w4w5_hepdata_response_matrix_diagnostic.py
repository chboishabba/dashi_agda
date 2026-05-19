#!/usr/bin/env python3
"""Non-promoting W4/W5 HEPData response-matrix diagnostic.

This runner tests the narrow claim that CMS-SMP-20-003 / HEPData
``ins2079374`` response matrices are publicly fetchable and whether their YAML
schema is sufficient to act as the missing ``A(M, phi*)`` acceptance bridge.

It deliberately does not promote W4 or W5.  Response matrices can be migration
or unfolding inputs without being central-value acceptance/efficiency surfaces.
The output therefore records URL status, checksums, matrix dimensions, and the
exact missing map if the schema is not sufficient.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any
from urllib.error import HTTPError, URLError
from urllib.request import Request, urlopen

try:
    import yaml
except ModuleNotFoundError as exc:  # pragma: no cover - environment guard
    raise SystemExit("PyYAML is required for this diagnostic") from exc


RECORD = "ins2079374"
HEPDATA_RECORD_URL = f"https://www.hepdata.net/record/{RECORD}"
CMS_BASE_URL = (
    "https://cms-results.web.cern.ch/cms-results/public-results/publications/"
    "SMP-20-003/SMP-20-003_hepdata"
)
SUBMISSION_URL = f"{CMS_BASE_URL}/submission.yaml"
DEFAULT_LOCAL_DIR = Path("scripts/data/hepdata")
DEFAULT_OUTPUT = Path("scripts/data/outputs/w4w5_hepdata_response_matrix_diagnostic.json")
USER_AGENT = "Mozilla/5.0 dashi-w4w5-response-matrix-diagnostic/1.0"


@dataclass(frozen=True)
class ResponseSpec:
    doc_index: int
    name: str
    description: str
    data_file: str
    channel: str
    mass_window: str

    @property
    def cms_url(self) -> str:
        return f"{CMS_BASE_URL}/{self.data_file}"

    @property
    def local_name(self) -> str:
        return f"ins2079374_{self.data_file}"


@dataclass(frozen=True)
class SourcePayload:
    spec: ResponseSpec
    source_kind: str
    source: str
    content: bytes

    @property
    def sha256(self) -> str:
        return hashlib.sha256(self.content).hexdigest()


def http_get(url: str, timeout: int) -> bytes:
    request = Request(url, headers={"User-Agent": USER_AGENT})
    with urlopen(request, timeout=timeout) as response:
        return response.read()


def probe_url(url: str, timeout: int) -> dict[str, Any]:
    try:
        data = http_get(url, timeout)
    except HTTPError as exc:
        snippet = exc.read(220).decode("utf-8", "replace").replace("\n", "\\n")
        return {
            "url": url,
            "ok": False,
            "status": exc.code,
            "reason": exc.reason,
            "snippet": snippet,
        }
    except URLError as exc:
        return {"url": url, "ok": False, "status": None, "reason": str(exc.reason)}
    except TimeoutError:
        return {"url": url, "ok": False, "status": None, "reason": "timeout"}
    return {
        "url": url,
        "ok": True,
        "status": 200,
        "sha256": hashlib.sha256(data).hexdigest(),
        "bytes": len(data),
        "snippet": data[:160].decode("utf-8", "replace").replace("\n", "\\n"),
    }


def parse_mass_window(name: str) -> str:
    match = re.search(r"mass ([0-9]+-[0-9]+)", name)
    return match.group(1) if match else "unknown"


def parse_channel(name: str) -> str:
    if name.startswith("electron "):
        return "electron"
    if name.startswith("muon "):
        return "muon"
    return "unknown"


def load_submission(local_dir: Path, no_network: bool, timeout: int) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    local_path = local_dir / "ins2079374_submission.yaml"
    if local_path.exists():
        data = local_path.read_bytes()
        status = {
            "source_kind": "local_file",
            "source": str(local_path),
            "sha256": hashlib.sha256(data).hexdigest(),
            "bytes": len(data),
        }
    else:
        if no_network:
            raise FileNotFoundError(f"{local_path} is absent and --no-network was set")
        data = http_get(SUBMISSION_URL, timeout)
        local_dir.mkdir(parents=True, exist_ok=True)
        local_path.write_bytes(data)
        status = {
            "source_kind": "cms_public_yaml",
            "source": SUBMISSION_URL,
            "local_path": str(local_path),
            "sha256": hashlib.sha256(data).hexdigest(),
            "bytes": len(data),
        }
    docs = [doc for doc in yaml.safe_load_all(data) if isinstance(doc, dict)]
    return docs, status


def discover_response_specs(docs: list[dict[str, Any]]) -> list[ResponseSpec]:
    specs: list[ResponseSpec] = []
    for index, doc in enumerate(docs):
        name = str(doc.get("name") or "")
        description = str(doc.get("description") or "")
        data_file = str(doc.get("data_file") or "")
        if "response phistar mass" not in name.lower():
            continue
        if not data_file:
            continue
        specs.append(
            ResponseSpec(
                doc_index=index,
                name=name,
                description=description,
                data_file=data_file,
                channel=parse_channel(name),
                mass_window=parse_mass_window(name),
            )
        )
    return specs


def load_payload(spec: ResponseSpec, local_dir: Path, no_network: bool, timeout: int) -> SourcePayload | None:
    local_path = local_dir / spec.local_name
    if local_path.exists():
        return SourcePayload(
            spec=spec,
            source_kind="local_file",
            source=str(local_path),
            content=local_path.read_bytes(),
        )
    if no_network:
        return None
    data = http_get(spec.cms_url, timeout)
    local_dir.mkdir(parents=True, exist_ok=True)
    local_path.write_bytes(data)
    return SourcePayload(
        spec=spec,
        source_kind="cms_public_yaml",
        source=spec.cms_url,
        content=data,
    )


def as_float(value: Any) -> float:
    result = float(value)
    if not math.isfinite(result):
        raise ValueError(f"non-finite numeric value: {value!r}")
    return result


def summarize_matrix(payload: SourcePayload, local_dir: Path) -> dict[str, Any]:
    parsed = yaml.safe_load(payload.content.decode("utf-8"))
    independent = parsed.get("independent_variables", [])
    dependent = parsed.get("dependent_variables", [])
    if len(dependent) != 1:
        raise ValueError(f"{payload.source}: expected one dependent variable, got {len(dependent)}")
    values = [as_float(row["value"]) for row in dependent[0].get("values", [])]
    n_values = len(values)
    dim = int(math.isqrt(n_values))
    is_square = dim * dim == n_values
    row_sums: list[float] = []
    col_sums: list[float] = []
    diagonal: list[float] = []
    if is_square:
        row_sums = [sum(values[row * dim : (row + 1) * dim]) for row in range(dim)]
        col_sums = [sum(values[row * dim + col] for row in range(dim)) for col in range(dim)]
        diagonal = [values[i * dim + i] for i in range(dim)]

    def stats(items: list[float]) -> dict[str, float] | None:
        if not items:
            return None
        return {
            "min": min(items),
            "max": max(items),
            "mean": sum(items) / len(items),
            "max_abs_gap_to_one": max(abs(item - 1.0) for item in items),
        }

    def bounded(items: list[float], *, tolerance: float = 0.0) -> bool | None:
        if not items:
            return None
        return all((0.0 - tolerance) <= item <= (1.0 + tolerance) for item in items)

    def round_vector(items: list[float]) -> list[float]:
        return [round(item, 12) for item in items]

    negative_count = sum(1 for value in values if value < 0.0)
    near_column_stochastic = bool(col_sums) and max(abs(item - 1.0) for item in col_sums) < 1.0e-3
    near_row_stochastic = bool(row_sums) and max(abs(item - 1.0) for item in row_sums) < 5.0e-2
    column_sums_in_unit_interval = bounded(col_sums)
    column_sums_in_unit_interval_with_roundoff = bounded(col_sums, tolerance=1.0e-5)
    diagonal_in_unit_interval = bounded(diagonal)
    diagonal_in_unit_interval_with_roundoff = bounded(diagonal, tolerance=1.0e-12)
    column_sum_efficiency_candidate_plausible = bool(
        col_sums
        and column_sums_in_unit_interval_with_roundoff
        and near_column_stochastic
        and min(col_sums) > 0.99
    )
    diagonal_efficiency_candidate_plausible = bool(
        diagonal
        and diagonal_in_unit_interval_with_roundoff
        and min(diagonal) >= 0.0
        and max(diagonal) <= 1.0 + 1.0e-12
    )
    local_path = local_dir / payload.spec.local_name

    return {
        "doc_index": payload.spec.doc_index,
        "hepdata_table_hint": f"t{payload.spec.doc_index}",
        "name": payload.spec.name,
        "description": payload.spec.description,
        "data_file": payload.spec.data_file,
        "channel": payload.spec.channel,
        "mass_window": payload.spec.mass_window,
        "source_kind": payload.source_kind,
        "source": payload.source,
        "local_path": str(local_path),
        "sha256": payload.sha256,
        "byte_count": len(payload.content),
        "independent_variable_count": len(independent),
        "independent_headers": [item.get("header", {}) for item in independent],
        "independent_value_counts": [len(item.get("values", [])) for item in independent],
        "dependent_variable_count": len(dependent),
        "dependent_headers": [item.get("header", {}) for item in dependent],
        "dependent_value_count": n_values,
        "matrix_dimension": [dim, dim] if is_square else None,
        "is_square_matrix": is_square,
        "value_min": min(values) if values else None,
        "value_max": max(values) if values else None,
        "negative_entry_count": negative_count,
        "matrix_value_sum": sum(values),
        "row_sum_stats": stats(row_sums),
        "column_sum_stats": stats(col_sums),
        "diagonal_stats": stats(diagonal),
        "acceptance_candidates": {
            "column_sum_definition": "A_col[j] = sum_i P[i][j]",
            "diagonal_definition": "A_diag[j] = P[j][j]",
            "column_sums": round_vector(col_sums),
            "diagonal": round_vector(diagonal),
            "column_sums_in_unit_interval_exact": column_sums_in_unit_interval,
            "column_sums_in_unit_interval_with_1e_minus_5_roundoff": column_sums_in_unit_interval_with_roundoff,
            "diagonal_in_unit_interval_exact": diagonal_in_unit_interval,
            "diagonal_in_unit_interval_with_1e_minus_12_roundoff": diagonal_in_unit_interval_with_roundoff,
            "column_sum_candidate_plausible_as_normalized_migration_probability": column_sum_efficiency_candidate_plausible,
            "diagonal_candidate_plausible_as_bin_retention_efficiency": diagonal_efficiency_candidate_plausible,
            "column_sum_candidate_note": (
                "Column sums are numerically one within roundoff, which is "
                "consistent with a truth-bin-normalized response/migration "
                "matrix. This makes A_col a valid local arithmetic extraction "
                "but not, by itself, evidence for an independent central "
                "acceptance-loss vector."
            ),
            "diagonal_candidate_note": (
                "The diagonal entries are in [0,1] and quantify same-bin "
                "retention/migration purity for the published binning. They "
                "are not identical to a full acceptance correction unless a "
                "gate consumer explicitly accepts that convention."
            ),
        },
        "looks_like_response_matrix": (
            is_square
            and len(independent) == 2
            and dependent[0].get("header", {}).get("name") == "P"
            and "response" in payload.spec.name.lower()
            and (near_column_stochastic or near_row_stochastic)
        ),
        "direct_acceptance_surface": False,
        "acceptance_bridge_note": (
            "This YAML exposes a square P migration/response matrix for one "
            "lepton channel and one mass window. It does not by itself expose "
            "a central-value A(M, phi*) acceptance/efficiency vector or an "
            "accepted observable-conversion law."
        ),
    }


def build_payload(local_dir: Path, no_network: bool, timeout: int) -> dict[str, Any]:
    docs, submission_status = load_submission(local_dir, no_network, timeout)
    specs = discover_response_specs(docs)

    hepd_attempts = []
    if not no_network:
        for table_index in range(68, 78):
            hepd_attempts.append(probe_url(f"https://www.hepdata.net/download/table/{RECORD}/t{table_index}/yaml", timeout))
            hepd_attempts.append(
                probe_url(
                    f"https://www.hepdata.net/download/table/{RECORD}/Table%20{table_index}/1/yaml",
                    timeout,
                )
            )

    matrix_summaries: list[dict[str, Any]] = []
    missing: list[dict[str, Any]] = []
    errors: list[str] = []
    for spec in specs:
        try:
            payload = load_payload(spec, local_dir, no_network, timeout)
        except (HTTPError, URLError, TimeoutError) as exc:
            payload = None
            errors.append(f"{spec.data_file}: fetch failed: {exc}")
        if payload is None:
            missing.append({"name": spec.name, "cms_url": spec.cms_url, "local_path": str(local_dir / spec.local_name)})
            continue
        try:
            matrix_summaries.append(summarize_matrix(payload, local_dir))
        except (KeyError, TypeError, ValueError) as exc:
            errors.append(f"{spec.data_file}: parse failed: {exc}")

    relevant_windows = {"50-76", "76-106", "106-170"}
    relevant = [
        item for item in matrix_summaries
        if item["mass_window"] in relevant_windows
    ]
    by_window: dict[str, list[str]] = {}
    for item in matrix_summaries:
        by_window.setdefault(item["mass_window"], []).append(item["channel"])

    all_relevant_fetched = len(relevant) == 6 and all(item["looks_like_response_matrix"] for item in relevant)
    all_t68_t77_fetched = len(matrix_summaries) == 10 and not missing
    any_direct_acceptance = any(item["direct_acceptance_surface"] for item in matrix_summaries)
    all_column_sum_candidates_roundoff_bounded = all(
        item["acceptance_candidates"]["column_sums_in_unit_interval_with_1e_minus_5_roundoff"]
        for item in matrix_summaries
    ) if matrix_summaries else False
    all_diagonal_candidates_bounded = all(
        item["acceptance_candidates"]["diagonal_in_unit_interval_exact"]
        for item in matrix_summaries
    ) if matrix_summaries else False
    column_sum_candidate_stats = [
        {
            "channel": item["channel"],
            "mass_window": item["mass_window"],
            "sha256": item["sha256"],
            "min": item["column_sum_stats"]["min"],
            "max": item["column_sum_stats"]["max"],
            "mean": item["column_sum_stats"]["mean"],
            "max_abs_gap_to_one": item["column_sum_stats"]["max_abs_gap_to_one"],
            "in_unit_interval_exact": item["acceptance_candidates"]["column_sums_in_unit_interval_exact"],
            "in_unit_interval_with_1e_minus_5_roundoff": item["acceptance_candidates"][
                "column_sums_in_unit_interval_with_1e_minus_5_roundoff"
            ],
        }
        for item in matrix_summaries
    ]
    diagonal_candidate_stats = [
        {
            "channel": item["channel"],
            "mass_window": item["mass_window"],
            "sha256": item["sha256"],
            "min": item["diagonal_stats"]["min"],
            "max": item["diagonal_stats"]["max"],
            "mean": item["diagonal_stats"]["mean"],
            "in_unit_interval_exact": item["acceptance_candidates"]["diagonal_in_unit_interval_exact"],
        }
        for item in matrix_summaries
    ]

    return {
        "artifact_schema": "dashi-w4w5-hepdata-response-matrix-diagnostic-v2",
        "status": "non_promoting_public_response_matrix_diagnostic",
        "record": RECORD,
        "record_url": HEPDATA_RECORD_URL,
        "cms_public_base_url": CMS_BASE_URL,
        "submission": submission_status,
        "network_mode": "disabled" if no_network else "enabled",
        "requested_range": "t68-t77 / CMS submission documents 68-77",
        "hepdata_direct_yaml_attempts": hepd_attempts,
        "discovered_response_specs": [
            {
                "doc_index": spec.doc_index,
                "hepdata_table_hint": f"t{spec.doc_index}",
                "name": spec.name,
                "data_file": spec.data_file,
                "channel": spec.channel,
                "mass_window": spec.mass_window,
                "cms_url": spec.cms_url,
            }
            for spec in specs
        ],
        "matrix_count": len(matrix_summaries),
        "relevant_50_76_76_106_106_170_matrix_count": len(relevant),
        "channels_by_mass_window": {key: sorted(value) for key, value in sorted(by_window.items())},
        "matrices": matrix_summaries,
        "acceptance_candidate_summary": {
            "column_sum_candidate_formula": "A_col[j] = sum_i P[i][j]",
            "diagonal_candidate_formula": "A_diag[j] = P[j][j]",
            "all_column_sum_candidates_bounded_with_1e_minus_5_roundoff": all_column_sum_candidates_roundoff_bounded,
            "all_diagonal_candidates_bounded_exact": all_diagonal_candidates_bounded,
            "column_sum_candidate_stats": column_sum_candidate_stats,
            "diagonal_candidate_stats": diagonal_candidate_stats,
            "interpretation": (
                "The published P matrices are numerically column-stochastic. "
                "The formal column-sum extraction is therefore locally "
                "computable and checksum-bound, but yields A_col approximately "
                "equal to one for every truth bin. The diagonal extraction is "
                "also locally computable and bounded in [0,1], but represents "
                "same-bin retention rather than a full acceptance vector unless "
                "a W4 gate receipt adopts that convention."
            ),
        },
        "missing": missing,
        "errors": errors,
        "diagnostic_findings": {
            "cms_public_mirror_fetch_succeeded": all_t68_t77_fetched,
            "hepdata_cli_direct_fetch_succeeded": any(item.get("ok") for item in hepd_attempts),
            "relevant_low_z_high_z_response_matrices_present": all_relevant_fetched,
            "response_matrices_look_like_unfolding_or_migration_data": all(
                item["looks_like_response_matrix"] for item in matrix_summaries
            ) if matrix_summaries else False,
            "column_sum_acceptance_candidate_computed": bool(matrix_summaries),
            "column_sum_acceptance_candidate_bounded_with_roundoff": all_column_sum_candidates_roundoff_bounded,
            "diagonal_acceptance_candidate_computed": bool(matrix_summaries),
            "diagonal_acceptance_candidate_bounded": all_diagonal_candidates_bounded,
            "direct_A_M_phi_acceptance_surface_present": any_direct_acceptance,
            "usable_for_A_M_phi_without_additional_law": False,
        },
        "exact_missing_map": {
            "local_arithmetic_now_available": (
                "A_col[j] = sum_i P[i][j] and A_diag[j] = P[j][j] are computed "
                "for every cached t68-t77 response matrix and bound to source "
                "SHA-256 digests."
            ),
            "missing_typed_receipt_or_gate_consumer": (
                "an existing W4 gate consumer that accepts either the column-sum "
                "or diagonal candidate as the W4 A(M, phi*) bridge and states "
                "the channel-combination, covariance, and observable-conversion "
                "convention"
            ),
            "why_response_matrix_still_does_not_promote": (
                "The column sums are numerically one within roundoff, indicating "
                "a normalized migration matrix rather than a visible acceptance "
                "loss surface. The diagonal is bounded and physically meaningful "
                "as bin-retention/purity, but no current gate consumer accepts it "
                "as the W4 bridge by type."
            ),
        },
        "governance": {
            "promotesW4": False,
            "promotesW5": False,
            "constructsAcceptedDYLuminosityConventionAuthority": False,
            "constructsPhiStarToMassAcceptanceBridge": False,
            "diagnostic_only": True,
        },
    }


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--local-dir", type=Path, default=DEFAULT_LOCAL_DIR)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--timeout", type=int, default=30)
    parser.add_argument("--no-network", action="store_true")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        payload = build_payload(args.local_dir, args.no_network, args.timeout)
    except Exception as exc:  # pragma: no cover - top-level diagnostic guard
        print(f"response-matrix diagnostic failed: {exc}", file=sys.stderr)
        return 2

    encoded = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(encoded, encoding="utf-8")
    print(encoded, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
