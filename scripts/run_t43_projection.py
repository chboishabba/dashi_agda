#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import hashlib
import importlib
import json
import math
import sys
from pathlib import Path
from typing import Any, Callable

EXIT_USAGE = 64
EXIT_DIGEST_MISMATCH = 20
EXIT_PARSE_ERROR = 21
EXIT_PREDICTION_MISSING = 42
EXIT_PREDICTION_INVALID = 43

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

DATA_DIR = REPO_ROOT / "scripts" / "data" / "hepdata"
T43_PATH = DATA_DIR / "ins2079374_phistar_mass_50-76_over_mass_76-106_t43.csv"
T44_PATH = DATA_DIR / "ins2079374_Covariance_phistar_mass_50-76_over_mass_76-106_t44.csv"
T45_PATH = DATA_DIR / "ins2079374_phistar_mass_106-170_over_mass_76-106_t45.csv"
T46_PATH = DATA_DIR / "ins2079374_Covariance_phistar_mass_106-170_over_mass_76-106_t46.csv"
T21_PATH = DATA_DIR / "ins2079374_phistar_mass_76-106_t21.csv"
T22_PATH = DATA_DIR / "ins2079374_Covariance_phistar_mass_76-106_t22.csv"

KNOWN_DIGESTS = {
    T21_PATH.name: "4ece677d0e2640a786351e19d0190454aeb3dc49f7e6fbda4814e3fe88dc3270",
    T22_PATH.name: "718588d67d3c41195d25a6f01c4ff4bcf2d0d85c193e27ebd22925474a0d9ea7",
    T43_PATH.name: "0c46377d8f119abce35e6304c9a88dd03da663833b63848572e062ea532c7d2b",
    T44_PATH.name: "3526be84e53db1b1ae13d8e17ed3ab724750ae1298ca6b4fa11e9c0253ecb54b",
    T45_PATH.name: "bcc1450c5c7818e2792f06f1882c6facdea2e4079070b777f2c5ac3b87343433",
    T46_PATH.name: "e325d82ec3ba6962042c54f6b98a911d456f9bf00db22d2238b0cd76e71dcb3f",
}


def display_path(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(REPO_ROOT))
    except ValueError:
        return str(path)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def verify_digest(path: Path) -> dict[str, Any]:
    expected = KNOWN_DIGESTS.get(path.name)
    if expected is None:
        if not path.exists():
            return {
                "path": display_path(path),
                "sha256": None,
                "expectedSha256": None,
                "status": "missing",
            }
        return {
            "path": display_path(path),
            "sha256": None,
            "expectedSha256": None,
            "status": "unknown-input",
        }
    try:
        actual = sha256_file(path)
    except OSError as exc:
        return {
            "path": display_path(path),
            "sha256": None,
            "expectedSha256": expected,
            "status": "unreadable",
            "error": str(exc),
        }
    return {
        "path": display_path(path),
        "sha256": actual,
        "expectedSha256": expected,
        "status": "ok" if actual == expected else "mismatch",
    }


def _to_float(raw: str, *, context: str) -> float:
    try:
        value = float(raw)
    except ValueError as exc:
        raise ValueError(f"{context}: expected float, got {raw!r}") from exc
    if not math.isfinite(value):
        raise ValueError(f"{context}: expected finite float, got {raw!r}")
    return value


def read_hepdata_csv(path: Path) -> tuple[list[str], list[list[str]], list[str]]:
    comments: list[str] = []
    records: list[list[str]] = []
    header: list[str] | None = None

    with path.open("r", encoding="utf-8", newline="") as handle:
        for raw_line in handle:
            if raw_line.startswith("#:"):
                comments.append(raw_line.rstrip("\n"))
                continue
            if not raw_line.strip():
                continue
            row = next(csv.reader([raw_line]))
            if header is None:
                header = row
            else:
                records.append(row)

    if header is None:
        raise ValueError(f"{path}: missing CSV header")
    return header, records, comments


def parse_t43(path: Path) -> dict[str, Any]:
    header, rows, comments = read_hepdata_csv(path)
    expected_prefix = [
        "$\\varphi^*$",
        "$\\varphi^*$ LOW",
        "$\\varphi^*$ HIGH",
    ]
    if header[:3] != expected_prefix or len(header) < 4:
        raise ValueError(f"{path}: unexpected data header prefix {header[:4]!r}")
    value_column = header[3]

    bins: list[dict[str, Any]] = []
    for index, row in enumerate(rows):
        if len(row) != len(header):
            raise ValueError(f"{path}: row {index} has {len(row)} fields, expected {len(header)}")
        bins.append(
            {
                "index": index,
                "phiStar": _to_float(row[0], context=f"t43 row {index} phiStar"),
                "phiStarLow": _to_float(row[1], context=f"t43 row {index} phiStarLow"),
                "phiStarHigh": _to_float(row[2], context=f"t43 row {index} phiStarHigh"),
                "ratio": _to_float(row[3], context=f"t43 row {index} ratio"),
                "valueColumn": value_column,
                "uncertainties": {
                    header[column]: _to_float(row[column], context=f"t43 row {index} {header[column]}")
                    for column in range(4, len(header))
                },
            }
        )

    return {
        "path": display_path(path),
        "commentPreamble": comments,
        "columns": header,
        "valueColumn": value_column,
        "rowCount": len(bins),
        "bins": bins,
    }


def parse_t44(path: Path, bins: list[dict[str, Any]]) -> dict[str, Any]:
    header, rows, comments = read_hepdata_csv(path)
    expected_prefix = [
        "$\\varphi^*$",
        "$\\varphi^*$ LOW",
        "$\\varphi^*$ HIGH",
        "$\\varphi^*$",
        "$\\varphi^*$ LOW",
        "$\\varphi^*$ HIGH",
    ]
    if header[:6] != expected_prefix or len(header) != 7:
        raise ValueError(f"{path}: unexpected t44 header {header!r}")

    sections: dict[str, list[list[str]]] = {header[6]: []}
    current_label = header[6]
    for row in rows:
        if row[:6] == expected_prefix and len(row) == 7:
            current_label = row[6]
            sections.setdefault(current_label, [])
            continue
        sections[current_label].append(row)

    n = len(bins)
    total_label = next((label for label in sections if label.startswith("Total uncertainty")), None)
    if total_label is None:
        raise ValueError(f"{path}: missing Total uncertainty covariance section")
    total_rows = sections[total_label]
    if len(total_rows) != n * n:
        raise ValueError(
            f"{path}: expected {n * n} Total uncertainty covariance rows for {n} bins, got {len(total_rows)}"
        )

    by_bin = {
        (round(item["phiStar"], 15), round(item["phiStarLow"], 15), round(item["phiStarHigh"], 15)): item["index"]
        for item in bins
    }
    covariance = [[0.0 for _ in range(n)] for _ in range(n)]
    entries: list[dict[str, Any]] = []

    for row_index, row in enumerate(total_rows):
        if len(row) != len(header):
            raise ValueError(f"{path}: row {row_index} has {len(row)} fields, expected {len(header)}")
        left = tuple(round(_to_float(row[column], context=f"t44 row {row_index} left {column}"), 15) for column in range(3))
        right = tuple(round(_to_float(row[column], context=f"t44 row {row_index} right {column}"), 15) for column in range(3, 6))
        if left not in by_bin or right not in by_bin:
            raise ValueError(f"{path}: row {row_index} references a bin not present in t43")
        i = by_bin[left]
        j = by_bin[right]
        value = _to_float(row[6], context=f"t44 row {row_index} total uncertainty")
        covariance[i][j] = value
        entries.append({"row": i, "column": j, "totalUncertainty": value})

    symmetric = all(
        math.isclose(covariance[i][j], covariance[j][i], rel_tol=1e-12, abs_tol=1e-18)
        for i in range(n)
        for j in range(n)
    )

    return {
        "path": display_path(path),
        "commentPreamble": comments,
        "columns": header,
        "rowCount": len(total_rows),
        "sectionCount": len(sections),
        "totalUncertaintySection": total_label,
        "sections": [
            {"name": name, "rowCount": len(section_rows)}
            for name, section_rows in sections.items()
        ],
        "matrixShape": [n, n],
        "symmetric": symmetric,
        "covariance": covariance,
        "entries": entries,
    }


def load_prediction_api(spec: str | None) -> tuple[Callable[[list[dict[str, Any]]], list[float]] | None, str]:
    if not spec:
        return None, "no --prediction-api supplied; compute_dashi_ratio is not wired"
    if ":" not in spec:
        raise ValueError("--prediction-api must use module:function")
    module_name, function_name = spec.split(":", 1)
    module = importlib.import_module(module_name)
    function = getattr(module, function_name)
    if not callable(function):
        raise TypeError(f"{spec} is not callable")
    return function, f"loaded {spec}"


def finalize_artifact(payload: dict[str, Any]) -> dict[str, Any]:
    payload = dict(payload)
    payload["projectionDigest"] = ""
    stable = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    payload["projectionDigest"] = hashlib.sha256(stable.encode("utf-8")).hexdigest()
    return payload


def incomplete_artifact(
    *,
    mode: str,
    freeze_hash: str,
    digest_results: list[dict[str, Any]],
    t43: dict[str, Any] | None,
    t44: dict[str, Any] | None,
    reason: str,
    prediction_api_status: str,
) -> dict[str, Any]:
    return finalize_artifact({
        "artifactSchema": "dashi-hepdata-t43-projection-v1",
        "schemaVersion": "0.1.0",
        "generatedUtc": "deterministic-artifact",
        "worker": "HEP-R32",
        "scope": "scripts-only fail-closed t43/t44 projection runner",
        "mode": mode,
        "projectionComplete": False,
        "comparisonLawStatus": "incomplete",
        "failureCode": "prediction-missing",
        "failureReason": reason,
        "nonPromotionBoundary": [
            "no W3 promotion",
            "no W4 promotion",
            "no W5 promotion",
            "no W8 promotion",
            "no empirical adequacy claim",
            "no fake DASHI projection",
        ],
        "predictionFreeze": {
            "freezeHash": freeze_hash,
            "runnerHashBinding": "caller-supplied",
            "worktreeCleanCertificate": "not asserted by this runner",
        },
        "sourceAuthority": {
            "record": "ins2079374",
            "ratioTableDoi": "10.17182/hepdata.115656.v1/t43",
            "covarianceTableDoi": "10.17182/hepdata.115656.v1/t44",
        },
        "inputs": {
            "digests": digest_results,
            "t43": t43,
            "t44": t44,
        },
        "predictionApi": {
            "expected": "compute_dashi_ratio",
            "status": prediction_api_status,
        },
        "comparison": {
            "chi2": None,
            "chi2PerDof": None,
            "perBinTwoSigmaLaw": None,
            "status": "not-computed",
        },
    })


def _validate_prediction_values(raw: Any, *, expected_len: int) -> list[float]:
    if not isinstance(raw, list):
        raise TypeError("prediction API must return a list[float]")
    if len(raw) != expected_len:
        raise ValueError(f"prediction API returned {len(raw)} values, expected {expected_len}")
    values: list[float] = []
    for index, item in enumerate(raw):
        if not isinstance(item, (int, float)):
            raise TypeError(f"prediction value {index} is not numeric: {item!r}")
        value = float(item)
        if not math.isfinite(value):
            raise ValueError(f"prediction value {index} is not finite: {item!r}")
        values.append(value)
    return values


def completed_projection_artifact(
    *,
    mode: str,
    freeze_hash: str,
    digest_results: list[dict[str, Any]],
    t43: dict[str, Any],
    t44: dict[str, Any],
    prediction_api_status: str,
    predictions: list[float],
) -> dict[str, Any]:
    bins: list[dict[str, Any]] = []
    per_bin: list[dict[str, Any]] = []
    for row, prediction in zip(t43["bins"], predictions, strict=True):
        data = row["ratio"]
        index = row["index"]
        uncertainty = math.sqrt(t44["covariance"][index][index])
        residual = prediction - data
        pull = residual / uncertainty if uncertainty > 0.0 else 0.0
        bins.append(
            {
                "index": index,
                "phiStar": row["phiStar"],
                "phiStarLow": row["phiStarLow"],
                "phiStarHigh": row["phiStarHigh"],
                "R_data": data,
                "R_dashi": prediction,
                "residual": residual,
                "uncertainties": row["uncertainties"],
            }
        )
        per_bin.append(
            {
                "bin": index,
                "phiStar": row["phiStar"],
                "phiStarLow": row["phiStarLow"],
                "phiStarHigh": row["phiStarHigh"],
                "pred": prediction,
                "data": data,
                "unc": uncertainty,
                "pull": pull,
            }
        )

    return finalize_artifact({
        "artifactSchema": "dashi-hepdata-t43-projection-v1",
        "schemaVersion": "0.1.0",
        "generatedUtc": "deterministic-artifact",
        "worker": "HEP-R33",
        "scope": "digest-bound t43/t44 projection runner with caller-supplied prediction API",
        "mode": mode,
        "projectionComplete": True,
        "comparisonLawStatus": "not-claimed",
        "failureCode": None,
        "failureReason": None,
        "nonPromotionBoundary": [
            "no W3 promotion",
            "no W4 promotion",
            "no W5 promotion",
            "no W8 promotion",
            "no empirical adequacy claim",
            "projection artifact still requires comparison-law receipt review",
        ],
        "predictionFreeze": {
            "freezeHash": freeze_hash,
            "runnerHashBinding": "caller-supplied",
            "worktreeCleanCertificate": "not asserted by this runner",
        },
        "sourceAuthority": {
            "record": "ins2079374",
            "ratioTableDoi": "10.17182/hepdata.115656.v1/t43",
            "covarianceTableDoi": "10.17182/hepdata.115656.v1/t44",
        },
        "inputs": {
            "digests": digest_results,
            "t43": {
                "path": t43["path"],
                "columns": t43["columns"],
                "rowCount": t43["rowCount"],
            },
            "t44": {
                "path": t44["path"],
                "columns": t44["columns"],
                "rowCount": t44["rowCount"],
                "sectionCount": t44["sectionCount"],
                "matrixShape": t44["matrixShape"],
                "symmetric": t44["symmetric"],
            },
        },
        "predictionApi": {
            "expected": "batch callable: list[t43 bin dict] -> list[float]",
            "status": prediction_api_status,
        },
        "bins": bins,
        "per_bin": per_bin,
        "comparison": {
            "chi2": None,
            "chi2PerDof": None,
            "perBinTwoSigmaLaw": None,
            "status": "not-computed",
        },
    })


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Fail-closed HEPData ratio/covariance DASHI projection runner.")
    parser.add_argument(
        "--freeze-hash",
        "--freeze",
        dest="freeze_hash",
        required=True,
        help="Caller-supplied prediction freeze hash.",
    )
    parser.add_argument(
        "--output",
        default="/tmp/t43_projection_diagnostic.json",
        help="JSON artifact path. Defaults to /tmp/t43_projection_diagnostic.json.",
    )
    parser.add_argument(
        "--mode",
        choices=["t43-ratio", "dirty-z-peak"],
        default="t43-ratio",
        help="Diagnostic mode label. dirty-z-peak still requires local t21/t22 artifacts and compatible schema.",
    )
    parser.add_argument("--t43", dest="data", default=str(T43_PATH), help="Path to t43 ratio CSV.")
    parser.add_argument("--t44", dest="covariance", default=str(T44_PATH), help="Path to t44 covariance CSV.")
    parser.add_argument("--data", dest="data", help="Path to measurement/ratio CSV. Alias for --t43.")
    parser.add_argument("--covariance", dest="covariance", help="Path to covariance CSV. Alias for --t44.")
    parser.add_argument(
        "--prediction-api",
        help="Optional module:function callable. Omit until compute_dashi_ratio is wired.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    t43_path = Path(args.data)
    t44_path = Path(args.covariance)
    output_path = Path(args.output)

    digest_results = [verify_digest(t43_path), verify_digest(t44_path)]
    if any(result["status"] != "ok" for result in digest_results):
        artifact = incomplete_artifact(
            mode=args.mode,
            freeze_hash=args.freeze_hash,
            digest_results=digest_results,
            t43=None,
            t44=None,
            reason="data/covariance digest verification failed",
            prediction_api_status="not-attempted",
        )
        artifact["failureCode"] = "digest-mismatch"
        artifact = finalize_artifact(artifact)
        write_json(output_path, artifact)
        return EXIT_DIGEST_MISMATCH

    try:
        t43 = parse_t43(t43_path)
        t44 = parse_t44(t44_path, t43["bins"])
    except Exception as exc:
        artifact = incomplete_artifact(
            mode=args.mode,
            freeze_hash=args.freeze_hash,
            digest_results=digest_results,
            t43=None,
            t44=None,
            reason=f"data/covariance CSV parse failed: {exc}",
            prediction_api_status="not-attempted",
        )
        artifact["failureCode"] = "parse-error"
        artifact = finalize_artifact(artifact)
        write_json(output_path, artifact)
        return EXIT_PARSE_ERROR

    try:
        prediction_api, prediction_status = load_prediction_api(args.prediction_api)
    except Exception as exc:
        prediction_api = None
        prediction_status = f"unavailable: {exc}"

    if prediction_api is None:
        artifact = incomplete_artifact(
            mode=args.mode,
            freeze_hash=args.freeze_hash,
            digest_results=digest_results,
            t43=t43,
            t44=t44,
            reason="DASHI ratio prediction is unavailable; compute_dashi_ratio is not wired",
            prediction_api_status=prediction_status,
        )
        write_json(output_path, artifact)
        return EXIT_PREDICTION_MISSING

    try:
        predictions = _validate_prediction_values(
            prediction_api(t43["bins"]),
            expected_len=t43["rowCount"],
        )
    except Exception as exc:
        artifact = incomplete_artifact(
            mode=args.mode,
            freeze_hash=args.freeze_hash,
            digest_results=digest_results,
            t43=t43,
            t44=t44,
            reason=f"prediction API returned invalid output: {exc}",
            prediction_api_status=prediction_status,
        )
        artifact["failureCode"] = "prediction-invalid"
        artifact = finalize_artifact(artifact)
        write_json(output_path, artifact)
        return EXIT_PREDICTION_INVALID

    artifact = completed_projection_artifact(
        mode=args.mode,
        freeze_hash=args.freeze_hash,
        digest_results=digest_results,
        t43=t43,
        t44=t44,
        prediction_api_status=prediction_status,
        predictions=predictions,
    )
    write_json(output_path, artifact)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except BrokenPipeError:
        raise SystemExit(EXIT_USAGE)
