#!/usr/bin/env python3
"""Non-promoting W4/W5 public pT-table integral diagnostic.

This runner tests whether the public CMS-SMP-20-003 / HEPData ``ins2079374``
absolute ``d sigma / d pT(ll)`` tables supply mass-window integrated ratios
that can be compared with the older W5 target ``0.8804486068``.

It is deliberately fail-closed:

* HEPData direct table downloads are attempted only as availability checks and
  may return HTTP 403 / Cloudflare from CLI.
* CMS public YAML mirrors are used as the network fallback when local YAML files
  are absent.
* Every consumed source payload is SHA-256 hashed in the output artifact.
* The output is diagnostic only and never promotes W4 or W5.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
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
DEFAULT_LOCAL_DIR = Path("scripts/data/hepdata")
DEFAULT_OUTPUT = Path("scripts/data/outputs/w4w5_hepdata_pt_integral.json")
TARGET_RATIO = 0.8804486068


@dataclass(frozen=True)
class TableSpec:
    key: str
    display_name: str
    cms_file: str
    table_hint: str
    mass_window: str
    jet_required: bool

    @property
    def cms_url(self) -> str:
        return f"{CMS_BASE_URL}/{self.cms_file}"

    @property
    def local_path(self) -> Path:
        return DEFAULT_LOCAL_DIR / f"ins2079374_{self.cms_file}"


TABLES = [
    TableSpec(
        key="inclusive_50_76",
        display_name="pT ll mass 50-76",
        cms_file="pt_ll_mass_50-76.yaml",
        table_hint="t1 / Table 1",
        mass_window="50-76 GeV",
        jet_required=False,
    ),
    TableSpec(
        key="inclusive_76_106",
        display_name="pT ll mass 76-106",
        cms_file="pt_ll_mass_76-106.yaml",
        table_hint="t3 / Table 3",
        mass_window="76-106 GeV",
        jet_required=False,
    ),
    TableSpec(
        key="inclusive_106_170",
        display_name="pT ll mass 106-170",
        cms_file="pt_ll_mass_106-170.yaml",
        table_hint="t5 / Table 5",
        mass_window="106-170 GeV",
        jet_required=False,
    ),
    TableSpec(
        key="jet_50_76",
        display_name="pT ll mass 50-76 jet",
        cms_file="pt_ll_mass_50-76_jet.yaml",
        table_hint="jet absolute pT table",
        mass_window="50-76 GeV",
        jet_required=True,
    ),
    TableSpec(
        key="jet_76_106",
        display_name="pT ll mass 76-106 jet",
        cms_file="pt_ll_mass_76-106_jet.yaml",
        table_hint="jet absolute pT table",
        mass_window="76-106 GeV",
        jet_required=True,
    ),
    TableSpec(
        key="jet_106_170",
        display_name="pT ll mass 106-170 jet",
        cms_file="pt_ll_mass_106-170_jet.yaml",
        table_hint="jet absolute pT table",
        mass_window="106-170 GeV",
        jet_required=True,
    ),
]

HEPDATA_ATTEMPTS = [
    "https://www.hepdata.net/download/table/ins2079374/t1/csv",
    "https://www.hepdata.net/download/table/ins2079374/t3/csv",
    "https://www.hepdata.net/download/table/ins2079374/t21/csv",
    "https://www.hepdata.net/download/table/ins2079374/t22/csv",
    "https://www.hepdata.net/download/table/ins2079374/Table%201/1/csv",
    "https://www.hepdata.net/download/table/ins2079374/Table%203/1/csv",
]


@dataclass(frozen=True)
class SourcePayload:
    spec: TableSpec
    source_kind: str
    source: str
    content: bytes

    @property
    def sha256(self) -> str:
        return hashlib.sha256(self.content).hexdigest()


def http_get(url: str, timeout: int) -> bytes:
    request = Request(url, headers={"User-Agent": "Mozilla/5.0 dashi-w4w5-pt-integral/1.0"})
    with urlopen(request, timeout=timeout) as response:
        return response.read()


def probe_url(url: str, timeout: int) -> dict[str, Any]:
    try:
        data = http_get(url, timeout)
    except HTTPError as exc:
        snippet = exc.read(180).decode("utf-8", "replace").replace("\n", "\\n")
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
        "snippet": data[:120].decode("utf-8", "replace").replace("\n", "\\n"),
    }


def load_payload(spec: TableSpec, local_dir: Path, no_network: bool, timeout: int) -> SourcePayload | None:
    local_path = local_dir / f"ins2079374_{spec.cms_file}"
    if local_path.exists():
        return SourcePayload(
            spec=spec,
            source_kind="local_file",
            source=str(local_path),
            content=local_path.read_bytes(),
        )
    if no_network:
        return None
    try:
        data = http_get(spec.cms_url, timeout)
    except (HTTPError, URLError, TimeoutError):
        return None
    return SourcePayload(
        spec=spec,
        source_kind="cms_public_yaml",
        source=spec.cms_url,
        content=data,
    )


def as_float(value: Any, label: str) -> float:
    try:
        result = float(value)
    except (TypeError, ValueError) as exc:
        raise ValueError(f"{label}: not numeric: {value!r}") from exc
    if not math.isfinite(result):
        raise ValueError(f"{label}: not finite: {value!r}")
    return result


def integrate_pt_table(payload: SourcePayload) -> dict[str, Any]:
    parsed = yaml.safe_load(payload.content.decode("utf-8"))
    independent = parsed["independent_variables"][0]
    dependent = parsed["dependent_variables"][0]
    x_values = independent["values"]
    y_values = dependent["values"]
    if len(x_values) != len(y_values):
        raise ValueError(f"{payload.source}: independent/dependent row count mismatch")

    integral_pb = 0.0
    bins: list[dict[str, float]] = []
    for index, (x_row, y_row) in enumerate(zip(x_values, y_values), start=1):
        low = as_float(x_row["low"], f"{payload.source}: bin {index} low")
        high = as_float(x_row["high"], f"{payload.source}: bin {index} high")
        value = as_float(y_row["value"], f"{payload.source}: bin {index} value")
        width = high - low
        if width <= 0.0:
            raise ValueError(f"{payload.source}: bin {index} has non-positive width")
        if value < 0.0:
            raise ValueError(f"{payload.source}: bin {index} has negative cross-section")
        contribution = value * width
        integral_pb += contribution
        bins.append(
            {
                "low": low,
                "high": high,
                "width": width,
                "value_pb_per_gev": value,
                "contribution_pb": contribution,
            }
        )

    return {
        "key": payload.spec.key,
        "name": payload.spec.display_name,
        "table_hint": payload.spec.table_hint,
        "mass_window": payload.spec.mass_window,
        "jet_required": payload.spec.jet_required,
        "source_kind": payload.source_kind,
        "source": payload.source,
        "cms_url": payload.spec.cms_url,
        "sha256": payload.sha256,
        "byte_count": len(payload.content),
        "observable": dependent.get("header", {}).get("name"),
        "units": dependent.get("header", {}).get("units"),
        "x_axis": independent.get("header", {}).get("name"),
        "x_units": independent.get("header", {}).get("units"),
        "bin_count": len(bins),
        "pt_range": [bins[0]["low"], bins[-1]["high"]],
        "integral_pb": integral_pb,
        "formula": "sum_i (d sigma / d pT(ll))_i * (pT_high_i - pT_low_i)",
    }


def ratio(numerator: dict[str, Any], denominator: dict[str, Any], name: str) -> dict[str, Any]:
    den = denominator["integral_pb"]
    if den <= 0.0:
        raise ValueError(f"{denominator['key']}: denominator integral is not positive")
    value = numerator["integral_pb"] / den
    return {
        "name": name,
        "numerator_key": numerator["key"],
        "denominator_key": denominator["key"],
        "numerator_integral_pb": numerator["integral_pb"],
        "denominator_integral_pb": den,
        "value": value,
        "abs_gap_to_0_8804486068": abs(value - TARGET_RATIO),
        "formula": "integral(numerator d sigma / d pT) / integral(denominator d sigma / d pT)",
    }


def build_payload(local_dir: Path, no_network: bool, timeout: int) -> dict[str, Any]:
    hepd_attempts = [probe_url(url, timeout) for url in HEPDATA_ATTEMPTS if not no_network]
    sources: dict[str, SourcePayload] = {}
    missing: list[dict[str, Any]] = []
    errors: list[str] = []

    for spec in TABLES:
        payload = load_payload(spec, local_dir, no_network, timeout)
        if payload is None:
            missing.append(
                {
                    "key": spec.key,
                    "local_path": str(local_dir / f"ins2079374_{spec.cms_file}"),
                    "cms_url": spec.cms_url,
                    "hepdata_hint": f"{HEPDATA_RECORD_URL}; direct table hint {spec.table_hint}",
                }
            )
            continue
        sources[spec.key] = payload

    integrals: dict[str, dict[str, Any]] = {}
    for key, source in sources.items():
        try:
            integrals[key] = integrate_pt_table(source)
        except (KeyError, TypeError, ValueError) as exc:
            errors.append(f"{key}: {exc}")

    computed: dict[str, Any] = {}
    if "inclusive_50_76" in integrals and "inclusive_76_106" in integrals:
        computed["inclusive_50_76_over_76_106"] = ratio(
            integrals["inclusive_50_76"],
            integrals["inclusive_76_106"],
            "inclusive pT-integrated 50-76 / 76-106",
        )
    if "inclusive_106_170" in integrals and "inclusive_76_106" in integrals:
        computed["inclusive_106_170_over_76_106"] = ratio(
            integrals["inclusive_106_170"],
            integrals["inclusive_76_106"],
            "inclusive pT-integrated 106-170 / 76-106",
        )
    if "inclusive_106_170" in integrals and "inclusive_50_76" in integrals:
        computed["inclusive_106_170_over_50_76"] = ratio(
            integrals["inclusive_106_170"],
            integrals["inclusive_50_76"],
            "inclusive pT-integrated 106-170 / 50-76",
        )
    if "jet_50_76" in integrals and "jet_76_106" in integrals:
        computed["jet_50_76_over_76_106"] = ratio(
            integrals["jet_50_76"],
            integrals["jet_76_106"],
            "at-least-one-jet pT-integrated 50-76 / 76-106",
        )
    if "jet_106_170" in integrals and "jet_76_106" in integrals:
        computed["jet_106_170_over_76_106"] = ratio(
            integrals["jet_106_170"],
            integrals["jet_76_106"],
            "at-least-one-jet pT-integrated 106-170 / 76-106",
        )
    if "jet_106_170" in integrals and "jet_50_76" in integrals:
        computed["jet_106_170_over_50_76"] = ratio(
            integrals["jet_106_170"],
            integrals["jet_50_76"],
            "at-least-one-jet pT-integrated 106-170 / 50-76",
        )

    return {
        "artifact_schema": "dashi-w4w5-hepdata-pt-integral-diagnostic-v1",
        "status": "non_promoting_public_hepdata_pt_integral_diagnostic",
        "record": RECORD,
        "record_url": HEPDATA_RECORD_URL,
        "cms_public_base_url": CMS_BASE_URL,
        "target_under_test": TARGET_RATIO,
        "network_mode": "disabled" if no_network else "enabled",
        "hepdata_direct_download_attempts": hepd_attempts,
        "manual_download_links_if_needed": missing,
        "source_integrals": integrals,
        "computed_ratios": computed,
        "errors": errors,
        "interpretation": {
            "claim_tested": (
                "public absolute pT tables may yield mass-window integrated ratios "
                "closer to the older W5 target 0.8804486068"
            ),
            "diagnostic_only": True,
            "does_not_establish_dsigma_dm": True,
            "does_not_construct_acceptance_bridge": True,
            "does_not_construct_w4_or_w5_authority": True,
        },
        "governance": {
            "no_w4_promotion": True,
            "no_w5_promotion": True,
            "no_authority_promotion": True,
            "accepted_authority_receipt_present": False,
        },
    }


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--local-dir", type=Path, default=DEFAULT_LOCAL_DIR)
    parser.add_argument("--no-network", action="store_true")
    parser.add_argument("--timeout", type=int, default=30)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        payload = build_payload(args.local_dir, args.no_network, args.timeout)
    except Exception as exc:  # pragma: no cover - top-level diagnostic guard
        print(f"hepdata pT-integral diagnostic failed: {exc}", file=sys.stderr)
        return 2

    encoded = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded, encoding="utf-8")
    print(encoded, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
