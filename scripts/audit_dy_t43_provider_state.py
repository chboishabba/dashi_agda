#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import shutil
from pathlib import Path
from typing import Any


DEFAULT_T43 = Path("scripts/data/hepdata/ins2079374_phistar_mass_50-76_over_mass_76-106_t43.csv")
DEFAULT_T44 = Path("scripts/data/hepdata/ins2079374_Covariance_phistar_mass_50-76_over_mass_76-106_t44.csv")
DEFAULT_SUBMISSION = Path("scripts/data/hepdata/ins2079374_submission.yaml")
DEFAULT_DYTURBO_SOURCE = Path("temp-DOWNLOADED/dyturbo/source/dyturbo-1.4.2")
DEFAULT_OUTPUT = Path("scripts/data/outputs/dy_t43_provider_audit_20260517.json")

TOOLS = [
    "rivet",
    "rivet-buildplugin",
    "yoda",
    "yodamerge",
    "sherpa",
    "Sherpa",
    "mg5_aMC",
    "MadGraph",
    "pythia8-config",
    "Herwig",
    "herwig",
]


def _read_header(path: Path, max_lines: int = 12) -> list[str]:
    if not path.exists():
        return []
    lines = []
    with path.open("r", encoding="utf-8", errors="replace") as handle:
        for _ in range(max_lines):
            line = handle.readline()
            if not line:
                break
            lines.append(line.rstrip("\n"))
    return lines


def _contains(path: Path, needle: str) -> bool:
    if not path.exists():
        return False
    return needle in path.read_text(encoding="utf-8", errors="replace")


def _tool_report() -> dict[str, str | None]:
    return {tool: shutil.which(tool) for tool in TOOLS}


def _dyturbo_report(source: Path) -> dict[str, Any]:
    hbook = source / "histo" / "HistoBook.h"
    user_cuts = source / "user" / "user_cuts.h"
    interface_c = source / "src" / "interface.C"
    kinematics_cxx = source / "histo" / "Kinematics.cxx"
    user_kinem = source / "user" / "user_kinem.h"
    user_book = source / "user" / "user_book.h"

    return {
        "source_path": str(source),
        "source_exists": source.exists(),
        "hphistareta_placeholder": _contains(hbook, "hphistareta")
        and _contains(hbook, "to be implemented"),
        "bos_phist_implemented": _contains(source / "histo" / "KinematicDefinitions.h", "BosPhist")
        and not _contains(hbook, "//Add( new Histo1D        <BosPhist"),
        "user_observable_hook_exists": user_kinem.exists(),
        "user_histogram_hook_exists": user_book.exists(),
        "compiled_user_cuts_marker_present": _contains(
            user_cuts, "DASHI_CMS_SMP_20_003_USER_CUTS_LEAD25_SUBLEAD20_ABSETA24"
        ),
        "user_cuts_lepton_only": _contains(user_cuts, "LepPT")
        and _contains(user_cuts, "ALpPT")
        and not _contains(user_cuts, "Jet"),
        "interface_cuts_discards_jets": _contains(interface_c, "p[2]")
        and _contains(interface_c, "p[3]")
        and _contains(interface_c, "KeepThisEvent"),
        "hist_fill_leptons_only": _contains(kinematics_cxx, "KeepThisEvent")
        and _contains(kinematics_cxx, "p3")
        and _contains(kinematics_cxx, "p4"),
    }


def build_audit(args: argparse.Namespace) -> dict[str, Any]:
    t43_header = _read_header(args.t43)
    t44_header = _read_header(args.t44)
    submission_text = (
        args.submission.read_text(encoding="utf-8", errors="replace")
        if args.submission.exists()
        else ""
    )
    tools = _tool_report()
    dyturbo = _dyturbo_report(args.dyturbo_source)
    rivet_available = bool(tools.get("rivet") and tools.get("yoda"))

    return {
        "artifact_schema": "dashi.dy_t43_provider_audit.v1",
        "status": "blocked" if not rivet_available else "provider_tools_available",
        "ratio_table": str(args.t43),
        "covariance_table": str(args.t44),
        "submission_metadata": str(args.submission),
        "t43_header": t43_header,
        "t44_header": t44_header,
        "contract": {
            "ratio_table_doi": "10.17182/hepdata.115656.v1/t43",
            "covariance_table_doi": "10.17182/hepdata.115656.v1/t44",
            "observable": "DSIG/DPHISTAR / DSIG/DPHISTAR",
            "mass_window_numerator": "50 <= M_ll < 76 GeV",
            "mass_window_denominator": "76 <= M_ll < 106 GeV",
            "event_level_phi_star_required": True,
            "at_least_one_jet_required": (
                any("At least one jet is required" in line for line in t43_header)
                and any("At least one jet is required" in line for line in t44_header)
            ),
            "anti_kt_source_bound_locally": "anti-kt" in submission_text.lower()
            or "anti kt" in submission_text.lower(),
        },
        "local_tools": tools,
        "rivet_route": {
            "available": rivet_available,
            "analysis": "CMS_2022_I2079374",
            "next_check": "rivet --list-analyses | rg CMS_2022_I2079374",
        },
        "dyturbo_route": dyturbo,
        "promotion_guard": {
            "qT_xs_route_promoting": False,
            "requires_native_phi_star": True,
            "requires_exact_jet_selection": True,
            "preferred_next_provider": "Rivet CMS_2022_I2079374 on a Z+jet event generator",
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--t43", type=Path, default=DEFAULT_T43)
    parser.add_argument("--t44", type=Path, default=DEFAULT_T44)
    parser.add_argument("--submission", type=Path, default=DEFAULT_SUBMISSION)
    parser.add_argument("--dyturbo-source", type=Path, default=DEFAULT_DYTURBO_SOURCE)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--print-progress", action="store_true")
    args = parser.parse_args()

    if args.print_progress:
        print("[1/4] reading local HEPData t43/t44 headers")
    audit = build_audit(args)
    if args.print_progress:
        print("[2/4] checking local Rivet/YODA/generator tools")
        print("[3/4] checking local DYTurbo source hooks")
        print("[4/4] writing audit artifact")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(audit, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"wrote {args.output}")
    print(f"status: {audit['status']}")
    print(f"at_least_one_jet_required: {audit['contract']['at_least_one_jet_required']}")
    print(f"rivet_route_available: {audit['rivet_route']['available']}")
    print(f"qT_xs_route_promoting: {audit['promotion_guard']['qT_xs_route_promoting']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
