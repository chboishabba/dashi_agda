#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path


DEFAULT_TEMPLATE = Path("temp-DOWNLOADED/dyturbo/source/dyturbo-1.4.2/input/default.in")
DEFAULT_OUTPUT_DIR = Path("temp-DOWNLOADED/dyturbo/run_cms_smoke/generated_cms_smp_20_003")
DEFAULT_DYTURBO_BIN = Path("temp-DOWNLOADED/dyturbo/unpacked/bin/dyturbo")
DEFAULT_USER_CUTS = Path("temp-DOWNLOADED/dyturbo/source/dyturbo-1.4.2/user/user_cuts.h")
EXACT_CMS_MARKER = "DASHI_CMS_SMP_20_003_USER_CUTS_LEAD25_SUBLEAD20_ABSETA24"

QT_BINS_T43 = (
    "0 0.3647504 0.7295008 1.0942512 1.4590016 1.823752 2.1885024 "
    "2.6444404 3.1003784 4.103442 5.1976932 6.5655072 8.2980716 "
    "10.395386 15.045954 23.526401 47.782302 105.1393 298.82177"
)

REQUIRED_KEYS = {
    "fixedorder_only",
    "order",
    "qtfpc",
    "LHAPDFset",
    "LHAPDFmember",
    "doBORN",
    "doCT",
    "doVJ",
    "doFPC",
    "BORNquad",
    "CTquad",
    "VJquad",
    "FPCquad",
    "intDimFPC",
    "cores",
    "makecuts",
    "lptcut",
    "lycut",
    "qtrec_naive",
    "qtrec_cs",
    "qtrec_kt0",
    "output_filename",
    "makehistos",
    "ptbinwidth",
    "ybinwidth",
    "mbinwidth",
    "qt_bins",
    "y_bins",
    "m_bins",
}


@dataclass(frozen=True)
class CardSpec:
    name: str
    mass_low: int
    mass_high: int


CARD_SPECS = (CardSpec("t43_num", 50, 76), CardSpec("t43_den", 76, 106))


def _key_pattern(key: str) -> re.Pattern[str]:
    return re.compile(rf"^(\s*{re.escape(key)}\s*=\s*)([^#\n]*)(.*)$", re.MULTILINE)


def _find_keys(text: str) -> set[str]:
    found = set()
    for line in text.splitlines():
        match = re.match(r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s*=", line)
        if match:
            found.add(match.group(1))
    return found


def _replace_value(text: str, key: str, value: str) -> str:
    pattern = _key_pattern(key)
    if not pattern.search(text):
        raise KeyError(key)

    def repl(match: re.Match[str]) -> str:
        suffix = match.group(3)
        if suffix.startswith("#"):
            suffix = "  " + suffix
        return f"{match.group(1)}{value}{suffix}"

    return pattern.sub(repl, text, count=1)


def _sha256_prefix(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()[:16]


def _verify_exact_user_cuts(path: Path) -> str:
    if not path.exists():
        raise SystemExit(f"exact CMS cut mode requires user_cuts.h evidence; missing: {path}")
    text = path.read_text(encoding="utf-8", errors="ignore")
    required = [
        EXACT_CMS_MARKER,
        "std::max(pt1, pt2)",
        "std::min(pt1, pt2)",
        "pt_lead < 25.0",
        "pt_sublead < 20.0",
    ]
    missing = [token for token in required if token not in text]
    if missing:
        raise SystemExit(
            "exact CMS cut mode requires the compiled user_cuts.h route; missing evidence: "
            + ", ".join(missing)
        )
    return _sha256_prefix(path)


def _render_card(
    template: str,
    spec: CardSpec,
    calls: int,
    seed: int,
    exact_cms: bool,
    qt_bins: str,
    xqtcut: str | None = None,
    output_suffix: str | None = None,
) -> str:
    suffix = "fpc_exactcms_fixed" if exact_cms else "fpc_stock25_fixed_smoke"
    if output_suffix:
        suffix = f"{suffix}_{output_suffix}"
    text = template
    replacements = {
        # Local DYTurbo 1.4.2 wires FPC as a fixed-order term:
        # src/dyturbo.C uses `opts.doFPC && opts.fixedorder`.
        "fixedorder_only": "true",
        "order": "1",
        "sroot": "13e3",
        "ih1": "1",
        "ih2": "1",
        "nproc": "3",
        "LHAPDFset": "CT18NNLO",
        "LHAPDFmember": "0",
        "qtfpc": "1e-4",
        "doBORN": "true",
        "doCT": "true",
        "doVJ": "true",
        "doFPC": "true",
        "BORNquad": "false",
        "CTquad": "false",
        "VJquad": "false",
        "FPCquad": "true",
        "intDimFPC": "2",
        "cores": "0",
        "makecuts": "true",
        # Exact CMS mode uses the stock common threshold as the subleading
        # 20 GeV guard; user/user_cuts.h supplies max(pt1,pt2) > 25 GeV.
        "lptcut": "20" if exact_cms else "25",
        "lycut": "2.4",
        "qtrec_naive": "false",
        "qtrec_cs": "true",
        "qtrec_kt0": "false",
        "output_filename": f"dyturbo_{spec.name}_{suffix}",
        "makehistos": "true",
        "ptbinwidth": "true",
        "ybinwidth": "false",
        "mbinwidth": "false",
        "qt_bins": f"[ {qt_bins} ]",
        "y_bins": "[ -2.4 2.4 ]",
        "m_bins": f"[ {spec.mass_low} {spec.mass_high} ]",
        "rseed": str(seed),
        "vegasncallsBORN": str(calls),
        "vegasncallsCT": str(calls),
        "vegasncallsVJLO": str(calls),
        "vegasncallsVJREAL": str(calls),
        "vegasncallsVJVIRT": str(calls),
    }
    if xqtcut is not None:
        replacements["xqtcut"] = xqtcut
        replacements["qtcut"] = "0."
    for key, value in replacements.items():
        text = _replace_value(text, key, value)
    if exact_cms:
        header = (
            "# Generated by scripts/generate_dyturbo_cms_cards.py\n"
            "# CMS-SMP-20-003 t43 phi* DYTurbo FPC exact-cut candidate card.\n"
            "# Requires DYTurbo rebuilt with user/user_cuts.h marker:\n"
            f"# {EXACT_CMS_MARKER}\n"
            "# lptcut=20 enforces the subleading threshold; user_cuts.h enforces leading 25 GeV and |eta|<2.4.\n"
            "# FPC is active here because fixedorder_only=true and doFPC=true.\n\n"
        )
    else:
        header = (
            "# Generated by scripts/generate_dyturbo_cms_cards.py\n"
            "# CMS-SMP-20-003 t43 phi* DYTurbo FPC smoke card.\n"
            "# Non-promoting: stock DYTurbo card cuts use lptcut=25 for both leptons,\n"
            "# not the exact CMS asymmetric leading/subleading 25/20 GeV cut.\n"
            "# FPC is active here because fixedorder_only=true and doFPC=true.\n\n"
        )
    return header + text


def _write_manifest(args: argparse.Namespace, written: list[Path], user_cuts_hash: str | None) -> Path:
    exact_cms = args.cut_mode == "exact-cms-leading-subleading"
    binary = Path(args.dyturbo_bin)
    binary_hash = _sha256_prefix(binary) if binary.exists() else None
    manifest = {
        "artifact_schema": "dashi.dyturbo.fpc_card_generation.v1",
        "status": "generated_exact_cms_candidate_cards" if exact_cms else "generated_non_promoting_smoke_cards",
        "cut_mode": args.cut_mode,
        "exact_cms_asymmetric_lepton_cuts": exact_cms,
        "user_cuts_h_patch": (
            "max(pt1,pt2)>25 && min(pt1,pt2)>20 && |eta_l|<2.4"
            if exact_cms
            else None
        ),
        "user_cuts_h_path": str(args.user_cuts_header),
        "user_cuts_h_sha256_16": user_cuts_hash,
        "dyturbo_binary": str(binary),
        "dyturbo_binary_sha256_16": binary_hash,
        "reason_non_promoting": None
        if exact_cms
        else (
            "Local stock DYTurbo card syntax exposes lptcut for a common charged-lepton pT "
            "threshold, lepptcut/alpptcut for charge-specific cuts, and lcptcut/lfptcut "
            "for rapidity-ordered cuts. It does not expose CMS leading/subleading pT "
            "ordering (25/20 GeV) as an input-card field. Exact CMS cuts require a "
            "compiled user_cuts.h route or an external fiducial provider."
        ),
        "fpc_local_semantics": {
            "active_condition": "src/dyturbo.C: bool fpc = opts.doFPC && opts.fixedorder",
            "required_card_values": {
                "fixedorder_only": True,
                "doFPC": True,
                "qtfpc": "1e-4",
                "FPCquad": True,
                "intDimFPC": 2,
            },
            "recoil_card_values": {
                "qtrec_naive": False,
                "qtrec_cs": True,
                "qtrec_kt0": False,
            },
            "note": "This local DYTurbo tree does not expose a literal `recoil = 2` key.",
        },
        "source_evidence": {
            "fpc_activation": "temp-DOWNLOADED/dyturbo/source/dyturbo-1.4.2/src/dyturbo.C:316",
            "fpc_settings": "temp-DOWNLOADED/dyturbo/source/dyturbo-1.4.2/src/settings.C:470-487,916-920,999-1008",
            "stock_cut_semantics": "temp-DOWNLOADED/dyturbo/source/dyturbo-1.4.2/histo/Kinematics.cxx:149-197",
            "user_cuts_hook": "temp-DOWNLOADED/dyturbo/source/dyturbo-1.4.2/user/user_cuts.h",
        },
        "generated_cards": [str(path) for path in written],
        "pdf": "CT18NNLO",
        "calls": args.calls,
        "seed": args.seed,
        "strict_log_provider_status": "consumer_ready_provider_not_exact_cms",
    }
    if exact_cms:
        manifest["strict_log_provider_status"] = "consumer_ready_exact_cms_candidate"
    manifest_path = Path(args.output_dir) / "fpc_card_manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return manifest_path


def generate(args: argparse.Namespace) -> list[Path]:
    exact_cms = args.cut_mode == "exact-cms-leading-subleading"
    user_cuts_hash = _verify_exact_user_cuts(Path(args.user_cuts_header)) if exact_cms else None
    template_path = Path(args.template)
    if not template_path.exists():
        raise SystemExit(f"template card not found: {template_path}")
    template = template_path.read_text(encoding="utf-8")
    found = _find_keys(template)
    missing = sorted(REQUIRED_KEYS - found)
    if missing:
        raise SystemExit(
            "template card is missing required DYTurbo keywords: "
            + ", ".join(missing)
            + f"\ntemplate={template_path}"
        )

    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    written = []
    for index, spec in enumerate(CARD_SPECS):
        suffix = "fpc_exactcms_fixed" if exact_cms else "fpc_stock25_fixed_smoke"
        out_path = output_dir / f"{spec.name}_{suffix}.in"
        qt_bins = args.qt_bins or QT_BINS_T43
        card = _render_card(
            template,
            spec,
            args.calls,
            args.seed + index,
            exact_cms,
            qt_bins,
            args.xqtcut,
            args.output_suffix,
        )
        out_path.write_text(card, encoding="utf-8")
        written.append(out_path)
    written.append(_write_manifest(args, written, user_cuts_hash))
    return written


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate fail-closed CMS-SMP-20-003 DYTurbo FPC/fiducial cards "
            "from a validated DYTurbo input template."
        )
    )
    parser.add_argument("--template", default=str(DEFAULT_TEMPLATE))
    parser.add_argument("--output-dir", default=str(DEFAULT_OUTPUT_DIR))
    parser.add_argument("--dyturbo-bin", default=str(DEFAULT_DYTURBO_BIN))
    parser.add_argument("--user-cuts-header", default=str(DEFAULT_USER_CUTS))
    parser.add_argument("--calls", type=int, default=2000)
    parser.add_argument("--seed", type=int, default=123456)
    parser.add_argument(
        "--qt-bins",
        help="Override qT bin edges, e.g. '0.7295008 1.0942512' for one targeted bin.",
    )
    parser.add_argument(
        "--output-suffix",
        help="Optional suffix appended to generated output_filename values.",
    )
    parser.add_argument(
        "--xqtcut",
        help=(
            "Override the dynamic qT-subtraction cutoff qt/m. "
            "Use 0.01 for the slow bin-0 elevated-boundary probe."
        ),
    )
    parser.add_argument(
        "--cut-mode",
        choices=("stock-symmetric25", "exact-cms-leading-subleading"),
        default="stock-symmetric25",
        help=(
            "stock-symmetric25 generates non-promoting smoke cards. "
            "exact-cms-leading-subleading fails closed unless a source-level user_cuts route is implemented."
        ),
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    written = generate(args)
    for path in written:
        print(path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
