#!/usr/bin/env python3
"""Small canonical NS proof-workset navigator, not a theorem prover.

Uses the existing NS Round extraction config. Historical package receipts
are queried only on explicit request, bounded and non-authoritative.
"""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
CONFIG = ROOT / "config/ns-round-extraction-targets.json"
RECEIPTS = ROOT / ".dashi/round-stranded/ns-packages.jsonl"
NEW_ROUND_UNIT = re.compile(
    r"(?:Round[0-9]+|NSBControl/[^/]*R[0-9]{3,})[^/]*\.(?:agda|lean)$"
)


def load_navigation(config: Path = CONFIG) -> dict:
    data = json.loads(config.read_text(encoding="utf-8"))
    nav = data["canonical_navigation"]
    if nav.get("schema_version") != 1 or not nav.get("routes"):
        raise ValueError("missing canonical navigation contract")
    seen_ids: set[str] = set()
    aliases: dict[str, dict] = {}
    for route in nav["routes"]:
        name = route["id"]
        if name in seen_ids:
            raise ValueError(f"duplicate route: {name}")
        seen_ids.add(name)
        owner = route["owner"]
        if re.search(r"Round[0-9]+", Path(owner["path"]).name):
            raise ValueError(f"historical Round selected as canonical owner: {name}")
        if not route.get("status") or not route.get("next"):
            raise ValueError(f"status/next missing from {name}")
        for a in [name, *route["aliases"]]:
            key = a.strip().casefold()
            if not key or key in aliases:
                raise ValueError(f"ambiguous canonical alias: {a}")
            aliases[key] = route
    return {"routes": nav["routes"], "aliases": aliases}


def select_route(query: str, navigation: dict) -> dict:
    key = query.strip().casefold()
    if key not in navigation["aliases"]:
        raise ValueError(
            f"unmapped NS owner {query!r}: use --list, or --historical-symbol "
            "with an exact declaration name. Do not create another Round unit."
        )
    route = navigation["aliases"][key]
    return {
        "route": route["id"],
        "owner": route["owner"],
        "support": route["support"][:3],
        "status": route["status"],
        "next": route["next"],
        "historical_Round_authority": False,
        "kernel_certified_by_navigation": False,
    }


def validate_local_owners(navigation: dict, root: Path = ROOT) -> list[str]:
    missing = []
    for route in navigation["routes"]:
        refs = [route["owner"], *route["support"]]
        for ref in refs:
            if ref["repo"] == "chboishabba/dashi_agda":
                p = Path(ref["path"])
                if p.is_absolute() or ".." in p.parts or not (root / p).is_file():
                    missing.append(f'{route["id"]}: {p}')
    return missing


def historical_symbol_receipts(
    symbol: str, receipts: Path = RECEIPTS, limit: int = 3
) -> dict:
    """Exact symbol only; stream receipts rather than dumping 30,000 packages."""
    if not symbol.strip():
        raise ValueError("historical declaration name cannot be empty")
    if limit < 1 or limit > 10:
        raise ValueError("historical receipt limit must be 1..10")
    if not receipts.is_file():
        raise FileNotFoundError(
            f"{receipts} missing: regenerate using classify_ns_round_packages.py; "
            "no negative absence or mathematical-closure inference is permitted"
        )
    matched = 0
    dispositions: Counter = Counter()
    items = []
    with receipts.open(encoding="utf-8") as handle:
        for line in handle:
            row = json.loads(line)
            if symbol not in row.get("candidate_names", []):
                continue
            matched += 1
            dispositions[row.get("disposition", "UNRESOLVED")] += 1
            if len(items) < limit:
                items.append({
                    "package_id": row.get("package_id"),
                    "disposition": row.get("disposition", "UNRESOLVED"),
                    "owner_hint": row.get("selected_canonical_owner"),
                    "source_locations": row.get("source_locations", [])[:2],
                    "unresolved": row.get("unresolved_residuals", [])[:2],
                })
    return {
        "symbol": symbol,
        "matching_packages": matched,
        "dispositions": dict(sorted(dispositions.items())),
        "sample": items,
        "sample_truncated": matched > len(items),
        "historical_receipts_establish_proof": False,
        "no_match_proves_absence": False,
    }


def new_round_units(added_paths: list[str]) -> list[str]:
    return sorted({p for p in added_paths if NEW_ROUND_UNIT.search(p)})


def check_added_units(base: str, root: Path = ROOT) -> list[str]:
    proc = subprocess.run(
        ["git", "diff", "--diff-filter=A", "--name-only", f"{base}...HEAD"],
        cwd=root, capture_output=True, text=True, check=True, timeout=30,
    )
    return new_round_units(proc.stdout.splitlines())


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--route", default="ns",
                    help="Conceptual obligation or exact historical alias, e.g. R823")
    ap.add_argument("--list", action="store_true", help="Six compact canonical routes")
    ap.add_argument("--validate", action="store_true", help="Check local Agda owner paths")
    ap.add_argument("--historical-symbol",
                    help="Exact declaration lookup in the existing JSONL receipt")
    ap.add_argument("--receipt-path", type=Path, default=RECEIPTS)
    ap.add_argument("--guard-new-rounds", metavar="BASE",
                    help="Fail if new RoundNNN/RNNN Lean units were added since BASE")
    args = ap.parse_args()
    nav = load_navigation()
    result = (
        [{"route": r["id"], "owner": r["owner"], "status": r["status"]}
         for r in nav["routes"]]
        if args.list else select_route(args.route, nav)
    )
    report: dict = {"schema": "dashi.ns.canonical-focus.v1", "workset": result}
    failed = False
    if args.validate:
        missing = validate_local_owners(nav)
        report["missing_local_paths"] = missing
        failed = failed or bool(missing)
    if args.historical_symbol:
        report["historical"] = historical_symbol_receipts(
            args.historical_symbol, args.receipt_path
        )
    if args.guard_new_rounds:
        found = check_added_units(args.guard_new_rounds)
        report["added_historical_style_units"] = found
        failed = failed or bool(found)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
