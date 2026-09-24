from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path

from .evidence import canonical_code


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _module_name(nodeid: str) -> str:
    return nodeid.rsplit("::", 1)[-1] if "::" in nodeid else nodeid


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        prog="dashi-agda-triage",
        description="Summarize a pytest Agda preflight JSON report.",
    )
    parser.add_argument(
        "report",
        nargs="?",
        type=Path,
        default=Path(".cache/agda_preflight/report.json"),
    )
    parser.add_argument("--top", type=int, default=15)
    parser.add_argument("--code", help="show only one TSAGDA code/root cause")
    parser.add_argument(
        "--raw-codes",
        action="store_true",
        help="do not collapse compatibility alias diagnostics",
    )
    parser.add_argument(
        "--deferred",
        action="store_true",
        help="show deferred findings rather than hard errors",
    )
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    payload = _load(args.report)
    rows = []
    for module in payload.get("modules", []):
        name = _module_name(module.get("nodeid", ""))
        for diagnostic in module.get("diagnostics", []):
            raw_code = diagnostic.get("code", "UNKNOWN")
            code = raw_code if args.raw_codes else canonical_code(raw_code)
            requested = (
                args.code
                if args.raw_codes or not args.code
                else canonical_code(args.code)
            )
            if requested and code != requested:
                continue
            deferred = not diagnostic.get("evidence_sufficient", True)
            hard = diagnostic.get("severity") == "error"
            diagnostic = dict(diagnostic)
            diagnostic["triage_code"] = code
            if args.deferred:
                if not deferred:
                    continue
            elif not hard:
                continue
            rows.append((name, diagnostic))

    by_code = Counter(diagnostic.get("triage_code", diagnostic.get("code", "UNKNOWN")) for _, diagnostic in rows)
    by_module = Counter(name for name, _ in rows)

    if args.json:
        result = {
            "mode": "deferred" if args.deferred else "hard",
            "count": len(rows),
            "by_code": dict(by_code.most_common()),
            "by_module": dict(by_module.most_common()),
        }
        print(json.dumps(result, indent=2, sort_keys=True))
        return 0

    mode = "deferred" if args.deferred else "hard errors"
    print(f"Agda triage: {mode} ({len(rows)})")
    if args.code:
        print(f"filter: {args.code}")

    print("\ntop codes:")
    for code, count in by_code.most_common(args.top):
        print(f"  {code:<12} {count}")

    print("\ntop modules:")
    for module, count in by_module.most_common(args.top):
        print(f"  {count:>5}  {module}")

    if rows:
        print("\nfirst examples:")
        for module, diagnostic in rows[: min(args.top, len(rows))]:
            print(
                f"  {diagnostic.get('triage_code', diagnostic.get('code'))} {module}:"
                f"{diagnostic.get('line', 1)}:{diagnostic.get('column', 1)} "
                f"{diagnostic.get('message', '')}"
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
