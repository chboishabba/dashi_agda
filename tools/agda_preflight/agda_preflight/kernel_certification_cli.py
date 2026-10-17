from __future__ import annotations

import argparse
import json
from pathlib import Path

from .kernel_certification import certify_artifact, load_receipt


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        prog="dashi-repo-kernel-certify",
        description="Run an independent Agda/Lean kernel check over the exact file bytes named by an ITIR artifact-resolution receipt.",
    )
    parser.add_argument("--artifact-resolution-receipt", type=Path, required=True)
    parser.add_argument("--demand-ref", required=True)
    parser.add_argument("--obligation-ref", required=True)
    parser.add_argument("--statement-digest", required=True)
    parser.add_argument("--da51")
    parser.add_argument("--checker", choices=("agda", "lean"))
    parser.add_argument("--source-root", type=Path)
    parser.add_argument("--result-kind", default="formal-proof")
    parser.add_argument("--dependency", action="append", dest="dependencies", default=[])
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args(argv)

    receipt = certify_artifact(
        artifact_resolution_receipt=load_receipt(args.artifact_resolution_receipt),
        demand_ref=args.demand_ref,
        obligation_ref=args.obligation_ref,
        statement_digest=args.statement_digest,
        da51_address=args.da51,
        checker=args.checker,
        source_root=args.source_root,
        result_kind=args.result_kind,
        dependencies=args.dependencies,
    )
    args.output.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    for key in (
        "demandRef",
        "obligationRef",
        "statementDigest",
        "da51Address",
        "producer",
        "artifactRef",
        "artifactDigest",
        "checker",
        "checkerRevision",
        "sourceRevision",
        "resultKind",
        "certificationState",
    ):
        value = receipt.get(key)
        print(f"{key}\t{value if value is not None else '-'}")
    print(f"dependencies\t{','.join(receipt['dependencies'])}")
    print(f"kernel_certification_receipt\t{args.output.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
