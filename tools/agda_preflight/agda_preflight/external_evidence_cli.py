from __future__ import annotations

import argparse
import json
from pathlib import Path

from .external_proof_bridge import ExternalFormalEvidence, ExternalProofRouter
from .product_cli import _connect
from .proof_router import ProofRouter
from .repository_store import DEFAULT_REPOSITORY_DB


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        prog="dashi-repo-formal-evidence",
        description=(
            "Persist authority-neutral formal evidence for an existing external proof demand, "
            "optionally binding a verified ITIR shared-shard artifact resolution receipt."
        ),
    )
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--database", type=Path, default=DEFAULT_REPOSITORY_DB)
    parser.add_argument("--evidence-ref", required=True)
    parser.add_argument("--demand-ref", required=True)
    parser.add_argument("--obligation-ref", required=True)
    parser.add_argument("--statement-digest", required=True)
    parser.add_argument("--da51")
    parser.add_argument("--producer", required=True)
    parser.add_argument("--artifact-ref", required=True)
    parser.add_argument("--artifact-digest", required=True)
    parser.add_argument("--checker", required=True)
    parser.add_argument("--checker-revision", required=True)
    parser.add_argument("--result-kind", required=True)
    parser.add_argument("--certification-state", required=True)
    parser.add_argument("--artifact-resolution-receipt", type=Path)
    args = parser.parse_args(argv)

    root = args.root.resolve()
    receipt = None
    if args.artifact_resolution_receipt is not None:
        receipt_path = args.artifact_resolution_receipt
        if not receipt_path.is_absolute():
            receipt_path = root / receipt_path
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))

    with _connect(root, args.database) as conn:
        base = ProofRouter(
            discovery=lambda query, **kwargs: {
                "query": query,
                "absence_claim_permitted": False,
                "absence_status": "not-requested",
            },
            connection=conn,
        )
        result = ExternalProofRouter(base, conn).record_evidence(
            ExternalFormalEvidence(
                evidence_ref=args.evidence_ref,
                demand_ref=args.demand_ref,
                external_obligation_ref=args.obligation_ref,
                statement_digest=args.statement_digest,
                da51_address=args.da51,
                producer=args.producer,
                artifact_ref=args.artifact_ref,
                artifact_digest=args.artifact_digest,
                checker=args.checker,
                checker_revision=args.checker_revision,
                result_kind=args.result_kind,
                certification_state=args.certification_state,
                artifact_resolution_receipt=receipt,
            )
        )

    print(f"evidence_ref\t{result['evidence_ref']}")
    print(f"authority\t{result['authority']}")
    print(f"establishes_proof\t{result['establishes_proof']}")
    artifact_resolution = result.get("artifact_resolution")
    if artifact_resolution is not None:
        print(f"artifact_ref\t{artifact_resolution['logical_artifact_ref']}")
        print(f"artifact_sink\t{artifact_resolution['sink']}")
        print(f"artifact_uri\t{artifact_resolution['uri']}")
        print(f"artifact_cid\t{artifact_resolution.get('cid')}")
        print(f"artifact_digest\t{artifact_resolution['content_digest']}")
        print(f"artifact_verified\t{artifact_resolution['verified']}")
        print(f"artifact_authority\t{artifact_resolution['authority']}")
        print(f"artifact_establishes_proof\t{artifact_resolution['establishes_proof']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
