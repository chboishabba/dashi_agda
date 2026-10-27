from __future__ import annotations

import argparse
from pathlib import Path

from .external_proof_bridge import ExternalProofRouter
from .kernel_evidence_handoff import (
    as_external_formal_evidence,
    load_json,
    stable_evidence_ref,
    validate_kernel_handoff,
)
from .product_cli import _connect
from .proof_router import ProofRouter
from .repository_store import DEFAULT_REPOSITORY_DB


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        prog="dashi-repo-formal-evidence-from-kernel",
        description=(
            "Persist dashi ExternalFormalEvidence only from a verified ITIR transport receipt "
            "and an independently produced kernel-certification receipt."
        ),
    )
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--database", type=Path, default=DEFAULT_REPOSITORY_DB)
    parser.add_argument("--artifact-resolution-receipt", type=Path, required=True)
    parser.add_argument("--kernel-certification-receipt", type=Path, required=True)
    parser.add_argument("--evidence-ref")
    args = parser.parse_args(argv)

    root = args.root.resolve()
    artifact_path = args.artifact_resolution_receipt
    kernel_path = args.kernel_certification_receipt
    if not artifact_path.is_absolute():
        artifact_path = root / artifact_path
    if not kernel_path.is_absolute():
        kernel_path = root / kernel_path

    artifact_receipt = load_json(artifact_path)
    kernel_receipt = load_json(kernel_path)
    normalized = validate_kernel_handoff(kernel_receipt, artifact_receipt)
    evidence_ref = args.evidence_ref or stable_evidence_ref(normalized)
    evidence = as_external_formal_evidence(normalized, evidence_ref)
    evidence = type(evidence)(
        evidence_ref=evidence.evidence_ref,
        demand_ref=evidence.demand_ref,
        external_obligation_ref=evidence.external_obligation_ref,
        statement_digest=evidence.statement_digest,
        da51_address=evidence.da51_address,
        producer=evidence.producer,
        artifact_ref=evidence.artifact_ref,
        artifact_digest=evidence.artifact_digest,
        checker=evidence.checker,
        checker_revision=evidence.checker_revision,
        result_kind=evidence.result_kind,
        certification_state=evidence.certification_state,
        artifact_resolution_receipt=artifact_receipt,
    )

    with _connect(root, args.database) as conn:
        base = ProofRouter(
            discovery=lambda query, **kwargs: {
                "query": query,
                "absence_claim_permitted": False,
                "absence_status": "not-requested",
            },
            connection=conn,
        )
        result = ExternalProofRouter(base, conn).record_evidence(evidence)

    print(f"ITIR_MABO_FORMAL_EVIDENCE_REF\t{result['evidence_ref']}")
    print(f"ITIR_MABO_FORMAL_DEMAND_REF\t{normalized['demand_ref']}")
    print(f"ITIR_MABO_FORMAL_OBLIGATION_REF\t{normalized['obligation_ref']}")
    print(f"ITIR_MABO_DA51_ADDRESS\t{normalized.get('da51_address') or '-'}")
    print(f"ITIR_MABO_FORMAL_PRODUCER\t{normalized['producer']}")
    print(f"ITIR_MABO_FORMAL_ARTIFACT_REF\t{normalized['artifact_ref']}")
    print(f"ITIR_MABO_FORMAL_ARTIFACT_DIGEST\t{normalized['artifact_digest']}")
    print(f"ITIR_MABO_FORMAL_STATEMENT_DIGEST\t{normalized['statement_digest']}")
    print(f"ITIR_MABO_FORMAL_CHECKER\t{normalized['checker']}")
    print(f"ITIR_MABO_FORMAL_CHECKER_REVISION\t{normalized['checker_revision']}")
    print(f"ITIR_MABO_FORMAL_SOURCE_REVISION\t{normalized['source_revision']}")
    print(f"ITIR_MABO_FORMAL_RESULT_KIND\t{normalized['result_kind']}")
    print(f"ITIR_MABO_FORMAL_CERTIFICATION_STATE\t{normalized['certification_state']}")
    print(f"ITIR_MABO_FORMAL_DEPENDENCY_REFS\t{','.join(normalized['dependencies'])}")
    print(f"dashi_authority\t{result['authority']}")
    print(f"dashi_establishes_proof\t{result['establishes_proof']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
