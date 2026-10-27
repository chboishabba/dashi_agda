from __future__ import annotations

import json
from pathlib import Path
import sqlite3

from agda_preflight.external_evidence_cli import main
from agda_preflight.external_proof_bridge import ExternalProofDemand, ExternalProofRouter
from agda_preflight.product_cli import _connect
from agda_preflight.proof_router import ProofRouter


DIGEST = "a" * 64


def _seed_demand(root: Path) -> None:
    with _connect(root, Path(".dashi/repository.sqlite3")) as conn:
        base = ProofRouter(
            discovery=lambda query, **kwargs: {
                "query": query,
                "live_matches": [],
                "related": {},
                "query_similar": [],
                "historical_matches": [],
                "absence_status": "confirmed_absent",
                "absence_claim_permitted": True,
            },
            connection=conn,
        )
        ExternalProofRouter(base, conn).route(
            ExternalProofDemand(
                demand_ref="formal-demand:mabo:1",
                external_obligation_ref="proof-obligation:mabo:1",
                statement_digest="sha256:statement-a",
                query="Mabo formal premise",
                target_prover="lean",
                mathematical_status="source-established",
                statement_status="source-aligned",
                da51_address="0xDA51831100800000",
            )
        )


def test_external_evidence_cli_ingests_verified_artifact_receipt(tmp_path: Path, capsys) -> None:
    _seed_demand(tmp_path)
    receipt_path = tmp_path / "artifact-receipt.json"
    receipt_path.write_text(
        json.dumps(
            {
                "schemaVersion": "artifact-resolution-receipt/v1",
                "logicalContractVersion": "shared-shard-artifact/v1",
                "logicalArtifactRef": "mabo-formal-proof@rev-1#proof-1",
                "artifactId": "mabo-formal-proof",
                "artifactRevision": "rev-1",
                "shardId": "proof-1",
                "contentDigest": f"sha256:{DIGEST}",
                "payloadDigest": f"sha256:{DIGEST}",
                "payloadSizeBytes": 12,
                "objectRef": {
                    "sink": "ipfs",
                    "uri": "ipfs://bafy-demo-erdfa-tar",
                    "memberPath": "payload/proof-1.olean",
                    "sizeBytes": 12,
                    "contentDigest": f"sha256:{DIGEST}",
                },
                "transport": {
                    "sink": "ipfs",
                    "uri": "ipfs://bafy-demo-erdfa-tar",
                    "cid": "bafy-demo-erdfa-tar",
                    "memberPath": "payload/proof-1.olean",
                },
                "verified": True,
                "authority": "transport-only",
                "establishesProof": False,
            }
        ),
        encoding="utf-8",
    )

    code = main(
        [
            "--root", str(tmp_path),
            "--evidence-ref", "formal-evidence:mabo:1",
            "--demand-ref", "formal-demand:mabo:1",
            "--obligation-ref", "proof-obligation:mabo:1",
            "--statement-digest", "sha256:statement-a",
            "--da51", "0xDA51831100800000",
            "--producer", "lean-kernel",
            "--artifact-ref", "mabo-formal-proof@rev-1#proof-1",
            "--artifact-digest", f"sha256:{DIGEST}",
            "--checker", "lean",
            "--checker-revision", "lean:head",
            "--result-kind", "formal-proof",
            "--certification-state", "kernel-certified",
            "--artifact-resolution-receipt", str(receipt_path),
        ]
    )

    assert code == 0
    output = capsys.readouterr().out
    assert "authority\tevidence-only" in output
    assert "establishes_proof\tFalse" in output
    assert "artifact_sink\tipfs" in output
    assert "artifact_cid\tbafy-demo-erdfa-tar" in output

    database = tmp_path / ".dashi/repository.sqlite3"
    with sqlite3.connect(database) as conn:
        assert conn.execute("SELECT count(*) FROM external_formal_evidence").fetchone()[0] == 1
        assert conn.execute("SELECT count(*) FROM external_artifact_resolutions").fetchone()[0] == 1
