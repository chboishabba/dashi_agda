from __future__ import annotations

import json

from agda_preflight.product_cli import main


def _payload() -> dict:
    return {
        "schema": "dashi.xpollenation-neighbourhood/v1",
        "subject": {"namespace": "rhea", "identifier": "RHEA:11920"},
        "edges": [
            {
                "edgeId": "edge:pcbd1",
                "subject": {"namespace": "rhea", "identifier": "RHEA:11920"},
                "relation": "catalysed-by",
                "object": {"namespace": "uniprot", "identifier": "P61457"},
                "sourceRef": "panel",
                "sourceRevision": "rev",
                "acquisitionReceipt": "receipt",
                "status": "identity-paid",
                "sameObjectClaimed": False,
                "sameObjectVerified": False,
                "contextEquivalent": False,
                "promotionAllowed": False,
            }
        ],
        "authority": "navigation-enrichment-only",
        "establishesProof": False,
        "establishesPayment": False,
    }


def test_product_cli_ingests_and_shows_xpollenation(tmp_path, capsys) -> None:
    payload_path = tmp_path / "neighbourhood.json"
    payload_path.write_text(json.dumps(_payload()), encoding="utf-8")
    db = tmp_path / "repo.sqlite3"

    code = main(
        [
            "xpollenation",
            "ingest",
            "--root",
            str(tmp_path),
            "--database",
            str(db),
            "--input",
            str(payload_path),
            "--da51",
            "0xDA51800100000000",
        ]
    )
    assert code == 0
    out = capsys.readouterr().out
    assert "edge_count\t1" in out
    assert "authority\tnavigation-enrichment-only" in out

    code = main(
        [
            "xpollenation",
            "show",
            "rhea",
            "RHEA:11920",
            "--root",
            str(tmp_path),
            "--database",
            str(db),
        ]
    )
    assert code == 0
    out = capsys.readouterr().out
    assert "da51\t0xDA51800100000000" in out
    assert "edge\tedge:pcbd1\trhea:RHEA:11920\tcatalysed-by\tuniprot:P61457" in out
