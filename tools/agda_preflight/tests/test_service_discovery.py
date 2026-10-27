import json
from pathlib import Path

from agda_preflight.service import DashiAgdaService


def test_service_exposes_discovery_and_lineage_without_parsing(tmp_path: Path):
    service = DashiAgdaService(root=tmp_path, index_path=tmp_path / "index.sqlite3")
    try:
        service.index.connection.execute(
            """
            INSERT OR REPLACE INTO modules(
                path, module_name, mtime_ns, size, source_sha256,
                api_base_sha256, api_fingerprint, public_imports_json,
                interface_json, dependency_fingerprint, diagnostics_json,
                top_diagnostic_json, top_fixable_diagnostic_json, updated_ns
            ) VALUES(?, ?, 0, 0, '', '', '', '[]', ?, '', '[]', '', '', 0)
            """,
            (
                "DASHI/Core/Foo.agda",
                "DASHI.Core.Foo",
                json.dumps({"functions": [{"name": "target", "type": "Nat → Nat"}]}),
            ),
        )
        service.index.connection.commit()
        service.index.refresh_semantic_catalog()
        receipt = service.discover("target")
        lineage = service.round_lineage()
    finally:
        service.close()

    assert receipt["live_matches"][0]["name"] == "target"
    assert receipt["absence_claim_permitted"] is False
    assert lineage == {"families": []}
