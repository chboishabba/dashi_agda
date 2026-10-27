import json
from pathlib import Path

from agda_preflight.source_index import SourceIndex


def test_catalog_tolerates_mapping_and_string_interface_entries(tmp_path: Path):
    db = tmp_path / "index.sqlite3"
    with SourceIndex(tmp_path, db) as index:
        interface = {
            "functions": {"foo": {"name": "foo", "type": "Nat"}},
            "constructors": ["mkFoo"],
            "exports": {"bar": {"kind": "function", "type": "Bool"}},
        }
        index.connection.execute(
            """
            INSERT OR REPLACE INTO modules(
                path, module_name, mtime_ns, size, source_sha256,
                api_base_sha256, api_fingerprint, public_imports_json,
                interface_json, dependency_fingerprint, diagnostics_json,
                top_diagnostic_json, top_fixable_diagnostic_json, updated_ns
            ) VALUES(?, ?, 0, 0, '', '', '', '[]', ?, '', '[]', '', '', 0)
            """,
            ("DASHI/Core/Test.agda", "DASHI.Core.Test", json.dumps(interface)),
        )
        index.connection.commit()
        count = index.refresh_semantic_catalog()
        rows = index.search_symbols("foo", include_history=True)

    assert count >= 3
    assert rows[0]["qualified_name"] == "DASHI.Core.Test.foo"
