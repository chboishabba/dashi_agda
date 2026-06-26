from __future__ import annotations

import json
import subprocess
import tempfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
ROWCOL_SCRIPT = REPO_ROOT / "scripts" / "ns_triad_kn_pair_incidence_row_column_audit.py"
ROUTE_SCRIPT = REPO_ROOT / "scripts" / "ns_triad_kn_exact_operator_route_audit.py"
ROWCOL_RECEIPT = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSTriadKNPairIncidenceRowColumnAuditReceipt.agda"
)
ROUTE_RECEIPT = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSTriadKNExactOperatorRouteAuditReceipt.agda"
)
ROWCOL_DOC = REPO_ROOT / "docs" / "ns_triad_kn_pair_incidence_row_column_audit.md"
ROUTE_DOC = REPO_ROOT / "docs" / "ns_triad_kn_exact_operator_route_audit.md"


def _payload_from_stdout(stdout: str) -> dict:
    lines = [line for line in stdout.splitlines() if line.strip()]
    return json.loads(lines[-1])


def test_row_column_audit_script_runs() -> None:
    out_dir = Path(tempfile.gettempdir()) / "dashi_ns_triad_kn_pair_incidence_row_column_audit"
    if out_dir.exists():
        for path in sorted(out_dir.rglob("*"), reverse=True):
            if path.is_file():
                path.unlink()
            elif path.is_dir():
                path.rmdir()
    result = subprocess.run(
        ["python", str(ROWCOL_SCRIPT), "--output-dir", str(out_dir)],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    payload = _payload_from_stdout(result.stdout)
    assert payload["contract"] == "ns_triad_kn_pair_incidence_row_column_audit"
    assert payload["fail_closed"] is True
    assert payload["uniform_profile_independent_bound_closed"] is False
    assert payload["exact_script_constant_column_claim_validated"] is False
    assert "log_entries" in payload
    assert payload["elapsed_ms"] >= 0.0


def test_exact_operator_route_audit_script_runs() -> None:
    out_dir = Path(tempfile.gettempdir()) / "dashi_ns_triad_kn_exact_operator_route_audit"
    if out_dir.exists():
        for path in sorted(out_dir.rglob("*"), reverse=True):
            if path.is_file():
                path.unlink()
            elif path.is_dir():
                path.rmdir()
    result = subprocess.run(
        ["python", str(ROUTE_SCRIPT), "--output-dir", str(out_dir)],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    payload = _payload_from_stdout(result.stdout)
    assert payload["contract"] == "ns_triad_kn_exact_operator_route_audit"
    assert payload["fail_closed"] is True
    assert len(payload["gate_rows"]) == 4
    assert all(row["closed"] is False for row in payload["gate_rows"])
    assert payload["residence_status"]["recorded"] is True
    assert "log_entries" in payload
    assert payload["elapsed_ms"] >= 0.0


def test_route_audit_receipts_and_docs_exist() -> None:
    assert ROWCOL_RECEIPT.is_file()
    rowcol_text = ROWCOL_RECEIPT.read_text(encoding="utf-8")
    assert "NSTriadKNPairIncidenceRowColumnAuditReceipt" in rowcol_text
    assert 'exactScriptConstantColumnClaimValidated ≡ false' in rowcol_text
    assert 'uniformProfileIndependentBoundClosed ≡ false' in rowcol_text

    assert ROUTE_RECEIPT.is_file()
    route_text = ROUTE_RECEIPT.read_text(encoding="utf-8")
    assert "NSTriadKNExactOperatorRouteAuditReceipt" in route_text
    assert "NSTriadKNPairIncidenceRowColumnAuditReceipt" in route_text
    assert "NSSprint99ResidenceTimeAgainstViscosity" in route_text
    assert 'residenceTimeExclusionClosed ≡ false' in route_text

    assert ROWCOL_DOC.is_file()
    assert "column supremum is `O(1)`" in ROWCOL_DOC.read_text(encoding="utf-8")
    assert ROUTE_DOC.is_file()
    route_doc = ROUTE_DOC.read_text(encoding="utf-8")
    assert "SchurResidueScale" in route_doc
    assert "pre-theorem state" in route_doc
