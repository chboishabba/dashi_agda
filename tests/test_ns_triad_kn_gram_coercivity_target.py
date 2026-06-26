from __future__ import annotations

import json
import subprocess
import tempfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_triad_kn_gram_coercivity_decomposition.py"
DOC = REPO_ROOT / "docs" / "ns_triad_kn_gram_coercivity_target.md"
RECEIPT = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSTriadKNGramCoercivityTargetReceipt.agda"
)


def _payload_from_stdout(stdout: str) -> dict:
    lines = [line for line in stdout.splitlines() if line.strip()]
    return json.loads(lines[-1])


def test_gram_coercivity_decomposition_runs() -> None:
    out_dir = Path(tempfile.gettempdir()) / "dashi_ns_triad_kn_gram_coercivity_decomposition"
    if out_dir.exists():
        for path in sorted(out_dir.rglob("*"), reverse=True):
            if path.is_file():
                path.unlink()
            elif path.is_dir():
                path.rmdir()
    result = subprocess.run(
        ["python", str(SCRIPT), "--output-dir", str(out_dir)],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    payload = _payload_from_stdout(result.stdout)
    assert payload["contract"] == "ns_triad_kn_gram_coercivity_decomposition"
    assert payload["fail_closed"] is True
    assert payload["candidate_only"] is True
    assert payload["sampled_schur_script_match"] is True
    assert len(payload["rows"]) == 4
    assert len(payload["lemma_rows"]) == 4
    assert payload["log_entries"][0]["message"] == "started Gram-coercivity decomposition run"
    assert payload["log_entries"][-1]["message"] == "completed Gram-coercivity decomposition run"
    assert float(payload["elapsed_ms"]) >= 0.0
    for row in payload["rows"]:
        assert row["diag_contribution"] > row["offdiag_contribution"]
        assert row["coherence_mu"] < 0.2
        assert row["verdict"] == "coercivity_plausible"


def test_gram_coercivity_doc_and_receipt_exist() -> None:
    assert DOC.is_file(), f"missing {DOC}"
    doc_text = DOC.read_text(encoding="utf-8")
    assert "Retired:" in doc_text
    assert "Live:" in doc_text
    assert "Open theorem:" in doc_text
    assert "inf_A lambda_min(K_N(A)) >= c / N" in doc_text
    assert "scripts/ns_triad_kn_gram_coercivity_decomposition.py" in doc_text

    assert RECEIPT.is_file(), f"missing {RECEIPT}"
    receipt_text = RECEIPT.read_text(encoding="utf-8")
    assert "NSTriadKNGramCoercivityTargetReceipt" in receipt_text
    assert "docs/ns_triad_kn_gram_coercivity_target.md" in receipt_text
    assert "scripts/ns_triad_kn_gram_coercivity_decomposition.py" in receipt_text
    assert 'candidateOnly ≡ true' in receipt_text
    assert 'theoremPromoted ≡ false' in receipt_text
