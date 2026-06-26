from __future__ import annotations

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
RECEIPT = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSTriadKNExactAlgebraicDefinitionReceipt.agda"
)
DOC = REPO_ROOT / "docs" / "ns_triad_kn_KN_exact_algebraic_definition.md"


def test_exact_algebraic_definition_receipt_exists() -> None:
    assert RECEIPT.is_file(), f"missing {RECEIPT}"
    text = RECEIPT.read_text(encoding="utf-8")
    assert "NSTriadKNExactAlgebraicDefinitionReceipt" in text
    assert "docs/ns_triad_kn_KN_exact_algebraic_definition.md" in text
    assert "scripts/ns_triad_kn_matrix_free_operator.py" in text
    assert "scripts/ns_triad_kn_exact_identity_scan.py" in text
    assert '"candidate_checked"' in text
    assert "exactKDefinitionWritten ≡ true" in text
    assert "scriptObjectMatched ≡ true" in text
    assert "gramCoercivityClosed ≡ false" in text


def test_exact_algebraic_definition_doc_exists() -> None:
    assert DOC.is_file(), f"missing {DOC}"
    text = DOC.read_text(encoding="utf-8")
    assert "A_m = sqrt(max(p_m, 0))" in text
    assert "w_t^pair(A) = w_t(A) / 3" in text
    assert "L_abs(A) = B_N^T W_abs(A) B_N" in text
    assert "L_neg(A) = B_N^T W_neg(A) B_N" in text
    assert "L_signed_norm = I - 2 K_N" in text
    assert "lambda_min(K_N(A)) = inf_(|v|_2 = 1) <v, K_N(A) v> >= c / N" in text
