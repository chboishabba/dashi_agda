"""Tests for non-promoting local-byte receipts, not empirical results."""
import hashlib
import zipfile

import pytest

from scripts.audit_wong2022_source_bytes import file_digest_receipt


def _xlsx_stub(path):
    with zipfile.ZipFile(path, "w") as archive:
        archive.writestr("xl/workbook.xml", "<workbook />")
    return path


def test_local_workbook_digest_is_not_publisher_authentication(tmp_path):
    path = _xlsx_stub(tmp_path / "source-data.xlsx")
    data = path.read_bytes()
    expected = hashlib.sha256(data).hexdigest()
    result = file_digest_receipt(
        path, kind="source_data_xlsx", independently_expected_sha256=expected
    )
    assert result["sha256"] == expected
    assert result["byte_count"] == len(data)
    assert result["external_expected_digest_matched"] is True
    assert result["publisher_file_identity_authenticated"] is False
    assert result["paper_figure_same_object_authenticated"] is False
    assert result["underlying_values_analysed"] is False
    assert result["independent_experiment_verification"] is False


def test_unverified_workbook_source_is_never_claimed_verified(tmp_path):
    path = _xlsx_stub(tmp_path / "source-data.xlsx")
    result = file_digest_receipt(path, kind="source_data_xlsx")
    assert result["external_expected_digest_matched"] is False
    assert result["publisher_file_identity_authenticated"] is False


def test_missing_workbook_structure_fails_closed(tmp_path):
    path = tmp_path / "wrong.xlsx"
    with zipfile.ZipFile(path, "w") as archive:
        archive.writestr("not-a-workbook", "text")
    with pytest.raises(ValueError, match="xl/workbook.xml"):
        file_digest_receipt(path, kind="source_data_xlsx")


def test_bad_expected_hash_rejected(tmp_path):
    path = _xlsx_stub(tmp_path / "source-data.xlsx")
    with pytest.raises(ValueError, match="64 hexadecimal"):
        file_digest_receipt(path, kind="source_data_xlsx", independently_expected_sha256="abc")
    with pytest.raises(ValueError, match="do not match"):
        file_digest_receipt(path, kind="source_data_xlsx", independently_expected_sha256="0" * 64)


def test_pdf_header_is_only_container_signal(tmp_path):
    path = tmp_path / "supplementary.pdf"
    path.write_bytes(b"%PDF-1.7\nminimal mock bytes")
    result = file_digest_receipt(path, kind="supplementary_pdf")
    assert result["container_signature_checked"] is True
    assert result["publisher_file_identity_authenticated"] is False
    assert result["underlying_values_analysed"] is False
    path.write_bytes(b"not a pdf")
    with pytest.raises(ValueError, match="%PDF-"):
        file_digest_receipt(path, kind="supplementary_pdf")
