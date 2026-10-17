from __future__ import annotations

from pathlib import Path

from agda_preflight.kernel_certification import (
    _agda_check_command,
    build_kernel_certification_receipt,
)


def _artifact_receipt() -> dict:
    digest = "sha256:" + "22" * 32
    return {
        "schemaVersion": "artifact-resolution-receipt/v1",
        "logicalArtifactRef": "formal-proof:demo@rev#formal-proof-source",
        "contentDigest": digest,
        "verified": True,
        "authority": "transport-only",
        "establishesProof": False,
        "objectRef": {"sink": "file", "uri": "file:///tmp/proof.agda"},
        "transport": {"sink": "file", "uri": "file:///tmp/proof.agda"},
    }


def test_kernel_receipt_binds_exact_transport_and_demand() -> None:
    receipt = build_kernel_certification_receipt(
        artifact_resolution_receipt=_artifact_receipt(),
        demand_ref="formal-demand:mabo:1",
        obligation_ref="legal-obligation:mabo:1",
        statement_digest="sha256:" + "11" * 32,
        da51_address="0xDA51831100800000",
        checker="agda",
        checker_revision="Agda version 2.8.0",
        source_revision="git:abc123",
        result_kind="formal-proof",
        dependencies=("DASHI.Law.MaboRevisionReopenExact",),
        stdout_digest="sha256:" + "33" * 32,
        stderr_digest="sha256:" + "44" * 32,
    )
    assert receipt["certificationState"] == "kernel-certified"
    assert receipt["artifactRef"] == _artifact_receipt()["logicalArtifactRef"]
    assert receipt["artifactDigest"] == _artifact_receipt()["contentDigest"]
    assert receipt["statementDigest"] == "sha256:" + "11" * 32
    assert receipt["authority"] == "formal-checker-only"
    assert receipt["createsLegalAuthority"] is False
    assert receipt["applicabilityPromoted"] is False
    assert receipt["claimTruthPromoted"] is False


def test_transport_receipt_must_remain_transport_only() -> None:
    artifact = _artifact_receipt()
    artifact["establishesProof"] = True
    try:
        build_kernel_certification_receipt(
            artifact_resolution_receipt=artifact,
            demand_ref="demand:1",
            obligation_ref="obligation:1",
            statement_digest="sha256:" + "11" * 32,
            da51_address=None,
            checker="agda",
            checker_revision="Agda version 2.8.0",
            source_revision="git:abc123",
            result_kind="formal-proof",
            dependencies=(),
            stdout_digest="sha256:" + "33" * 32,
            stderr_digest="sha256:" + "44" * 32,
        )
    except ValueError as error:
        assert "transport-only" in str(error)
    else:
        raise AssertionError("transport receipt with proof authority must fail closed")


def test_agda_checker_selects_named_dashi_library_in_multi_library_root(tmp_path: Path) -> None:
    for name in ("bishop.agda-lib", "dashi-agda.agda-lib", "dchott-agda.agda-lib"):
        (tmp_path / name).write_text(f"name: {name.removesuffix('.agda-lib')}\n", encoding="utf-8")

    source = Path("DASHI/Law/SensibLawMaboBrennanRecognitionFormalDemandExact.agda")
    assert _agda_check_command(tmp_path, source) == [
        "agda",
        "-l",
        "dashi-agda",
        str(source),
    ]


def test_agda_checker_requires_canonical_dashi_library_file(tmp_path: Path) -> None:
    (tmp_path / "bishop.agda-lib").write_text("name: bishop\n", encoding="utf-8")
    try:
        _agda_check_command(tmp_path, Path("DASHI/Law/Proof.agda"))
    except ValueError as error:
        assert "dashi-agda.agda-lib" in str(error)
    else:
        raise AssertionError("Agda checker must fail closed without canonical DASHI library file")
