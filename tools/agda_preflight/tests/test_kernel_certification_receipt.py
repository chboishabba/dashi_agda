from __future__ import annotations

import hashlib
from pathlib import Path
import shutil
import subprocess

import pytest

from agda_preflight.kernel_certification import (
    _agda_check_command,
    _isolated_agda_workspace,
    build_kernel_certification_receipt,
    certify_artifact,
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


def _artifact_receipt_for(path: Path) -> dict:
    payload = path.read_bytes()
    digest = "sha256:" + hashlib.sha256(payload).hexdigest()
    uri = path.resolve().as_uri()
    return {
        "schemaVersion": "artifact-resolution-receipt/v1",
        "logicalArtifactRef": "formal-proof:mabo@rev#formal-proof-source",
        "contentDigest": digest,
        "verified": True,
        "authority": "transport-only",
        "establishesProof": False,
        "objectRef": {"sink": "file", "uri": uri},
        "transport": {"sink": "file", "uri": uri},
    }


def _populate_fake_agda_dependencies(root: Path) -> None:
    dashi_library = root / "dashi-agda.agda-lib"
    dashi_library.write_text(
        "name: dashi-agda\n"
        "depend: standard-library\n"
        "        dchott-agda\n"
        "        bishop\n"
        "        cubical-0.9\n"
        "include: .\n"
        "         bishop\n",
        encoding="utf-8",
    )
    (root / "bishop.agda-lib").write_text(
        "name: bishop\ninclude: vendor/bishop\n", encoding="utf-8"
    )
    (root / "dchott-agda.agda-lib").write_text(
        "name: dchott-agda\ninclude: DCHoTT-Agda\n", encoding="utf-8"
    )
    (root / "cubical").mkdir()
    (root / "cubical/cubical.agda-lib").write_text(
        "name: cubical-0.9\ninclude: .\n", encoding="utf-8"
    )
    (root / "vendor/bishop").mkdir(parents=True)
    (root / "vendor/bishop/Prelude.agda").write_text(
        "module Prelude where\n", encoding="utf-8"
    )
    (root / "DCHoTT-Agda").mkdir()
    (root / "DCHoTT-Agda/Prelude.agda").write_text(
        "module Prelude where\n", encoding="utf-8"
    )


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


def test_agda_certification_invokes_kernel_on_materialized_source_in_single_library_workspace(
    tmp_path: Path, monkeypatch
) -> None:
    root = tmp_path / "repo"
    source = root / "DASHI/Law/SensibLawMaboBrennanRecognitionFormalDemandExact.agda"
    source.parent.mkdir(parents=True)
    source.write_text(
        "module DASHI.Law.SensibLawMaboBrennanRecognitionFormalDemandExact where\n",
        encoding="utf-8",
    )
    _populate_fake_agda_dependencies(root)
    # A DASHI import may transitively reference an Agda module at repo root.
    (root / "Base369.agda").write_text(
        "module Base369 where\n", encoding="utf-8"
    )
    (root / "RootTransit.agda").write_text(
        "module RootTransit where\nopen import Base369\n", encoding="utf-8"
    )

    home = tmp_path / "home"
    (home / ".agda").mkdir(parents=True)
    (home / ".agda/libraries").write_text(
        "/opt/agda/standard-library.agda-lib\n",
        encoding="utf-8",
    )
    monkeypatch.setenv("HOME", str(home))

    observed: dict[str, object] = {}

    def fake_run(command, *, cwd=None, check=False, capture_output=False, text=False):
        command = list(command)
        if command[:3] == ["git", "-C", str(root)] and command[3:] == ["rev-parse", "HEAD"]:
            return subprocess.CompletedProcess(command, 0, stdout="deadbeef\n", stderr="")
        if command == ["agda", "--version"]:
            return subprocess.CompletedProcess(command, 0, stdout="Agda version 2.8.0\n", stderr="")
        if command and command[0] == "agda":
            workspace = Path(cwd)
            workspace_source = workspace / "DASHI/Law/SensibLawMaboBrennanRecognitionFormalDemandExact.agda"
            observed["command"] = command
            observed["cwd"] = workspace
            observed["library_files"] = sorted(path.name for path in workspace.glob("*.agda-lib"))
            observed["source_is_file"] = workspace_source.is_file()
            observed["source_is_symlink"] = workspace_source.is_symlink()
            observed["source_bytes"] = workspace_source.read_bytes()
            observed["root_closure_files"] = {
                name: (workspace / name).read_bytes()
                for name in ("Base369.agda", "RootTransit.agda")
            }
            assert not (workspace / "Base369.agda").is_symlink()
            observed["source_resolved"] = workspace_source.resolve()
            library_flag = next(arg for arg in command if arg.startswith("--library-file="))
            registry = Path(library_flag.split("=", 1)[1])
            observed["registry"] = registry.read_text(encoding="utf-8")
            observed["temporary_dashi_library"] = (workspace / "dashi-agda.agda-lib").read_text(encoding="utf-8")
            observed["staged_import_is_regular"] = (workspace / "DASHI/Law/SensibLawMaboBrennanRecognitionFormalDemandExact.agda").is_file()
            assert str(root.resolve()) not in observed["temporary_dashi_library"]
            assert str(root / "dashi-agda.agda-lib") not in observed["registry"]
            assert str(workspace / "dashi-agda.agda-lib") in observed["registry"]
            return subprocess.CompletedProcess(command, 0, stdout=b"checked", stderr=b"")
        raise AssertionError(f"unexpected subprocess invocation: {command}")

    monkeypatch.setattr(subprocess, "run", fake_run)

    artifact = _artifact_receipt_for(source)
    receipt = certify_artifact(
        artifact_resolution_receipt=artifact,
        demand_ref="formal-demand:mabo:1",
        obligation_ref="legal-obligation:mabo:1",
        statement_digest="sha256:" + "11" * 32,
        da51_address=None,
        checker="agda",
        source_root=root,
        result_kind="formal-proof",
    )

    assert observed["cwd"] != root
    assert observed["library_files"] == ["dashi-agda.agda-lib"]
    assert observed["source_is_file"] is True
    assert observed["source_is_symlink"] is False
    assert observed["source_bytes"] == source.read_bytes()
    assert observed["root_closure_files"]["Base369.agda"] == (root / "Base369.agda").read_bytes()
    assert observed["root_closure_files"]["RootTransit.agda"] == (root / "RootTransit.agda").read_bytes()
    assert observed["source_resolved"] != source.resolve()
    assert observed["staged_import_is_regular"] is True
    assert str(root.resolve()) not in observed["temporary_dashi_library"]
    assert observed["command"][-1] == "DASHI/Law/SensibLawMaboBrennanRecognitionFormalDemandExact.agda"
    assert "-l" in observed["command"] and "dashi-agda" in observed["command"]
    registry = str(observed["registry"])
    assert "/opt/agda/standard-library.agda-lib" in registry
    assert str(root / "bishop.agda-lib") in registry
    assert str(root / "dchott-agda.agda-lib") in registry
    assert str(root / "cubical/cubical.agda-lib") in registry
    assert receipt["artifactUri"] == source.resolve().as_uri()
    assert receipt["artifactDigest"] == artifact["contentDigest"]
    assert receipt["sourceRevision"] == "git:deadbeef"


def test_real_agda_runs_against_materialized_temporary_witness_source() -> None:
    if shutil.which("agda") is None:
        pytest.skip("Agda executable is not available")

    repo_root = Path(__file__).resolve().parents[3]
    source = repo_root / "DASHI/Law/SensibLawMaboBrennanRecognitionFormalDemandExact.agda"
    if not source.is_file():
        pytest.skip("live Mabo witness is not present in this checkout")
    required_populated = (
        repo_root / "vendor/bishop",
        repo_root / "DCHoTT-Agda",
        repo_root / "cubical",
    )
    if any(not path.is_dir() or not any(path.iterdir()) for path in required_populated):
        pytest.skip("canonical Agda dependencies are not populated in this checkout")

    expected_digest = "sha256:" + hashlib.sha256(source.read_bytes()).hexdigest()
    relative_source = source.relative_to(repo_root)

    with _isolated_agda_workspace(
        root=repo_root,
        relative_source=relative_source,
        original_source=source,
        expected_digest=expected_digest,
    ) as (workspace, library_registry):
        workspace_source = workspace / relative_source
        assert workspace_source.is_file()
        assert not workspace_source.is_symlink()
        assert workspace_source.resolve() != source.resolve()
        assert str(repo_root.resolve()) not in (workspace / "dashi-agda.agda-lib").read_text(encoding="utf-8")
        registered_libraries = library_registry.read_text(encoding="utf-8").splitlines()
        assert str(workspace / "dashi-agda.agda-lib") in registered_libraries
        assert str(repo_root / "dashi-agda.agda-lib") not in registered_libraries
        assert "sha256:" + hashlib.sha256(workspace_source.read_bytes()).hexdigest() == expected_digest
        checked = subprocess.run(
            _agda_check_command(library_registry, relative_source),
            cwd=workspace,
            check=False,
            capture_output=True,
        )
        assert checked.returncode == 0, (
            checked.stdout.decode("utf-8", errors="replace")
            + "\n"
            + checked.stderr.decode("utf-8", errors="replace")
        )


def test_agda_certification_requires_populated_canonical_dependencies(
    tmp_path: Path, monkeypatch
) -> None:
    root = tmp_path / "repo"
    source = root / "DASHI/Law/Proof.agda"
    source.parent.mkdir(parents=True)
    source.write_text("module DASHI.Law.Proof where\n", encoding="utf-8")
    (root / "dashi-agda.agda-lib").write_text("name: dashi-agda\n", encoding="utf-8")

    monkeypatch.setattr(
        subprocess,
        "run",
        lambda command, **kwargs: subprocess.CompletedProcess(command, 0, stdout="deadbeef\n", stderr=""),
    )

    try:
        certify_artifact(
            artifact_resolution_receipt=_artifact_receipt_for(source),
            demand_ref="demand:1",
            obligation_ref="obligation:1",
            statement_digest="sha256:" + "11" * 32,
            da51_address=None,
            checker="agda",
            source_root=root,
        )
    except ValueError as error:
        assert "canonical Agda dependency" in str(error)
    else:
        raise AssertionError("Agda checker must fail closed when canonical dependencies are not populated")
