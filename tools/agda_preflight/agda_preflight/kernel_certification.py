from __future__ import annotations

from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
from typing import Any, Iterable, Iterator, Optional
from urllib.parse import unquote, urlparse

_SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")


def _required(name: str, value: Any) -> str:
    text = str(value or "").strip()
    if not text:
        raise ValueError(f"{name} must be non-empty")
    return text


def _digest(name: str, value: Any) -> str:
    text = _required(name, value).lower()
    if not _SHA256_RE.fullmatch(text):
        raise ValueError(f"{name} must be canonical sha256:<64 lowercase hex>")
    return text


def _sha256_bytes(payload: bytes) -> str:
    return "sha256:" + hashlib.sha256(payload).hexdigest()


def _validate_artifact_resolution(receipt: dict[str, Any]) -> tuple[str, str, str]:
    if receipt.get("schemaVersion") != "artifact-resolution-receipt/v1":
        raise ValueError("unsupported artifact-resolution receipt schema")
    if receipt.get("verified") is not True:
        raise ValueError("artifact-resolution receipt must be verified")
    if receipt.get("authority") != "transport-only" or receipt.get("establishesProof") is not False:
        raise ValueError("artifact-resolution receipt must remain transport-only and non-proof")
    logical_ref = _required("logicalArtifactRef", receipt.get("logicalArtifactRef"))
    content_digest = _digest("contentDigest", receipt.get("contentDigest"))
    object_ref = receipt.get("objectRef") or {}
    transport = receipt.get("transport") or {}
    if object_ref.get("sink") != "file" or transport.get("sink") != "file":
        raise ValueError("independent local kernel runner currently requires a file transport receipt")
    object_uri = _required("objectRef.uri", object_ref.get("uri"))
    transport_uri = _required("transport.uri", transport.get("uri"))
    if object_uri != transport_uri:
        raise ValueError("artifact object and transport URI disagree")
    return logical_ref, content_digest, object_uri


def build_kernel_certification_receipt(
    *,
    artifact_resolution_receipt: dict[str, Any],
    demand_ref: str,
    obligation_ref: str,
    statement_digest: str,
    da51_address: Optional[str],
    checker: str,
    checker_revision: str,
    source_revision: str,
    result_kind: str,
    dependencies: Iterable[str],
    stdout_digest: str,
    stderr_digest: str,
) -> dict[str, Any]:
    artifact_ref, artifact_digest, artifact_uri = _validate_artifact_resolution(
        artifact_resolution_receipt
    )
    dependency_refs = tuple(_required("dependency", value) for value in dependencies)
    checker_name = _required("checker", checker)
    if checker_name not in {"agda", "lean"}:
        raise ValueError("checker must be agda or lean")
    da51 = None if da51_address is None else _required("da51_address", da51_address)
    return {
        "schemaVersion": "kernel-certification-receipt/v1",
        "demandRef": _required("demand_ref", demand_ref),
        "obligationRef": _required("obligation_ref", obligation_ref),
        "statementDigest": _digest("statement_digest", statement_digest),
        "da51Address": da51,
        "producer": f"{checker_name}-kernel",
        "artifactRef": artifact_ref,
        "artifactDigest": artifact_digest,
        "artifactUri": artifact_uri,
        "checker": checker_name,
        "checkerRevision": _required("checker_revision", checker_revision),
        "sourceRevision": _required("source_revision", source_revision),
        "resultKind": _required("result_kind", result_kind),
        "certificationState": "kernel-certified",
        "dependencies": list(dependency_refs),
        "stdoutDigest": _digest("stdout_digest", stdout_digest),
        "stderrDigest": _digest("stderr_digest", stderr_digest),
        "authority": "formal-checker-only",
        "certifiesFormalResult": True,
        "createsLegalAuthority": False,
        "applicabilityPromoted": False,
        "claimTruthPromoted": False,
    }


def _path_from_file_uri(uri: str) -> Path:
    parsed = urlparse(uri)
    if parsed.scheme != "file":
        raise ValueError("kernel checker requires file:// artifact URI")
    if parsed.netloc not in ("", "localhost"):
        raise ValueError("non-local file URI is not supported")
    return Path(unquote(parsed.path)).resolve()


def _git(root_or_child: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", "-C", str(root_or_child), *args],
        check=True,
        capture_output=True,
        text=True,
    )
    return result.stdout.strip()


def _require_populated_directory(root: Path, relative: str) -> Path:
    directory = root / relative
    if not directory.is_dir() or not any(directory.iterdir()):
        raise ValueError(
            f"canonical Agda dependency is not populated: {relative}; use a checkout with populated submodules"
        )
    return directory


def _canonical_agda_dependency_files(root: Path) -> tuple[Path, ...]:
    canonical_library = root / "dashi-agda.agda-lib"
    bishop_library = root / "bishop.agda-lib"
    dchott_library = root / "dchott-agda.agda-lib"
    cubical_library = root / "cubical/cubical.agda-lib"
    for path in (canonical_library, bishop_library, dchott_library, cubical_library):
        if not path.is_file():
            raise ValueError(f"canonical Agda dependency/library file is missing: {path}")
    _require_populated_directory(root, "vendor/bishop")
    _require_populated_directory(root, "DCHoTT-Agda")
    _require_populated_directory(root, "cubical")
    return canonical_library, bishop_library, dchott_library, cubical_library


def _agda_user_libraries_file() -> Path:
    configured = os.environ.get("AGDA_DIR")
    agda_dir = Path(configured).expanduser() if configured else Path.home() / ".agda"
    return agda_dir / "libraries"


def _write_isolated_library_registry(
    *,
    workspace: Path,
    bishop_library: Path,
    dchott_library: Path,
    cubical_library: Path,
) -> Path:
    registry = workspace / "libraries"
    inherited: list[str] = []
    user_registry = _agda_user_libraries_file()
    if user_registry.is_file():
        for raw in user_registry.read_text(encoding="utf-8").splitlines():
            line = raw.strip()
            if not line or line.startswith("--") or line.startswith("#"):
                continue
            expanded = str(Path(line).expanduser())
            basename = Path(expanded).name
            if basename in {
                "dashi-agda.agda-lib",
                "bishop.agda-lib",
                "dchott-agda.agda-lib",
                "cubical.agda-lib",
            }:
                continue
            if expanded not in inherited:
                inherited.append(expanded)

    canonical_entries = [
        str(bishop_library.resolve()),
        str(dchott_library.resolve()),
        str(cubical_library.resolve()),
        str((workspace / "dashi-agda.agda-lib").resolve()),
    ]
    entries = inherited + [entry for entry in canonical_entries if entry not in inherited]
    registry.write_text("\n".join(entries) + "\n", encoding="utf-8")
    return registry


def _write_isolated_dashi_library(*, root: Path, workspace: Path) -> Path:
    """Create the single project library Agda sees for kernel checking.

    The demanded artifact itself lives physically under ``workspace``. Existing
    DASHI modules are staged as ordinary files inside the temporary source
    root. Never include the original checkout root: doing so introduces two
    definitions of the demanded witness and defeats isolation.
    """
    library = workspace / "dashi-agda.agda-lib"
    library.write_text(
        "name: dashi-agda\n"
        "depend: standard-library\n"
        "        dchott-agda\n"
        "        bishop\n"
        "        cubical-0.9\n"
        "include: .\n",
        encoding="utf-8",
    )
    return library


@contextmanager
def _isolated_agda_workspace(
    *,
    root: Path,
    relative_source: Path,
    original_source: Path,
    expected_digest: str,
) -> Iterator[tuple[Path, Path]]:
    _canonical_library, bishop_library, dchott_library, cubical_library = (
        _canonical_agda_dependency_files(root)
    )
    if not (root / "DASHI").is_dir():
        raise ValueError("canonical DASHI source directory is missing from source root")

    expected = _digest("expected_digest", expected_digest)
    original_bytes = original_source.read_bytes()
    if _sha256_bytes(original_bytes) != expected:
        raise ValueError("original source bytes no longer match the ITIR artifact digest")

    with tempfile.TemporaryDirectory(prefix="dashi-agda-kernel-") as temporary:
        workspace = Path(temporary)
        _write_isolated_dashi_library(root=root, workspace=workspace)

        # Materialise the DASHI tree, not a symlink and not a second include
        # pointing at the original repository root. This gives Agda one
        # canonical module path for both the witness and its local imports.
        shutil.copytree(root / "DASHI", workspace / "DASHI", symlinks=False)
        # DASHI imports can reach top-level modules (e.g. Base369).
        # Materialise root-level Agda modules as ordinary files. This is a
        # conservative compiler-input closure, not independent evidence or a
        # claim that all these modules participate in the proof. Do not add
        # the original checkout to the include path: that would duplicate
        # the demanded witness's module name.
        for root_module in root.glob("*.agda"):
            if not root_module.is_file():
                continue
            staged = workspace / root_module.name
            staged.write_bytes(root_module.read_bytes())
            if staged.is_symlink() or staged.resolve() == root_module.resolve():
                raise ValueError("root-level Agda module escaped isolated workspace")
        workspace_source = workspace / relative_source
        if not workspace_source.is_file():
            raise ValueError("isolated Agda workspace cannot locate its materialized witness")
        if workspace_source.is_symlink():
            raise ValueError("isolated Agda witness cannot be a symlink")
        workspace_source.parent.mkdir(parents=True, exist_ok=True)
        workspace_source.write_bytes(original_bytes)
        if workspace_source.is_symlink():
            raise ValueError("isolated Agda source must be materialized, not symlinked")
        if workspace_source.resolve() == original_source.resolve():
            raise ValueError("isolated Agda source resolved back to the original repository")
        if _sha256_bytes(workspace_source.read_bytes()) != expected:
            raise ValueError("materialized Agda source bytes differ from the ITIR artifact digest")

        library_registry = _write_isolated_library_registry(
            workspace=workspace,
            bishop_library=bishop_library,
            dchott_library=dchott_library,
            cubical_library=cubical_library,
        )
        yield workspace, library_registry


def _agda_check_command(library_registry: Path, relative_source: Path) -> list[str]:
    return [
        "agda",
        f"--library-file={library_registry}",
        "-l",
        "dashi-agda",
        str(relative_source),
    ]


def certify_artifact(
    *,
    artifact_resolution_receipt: dict[str, Any],
    demand_ref: str,
    obligation_ref: str,
    statement_digest: str,
    da51_address: Optional[str],
    checker: Optional[str] = None,
    source_root: Optional[Path] = None,
    result_kind: str = "formal-proof",
    dependencies: Iterable[str] = (),
) -> dict[str, Any]:
    _artifact_ref, expected_digest, uri = _validate_artifact_resolution(
        artifact_resolution_receipt
    )
    source_path = _path_from_file_uri(uri)
    if not source_path.is_file():
        raise ValueError(f"artifact file does not exist: {source_path}")
    original_bytes = source_path.read_bytes()
    observed_digest = _sha256_bytes(original_bytes)
    if observed_digest != expected_digest:
        raise ValueError("artifact bytes no longer match the ITIR resolution receipt")

    checker_name = checker or (
        "agda"
        if source_path.suffix == ".agda"
        else "lean"
        if source_path.suffix == ".lean"
        else None
    )
    if checker_name not in {"agda", "lean"}:
        raise ValueError("checker must be supplied for non-.agda/.lean artifacts")

    root = source_root.resolve() if source_root is not None else Path(
        _git(source_path.parent, "rev-parse", "--show-toplevel")
    ).resolve()
    try:
        relative_source = source_path.relative_to(root)
    except ValueError as error:
        raise ValueError("artifact source is outside the declared source repository") from error
    source_revision = "git:" + _git(root, "rev-parse", "HEAD")

    if checker_name == "agda":
        with _isolated_agda_workspace(
            root=root,
            relative_source=relative_source,
            original_source=source_path,
            expected_digest=expected_digest,
        ) as (workspace, library_registry):
            version = subprocess.run(
                ["agda", "--version"],
                cwd=workspace,
                check=True,
                capture_output=True,
                text=True,
            ).stdout.strip()
            checked = subprocess.run(
                _agda_check_command(library_registry, relative_source),
                cwd=workspace,
                check=False,
                capture_output=True,
            )
    else:
        version = subprocess.run(
            ["lake", "env", "lean", "--version"],
            cwd=root,
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()
        checked = subprocess.run(
            ["lake", "env", "lean", str(relative_source)],
            cwd=root,
            check=False,
            capture_output=True,
        )

    if checked.returncode != 0:
        stderr = checked.stderr.decode("utf-8", errors="replace")
        stdout = checked.stdout.decode("utf-8", errors="replace")
        raise RuntimeError(
            f"{checker_name} kernel check failed with exit {checked.returncode}\nstdout:\n{stdout}\nstderr:\n{stderr}"
        )

    return build_kernel_certification_receipt(
        artifact_resolution_receipt=artifact_resolution_receipt,
        demand_ref=demand_ref,
        obligation_ref=obligation_ref,
        statement_digest=statement_digest,
        da51_address=da51_address,
        checker=checker_name,
        checker_revision=version,
        source_revision=source_revision,
        result_kind=result_kind,
        dependencies=dependencies,
        stdout_digest=_sha256_bytes(checked.stdout),
        stderr_digest=_sha256_bytes(checked.stderr),
    )


def load_receipt(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))
