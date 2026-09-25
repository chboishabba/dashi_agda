from __future__ import annotations

import hashlib
from importlib import metadata
from pathlib import Path
from typing import Iterable, Tuple


_PACKAGE_ROOT = Path(__file__).resolve().parent

_INTERFACE_FILES = (
    "ast_index.py",
    "interfaces.py",
    "shapes.py",
)

_DIAGNOSTIC_FILES = (
    "checker.py",
    "rules.py",
    "evidence.py",
    "fix_engine.py",
    "fixes.py",
)


def _package_version(name: str) -> str:
    try:
        return metadata.version(name)
    except metadata.PackageNotFoundError:
        return "missing"


def _fingerprint(
    files: Iterable[str],
    *,
    prefix: str,
    extra: Iterable[Tuple[str, str]] = (),
) -> str:
    digest = hashlib.sha256()
    digest.update(prefix.encode("utf-8"))
    digest.update(b"\n")
    for name, value in sorted(extra):
        digest.update(name.encode("utf-8"))
        digest.update(b"=")
        digest.update(value.encode("utf-8"))
        digest.update(b"\n")
    for relative in sorted(set(files)):
        path = _PACKAGE_ROOT / relative
        digest.update(relative.encode("utf-8"))
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\n")
    return digest.hexdigest()


def analyzer_fingerprints() -> Tuple[str, str]:
    parser_versions = (
        ("tree-sitter", _package_version("tree-sitter")),
        ("tree-sitter-agda", _package_version("tree-sitter-agda")),
    )
    interface = _fingerprint(
        _INTERFACE_FILES,
        prefix="dashi-agda-interface-v1",
        extra=parser_versions,
    )
    diagnostics = _fingerprint(
        (*_INTERFACE_FILES, *_DIAGNOSTIC_FILES),
        prefix="dashi-agda-diagnostics-v1",
        extra=(
            *parser_versions,
            ("interface", interface),
        ),
    )
    return interface, diagnostics
