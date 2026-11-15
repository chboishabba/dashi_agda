#!/usr/bin/env python3
"""Ephemeral Lean 4 source elaboration with pinned Nix shell and compiled cache.

Input: exact verified source receipt and bytes from lean_world_source_world.
This compiles a SINGLE Lean file, not a recursive checkout or untrusted source
world -> theorem promotion. Dependencies must already be compiled into an
explicit, pinned directory; callers provide an exact dependency closure digest.

An exit status of zero is a Lean front-end compilation receipt, NOT a guarantee
that exported declarations are axiom/sorry-free, nor a canonical kernel-term
serialization. A separate validated Lean exporter is required for FibreIndex.

Cache keys bind source bytes, pinned profile, dependency closure fingerprint,
Lean executable version, relative module path, and compilation flags.
"""
from __future__ import annotations
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import tempfile
from typing import Callable

from lean_world_source_world import SourceWorldBuilder, SourceConflict

def compiled_dependency_digest(root: Path | None) -> str:
    """Hash exact relative filenames and OLean bytes, not caller assertions."""
    h = hashlib.sha256()
    if root is None:
        h.update(b"dashi-empty-compiled-dependency-closure-v1")
        return h.hexdigest()
    if not root.is_dir():
        raise ElaborationError("compiled dependency closure directory missing")
    paths = sorted(p for p in root.rglob("*.olean") if p.is_file())
    for file in paths:
        relative = file.relative_to(root).as_posix().encode("utf-8")
        h.update(len(relative).to_bytes(8, "big"))
        h.update(relative)
        with file.open("rb") as stream:
            while chunk := stream.read(65536):
                h.update(chunk)
    return h.hexdigest()


HEX = re.compile(r"^[0-9a-f]{64}$")
MODULE = re.compile(r"^[A-Za-z0-9_./-]+\.lean$")


class ElaborationError(RuntimeError):
    pass


@dataclass(frozen=True)
class Result:
    status: str
    source_sha256: str
    closure_digest: str
    cache_key: str
    olean_sha256: str | None
    compiler_version: str
    reused: bool
    stdout: str
    stderr: str


def _sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _run(argv: list[str], *, cwd: Path, env: dict,
         input_bytes: bytes | None = None, timeout: int = 180):
    try:
        return subprocess.run(argv, input=input_bytes, cwd=cwd, env=env,
                              capture_output=True, timeout=timeout,
                              check=False)
    except (OSError, subprocess.TimeoutExpired) as e:
        raise ElaborationError(f"worker execution failed ({type(e).__name__})") from e


class EphemeralLeanWorker:
    def __init__(self, *, flake: Path, cache: Path, closure_digest: str,
                 dependency_olean_dir: Path | None = None,
                 command: tuple[str, ...] | None = None,
                 timeout: int = 180):
        if not HEX.fullmatch(closure_digest):
            raise ValueError("explicit 64-digit pinned dependency closure digest required")
        self.flake = flake.resolve()
        self.cache = cache.resolve()
        self.closure_digest = closure_digest
        self.dependency_olean_dir = (
            dependency_olean_dir.resolve() if dependency_olean_dir else None)
        if command is None:
            command = ("nix", "develop", str(self.flake) + "#lean-world",
                       "--command", "lean")
        if not command or any(not part for part in command):
            raise ValueError("nonempty argv command required")
        self.command = tuple(command)
        self.timeout = timeout

    @staticmethod
    def safe_environment(home: Path | None = None) -> dict[str, str]:
        # Lean macros and elaborators may execute code. Never pass OAuth/API
        # tokens, AWS/cloud credentials, SSH agent sockets or unrelated user
        # secrets into a source-controlled compiler subprocess.
        allowed = (
            "PATH", "USER", "LOGNAME", "LANG", "LC_ALL", "LC_CTYPE",
            "SSL_CERT_FILE", "NIX_PATH", "NIX_CONFIG", "NIX_SSL_CERT_FILE",
            "NIX_REMOTE", "NIX_PROFILES", "TZ",
        )
        env = {key:os.environ[key] for key in allowed if key in os.environ}
        if home:
            env["HOME"] = str(home)
        return env

    def compiler_version(self) -> str:
        command = list(self.command) + ["--version"]
        output = _run(command, cwd=self.flake, env=self.safe_environment(),
                      timeout=self.timeout)
        if output.returncode or not output.stdout.strip():
            raise ElaborationError("pinned Lean compiler version unavailable")
        return output.stdout.decode("utf-8", errors="replace").strip()

    def elaborate(self, receipt: dict, source: bytes, module: str) -> Result:
        SourceWorldBuilder._validate_receipt(receipt, source)
        if (not MODULE.fullmatch(module) or
            any(part in ("", ".", "..") for part in PurePosixPath(module).parts)):
            raise ValueError("unsafe Lean module name")
        observed_closure = compiled_dependency_digest(self.dependency_olean_dir)
        if observed_closure != self.closure_digest:
            raise ElaborationError("compiled dependency closure contents do not match pinned digest")
        version = self.compiler_version()
        lock = self.flake / "flake.lock"
        if not lock.is_file() and self.command[:1] == ("nix",):
            raise ElaborationError("pinned Nix flake.lock missing")
        lock_digest = _sha(lock.read_bytes()) if lock.is_file() else "external-compiler"
        identity = {
            "format": "dashi-lean-world-olean-cache-v1",
            "compiler_version": version,
            "flake_lock_sha256": lock_digest,
            "source_sha256": _sha(source),
            "repository": receipt["repository"],
            "revision": receipt["revision"],
            "path": receipt["path"],
            "module": module,
            "closure_digest": self.closure_digest,
            "argv": list(self.command),
        }
        cache_key = _sha(json.dumps(identity, sort_keys=True).encode())
        directory = self.cache / cache_key[:2] / cache_key
        out = directory / "module.olean"
        manifest = directory / "receipt.json"
        if manifest.is_file() and out.is_file():
            try:
                previous = json.loads(manifest.read_text("utf-8"))
                if (previous.get("identity") == identity and
                    previous.get("olean_sha256") == _sha(out.read_bytes())):
                    return Result("lean-compiled-not-exported", _sha(source),
                                  self.closure_digest, cache_key,
                                  previous["olean_sha256"], version,
                                  True, "", "")
            except (OSError, ValueError):
                pass
        self.cache.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="dashi-lean-worker-") as td:
            root = Path(td)
            file = root / module
            file.parent.mkdir(parents=True, exist_ok=True)
            file.write_bytes(source)
            target = root / "output.olean"
            (root / "home").mkdir()
            env = self.safe_environment(root / "home")
            if self.dependency_olean_dir:
                if not self.dependency_olean_dir.is_dir():
                    raise ElaborationError("pinned compiled dependency directory missing")
                env["LEAN_PATH"] = str(self.dependency_olean_dir)
            elif b"import " in source:
                # Imported modules may use Lean's standard library, but an
                # arbitrary package/dependency graph needs an explicit closure.
                pass
            argv = list(self.command) + ["-o", str(target), str(file)]
            result = _run(argv, cwd=root, env=env, timeout=self.timeout)
            if result.returncode:
                return Result("lean-elaboration-failed", _sha(source),
                              self.closure_digest, cache_key, None, version,
                              False, result.stdout.decode(errors="replace")[-4096:],
                              result.stderr.decode(errors="replace")[-4096:])
            if not target.is_file():
                raise ElaborationError("Lean reported success without compiled .olean")
            compiled = target.read_bytes()
            digest = _sha(compiled)
            directory.mkdir(parents=True, exist_ok=True)
            # Atomic replacements; no partial cache receipt admitted.
            temp_olean = directory / "module.olean.tmp"
            temp_manifest = directory / "receipt.json.tmp"
            temp_olean.write_bytes(compiled)
            temp_manifest.write_text(json.dumps(
                {"identity": identity, "olean_sha256": digest},
                sort_keys=True), encoding="utf-8")
            os.replace(temp_olean, out)
            os.replace(temp_manifest, manifest)
            return Result("lean-compiled-not-exported", _sha(source),
                          self.closure_digest, cache_key, digest, version,
                          False, result.stdout.decode(errors="replace")[-4096:],
                          result.stderr.decode(errors="replace")[-4096:])
