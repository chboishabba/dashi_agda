#!/usr/bin/env python3
"""Pinned external lean4export checker runner; evidence, NOT admission.

Accepts the immutable PendingExport contract and invokes an operator-pinned
checker (e.g. a Nix-built Tenet checker) without a shell. Exit zero records
an observation; only separately authenticated checker policy and trusted
world-builder authority may promote mathematical proof status.
"""
from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
from pathlib import Path
import os
import re
import subprocess
import tempfile

from lean_world_builder_contract import PendingExport

HEX64 = re.compile(r"[0-9a-f]{64}\Z")


class CheckerError(ValueError):
    pass


@dataclass(frozen=True)
class ExternalCheckReceipt:
    handoff_key: str
    artifact_sha256: str
    executable_sha256: str
    executable_path: str
    argv: tuple[str, ...]
    stdout_sha256: str
    stderr_sha256: str
    status: str = "external-checker-exit-zero-uncertified"
    world_admitted: bool = False
    kernel_certified: bool = False


def check_native_export(export: PendingExport, executable: Path, *,
                        expected_executable_sha256: str,
                        arguments: tuple[str, ...] = ("check",),
                        timeout: int = 180, max_output_bytes: int = 8_000_000
                        ) -> ExternalCheckReceipt:
    """Run a configured checker against exact bytes, fail closed.

    The supplied executable MUST be trusted by an external pinning policy;
    matching its hash is necessary but does not establish its correctness.
    Arguments are operator-controlled and may not interpolate artifact paths.
    The checked file is always the final positional argument.
    """
    if not isinstance(export, PendingExport):
        raise CheckerError("PendingExport required")
    if sha256(export.artifact).hexdigest() != export.artifact_sha256:
        raise CheckerError("export content identity mismatch")
    if not isinstance(expected_executable_sha256, str) or not HEX64.fullmatch(
            expected_executable_sha256):
        raise CheckerError("missing immutable checker executable digest")
    if not isinstance(timeout, int) or not 1 <= timeout <= 1800:
        raise CheckerError("invalid checker timeout")
    if not isinstance(max_output_bytes, int) or max_output_bytes < 0:
        raise CheckerError("invalid output budget")
    if (not isinstance(arguments, tuple) or
        any(not isinstance(arg, str) or not arg or "\x00" in arg
            for arg in arguments)):
        raise CheckerError("invalid operator checker arguments")
    executable = Path(executable).resolve(strict=True)
    if not executable.is_file() or not os.access(executable, os.X_OK):
        raise CheckerError("checker executable unavailable")
    executable_bytes_hash = sha256(executable.read_bytes()).hexdigest()
    if executable_bytes_hash != expected_executable_sha256:
        raise CheckerError("checker executable pin mismatch")
    with tempfile.TemporaryDirectory(prefix="dashi-lean-check-") as td:
        root = Path(td)
        native = root / "original.ndjson"
        native.write_bytes(export.artifact)
        stdout = root / "stdout"
        stderr = root / "stderr"
        argv = (str(executable), *arguments, str(native))
        # No shell, user tokens, SSH agent or ambient Python path supplied.
        env = {"PATH": "/usr/bin:/bin", "HOME": td, "LC_ALL": "C", "TZ": "UTC"}
        try:
            with stdout.open("wb") as out, stderr.open("wb") as err:
                completed = subprocess.run(
                    argv, cwd=td, env=env, stdin=subprocess.DEVNULL,
                    stdout=out, stderr=err, check=False, timeout=timeout)
        except (OSError, subprocess.TimeoutExpired) as exc:
            raise CheckerError("external checker unavailable or timed out") from exc
        if (stdout.stat().st_size > max_output_bytes or
            stderr.stat().st_size > max_output_bytes):
            raise CheckerError("external checker output exceeded budget")
        if completed.returncode != 0:
            raise CheckerError("external checker rejected native export")
        if sha256(executable.read_bytes()).hexdigest() != expected_executable_sha256:
            raise CheckerError("checker executable changed during run")
        if sha256(native.read_bytes()).hexdigest() != export.artifact_sha256:
            raise CheckerError("checker modified staged native artifact")
        return ExternalCheckReceipt(
            export.handoff_key, export.artifact_sha256,
            expected_executable_sha256, str(executable),
            tuple(arguments), sha256(stdout.read_bytes()).hexdigest(),
            sha256(stderr.read_bytes()).hexdigest())
