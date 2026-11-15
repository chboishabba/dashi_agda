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
import resource
import signal
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
        def limit_output():
            # A failing or hostile checker cannot write unbounded log files.
            # SIGXFSZ causes nonzero exit, which never authorizes a receipt.
            # Permit one byte beyond the configured budget so the post-run
            # size check can distinguish truncation by RLIMIT_FSIZE from an
            # ordinary checker rejection.  The extra byte is never admitted
            # into the receipt.
            cap = max(1, max_output_bytes + 1)
            resource.setrlimit(resource.RLIMIT_FSIZE, (cap, cap))
        try:
            with stdout.open("wb") as out, stderr.open("wb") as err:
                completed = subprocess.run(
                    argv, cwd=td, env=env, stdin=subprocess.DEVNULL,
                    stdout=out, stderr=err, check=False, timeout=timeout,
                    preexec_fn=limit_output)
        except (OSError, subprocess.TimeoutExpired) as exc:
            raise CheckerError("external checker unavailable or timed out") from exc
        if (stdout.stat().st_size > max_output_bytes or
            stderr.stat().st_size > max_output_bytes):
            raise CheckerError("external checker output exceeded budget")
        # A checker may die from SIGXFSZ or catch EFBIG and exit nonzero
        # after filling the capped log (notably Python flush-on-exit).
        # Both are overflow failures, not ordinary proof rejection.
        if (completed.returncode == -signal.SIGXFSZ or
            (completed.returncode != 0 and
             ((max_output_bytes == 0 and
               (stdout.stat().st_size > 0 or stderr.stat().st_size > 0)) or
              (max_output_bytes > 0 and
               (stdout.stat().st_size >= max_output_bytes or
                stderr.stat().st_size >= max_output_bytes))))):
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


def check_native_export_nanoda(export: PendingExport, executable: Path, *,
                              expected_executable_sha256: str,
                              timeout: int = 180,
                              max_output_bytes: int = 8_000_000
                              ) -> ExternalCheckReceipt:
    """Run pinned Rust nanoda with its documented config-file interface.

    This never grants kernel certification, even when nanoda succeeds. The
    executable SHA-256 is a necessary byte pin, not full closure attestation.
    """
    import json
    from run_lean_world_real_semantic_acceptance import nanoda_policy
    if not isinstance(export, PendingExport):
        raise CheckerError("PendingExport required")
    if sha256(export.artifact).hexdigest() != export.artifact_sha256:
        raise CheckerError("export content identity mismatch")
    if (not isinstance(expected_executable_sha256, str) or
        not HEX64.fullmatch(expected_executable_sha256)):
        raise CheckerError("missing immutable Rust checker digest")
    if not isinstance(timeout, int) or not 1 <= timeout <= 1800:
        raise CheckerError("invalid checker timeout")
    if not isinstance(max_output_bytes, int) or max_output_bytes <= 0:
        raise CheckerError("invalid checker output budget")
    executable = Path(executable).resolve(strict=True)
    if not executable.is_file() or not os.access(executable, os.X_OK):
        raise CheckerError("Rust checker executable unavailable")
    if sha256(executable.read_bytes()).hexdigest() != expected_executable_sha256:
        raise CheckerError("Rust checker executable pin mismatch")
    with tempfile.TemporaryDirectory(prefix="dashi-rust-nanoda-") as td:
        root=Path(td)
        export_path=root/"original.ndjson"
        export_path.write_bytes(export.artifact)
        policy=nanoda_policy()
        policy["export_file_path"]=str(export_path)
        policy["use_stdin"]=False
        config_path=root/"checker-config.json"
        config_path.write_text(json.dumps(policy,sort_keys=True))
        out_path=root/"stdout"
        err_path=root/"stderr"
        def cap_logs():
            resource.setrlimit(resource.RLIMIT_FSIZE,
                               (max_output_bytes,max_output_bytes))
        try:
            with out_path.open("wb") as out, err_path.open("wb") as err:
                result=subprocess.run(
                    (str(executable),str(config_path)),
                    cwd=td,
                    env={"PATH":"/usr/bin:/bin","HOME":td,
                         "LC_ALL":"C","TZ":"UTC"},
                    stdin=subprocess.DEVNULL,stdout=out,stderr=err,
                    check=False,timeout=timeout,preexec_fn=cap_logs)
        except (OSError,subprocess.TimeoutExpired) as exc:
            raise CheckerError("Rust checker unavailable or timed out") from exc
        if (out_path.stat().st_size >= max_output_bytes or
            err_path.stat().st_size >= max_output_bytes or
            result.returncode == -signal.SIGXFSZ):
            raise CheckerError("Rust checker output exceeded budget")
        if result.returncode:
            raise CheckerError("Rust checker rejected native export")
        stdout=out_path.read_bytes()
        if b"Checked " not in stdout or b" no errors" not in stdout:
            raise CheckerError("Rust checker returned no explicit success statement")
        if sha256(executable.read_bytes()).hexdigest()!=expected_executable_sha256:
            raise CheckerError("Rust checker changed during execution")
        if sha256(export_path.read_bytes()).hexdigest()!=export.artifact_sha256:
            raise CheckerError("Rust checker modified original export")
        return ExternalCheckReceipt(
            export.handoff_key,export.artifact_sha256,
            expected_executable_sha256,str(executable),
            ("nanoda-config",sha256(config_path.read_bytes()).hexdigest()),
            sha256(stdout).hexdigest(),
            sha256(err_path.read_bytes()).hexdigest())
