from __future__ import annotations

from dataclasses import dataclass
import json
import os
from pathlib import Path
import shlex
import subprocess
import tempfile
import time
from typing import Dict, Optional, Sequence, Union


@dataclass(frozen=True)
class PromotionCommandResult:
    returncode: int
    elapsed_ms: float
    stdout: str
    stderr: str
    receipt: Optional[dict]

    def as_dict(self) -> dict:
        return {
            "returncode": self.returncode,
            "elapsed_ms": self.elapsed_ms,
            "stdout": self.stdout,
            "stderr": self.stderr,
            "receipt": self.receipt,
        }


class CommandPromoter:
    """Explicit external semantic promoter.

    The command is never used by diagnose/next_error. Placeholders are expanded
    per request: {file}, {module}, {root}, {catalog}, and {receipt}. Leading
    KEY=VALUE assignments are merged into the child environment without using
    a shell.
    """

    def __init__(
        self,
        command: Union[Sequence[str], str],
        *,
        root: Path,
        catalog: Path,
        timeout: float = 900.0,
    ) -> None:
        if isinstance(command, str):
            command = shlex.split(command)
        parts = list(command)
        env: Dict[str, str] = {}
        while parts:
            token = parts[0]
            if "=" not in token or token.startswith("="):
                break
            key, value = token.split("=", 1)
            if (
                not key
                or key[0].isdigit()
                or not all(ch.isalnum() or ch == "_" for ch in key)
            ):
                break
            env[key] = value
            parts.pop(0)
        if not parts:
            raise ValueError("promoter command is empty")
        self.command = tuple(parts)
        self.env_overrides = env
        self.root = root.resolve()
        self.catalog = catalog.resolve()
        self.timeout = timeout

    def _argv(
        self,
        *,
        path: Path,
        module: str,
        receipt: Path,
    ) -> list[str]:
        replacements = {
            "{file}": str(path.resolve()),
            "{module}": module,
            "{root}": str(self.root),
            "{catalog}": str(self.catalog),
            "{receipt}": str(receipt),
        }
        argv = []
        used_file = False
        for token in self.command:
            rendered = token
            for placeholder, value in replacements.items():
                if placeholder in rendered:
                    rendered = rendered.replace(placeholder, value)
                    if placeholder == "{file}":
                        used_file = True
            argv.append(rendered)
        if not used_file and not any(
            placeholder in token
            for token in self.command
            for placeholder in ("{module}", "{receipt}")
        ):
            argv.append(str(path.resolve()))
        return argv

    def run(
        self,
        *,
        path: Path,
        module: str,
    ) -> PromotionCommandResult:
        receipt_dir = self.root / ".cache" / "agda_preflight" / "promotion"
        receipt_dir.mkdir(parents=True, exist_ok=True)
        handle = tempfile.NamedTemporaryFile(
            dir=receipt_dir,
            prefix="promotion-",
            suffix=".json",
            delete=False,
        )
        handle.close()
        receipt_path = Path(handle.name)
        # A zero-length placeholder is not itself a receipt.
        receipt_path.unlink(missing_ok=True)

        env = os.environ.copy()
        env.update(self.env_overrides)
        started = time.perf_counter_ns()
        try:
            completed = subprocess.run(
                self._argv(
                    path=path,
                    module=module,
                    receipt=receipt_path,
                ),
                cwd=self.root,
                env=env,
                text=True,
                capture_output=True,
                timeout=self.timeout,
                check=False,
            )
            elapsed_ms = (
                time.perf_counter_ns() - started
            ) / 1_000_000.0
        except subprocess.TimeoutExpired as error:
            elapsed_ms = (
                time.perf_counter_ns() - started
            ) / 1_000_000.0
            return PromotionCommandResult(
                returncode=124,
                elapsed_ms=elapsed_ms,
                stdout=error.stdout or "",
                stderr=error.stderr or "promotion timed out",
                receipt=None,
            )

        receipt = None
        if receipt_path.is_file():
            try:
                receipt = json.loads(
                    receipt_path.read_text(encoding="utf-8")
                )
            except (OSError, json.JSONDecodeError):
                receipt = None
            finally:
                receipt_path.unlink(missing_ok=True)

        return PromotionCommandResult(
            returncode=completed.returncode,
            elapsed_ms=elapsed_ms,
            stdout=completed.stdout,
            stderr=completed.stderr,
            receipt=receipt,
        )
