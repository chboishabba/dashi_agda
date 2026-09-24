from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path
import shlex
import subprocess
from typing import List, Protocol, Sequence, Set, Tuple

from .evidence import EvidenceLevel, evidence_name, policy_for


DiagnosticKey = Tuple[str, int, int]


def diagnostic_key(diagnostic) -> DiagnosticKey:
    return (diagnostic.code, diagnostic.line, diagnostic.column)


@dataclass(frozen=True)
class ScopeRefinement:
    confirmed: Set[DiagnosticKey]
    suppressed: Set[DiagnosticKey]


class ScopeBackend(Protocol):
    def refine(self, summary, diagnostics: List):
        ...


class ExternalScopeBackend:
    """Bridge to an external Agda-aware scope/elaboration command.

    The command receives the absolute module path as its final argument unless
    the literal placeholder {file} appears in the configured argv. It must
    write one JSON object with confirmed/suppressed diagnostic locations.

    A confirmation upgrades provenance to AGDA_SCOPE. A suppression removes
    the structural suspicion. Malformed output is ignored conservatively.
    """

    def __init__(
        self,
        command: Sequence[str] | str,
        *,
        cwd: Path | None = None,
        timeout: float = 30.0,
    ):
        if isinstance(command, str):
            command = shlex.split(command)
        self.command = tuple(command)
        self.cwd = cwd
        self.timeout = timeout

    def _argv(self, path: Path) -> List[str]:
        absolute = str(path.resolve())
        if any("{file}" in part for part in self.command):
            return [part.replace("{file}", absolute) for part in self.command]
        return [*self.command, absolute]

    def _run(self, path: Path) -> ScopeRefinement:
        completed = subprocess.run(
            self._argv(path),
            cwd=self.cwd,
            text=True,
            capture_output=True,
            timeout=self.timeout,
            check=False,
        )
        if completed.returncode != 0:
            return ScopeRefinement(set(), set())

        try:
            payload = json.loads(completed.stdout)
        except (json.JSONDecodeError, TypeError):
            return ScopeRefinement(set(), set())

        def keys(name: str) -> Set[DiagnosticKey]:
            result: Set[DiagnosticKey] = set()
            for item in payload.get(name, ()):
                try:
                    result.add((
                        str(item["code"]),
                        int(item["line"]),
                        int(item.get("column", 1)),
                    ))
                except (KeyError, TypeError, ValueError):
                    continue
            return result

        return ScopeRefinement(keys("confirmed"), keys("suppressed"))

    def refine(self, summary, diagnostics: List):
        refinement = self._run(summary.path)
        out = []
        for diagnostic in diagnostics:
            key = diagnostic_key(diagnostic)
            if key in refinement.suppressed:
                continue

            if key in refinement.confirmed:
                policy = policy_for(diagnostic.code)
                sufficient = EvidenceLevel.AGDA_SCOPE >= policy.minimum
                severity = diagnostic.severity
                confidence = diagnostic.confidence
                hint = diagnostic.hint

                if sufficient:
                    confidence = "scope-confirmed"
                    if (
                        diagnostic.confidence == "insufficient-evidence"
                        and policy.hard_error_allowed
                    ):
                        severity = "error"
                    hint_extra = "Confirmed by Agda-resolved scope/elaboration."
                    hint = f"{hint} {hint_extra}".strip() if hint else hint_extra

                out.append(diagnostic.__class__(
                    diagnostic.code,
                    diagnostic.message,
                    diagnostic.path,
                    diagnostic.line,
                    diagnostic.column,
                    hint,
                    severity,
                    confidence,
                    evidence_name(EvidenceLevel.AGDA_SCOPE),
                    diagnostic.minimum_evidence,
                    sufficient,
                ))
                continue

            out.append(diagnostic)
        return out


class AgdaScopeCheckBackend:
    """Use Agda's own --only-scope-checking mode as a negative oracle.

    Success means scope-dependent structural suspicions are false positives for
    that module and can be removed. Failure does not identify a specific
    TSAGDA suspicion, so diagnostics remain advisory rather than being promoted.
    """

    def __init__(
        self,
        agda_bin: str = "agda",
        *,
        cwd: Path | None = None,
        timeout: float = 60.0,
        extra_args: Sequence[str] = (),
    ):
        self.agda_bin = agda_bin
        self.cwd = cwd
        self.timeout = timeout
        self.extra_args = tuple(extra_args)

    def _scope_ok(self, path: Path) -> bool:
        completed = subprocess.run(
            [
                self.agda_bin,
                "--only-scope-checking",
                *self.extra_args,
                str(path.resolve()),
            ],
            cwd=self.cwd,
            text=True,
            capture_output=True,
            timeout=self.timeout,
            check=False,
        )
        return completed.returncode == 0

    def refine(self, summary, diagnostics: List):
        if not self._scope_ok(summary.path):
            return diagnostics

        out = []
        for diagnostic in diagnostics:
            policy = policy_for(diagnostic.code)
            if policy.minimum == EvidenceLevel.AGDA_SCOPE:
                # Successful Agda scope checking is stronger evidence than our
                # structural suspicion for scope/name-resolution questions.
                continue
            out.append(diagnostic)
        return out


class AgdaTypecheckBackend:
    """Use a successful full Agda check as a negative oracle.

    If Agda accepts the module, structural suspicions that require AGDA_SCOPE
    or AGDA_TYPECHECKER evidence are necessarily false positives. Policy/trust
    diagnostics and syntax/index facts remain visible because Agda acceptance
    does not invalidate those architectural constraints.
    """

    def __init__(
        self,
        agda_bin: str = "agda",
        *,
        cwd: Path | None = None,
        timeout: float = 300.0,
        extra_args: Sequence[str] = (),
    ):
        self.agda_bin = agda_bin
        self.cwd = cwd
        self.timeout = timeout
        self.extra_args = tuple(extra_args)

    def _typecheck_ok(self, path: Path) -> bool:
        completed = subprocess.run(
            [
                self.agda_bin,
                *self.extra_args,
                str(path.resolve()),
            ],
            cwd=self.cwd,
            text=True,
            capture_output=True,
            timeout=self.timeout,
            check=False,
        )
        return completed.returncode == 0

    def refine(self, summary, diagnostics: List):
        if not self._typecheck_ok(summary.path):
            return diagnostics

        out = []
        for diagnostic in diagnostics:
            policy = policy_for(diagnostic.code)
            if policy.minimum in {
                EvidenceLevel.AGDA_SCOPE,
                EvidenceLevel.AGDA_TYPECHECKER,
            }:
                continue
            out.append(diagnostic)
        return out
