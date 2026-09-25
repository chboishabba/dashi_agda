from __future__ import annotations

from dataclasses import dataclass
import json
import os
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

        env_overrides = {}
        command_parts = list(command)
        while command_parts:
            part = command_parts[0]
            if "=" not in part or part.startswith("="):
                break
            key, value = part.split("=", 1)
            if not key or not all(ch.isalnum() or ch == "_" for ch in key):
                break
            if key[0].isdigit():
                break
            env_overrides[key] = value
            command_parts.pop(0)

        self.command = tuple(command_parts)
        self.env_overrides = env_overrides
        self.cwd = cwd
        self.timeout = timeout

    def _argv(self, path: Path) -> List[str]:
        absolute = str(path.resolve())
        if any("{file}" in part for part in self.command):
            return [part.replace("{file}", absolute) for part in self.command]
        return [*self.command, absolute]

    def _run(self, path: Path) -> ScopeRefinement:
        try:
            env = os.environ.copy()
            env.update(self.env_overrides)
            completed = subprocess.run(
                self._argv(path),
                cwd=self.cwd,
                env=env,
                text=True,
                capture_output=True,
                timeout=self.timeout,
                check=False,
            )
            if completed.returncode != 0:
                return ScopeRefinement(set(), set())
        except subprocess.TimeoutExpired:
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


class CommandScopeCheckBackend:
    """Use an arbitrary exit-code command as the scope-check negative oracle.

    The command receives the absolute module path as its final argument unless
    the literal placeholder {file} appears in argv. Exit status 0 means the
    module scope-check succeeded; any nonzero status leaves structural scope
    suspicions unresolved.
    """

    def __init__(
        self,
        command: Sequence[str] | str,
        *,
        cwd: Path | None = None,
        timeout: float = 300.0,
    ):
        if isinstance(command, str):
            command = shlex.split(command)
        self.command = tuple(command)
        self.cwd = cwd
        self.timeout = timeout
        self.attempted = 0
        self.succeeded = 0
        self.failed = 0
        self.last_checked_modules: Tuple[str, ...] = ()
        self.last_partial_validated_modules: Tuple[str, ...] = ()
        self.partial_validated_modules: Set[str] = set()

    @staticmethod
    def _checked_modules(output: str) -> Tuple[str, ...]:
        modules = []
        seen = set()
        for raw_line in output.splitlines():
            line = raw_line.strip()
            if not line.startswith("Checking "):
                continue
            if line.startswith("Checking:"):
                continue
            rest = line[len("Checking "):]
            module = rest.split(" (", 1)[0].strip()
            if not module or " " in module or "/" in module:
                continue
            if module not in seen:
                seen.add(module)
                modules.append(module)
        return tuple(modules)

    def _argv(self, path: Path) -> List[str]:
        absolute = str(path.resolve())
        if any("{file}" in part for part in self.command):
            return [part.replace("{file}", absolute) for part in self.command]
        return [*self.command, absolute]

    def _scope_ok(self, path: Path) -> bool:
        self.attempted += 1
        output = ""
        try:
            completed = subprocess.run(
                self._argv(path),
                cwd=self.cwd,
                text=True,
                capture_output=True,
                timeout=self.timeout,
                check=False,
            )
            output = (completed.stdout or "") + "\n" + (completed.stderr or "")
            ok = completed.returncode == 0
        except subprocess.TimeoutExpired as exc:
            stdout = exc.stdout.decode() if isinstance(exc.stdout, bytes) else (exc.stdout or "")
            stderr = exc.stderr.decode() if isinstance(exc.stderr, bytes) else (exc.stderr or "")
            output = stdout + "\n" + stderr
            ok = False

        checked = self._checked_modules(output)
        self.last_checked_modules = checked
        self.last_partial_validated_modules = checked if ok else checked[:-1]
        self.partial_validated_modules.update(self.last_partial_validated_modules)

        if ok:
            self.succeeded += 1
        else:
            self.failed += 1
        return ok

    def refine(self, summary, diagnostics: List):
        if not self._scope_ok(summary.path):
            return diagnostics
        return [
            diagnostic
            for diagnostic in diagnostics
            if policy_for(diagnostic.code).minimum != EvidenceLevel.AGDA_SCOPE
        ]


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
        self.attempted = 0
        self.succeeded = 0
        self.failed = 0

    def _scope_ok(self, path: Path) -> bool:
        self.attempted += 1
        try:
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
            ok = completed.returncode == 0
        except subprocess.TimeoutExpired:
            ok = False
        if ok:
            self.succeeded += 1
        else:
            self.failed += 1
        return ok

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
        self.attempted = 0
        self.succeeded = 0
        self.failed = 0

    def _typecheck_ok(self, path: Path) -> bool:
        self.attempted += 1
        try:
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
            ok = completed.returncode == 0
        except subprocess.TimeoutExpired:
            ok = False
        if ok:
            self.succeeded += 1
        else:
            self.failed += 1
        return ok

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


class CommandTypecheckBackend(CommandScopeCheckBackend):
    """Use an arbitrary exit-code command as a full Agda typecheck oracle."""

    def _typecheck_ok(self, path: Path) -> bool:
        return self._scope_ok(path)

    def refine(self, summary, diagnostics: List):
        if not self._typecheck_ok(summary.path):
            return diagnostics
        return [
            diagnostic
            for diagnostic in diagnostics
            if policy_for(diagnostic.code).minimum
            not in {
                EvidenceLevel.AGDA_SCOPE,
                EvidenceLevel.AGDA_TYPECHECKER,
            }
        ]


class AgdaAutoRefineBackend:
    """Demand-driven evidence refinement.

    Fast structural checking always runs first. Agda scope checking is invoked
    only when the module actually contains diagnostics whose minimum evidence is
    AGDA_SCOPE. Optional full typechecking is invoked only when AGDA_TYPECHECKER
    diagnostics remain after the scope stage.

    This keeps the common path cheap while making large aggregate sweeps
    self-triaging instead of dumping every deferred suspicion on the user.
    """

    def __init__(
        self,
        agda_bin: str = "agda",
        *,
        cwd: Path | None = None,
        scope_timeout: float = 300.0,
        typecheck_timeout: float = 300.0,
        typecheck: bool = False,
        extra_args: Sequence[str] = (),
        scope_command: Sequence[str] | str | None = None,
        typecheck_command: Sequence[str] | str | None = None,
    ):
        if scope_command is None:
            self.scope = AgdaScopeCheckBackend(
                agda_bin,
                cwd=cwd,
                timeout=scope_timeout,
                extra_args=extra_args,
            )
        else:
            self.scope = CommandScopeCheckBackend(
                scope_command,
                cwd=cwd,
                timeout=scope_timeout,
            )
        if typecheck_command is None:
            self.typecheck = AgdaTypecheckBackend(
                agda_bin,
                cwd=cwd,
                timeout=typecheck_timeout,
                extra_args=extra_args,
            )
        else:
            self.typecheck = CommandTypecheckBackend(
                typecheck_command,
                cwd=cwd,
                timeout=typecheck_timeout,
            )
        self.use_typecheck = typecheck
        self._scope_validated: Set[Path] = set()
        self._scope_failed: Set[Path] = set()
        self._scope_probe_roots: Set[Path] = set()
        self._scope_candidates: Set[Path] = set()
        self._typecheck_validated: Set[Path] = set()
        self._typecheck_failed: Set[Path] = set()
        self._typecheck_probe_roots: Set[Path] = set()
        self._typecheck_candidates: Set[Path] = set()

    @staticmethod
    def _key(path: Path) -> Path:
        return path.resolve()

    def scope_known(self, path: Path) -> bool:
        key = self._key(path)
        return key in self._scope_validated or key in self._scope_failed

    def scope_validated(self, path: Path) -> bool:
        return self._key(path) in self._scope_validated

    def scope_failed(self, path: Path) -> bool:
        return self._key(path) in self._scope_failed

    def probe_scope(self, path: Path, *, aggregate_root: bool = False) -> bool:
        """Run at most one scope probe for PATH and cache the result."""
        key = self._key(path)
        if key in self._scope_validated:
            return True
        if key in self._scope_failed:
            return False
        ok = self.scope._scope_ok(key)
        if aggregate_root:
            self._scope_probe_roots.add(key)
        if ok:
            self._scope_validated.add(key)
        else:
            self._scope_failed.add(key)
        return ok

    def mark_scope_validated(self, paths) -> None:
        for path in paths:
            key = self._key(path)
            self._scope_validated.add(key)
            self._scope_failed.discard(key)

    def set_scope_candidates(self, paths) -> None:
        self._scope_candidates = {self._key(path) for path in paths}

    def typecheck_known(self, path: Path) -> bool:
        key = self._key(path)
        return key in self._typecheck_validated or key in self._typecheck_failed

    def typecheck_validated(self, path: Path) -> bool:
        return self._key(path) in self._typecheck_validated

    def typecheck_failed(self, path: Path) -> bool:
        return self._key(path) in self._typecheck_failed

    def probe_typecheck(self, path: Path, *, aggregate_root: bool = False) -> bool:
        key = self._key(path)
        if key in self._typecheck_validated:
            return True
        if key in self._typecheck_failed:
            return False
        ok = self.typecheck._typecheck_ok(key)
        if aggregate_root:
            self._typecheck_probe_roots.add(key)
        if ok:
            self._typecheck_validated.add(key)
        else:
            self._typecheck_failed.add(key)
        return ok

    def mark_typecheck_validated(self, paths) -> None:
        for path in paths:
            key = self._key(path)
            self._typecheck_validated.add(key)
            self._typecheck_failed.discard(key)

    def set_typecheck_candidates(self, paths) -> None:
        self._typecheck_candidates = {self._key(path) for path in paths}

    @staticmethod
    def _needs(diagnostics: List, level: EvidenceLevel) -> bool:
        return any(
            not diagnostic.evidence_sufficient
            and policy_for(diagnostic.code).minimum == level
            for diagnostic in diagnostics
        )

    def stats(self):
        return {
            "scope": {
                "attempted": self.scope.attempted,
                "succeeded": self.scope.succeeded,
                "failed": self.scope.failed,
            },
            "typecheck": {
                "attempted": self.typecheck.attempted,
                "succeeded": self.typecheck.succeeded,
                "failed": self.typecheck.failed,
            },
            "scope_cache": {
                "validated_modules": len(self._scope_validated),
                "failed_frontier_modules": len(self._scope_failed),
                "aggregate_probe_roots": len(self._scope_probe_roots),
                "candidate_modules": len(self._scope_candidates),
                "partial_progress_modules": len(
                    getattr(self.scope, "partial_validated_modules", ())
                ),
            },
            "typecheck_cache": {
                "validated_modules": len(self._typecheck_validated),
                "failed_frontier_modules": len(self._typecheck_failed),
                "aggregate_probe_roots": len(self._typecheck_probe_roots),
                "candidate_modules": len(self._typecheck_candidates),
                "partial_progress_modules": len(
                    getattr(self.typecheck, "partial_validated_modules", ())
                ),
            },
        }

    def refine(self, summary, diagnostics: List):
        current = diagnostics

        if self._needs(current, EvidenceLevel.AGDA_SCOPE):
            path = summary.path.resolve()
            if self.scope_validated(path):
                current = [
                    diagnostic
                    for diagnostic in current
                    if policy_for(diagnostic.code).minimum != EvidenceLevel.AGDA_SCOPE
                ]
            elif self.scope_failed(path):
                # A closure prepass already established that this module is on
                # the unresolved scope frontier. Do not launch the same failed
                # process again during the pytest item.
                return current
            else:
                scope_ok = self.probe_scope(path)
                if scope_ok:
                    current = [
                        diagnostic
                        for diagnostic in current
                        if policy_for(diagnostic.code).minimum != EvidenceLevel.AGDA_SCOPE
                    ]
                else:
                    # Full typechecking cannot succeed if scope checking already
                    # fails, so do not pay the more expensive oracle cost.
                    return current

        if self.use_typecheck and self._needs(current, EvidenceLevel.AGDA_TYPECHECKER):
            path = summary.path.resolve()
            if self.typecheck_validated(path):
                current = [
                    diagnostic
                    for diagnostic in current
                    if policy_for(diagnostic.code).minimum
                    not in {
                        EvidenceLevel.AGDA_SCOPE,
                        EvidenceLevel.AGDA_TYPECHECKER,
                    }
                ]
            elif not self.typecheck_failed(path) and self.probe_typecheck(path):
                current = [
                    diagnostic
                    for diagnostic in current
                    if policy_for(diagnostic.code).minimum
                    not in {
                        EvidenceLevel.AGDA_SCOPE,
                        EvidenceLevel.AGDA_TYPECHECKER,
                    }
                ]

        return current
