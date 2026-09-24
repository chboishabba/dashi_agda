from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List, Optional
import json
import shlex

import pytest

from .checker import Checker, Diagnostic
from .evidence import canonical_code
from .scope_backend import AgdaAutoRefineBackend, AgdaScopeCheckBackend, AgdaTypecheckBackend, ExternalScopeBackend


@dataclass(frozen=True)
class CollectedModule:
    module: str
    path: Path


def pytest_addoption(parser):
    group = parser.getgroup("agda-preflight")
    group.addoption(
        "--agda-preflight",
        action="store_true",
        default=False,
        help="collect Agda semantic preflight checks as pytest items",
    )
    group.addoption(
        "--agda-root",
        action="store",
        default=None,
        help="repository root for Agda module resolution (default: pytest rootdir)",
    )
    group.addoption(
        "--agda-closure",
        action="store_true",
        default=False,
        help="for selected .agda roots, also collect reverse-import consumers",
    )
    group.addoption(
        "--agda-deps",
        action="store_true",
        default=False,
        help="for selected .agda roots, collect recursive imports in dependency-first order",
    )
    group.addoption(
        "--agda-errors-only",
        action="store_true",
        default=False,
        help="suppress warning diagnostics in per-module reports",
    )
    group.addoption(
        "--agda-scope-command",
        action="store",
        default=None,
        help="optional Agda-aware command that confirms/suppresses scope diagnostics",
    )
    group.addoption(
        "--agda-scope-check",
        action="store_true",
        default=False,
        help="run Agda --only-scope-checking to suppress false scope diagnostics",
    )
    group.addoption(
        "--agda-typecheck-oracle",
        action="store_true",
        default=False,
        help="run full Agda checking to suppress false scope/type diagnostics",
    )
    group.addoption(
        "--agda-auto-refine",
        nargs="?",
        const="scope",
        choices=("scope", "typecheck"),
        default=None,
        help=(
            "run stronger Agda evidence only for modules with deferred findings; "
            "optional value 'typecheck' escalates typechecker-level findings"
        ),
    )
    group.addoption(
        "--agda-compact",
        action="store_true",
        default=False,
        help="suppress per-warning spam and compact failed-module diagnostics",
    )
    group.addoption(
        "--agda-report-json",
        action="store",
        default=None,
        help="write complete structured Agda preflight results to this JSON file",
    )
    group.addoption(
        "--agda-bin",
        action="store",
        default="agda",
        help="Agda executable for --agda-scope-check",
    )
    group.addoption(
        "--agda-extra-args",
        action="store",
        default="",
        help="extra arguments passed to Agda scope/typecheck refinement subprocesses",
    )


def pytest_configure(config):
    config.addinivalue_line(
        "markers",
        "agda_preflight: tree-sitter based Agda structural preflight item",
    )


def _repo_root(config) -> Path:
    configured = config.getoption("--agda-root")
    if configured:
        return Path(configured).resolve()
    rootpath = getattr(config, "rootpath", None)
    if rootpath is not None:
        return Path(rootpath).resolve()
    return Path(str(config.rootdir)).resolve()


def _checker(config) -> Checker:
    cached = getattr(config, "_dashi_agda_checker", None)
    if cached is None:
        root = _repo_root(config)
        command = config.getoption("--agda-scope-command")
        native_scope = config.getoption("--agda-scope-check")
        typecheck_oracle = config.getoption("--agda-typecheck-oracle")
        auto_refine = config.getoption("--agda-auto-refine")
        selected = sum(
            bool(value)
            for value in (command, native_scope, typecheck_oracle, auto_refine)
        )
        if selected > 1:
            raise pytest.UsageError(
                "--agda-scope-command, --agda-scope-check, "
                "--agda-typecheck-oracle and --agda-auto-refine are mutually exclusive"
            )
        agda_extra_args = tuple(
            shlex.split(config.getoption("--agda-extra-args") or "")
        )
        scope_backend = None
        if command:
            scope_backend = ExternalScopeBackend(command, cwd=root)
        elif native_scope:
            scope_backend = AgdaScopeCheckBackend(
                config.getoption("--agda-bin"),
                cwd=root,
                extra_args=agda_extra_args,
            )
        elif typecheck_oracle:
            scope_backend = AgdaTypecheckBackend(
                config.getoption("--agda-bin"),
                cwd=root,
                extra_args=agda_extra_args,
            )
        elif auto_refine:
            scope_backend = AgdaAutoRefineBackend(
                config.getoption("--agda-bin"),
                cwd=root,
                typecheck=auto_refine == "typecheck",
                extra_args=agda_extra_args,
            )
        cached = Checker(root, scope_backend=scope_backend)
        setattr(config, "_dashi_agda_checker", cached)
    return cached


def _module_path(checker: Checker, module: str) -> Path:
    return checker.module_path(module)


def _selected_modules(
    checker: Checker,
    path: Path,
    closure: bool,
    dependencies: bool,
) -> List[CollectedModule]:
    summary = checker.parse_summary(path)
    modules = [summary.module_name]
    if dependencies:
        modules = checker.dependency_modules(path)
    if closure:
        affected = checker.affected_modules(path)
        modules = list(dict.fromkeys([*modules, *affected]))

    result: List[CollectedModule] = []
    seen = set()
    for module in modules:
        if module in seen:
            continue
        seen.add(module)
        module_path = _module_path(checker, module)
        if module_path.exists():
            result.append(CollectedModule(module, module_path))
    return result


def _format_diagnostic(diagnostic: Diagnostic) -> str:
    head = (
        f"{diagnostic.path}:{diagnostic.line}:{diagnostic.column}: "
        f"{diagnostic.severity}: {diagnostic.code}: {diagnostic.message} "
        f"[evidence={diagnostic.evidence}; requires={diagnostic.minimum_evidence}]"
    )
    if diagnostic.hint:
        return f"{head}\n  hint: {diagnostic.hint}"
    return head

def _prime_scope_closure(
    checker: Checker,
    root_path: Path,
    collected: List[CollectedModule],
) -> None:
    """Recursively certify successful import subtrees with one scope probe each.

    If the aggregate root succeeds, its entire collected dependency closure is
    marked scope-valid. If it fails, descend only through direct imported
    subtrees that are still unresolved. This isolates a small failing frontier
    without paying one Agda process per module.
    """
    backend = checker.scope_backend
    if not isinstance(backend, AgdaAutoRefineBackend):
        return
    if len(collected) <= 1:
        return

    selected = {item.path.resolve() for item in collected}
    visiting = set()

    def closure_paths(path: Path) -> List[Path]:
        return [
            checker.module_path(module).resolve()
            for module in checker.dependency_modules(path)
            if checker.module_path(module).resolve() in selected
        ]

    def visit(path: Path, *, aggregate_root: bool = False) -> None:
        key = path.resolve()
        if key not in selected:
            return
        if backend.scope_known(key):
            return
        if key in visiting:
            return

        visiting.add(key)
        try:
            if backend.probe_scope(key, aggregate_root=aggregate_root):
                backend.mark_scope_validated(closure_paths(key))
                return

            try:
                summary = checker.parse_summary(key)
            except (OSError, UnicodeDecodeError):
                return

            direct_children = []
            for module in sorted(set(summary.imports.values())):
                child = checker.module_path(module).resolve()
                if child in selected:
                    direct_children.append(child)

            for child in direct_children:
                if not backend.scope_known(child):
                    visit(child, aggregate_root=True)
        finally:
            visiting.remove(key)

    visit(root_path.resolve(), aggregate_root=True)



class AgdaModuleFile(pytest.File):
    def collect(self):
        config = self.config
        checker = _checker(config)
        path = Path(str(self.path)).resolve()
        closure = config.getoption("--agda-closure")
        dependencies = config.getoption("--agda-deps")

        seen = getattr(config, "_dashi_agda_collected_modules", None)
        if seen is None:
            seen = set()
            setattr(config, "_dashi_agda_collected_modules", seen)

        selected = _selected_modules(checker, path, closure, dependencies)

        if dependencies and config.getoption("--agda-auto-refine"):
            primed = getattr(config, "_dashi_agda_scope_primed_roots", None)
            if primed is None:
                primed = set()
                setattr(config, "_dashi_agda_scope_primed_roots", primed)
            root_key = path.resolve()
            if root_key not in primed:
                _prime_scope_closure(checker, path, selected)
                primed.add(root_key)

        for collected in selected:
            if collected.module in seen:
                continue
            seen.add(collected.module)
            yield AgdaModuleItem.from_parent(
                self,
                name=collected.module,
                module_name=collected.module,
                module_path=collected.path,
            )


class AgdaModuleItem(pytest.Item):
    def __init__(self, *, module_name: str, module_path: Path, **kwargs):
        super().__init__(**kwargs)
        self.module_name = module_name
        self.module_path = module_path
        self._diagnostics: List[Diagnostic] = []
        self.add_marker("agda_preflight")

    def runtest(self):
        checker = _checker(self.config)
        diagnostics = checker.check(self.module_path)
        self._diagnostics = diagnostics

        self.user_properties.append(
            (
                "agda_diagnostics",
                [diagnostic.as_dict() for diagnostic in diagnostics],
            )
        )
        errors = [diagnostic for diagnostic in diagnostics if diagnostic.severity == "error"]
        warnings = [
            diagnostic for diagnostic in diagnostics
            if diagnostic.severity != "error"
        ]
        if (
            warnings
            and not self.config.getoption("--agda-errors-only")
            and not self.config.getoption("--agda-compact")
        ):
            for diagnostic in warnings:
                import warnings as _warnings
                _warnings.warn(
                    _format_diagnostic(diagnostic),
                    AgdaPreflightWarning,
                    stacklevel=1,
                )

        if errors:
            raise AgdaPreflightFailure(self.module_name, diagnostics)

    def repr_failure(self, excinfo, style=None):
        if isinstance(excinfo.value, AgdaPreflightFailure):
            diagnostics = excinfo.value.diagnostics
            if self.config.getoption("--agda-errors-only"):
                diagnostics = [d for d in diagnostics if d.severity == "error"]
            if self.config.getoption("--agda-compact"):
                errors = [d for d in diagnostics if d.severity == "error"]
                counts = Counter(d.code for d in errors)
                lines = [
                    f"{code}: {count}"
                    for code, count in counts.most_common(12)
                ]
                examples = errors[:5]
                if examples:
                    lines.append("")
                    lines.append("examples:")
                    lines.extend(
                        f"  {d.code} {d.path}:{d.line}:{d.column} {d.message}"
                        for d in examples
                    )
                body = "\n".join(lines) if lines else "no hard diagnostics"
            else:
                body = "\n\n".join(_format_diagnostic(d) for d in diagnostics)
            return f"Agda preflight failed for {self.module_name}\n\n{body}"
        return super().repr_failure(excinfo, style=style)

    def reportinfo(self):
        return self.module_path, 0, f"agda-preflight: {self.module_name}"


class AgdaPreflightWarning(UserWarning):
    pass


class AgdaPreflightFailure(Exception):
    def __init__(self, module_name: str, diagnostics: List[Diagnostic]):
        self.module_name = module_name
        self.diagnostics = diagnostics
        super().__init__(f"{module_name}: {len(diagnostics)} preflight diagnostics")


def pytest_collect_file(file_path, parent):
    config = parent.config
    if not config.getoption("--agda-preflight"):
        return None
    path = Path(str(file_path))
    if path.suffix != ".agda":
        return None
    return AgdaModuleFile.from_parent(parent, path=file_path)


def pytest_terminal_summary(terminalreporter, exitstatus, config):
    if not config.getoption("--agda-preflight"):
        return

    passed = 0
    failed = 0
    warning_count = 0
    error_count = 0
    deferred_count = 0
    code_counts = Counter()
    error_code_counts = Counter()
    deferred_code_counts = Counter()
    canonical_counts = Counter()
    canonical_error_counts = Counter()
    canonical_deferred_counts = Counter()
    report_modules = []

    for outcome in ("passed", "failed"):
        for report in terminalreporter.getreports(outcome):
            diagnostics = None
            for key, value in getattr(report, "user_properties", ()):
                if key == "agda_diagnostics":
                    diagnostics = value
                    break
            if diagnostics is None:
                continue

            module_entry = {
                "nodeid": report.nodeid,
                "outcome": outcome,
                "diagnostics": diagnostics,
            }
            report_modules.append(module_entry)

            if outcome == "passed":
                passed += 1
            else:
                failed += 1

            for diagnostic in diagnostics:
                code = diagnostic.get("code", "UNKNOWN")
                root_code = canonical_code(code)
                code_counts[code] += 1
                canonical_counts[root_code] += 1
                if diagnostic.get("severity") == "error":
                    error_count += 1
                    error_code_counts[code] += 1
                    canonical_error_counts[root_code] += 1
                else:
                    warning_count += 1
                if not diagnostic.get("evidence_sufficient", True):
                    deferred_count += 1
                    deferred_code_counts[code] += 1
                    canonical_deferred_counts[root_code] += 1

    terminalreporter.section("Agda preflight")
    terminalreporter.write_line(f"modules passed: {passed}")
    terminalreporter.write_line(f"modules failed: {failed}")
    terminalreporter.write_line(f"errors: {error_count}")
    terminalreporter.write_line(f"warnings: {warning_count}")
    terminalreporter.write_line(f"deferred for stronger evidence: {deferred_count}")

    checker = getattr(config, "_dashi_agda_checker", None)
    backend = getattr(checker, "scope_backend", None) if checker is not None else None
    stats_fn = getattr(backend, "stats", None)
    if callable(stats_fn):
        refinement = stats_fn()
        scope = refinement.get("scope", {})
        typecheck = refinement.get("typecheck", {})
        terminalreporter.write_line(
            "scope refinement: "
            f"{scope.get('succeeded', 0)}/{scope.get('attempted', 0)} succeeded, "
            f"{scope.get('failed', 0)} failed"
        )
        terminalreporter.write_line(
            "typecheck refinement: "
            f"{typecheck.get('succeeded', 0)}/{typecheck.get('attempted', 0)} succeeded, "
            f"{typecheck.get('failed', 0)} failed"
        )

    if code_counts:
        terminalreporter.write_line("")
        terminalreporter.write_line("top root-cause diagnostics:")
        for code, count in canonical_counts.most_common(12):
            hard = canonical_error_counts.get(code, 0)
            deferred = canonical_deferred_counts.get(code, 0)
            terminalreporter.write_line(
                f"  {code}: {count} total, {hard} hard, {deferred} deferred"
            )

    report_path = config.getoption("--agda-report-json")
    if report_path:
        payload = {
            "summary": {
                "modules_passed": passed,
                "modules_failed": failed,
                "errors": error_count,
                "warnings": warning_count,
                "deferred": deferred_count,
                "diagnostics_by_code": dict(code_counts),
                "hard_by_code": dict(error_code_counts),
                "deferred_by_code": dict(deferred_code_counts),
                "canonical_diagnostics_by_code": dict(canonical_counts),
                "canonical_hard_by_code": dict(canonical_error_counts),
                "canonical_deferred_by_code": dict(canonical_deferred_counts),
            },
            "modules": report_modules,
        }
        if checker is not None and callable(getattr(backend, "stats", None)):
            payload["summary"]["refinement"] = backend.stats()
        output = Path(report_path)
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(
            json.dumps(payload, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        terminalreporter.write_line(f"structured report: {output}")

