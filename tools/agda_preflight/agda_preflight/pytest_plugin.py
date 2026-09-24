from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List, Optional

import pytest

from .checker import Checker, Diagnostic
from .scope_backend import ExternalScopeBackend


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
        scope_backend = (
            ExternalScopeBackend(command, cwd=root)
            if command
            else None
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

        for collected in _selected_modules(checker, path, closure, dependencies):
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
        if warnings and not self.config.getoption("--agda-errors-only"):
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

    for outcome in ("passed", "failed"):
        for report in terminalreporter.getreports(outcome):
            diagnostics = None
            for key, value in getattr(report, "user_properties", ()):
                if key == "agda_diagnostics":
                    diagnostics = value
                    break
            if diagnostics is None:
                continue
            if outcome == "passed":
                passed += 1
            else:
                failed += 1
            warning_count += sum(
                1 for diagnostic in diagnostics
                if diagnostic.get("severity") != "error"
            )
            error_count += sum(
                1 for diagnostic in diagnostics
                if diagnostic.get("severity") == "error"
            )

    terminalreporter.section("Agda preflight")
    terminalreporter.write_line(f"modules passed: {passed}")
    terminalreporter.write_line(f"modules failed: {failed}")
    terminalreporter.write_line(f"errors: {error_count}")
    terminalreporter.write_line(f"warnings: {warning_count}")

