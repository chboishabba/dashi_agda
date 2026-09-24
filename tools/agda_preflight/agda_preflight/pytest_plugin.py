from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List, Optional

import pytest

from .checker import Checker, Diagnostic


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
        "--agda-errors-only",
        action="store_true",
        default=False,
        help="suppress warning diagnostics in per-module reports",
    )


def pytest_configure(config):
    config.addinivalue_line(
        "markers",
        "agda_preflight: tree-sitter based Agda structural preflight item",
    )
    config.addinivalue_line(
        "markers",
        "agda_imports: Agda import/module/name-resolution diagnostics",
    )
    config.addinivalue_line(
        "markers",
        "agda_records: Agda record/projection/adapter diagnostics",
    )
    config.addinivalue_line(
        "markers",
        "agda_arity: Agda telescope/application/arity diagnostics",
    )
    config.addinivalue_line(
        "markers",
        "agda_patterns: Agda pattern/coverage diagnostics",
    )
    config.addinivalue_line(
        "markers",
        "agda_equality: Agda equality-shape diagnostics",
    )
    config.addinivalue_line(
        "markers",
        "agda_trust: Agda trust-boundary/policy diagnostics",
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
        cached = Checker(_repo_root(config))
        setattr(config, "_dashi_agda_checker", cached)
    return cached


def _module_path(checker: Checker, module: str) -> Path:
    return checker.module_path(module)


def _selected_modules(checker: Checker, path: Path, closure: bool) -> List[CollectedModule]:
    summary = checker.parse_summary(path)
    modules = [summary.module_name]
    if closure:
        modules = checker.affected_modules(path)

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


def _marker_names(diagnostics: Iterable[Diagnostic]) -> set[str]:
    markers = {"agda_preflight"}
    for diagnostic in diagnostics:
        try:
            number = int(diagnostic.code.removeprefix("TSAGDA"))
        except ValueError:
            continue
        if 20 <= number <= 30 or 180 <= number <= 186:
            markers.add("agda_imports")
        if number in {1, 2, 3} or 49 <= number <= 68 or number in {200, 201, 203, 206, 208}:
            markers.add("agda_records")
        if 40 <= number <= 49 or 110 <= number <= 115:
            markers.add("agda_arity")
        if 80 <= number <= 89:
            markers.add("agda_patterns")
        if 100 <= number <= 105:
            markers.add("agda_equality")
        if 160 <= number <= 175 or 200 <= number <= 208:
            markers.add("agda_trust")
    return markers


def _format_diagnostic(diagnostic: Diagnostic) -> str:
    head = (
        f"{diagnostic.path}:{diagnostic.line}:{diagnostic.column}: "
        f"{diagnostic.severity}: {diagnostic.code}: {diagnostic.message}"
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

        for collected in _selected_modules(checker, path, closure):
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

    def runtest(self):
        checker = _checker(self.config)
        diagnostics = checker.check(self.module_path)
        self._diagnostics = diagnostics

        for marker in _marker_names(diagnostics):
            self.add_marker(marker)

        errors = [diagnostic for diagnostic in diagnostics if diagnostic.severity == "error"]
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
    warnings = 0
    errors = 0

    for report in terminalreporter.getreports("passed"):
        item = getattr(report, "nodeid", "")
        if ".agda" in item or "::DASHI." in item:
            passed += 1

    for report in terminalreporter.getreports("failed"):
        item = getattr(report, "nodeid", "")
        if ".agda" in item or "::DASHI." in item:
            failed += 1

    checker = getattr(config, "_dashi_agda_checker", None)
    if checker is not None:
        # Diagnostics are intentionally not re-run here. Counts are derived only
        # from collected items where pytest retained the item object via reports.
        pass

    terminalreporter.section("Agda preflight")
    terminalreporter.write_line(f"modules passed: {passed}")
    terminalreporter.write_line(f"modules failed: {failed}")
