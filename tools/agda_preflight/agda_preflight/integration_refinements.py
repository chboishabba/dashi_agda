from __future__ import annotations

from pathlib import Path

from .checker import Diagnostic
from .evidence import EvidenceLevel, evidence_name
from . import scope_backend


def _resolved_location(code, path, line, column):
    try:
        resolved = Path(path).resolve()
    except OSError:
        resolved = Path(path)
    return (code, str(resolved), line, column)


def _append_native_diagnostics(diagnostics, native, level):
    """Merge native Agda output by source location, upgrading predictions."""

    if not native:
        return list(diagnostics)
    out = list(diagnostics)
    positions = {
        _resolved_location(d.code, d.path, d.line, d.column): index
        for index, d in enumerate(out)
    }
    evidence = evidence_name(level)
    for item in native:
        key = _resolved_location(item.code, item.path, item.line, item.column)
        confirmed = Diagnostic(
            item.code,
            item.message,
            item.path,
            item.line,
            item.column,
            hint=f"Native Agda diagnostic class: {item.agda_class}.",
            severity=item.severity,
            confidence="agda-confirmed",
            evidence=evidence,
            minimum_evidence=evidence,
            evidence_sufficient=True,
            root_cause=f"Agda {item.agda_class}",
        )
        index = positions.get(key)
        if index is None:
            positions[key] = len(out)
            out.append(confirmed)
        else:
            out[index] = confirmed
    return out


def _cache_native(instance, attribute: str, native) -> None:
    cache = getattr(instance, attribute)
    for item in native:
        try:
            key = Path(item.path).resolve()
        except OSError:
            key = Path(item.path)
        cache.setdefault(key, []).append(item)


def install_scope_refinements() -> None:
    """Retain native diagnostics across cached auto-refine probe paths."""

    scope_backend._append_native_diagnostics = _append_native_diagnostics
    cls = scope_backend.AgdaAutoRefineBackend
    if getattr(cls, "_dashi_native_cache_refined", False):
        return

    original_init = cls.__init__
    original_probe_scope = cls.probe_scope
    original_probe_typecheck = cls.probe_typecheck
    original_refine = cls.refine

    def __init__(self, *args, **kwargs):
        original_init(self, *args, **kwargs)
        self._scope_native_by_path = {}
        self._typecheck_native_by_path = {}

    def probe_scope(self, path, *, aggregate_root=False):
        known = self.scope_known(path)
        result = original_probe_scope(self, path, aggregate_root=aggregate_root)
        if not known:
            _cache_native(
                self,
                "_scope_native_by_path",
                getattr(self.scope, "last_native_diagnostics", ()),
            )
        return result

    def probe_typecheck(self, path, *, aggregate_root=False):
        known = self.typecheck_known(path)
        result = original_probe_typecheck(self, path, aggregate_root=aggregate_root)
        if not known:
            _cache_native(
                self,
                "_typecheck_native_by_path",
                getattr(self.typecheck, "last_native_diagnostics", ()),
            )
        return result

    def refine(self, summary, diagnostics):
        path = summary.path.resolve()
        current = list(diagnostics)
        current = _append_native_diagnostics(
            current,
            self._scope_native_by_path.get(path, ()),
            EvidenceLevel.AGDA_SCOPE,
        )
        current = _append_native_diagnostics(
            current,
            self._typecheck_native_by_path.get(path, ()),
            EvidenceLevel.AGDA_TYPECHECKER,
        )
        return original_refine(self, summary, current)

    cls.__init__ = __init__
    cls.probe_scope = probe_scope
    cls.probe_typecheck = probe_typecheck
    cls.refine = refine
    cls._dashi_native_cache_refined = True
