from __future__ import annotations

from dataclasses import dataclass
from enum import IntEnum
from typing import Dict, Iterable, Mapping, Optional, Set


class EvidenceLevel(IntEnum):
    """Ordered semantic evidence available to the preflight engine.

    Higher layers may rely on all facts guaranteed by lower layers.
    """

    TREE_SITTER = 10
    DASHI_INDEX = 20
    AGDA_SCOPE = 30
    AGDA_TYPECHECKER = 40


@dataclass(frozen=True)
class DiagnosticPolicy:
    minimum: EvidenceLevel
    hard_error_allowed: bool = True
    description: str = ""


_DEFAULT_POLICY = DiagnosticPolicy(
    EvidenceLevel.DASHI_INDEX,
    True,
    "bounded structural/index evidence",
)


def _policy(
    minimum: EvidenceLevel,
    hard: bool = True,
    description: str = "",
) -> DiagnosticPolicy:
    """Build one explicit evidence contract."""

    return DiagnosticPolicy(minimum, hard, description)


_TREE_ONLY = {
    "TSAGDA000", "TSAGDA004", "TSAGDA005", "TSAGDA006", "TSAGDA007",
    "TSAGDA010", "TSAGDA011", "TSAGDA012", "TSAGDA013", "TSAGDA061",
    "TSAGDA090", "TSAGDA091", "TSAGDA150", "TSAGDA151", "TSAGDA152",
    "TSAGDA153", "TSAGDA161", "TSAGDA162", "TSAGDA163", "TSAGDA164",
    "TSAGDA165", "TSAGDA170", "TSAGDA172", "TSAGDA173", "TSAGDA174",
    "TSAGDA175", "TSAGDA201", "TSAGDA204",
}


_INDEX_SAFE = {
    "TSAGDA001", "TSAGDA002", "TSAGDA003",
    "TSAGDA008", "TSAGDA009",
    "TSAGDA020", "TSAGDA029", "TSAGDA030",
    "TSAGDA042", "TSAGDA043", "TSAGDA044", "TSAGDA046", "TSAGDA047",
    "TSAGDA048", "TSAGDA050", "TSAGDA051", "TSAGDA053", "TSAGDA054",
    "TSAGDA056", "TSAGDA060", "TSAGDA062", "TSAGDA063", "TSAGDA064",
    "TSAGDA065", "TSAGDA066", "TSAGDA067", "TSAGDA068",
    "TSAGDA070", "TSAGDA071", "TSAGDA073", "TSAGDA074", "TSAGDA077",
    "TSAGDA078", "TSAGDA079", "TSAGDA080", "TSAGDA081", "TSAGDA082",
    "TSAGDA083", "TSAGDA085", "TSAGDA086", "TSAGDA087", "TSAGDA088",
    "TSAGDA089", "TSAGDA100", "TSAGDA101", "TSAGDA102", "TSAGDA103",
    "TSAGDA105", "TSAGDA111", "TSAGDA112", "TSAGDA115",
    "TSAGDA120", "TSAGDA121", "TSAGDA122", "TSAGDA123",
    "TSAGDA130", "TSAGDA131", "TSAGDA140", "TSAGDA141", "TSAGDA142",
    "TSAGDA143", "TSAGDA160", "TSAGDA166", "TSAGDA171",
    "TSAGDA180", "TSAGDA181", "TSAGDA182", "TSAGDA183", "TSAGDA184",
    "TSAGDA185", "TSAGDA186", "TSAGDA200", "TSAGDA202", "TSAGDA203",
    "TSAGDA205", "TSAGDA207", "TSAGDA208",
    "TSAGDA303", "TSAGDA304",
    "TSAGDA300",
}


_SCOPE_REQUIRED = {
    "TSAGDA021", "TSAGDA022", "TSAGDA023", "TSAGDA024", "TSAGDA025",
    "TSAGDA026", "TSAGDA027", "TSAGDA028", "TSAGDA055", "TSAGDA084",
    "TSAGDA113", "TSAGDA154", "TSAGDA305",
    "TSAGDA049", "TSAGDA052",
}


_TYPECHECK_REQUIRED: Set[str] = {
    "TSAGDA040", "TSAGDA041", "TSAGDA045", "TSAGDA072", "TSAGDA075",
    "TSAGDA076", "TSAGDA104", "TSAGDA110", "TSAGDA114", "TSAGDA206",
}


_AGDA_NATIVE = {
    "TSAGDA301",
    "TSAGDA302",
    "TSAGDA390",
    "TSAGDA398",
    "TSAGDA399",
}


DIAGNOSTIC_ALIASES = {
    "TSAGDA002": ("TSAGDA171",),
    "TSAGDA003": ("TSAGDA065", "TSAGDA067"),
    "TSAGDA012": ("TSAGDA175",),
    "TSAGDA045": ("TSAGDA110",),
    "TSAGDA042": ("TSAGDA112",),
}

_ALIAS_TO_CANONICAL = {
    alias: canonical
    for canonical, aliases in DIAGNOSTIC_ALIASES.items()
    for alias in aliases
}
_ALIAS_TO_CANONICAL.update({
    "TSAGDA075": "TSAGDA072",
    "TSAGDA114": "TSAGDA072",
})


def canonical_code(code: str) -> str:
    """Collapse compatibility aliases for triage without changing emission."""

    return _ALIAS_TO_CANONICAL.get(code, code)


DIAGNOSTIC_POLICIES: Dict[str, DiagnosticPolicy] = {}
for code in _TREE_ONLY:
    DIAGNOSTIC_POLICIES[code] = _policy(
        EvidenceLevel.TREE_SITTER,
        True,
        "concrete syntax/tree structure",
    )
for code in _INDEX_SAFE:
    DIAGNOSTIC_POLICIES[code] = _policy(
        EvidenceLevel.DASHI_INDEX,
        True,
        "DASHI structural/module index",
    )
for code in _SCOPE_REQUIRED:
    DIAGNOSTIC_POLICIES[code] = _policy(
        EvidenceLevel.AGDA_SCOPE,
        True,
        "requires Agda-resolved scope/elaboration for a hard conclusion",
    )
for code in _TYPECHECK_REQUIRED:
    DIAGNOSTIC_POLICIES[code] = _policy(
        EvidenceLevel.AGDA_TYPECHECKER,
        False,
        "requires full Agda typechecking",
    )
for code in _AGDA_NATIVE:
    DIAGNOSTIC_POLICIES[code] = _policy(
        EvidenceLevel.AGDA_SCOPE,
        True,
        "native diagnostic emitted by an Agda process or Agda-compatible runner",
    )


def policy_for(code: str) -> DiagnosticPolicy:
    """Return the explicit evidence contract for CODE."""

    try:
        return DIAGNOSTIC_POLICIES[code]
    except KeyError as exc:
        raise KeyError(
            f"diagnostic {code} has no evidence policy; classify it before emitting"
        ) from exc


def classify_codes(codes: Iterable[str]) -> Mapping[EvidenceLevel, Set[str]]:
    """Group diagnostic codes by minimum evidence layer."""

    grouped: Dict[EvidenceLevel, Set[str]] = {}
    for code in codes:
        grouped.setdefault(policy_for(code).minimum, set()).add(code)
    return grouped


def evidence_name(level: EvidenceLevel) -> str:
    """Return the stable serialized name for an evidence level."""

    return {
        EvidenceLevel.TREE_SITTER: "tree-sitter",
        EvidenceLevel.DASHI_INDEX: "dashi-index",
        EvidenceLevel.AGDA_SCOPE: "agda-scope",
        EvidenceLevel.AGDA_TYPECHECKER: "agda-typechecker",
    }[level]
