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


# Default policy is intentionally conservative: an unclassified diagnostic may
# be emitted from the DASHI structural index, but not from raw syntax alone.
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
    return DiagnosticPolicy(minimum, hard, description)


# Diagnostics that are sound from concrete syntax alone.
_TREE_ONLY = {
    "TSAGDA004",  # module/path mismatch
    "TSAGDA005",  # duplicate declaration
    "TSAGDA006",  # duplicate field
    "TSAGDA007",  # duplicate constructor
    "TSAGDA010",  # duplicate identical clause
    "TSAGDA011",  # dangling structural block
    "TSAGDA012",  # interaction hole
    "TSAGDA013",  # raw underscore in exported signature
    "TSAGDA061",  # duplicate record assignment
    "TSAGDA150",  # fixity references unknown local declaration
    "TSAGDA151",  # conflicting fixity
    "TSAGDA152",  # local mixfix hole count
    "TSAGDA153",  # syntax declaration references unknown local symbol
    "TSAGDA161", "TSAGDA162", "TSAGDA163", "TSAGDA164", "TSAGDA165",
    "TSAGDA170", "TSAGDA172", "TSAGDA173", "TSAGDA174", "TSAGDA175",
    "TSAGDA201", "TSAGDA204",
}


# These rules need DASHI's cross-node/module structural index but do not require
# Agda elaboration. Their hard-error form is permitted only when the emitting
# rule has the corresponding rigid evidence.
_INDEX_SAFE = {
    "TSAGDA001", "TSAGDA002", "TSAGDA003",
    "TSAGDA008", "TSAGDA009",
    "TSAGDA020", 
    "TSAGDA029", "TSAGDA030",
    "TSAGDA042", "TSAGDA043", "TSAGDA044", 
    
    "TSAGDA050", "TSAGDA051", "TSAGDA054",
    "TSAGDA056",
    "TSAGDA060", "TSAGDA062", "TSAGDA063", "TSAGDA065",
    "TSAGDA066", "TSAGDA067", "TSAGDA068",
    "TSAGDA070", "TSAGDA071", "TSAGDA073", "TSAGDA074",
    "TSAGDA077", "TSAGDA078", 
    "TSAGDA080", "TSAGDA081", "TSAGDA083", "TSAGDA085",
    "TSAGDA086", "TSAGDA087", "TSAGDA088", "TSAGDA089",
    "TSAGDA100", "TSAGDA101", "TSAGDA102", "TSAGDA103", 
    "TSAGDA105",
    "TSAGDA111", "TSAGDA112", "TSAGDA115",
    
    "TSAGDA130", "TSAGDA131",
    "TSAGDA140", "TSAGDA141", "TSAGDA142", "TSAGDA143",
    "TSAGDA160", "TSAGDA166",
    "TSAGDA171",
    "TSAGDA180", "TSAGDA181", "TSAGDA182", "TSAGDA183", "TSAGDA184",
    "TSAGDA185", "TSAGDA186",
    "TSAGDA200", "TSAGDA202", "TSAGDA203", "TSAGDA205", "TSAGDA206",
    "TSAGDA207", "TSAGDA208",
}


# These are useful structural suspicions, but a *hard* conclusion depends on
# Agda-resolved scope/elaboration: opens/renamings, overloading, mixfix, implicit
# insertion, or local dependent scope can change the interpretation.
_SCOPE_REQUIRED = {
    "TSAGDA000",  # successful Agda scope proves tree-sitter ERROR nodes are grammar artifacts
    "TSAGDA021",  # qualified export availability is a scope-resolution fact
    "TSAGDA022",  # unknown/malformed alias use
    "TSAGDA023",  # using(...) export availability is a scope-resolution fact
    "TSAGDA025",  # renaming source availability is a scope-resolution fact
    "TSAGDA024",  # hiding entry validity through re-export chains
    "TSAGDA026",  # rename/open collision
    "TSAGDA027",  # ambiguous unqualified name from opens
    "TSAGDA028",  # conflicting import aliases are resolved/rejected by Agda scope
    "TSAGDA055",  # ambiguous opened projection
    "TSAGDA084",  # inaccessible pattern scope
    "TSAGDA113",  # visibly unbound RHS identifier
    "TSAGDA154",  # ambiguous opened operator
}


# Kept for future diagnostics whose truth genuinely requires the kernel.
_TYPECHECK_REQUIRED: Set[str] = {
    "TSAGDA046",  # constructor application arity is settled by elaboration
    "TSAGDA047",  # record constructor parameters/fields require elaborated arity
    "TSAGDA048",  # parameterized module application arity is elaboration-sensitive
    "TSAGDA064",  # field lambda arity may depend on target-type unfolding
    "TSAGDA082",  # constructor-pattern arity is a typing/elaboration judgment
    "TSAGDA040",  # over-application can depend on result-type unfolding
    "TSAGDA049",  # projection saturation/pointfree use is a typing judgment
    "TSAGDA052",  # a bare projection is a valid function value in pointfree contexts
    "TSAGDA053",  # projection result aliases may unfold to additional functions
    "TSAGDA079",  # zero shallow arity does not prove a term is non-functional after unfolding
    "TSAGDA104",  # target/result aliases may unfold to equality propositions
    "TSAGDA120",  # terms may themselves inhabit Set and validly appear as types
    "TSAGDA121",  # constructor result aliases require definitional equality
    "TSAGDA122",  # constructor target may reduce to the datatype under construction
    "TSAGDA123",  # type-valued projections/terms require typing, not name-class heuristics
    "TSAGDA041",  # under-application / saturation is a typing judgment
    "TSAGDA045",  # clause/signature arity can depend on pointfree eta/type unfolding
    "TSAGDA072",  # constructor/result-head comparison can require synonym unfolding
    "TSAGDA075",  # conservative: shared by rigid and synonym-sensitive ctor checks
    "TSAGDA076",  # partial application vs type use needs elaborated typing
    "TSAGDA110",  # compatibility alias of TSAGDA045
    "TSAGDA114",  # clause constructor/result-head comparison needs unfolding
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

# Some independently emitted diagnostics describe the same root cause but are
# retained as separate compatibility/reporting codes. Canonicalize them only
# for triage; do not synthesize extra emitted diagnostics.
_ALIAS_TO_CANONICAL.update({
    "TSAGDA052": "TSAGDA049",
    "TSAGDA075": "TSAGDA072",
    "TSAGDA114": "TSAGDA072",
    "TSAGDA123": "TSAGDA120",
})


def canonical_code(code: str) -> str:
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


def policy_for(code: str) -> DiagnosticPolicy:
    """Return the explicit evidence contract for CODE.

    New diagnostics must be classified deliberately. Falling back silently is
    exactly how an unsafe structural heuristic can accidentally become a hard
    error, so an unclassified code is a programming error.
    """
    try:
        return DIAGNOSTIC_POLICIES[code]
    except KeyError as exc:
        raise KeyError(
            f"diagnostic {code} has no evidence policy; classify it before emitting"
        ) from exc


def classify_codes(codes: Iterable[str]) -> Mapping[EvidenceLevel, Set[str]]:
    grouped: Dict[EvidenceLevel, Set[str]] = {}
    for code in codes:
        grouped.setdefault(policy_for(code).minimum, set()).add(code)
    return grouped


def evidence_name(level: EvidenceLevel) -> str:
    return {
        EvidenceLevel.TREE_SITTER: "tree-sitter",
        EvidenceLevel.DASHI_INDEX: "dashi-index",
        EvidenceLevel.AGDA_SCOPE: "agda-scope",
        EvidenceLevel.AGDA_TYPECHECKER: "agda-typechecker",
    }[level]
