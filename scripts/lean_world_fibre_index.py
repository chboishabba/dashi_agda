#!/usr/bin/env python3
"""Conservative, provenance-preserving fibre index for elaborated Lean declarations.

This indexes trusted *inputs* from an independent Lean kernel-term exporter.
It does not parse or elaborate Lean, certify equality of translated terms,
or turn search candidates into proofs. Same projection fibre != same theorem.
"""
from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
from collections import defaultdict
from typing import Iterable


@dataclass(frozen=True, order=True)
class SourceOccurrence:
    repository: str
    revision: str
    declaration: str
    term_digest: str
    attribution: str


@dataclass(frozen=True)
class Declaration:
    source: SourceOccurrence
    profile: str                    # Foundation/toolchain profile; do not erase
    type_head: str                  # Exporter-supplied conservative projection
    universe_shape: str
    canonical_type: bytes          # Exact exporter serialization; not source text
    dependencies: tuple[str, ...] = ()


@dataclass(frozen=True)
class SearchResult:
    matches: tuple[SourceOccurrence, ...]
    examined: int
    remaining: int
    complete: bool


class IdentityConflict(ValueError):
    pass


class FibreIndex:
    """Finite index whose exact buckets are lossless and whose search is bounded.

    Fibre projection is a retrieval constraint, not an equality certificate.
    Type bytes are compared before exact identity merging: digest collisions
    cannot silently merge incompatible statements.
    """

    def __init__(self) -> None:
        self._by_origin: dict[tuple[str, str, str], Declaration] = {}
        self._fibre: dict[tuple[str, str, str], set[tuple[str, str, str]]] = defaultdict(set)
        self._exact: dict[tuple[str, str], list[tuple[bytes, set[tuple[str, str, str]]]]] = defaultdict(list)

    @staticmethod
    def origin(d: Declaration) -> tuple[str, str, str]:
        return (d.source.repository, d.source.revision, d.source.declaration)

    @staticmethod
    def projection(d: Declaration) -> tuple[str, str, str]:
        return (d.profile, d.type_head, d.universe_shape)

    @staticmethod
    def fingerprint(d: Declaration) -> tuple[str, str]:
        return ("\\x1f".join((d.profile, d.type_head, d.universe_shape)),
                sha256(d.canonical_type).hexdigest())

    def admit(self, d: Declaration) -> bool:
        if not all((d.source.repository, d.source.revision, d.source.declaration,
                    d.source.term_digest, d.profile, d.type_head, d.universe_shape)):
            raise ValueError("source revision, proof digest and projection fields required")
        if not isinstance(d.canonical_type, bytes) or not d.canonical_type:
            raise ValueError("nonempty canonical type bytes required")
        key = self.origin(d)
        old = self._by_origin.get(key)
        if old is not None:
            if old != d:
                raise IdentityConflict("same pinned declaration changed: " + repr(key))
            return False
        self._by_origin[key] = d
        self._fibre[self.projection(d)].add(key)
        exact_bucket = self._exact[self.fingerprint(d)]
        for type_bytes, origins in exact_bucket:
            if type_bytes == d.canonical_type:
                origins.add(key)
                break
        else:
            exact_bucket.append((d.canonical_type, {key}))
        return True

    def exact_occurrences(self, d: Declaration) -> tuple[SourceOccurrence, ...]:
        # All proofs are retained, including same-type / different-term proofs.
        for type_bytes, origins in self._exact.get(self.fingerprint(d), ()):
            if type_bytes == d.canonical_type:
                return tuple(sorted(self._by_origin[k].source for k in origins))
        return ()

    def candidates(self, profile: str, type_head: str,
                   universe_shape: str, budget: int) -> SearchResult:
        """A deterministic limited search; completeness is explicit.

        A query covers only one requested projection fibre. Other fibres are
        *not* proven irrelevant. To avoid nondeterministic truncation, keys
        are sorted before taking the budget.
        """
        if budget < 0:
            raise ValueError("budget cannot be negative")
        keys = sorted(self._fibre.get((profile, type_head, universe_shape), ()))
        selected = keys[:budget]
        matches = tuple(self._by_origin[k].source for k in selected)
        remaining = len(keys) - len(selected)
        return SearchResult(matches, len(selected), remaining, remaining == 0)

    def occurrence_count(self) -> int:
        return len(self._by_origin)

    def exact_statement_count(self) -> int:
        return sum(len(bucket) for bucket in self._exact.values())

    def fibre_count(self) -> int:
        return len(self._fibre)

    def inventory(self) -> dict[str, int]:
        return {"occurrences": self.occurrence_count(),
                "exact_statements": self.exact_statement_count(),
                "fibres": self.fibre_count()}


def ingest(index: FibreIndex, declarations: Iterable[Declaration]) -> int:
    """Idempotent batch intake. Returns count of newly admitted occurrences."""
    return sum(index.admit(d) for d in declarations)
