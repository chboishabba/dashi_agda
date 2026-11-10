#!/usr/bin/env python3
"""Conservative Lean canonical statement DAG and context-indexed fibre retrieval.

Ingest externally supplied elaborated declaration export rows ONLY after exact
source occurrence admission. Source bytes, hashes and regex guesses are never
treated as canonical Lean types or kernel proofs. Statement identity is exact
canonical bytes under foundation/profile, not shared fibre projection. Distinct
proof terms and original source/author occurrences survive interning.

Dependency edges are explicit exporter-supplied original declaration names.
They are never fabricated from matching type names. Seal validates completeness
and acyclicity. The hyperfabric view is a context-indexed incidence/restriction
index, NOT a proof of geometric gluing/semantic theorem equivalence.
"""
from __future__ import annotations
from bisect import bisect_left, bisect_right, insort
from collections import defaultdict
from dataclasses import dataclass
import base64
import hashlib


class WorldError(ValueError):
    pass


@dataclass(frozen=True, order=True)
class Origin:
    repository: str
    revision: str
    declaration: str


@dataclass(frozen=True)
class Statement:
    statement_id: str
    profile: str
    canonical_type: bytes
    type_head: str
    universe_shape: str


class CanonicalLeanWorld:
    def __init__(self, source_manifest):
        self.sources = {}
        for receipt in source_manifest:
            if receipt.get("status") != "source-verified-not-elaborated":
                continue
            key = (receipt["repository"], receipt["revision"], receipt["path"])
            if key in self.sources and self.sources[key] != receipt:
                raise WorldError("conflicting source world origin")
            self.sources[key] = dict(receipt)
        self.statements: dict[str, Statement] = {}
        self.occurrences: dict[Origin, dict] = {}
        self._exact = defaultdict(list)
        self._fibre = defaultdict(list)
        self._dependencies = {}
        self.generation = 0
        self._sealed = False

    @staticmethod
    def _decoded_type(row: dict) -> bytes:
        raw = row.get("canonical_type_b64")
        if not isinstance(raw, str):
            raise WorldError("independently exported canonical type bytes required")
        try:
            value = base64.b64decode(raw, validate=True)
        except Exception as exc:
            raise WorldError("invalid base64 canonical type") from exc
        if not value:
            raise WorldError("empty canonical type")
        return value

    @staticmethod
    def _origin(item):
        if not isinstance(item, dict):
            raise WorldError("invalid dependency occurrence")
        try:
            origin = Origin(item["repository"], item["revision"],
                            item["declaration"])
        except (KeyError, TypeError) as exc:
            raise WorldError("missing dependency origin") from exc
        if not all(origin.__dict__.values()):
            raise WorldError("empty dependency origin")
        return origin

    def admit(self, row: dict) -> bool:
        if self._sealed:
            raise WorldError("sealed world is immutable")
        if row.get("kind") != "lean-elaborated-export":
            raise WorldError("raw source inventory cannot become Lean declaration")
        origin = self._origin(row)
        try:
            source_key = (origin.repository, origin.revision, row["path"])
            source = self.sources[source_key]
        except (KeyError, TypeError) as exc:
            raise WorldError("declaration has no pinned original source receipt") from exc
        if row.get("source_sha256") != source.get("sha256"):
            raise WorldError("source bytes do not match provenance receipt")
        for key in ("profile", "type_head", "universe_shape", "proof_digest",
                    "attribution", "exporter_profile"):
            if not isinstance(row.get(key), str) or not row[key]:
                raise WorldError("missing original elaboration/proof provenance: "+key)
        canonical = self._decoded_type(row)
        dependency_raw = row.get("dependencies")
        if not isinstance(dependency_raw, list):
            raise WorldError("explicit original dependency list required")
        dependencies = tuple(self._origin(x) for x in dependency_raw)
        if origin in dependencies:
            raise WorldError("declaration depends on itself")
        old = self.occurrences.get(origin)
        if old is not None:
            if old != row:
                raise WorldError("same original declaration changed content or provenance")
            return False

        # Fibre restriction is a search index, NOT an exact theorem quotient.
        fibre = (row["profile"], row["type_head"], row["universe_shape"])
        digest = hashlib.sha256(canonical).hexdigest()
        key = (row["profile"], digest)
        interned = None
        for sid in self._exact[key]:
            existing = self.statements[sid]
            if existing.canonical_type == canonical:
                interned = sid
                break
        if interned is None:
            # Exact type bytes are checked even when SHA-256 matches; a digest
            # collision never incorrectly unifies distinct statement carriers.
            interned = hashlib.sha256(
                (row["profile"]+"\0").encode()+canonical).hexdigest()
            if interned in self.statements:
                raise WorldError("statement ID collision")
            self.statements[interned] = Statement(
                interned, row["profile"], canonical, row["type_head"],
                row["universe_shape"])
            self._exact[key].append(interned)
        else:
            old_statement = self.statements[interned]
            if (old_statement.type_head,old_statement.universe_shape) != fibre[1:]:
                raise WorldError("same exact type given incompatible fibre projection")

        self.occurrences[origin] = dict(row)
        self.occurrences[origin]["statement_id"] = interned
        self._dependencies[origin] = dependencies
        insort(self._fibre[fibre], origin)
        self.generation += 1
        return True

    def seal(self):
        """Fail on missing dependency owners, cycles or invalid source context."""
        active=set()
        done=set()

        def visit(node):
            if node in active:
                raise WorldError("cyclic exporter dependency graph")
            if node in done:
                return
            if node not in self.occurrences:
                raise WorldError("unresolved original dependency: "+repr(node))
            active.add(node)
            for dep in self._dependencies[node]:
                visit(dep)
            active.remove(node)
            done.add(node)

        for origin in sorted(self.occurrences):
            visit(origin)
        self._sealed = True

    def fibre_candidates(self, profile, type_head, universe_shape, limit,
                         cursor=None):
        """Exact keyset ordering, max returned k; no same-fibre proof promotion.

        A cursor is only valid for the generation at which it was created.
        Arbitrary context restrictions may scan more than k original owners.
        """
        if limit < 0:
            raise WorldError("negative search budget")
        if cursor is not None and cursor.get("generation") != self.generation:
            raise WorldError("stale world-generation cursor")
        keys = self._fibre.get((profile,type_head,universe_shape), [])
        after = self._origin(cursor["after"]) if cursor else None
        start = bisect_right(keys,after) if after else 0
        matches = keys[start:start+limit]
        remaining = len(keys)-(start+len(matches))
        next_cursor = (
            {"generation":self.generation,
             "after":{"repository":matches[-1].repository,
                      "revision":matches[-1].revision,
                      "declaration":matches[-1].declaration}}
            if matches and remaining else None)
        return {"matches":[dict(self.occurrences[k]) for k in matches],
                "examined":len(matches), "remaining":remaining,
                "complete":remaining==0, "next_cursor":next_cursor,
                "projection_is_not_equivalence":True}

    def context_incidence(self, root: Origin, max_nodes: int = 100,
                          max_edges: int = 200):
        """Bounded source-original dependency incidence / hyperfabric view.

        Restriction to a context is only a view. It never implies that nodes
        are equal or that a commuting diagram has been proved.
        """
        if max_nodes < 1 or max_edges < 0:
            raise WorldError("invalid incidence limits")
        if not self._sealed:
            raise WorldError("dependency world must be sealed before retrieval")
        if root not in self.occurrences:
            raise WorldError("unknown original declaration")
        visited=set()
        frontier=[root]
        edges=[]
        truncated=False
        while frontier:
            current=frontier.pop(0)
            if current in visited:
                continue
            if len(visited)>=max_nodes:
                truncated=True;break
            visited.add(current)
            for dependency in self._dependencies[current]:
                if len(edges)>=max_edges:
                    truncated=True;break
                edges.append((current,dependency))
                if dependency not in visited:
                    frontier.append(dependency)
            if truncated:break
        def name(o):return (o.repository,o.revision,o.declaration)
        return {"nodes":[name(x) for x in sorted(visited)],
                "dependency_edges":[(name(a),name(b)) for a,b in edges],
                "complete":not truncated,"truncated":truncated,
                "context":"source-pinned-Lean-dependencies",
                "semantic_equivalence_certified":False}


    def populate_existing_fibre_index(self, module):
        """Reuse PR #1483 FibreIndex with exporter-produced exact statement bytes.

        The caller supplies the existing imported module (or module loaded from
        its separate PR worktree). This does not manufacture proof receipts
        from source fingerprints and does not require merging PRs prematurely.
        """
        if not self._sealed:
            raise WorldError("seal dependency graph before exporting world index")
        required = ("FibreIndex", "SourceOccurrence", "Declaration")
        if any(not hasattr(module, name) for name in required):
            raise WorldError("expected exact PR #1483 FibreIndex module")
        index = module.FibreIndex()
        for origin in sorted(self.occurrences):
            row = self.occurrences[origin]
            original = module.SourceOccurrence(
                origin.repository, origin.revision, origin.declaration,
                row["proof_digest"], row["attribution"])
            declared = module.Declaration(
                original, row["profile"], row["type_head"],
                row["universe_shape"],
                self.statements[row["statement_id"]].canonical_type,
                tuple(f"{d.repository}@{d.revision}:{d.declaration}"
                      for d in self._dependencies[origin]))
            index.admit(declared)
        if index.occurrence_count() != len(self.occurrences):
            raise WorldError("fibre index dropped original provenance occurrences")
        return index

    def counts(self):
        return {"source_files":len(self.sources),
                "statement_exact_nodes":len(self.statements),
                "proof_occurrences":len(self.occurrences),
                "fibres":len(self._fibre), "generation":self.generation}
