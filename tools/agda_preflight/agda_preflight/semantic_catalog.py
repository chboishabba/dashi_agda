from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import sqlite3
from typing import Dict, Iterable, Mapping, Optional


@dataclass(frozen=True)
class SemanticModule:
    module_name: str
    object_hash: str
    declaration_count: int
    term_count: int
    checked_source_sha256: Optional[str] = None
    current_source_sha256: Optional[str] = None
    freshness: str = "unknown"

    def as_dict(self) -> dict:
        return {
            "module_name": self.module_name,
            "object_hash": self.object_hash,
            "declaration_count": self.declaration_count,
            "term_count": self.term_count,
            "checked_source_sha256": self.checked_source_sha256,
            "current_source_sha256": self.current_source_sha256,
            "freshness": self.freshness,
        }


@dataclass(frozen=True)
class SemanticDeclaration:
    declaration_name: str
    module_name: str
    role: str
    mapping_mode: str
    object_hash: str
    checked_source_sha256: Optional[str]
    current_source_sha256: Optional[str]
    freshness: str
    source_file: str
    source_start_line: int
    source_end_line: int
    direct_dependencies: tuple[str, ...]

    def as_dict(self) -> dict:
        return {
            "declaration_name": self.declaration_name,
            "module_name": self.module_name,
            "role": self.role,
            "mapping_mode": self.mapping_mode,
            "object_hash": self.object_hash,
            "checked_source_sha256": self.checked_source_sha256,
            "current_source_sha256": self.current_source_sha256,
            "freshness": self.freshness,
            "source_file": self.source_file,
            "source_start_line": self.source_start_line,
            "source_end_line": self.source_end_line,
            "direct_dependencies": list(self.direct_dependencies),
            "authority": "translation-capability-only",
            "establishes_proof": False,
        }


class SemanticCatalog:
    """Read-only adapter over the agda2lean SQLite semantic catalog.

    Module heads establish content-addressed semantic snapshots and their
    checked source hashes. Declaration rows expose agda2lean's own proof-aware
    lowering classification (`Exact`, `Encoded`, `Reconstruct`, `Quarantined`,
    `Unsupported`). These are translation capabilities, never theorem authority.
    """

    def __init__(self, path: Path) -> None:
        self.path = path.resolve()
        uri = f"file:{self.path}?mode=ro"
        self.connection = sqlite3.connect(uri, uri=True)
        self.connection.row_factory = sqlite3.Row
        self._module_head_columns = {
            row["name"]
            for row in self.connection.execute(
                "PRAGMA table_info(module_heads)"
            ).fetchall()
        }
        self.has_checked_source_sha256 = (
            "checked_source_sha256" in self._module_head_columns
        )
        self.has_declarations = self._table_exists("declarations")
        self.has_direct_dependencies = self._table_exists("direct_dependencies")

    def _table_exists(self, table: str) -> bool:
        row = self.connection.execute(
            "SELECT 1 FROM sqlite_master WHERE type='table' AND name=?",
            (table,),
        ).fetchone()
        return row is not None

    def close(self) -> None:
        self.connection.close()

    def __enter__(self) -> "SemanticCatalog":
        return self

    def __exit__(self, exc_type, exc, tb) -> None:
        self.close()

    @staticmethod
    def _render_hash(value) -> str:
        if isinstance(value, bytes):
            return value.hex()
        return str(value)

    @staticmethod
    def _freshness(
        checked_source_sha256: Optional[str],
        current_source_sha256: Optional[str],
    ) -> str:
        if checked_source_sha256 is None or current_source_sha256 is None:
            return "unknown"
        return (
            "fresh"
            if checked_source_sha256.lower() == current_source_sha256.lower()
            else "stale"
        )

    def lookup(
        self,
        module_names: Iterable[str],
        current_source_hashes: Optional[Mapping[str, str]] = None,
    ) -> Dict[str, SemanticModule]:
        names = sorted(set(module_names))
        current = current_source_hashes or {}
        result: Dict[str, SemanticModule] = {}
        # Stay well below common SQLite parameter limits.
        for offset in range(0, len(names), 400):
            chunk = names[offset : offset + 400]
            if not chunk:
                continue
            placeholders = ",".join("?" for _ in chunk)
            checked_column = (
                "checked_source_sha256"
                if self.has_checked_source_sha256
                else "NULL AS checked_source_sha256"
            )
            rows = self.connection.execute(
                f"""
                SELECT module_name, object_hash, declaration_count, term_count,
                       {checked_column}
                FROM module_heads
                WHERE module_name IN ({placeholders})
                """,
                chunk,
            ).fetchall()
            for row in rows:
                module_name = row["module_name"]
                checked = row["checked_source_sha256"]
                current_hash = current.get(module_name)
                item = SemanticModule(
                    module_name=module_name,
                    object_hash=self._render_hash(row["object_hash"]),
                    declaration_count=int(row["declaration_count"]),
                    term_count=int(row["term_count"]),
                    checked_source_sha256=checked,
                    current_source_sha256=current_hash,
                    freshness=self._freshness(
                        checked,
                        current_hash,
                    ),
                )
                result[item.module_name] = item
        return result

    def declaration_capability(
        self,
        declaration_name: str,
        *,
        current_source_hash: Optional[str] = None,
    ) -> Optional[dict]:
        """Return agda2lean's exact lowering classification for one declaration.

        This reads only the translator's normalized SQLite catalog. A mapping
        mode reports what translation work is supported; even `Exact` does not
        itself certify the emitted Lean theorem.
        """
        if not self.has_declarations:
            return None
        checked_column = (
            "h.checked_source_sha256"
            if self.has_checked_source_sha256
            else "NULL AS checked_source_sha256"
        )
        row = self.connection.execute(
            f"""
            SELECT d.declaration_name, d.module_name, d.role, d.mapping_mode,
                   d.source_file, d.source_start_line, d.source_end_line,
                   h.object_hash, {checked_column}
            FROM declarations AS d
            JOIN module_heads AS h ON h.module_name = d.module_name
            WHERE d.declaration_name = ?
            """,
            (declaration_name,),
        ).fetchone()
        if row is None:
            return None
        dependencies: tuple[str, ...] = ()
        if self.has_direct_dependencies:
            dependencies = tuple(
                str(item[0])
                for item in self.connection.execute(
                    """
                    SELECT dependency_name
                    FROM direct_dependencies
                    WHERE declaration_name=?
                    ORDER BY dependency_name
                    """,
                    (declaration_name,),
                ).fetchall()
            )
        checked = row["checked_source_sha256"]
        item = SemanticDeclaration(
            declaration_name=str(row["declaration_name"]),
            module_name=str(row["module_name"]),
            role=str(row["role"]),
            mapping_mode=str(row["mapping_mode"]),
            object_hash=self._render_hash(row["object_hash"]),
            checked_source_sha256=(str(checked) if checked is not None else None),
            current_source_sha256=current_source_hash,
            freshness=self._freshness(
                str(checked) if checked is not None else None,
                current_source_hash,
            ),
            source_file=str(row["source_file"]),
            source_start_line=int(row["source_start_line"]),
            source_end_line=int(row["source_end_line"]),
            direct_dependencies=dependencies,
        )
        return item.as_dict()
