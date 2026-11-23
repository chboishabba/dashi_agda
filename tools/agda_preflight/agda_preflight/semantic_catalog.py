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


class SemanticCatalog:
    """Read-only adapter over the agda2lean SQLite module catalog.

    Newer agda2lean catalogs record the source SHA256 accepted when the
    semantic module head was stored. Older catalogs remain readable and report
    freshness='unknown'. A known checked hash is compared with the source
    index's current hash to classify the snapshot as fresh or stale.
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
