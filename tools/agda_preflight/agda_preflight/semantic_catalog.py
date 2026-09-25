from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import sqlite3
from typing import Dict, Iterable, List


@dataclass(frozen=True)
class SemanticModule:
    module_name: str
    object_hash: str
    declaration_count: int
    term_count: int
    freshness: str = "unknown"

    def as_dict(self) -> dict:
        return {
            "module_name": self.module_name,
            "object_hash": self.object_hash,
            "declaration_count": self.declaration_count,
            "term_count": self.term_count,
            "freshness": self.freshness,
        }


class SemanticCatalog:
    """Read-only adapter over the agda2lean SQLite module catalog.

    The current agda2lean schema records semantic module object identities but
    not the source SHA that produced each checked object. Consequently this
    adapter deliberately reports freshness='unknown'; callers must not treat a
    catalog hit as proof that the current source is type-valid.
    """

    def __init__(self, path: Path) -> None:
        self.path = path.resolve()
        uri = f"file:{self.path}?mode=ro"
        self.connection = sqlite3.connect(uri, uri=True)
        self.connection.row_factory = sqlite3.Row

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

    def lookup(self, module_names: Iterable[str]) -> Dict[str, SemanticModule]:
        names = sorted(set(module_names))
        result: Dict[str, SemanticModule] = {}
        # Stay well below common SQLite parameter limits.
        for offset in range(0, len(names), 400):
            chunk = names[offset : offset + 400]
            if not chunk:
                continue
            placeholders = ",".join("?" for _ in chunk)
            rows = self.connection.execute(
                f"""
                SELECT module_name, object_hash, declaration_count, term_count
                FROM module_heads
                WHERE module_name IN ({placeholders})
                """,
                chunk,
            ).fetchall()
            for row in rows:
                item = SemanticModule(
                    module_name=row["module_name"],
                    object_hash=self._render_hash(row["object_hash"]),
                    declaration_count=int(row["declaration_count"]),
                    term_count=int(row["term_count"]),
                )
                result[item.module_name] = item
        return result
