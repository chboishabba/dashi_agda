from __future__ import annotations

from pathlib import Path
import sqlite3
from typing import Any, Optional

from .repository_store import (
    DEFAULT_REPOSITORY_DB,
    ensure_repository_schema,
    search_narrative,
)


DEFAULT_PATH = DEFAULT_REPOSITORY_DB


def apply_narrative_gate(receipt: dict[str, Any], narrative: dict[str, Any]) -> dict[str, Any]:
    """Fail closed unless semantic and narrative absence checks both complete.

    Development narrative remains discovery evidence only. A narrative hit
    blocks a categorical absence claim because it may point to a renamed,
    superseded, partial, or historical object that requires formal inspection.
    """

    result = dict(receipt)
    coverage = dict(result.get("coverage", {}))
    coverage["narrative_archaeology_available"] = bool(narrative.get("available"))
    coverage["narrative_archaeology_complete"] = bool(narrative.get("complete"))
    coverage["narrative_archaeology_checked"] = bool(narrative.get("available"))
    result["coverage"] = coverage
    result["narrative_archaeology"] = narrative

    matches = narrative.get("matches", [])
    if matches:
        result["absence_claim_permitted"] = False
        result["absence_status"] = "historical_narrative_candidate_exists"
        return result

    if result.get("absence_claim_permitted") and not (
        narrative.get("available") and narrative.get("complete")
    ):
        result["absence_claim_permitted"] = False
        result["absence_status"] = "search_incomplete"
    return result


class NarrativeCache:
    """Compatibility reader over normalized narrative rows in the shared DB."""

    def __init__(
        self,
        root: Path,
        path: Optional[Path] = None,
        *,
        connection: Optional[sqlite3.Connection] = None,
    ) -> None:
        self.root = root.resolve()
        chosen = path or DEFAULT_PATH
        self.path = chosen if chosen.is_absolute() else self.root / chosen
        self.connection = connection
        self._owns_connection = connection is None

    def _open(self) -> Optional[sqlite3.Connection]:
        if self.connection is not None:
            return self.connection
        if not self.path.exists():
            return None
        conn = sqlite3.connect(self.path)
        conn.row_factory = sqlite3.Row
        ensure_repository_schema(conn)
        self.connection = conn
        return conn

    def close(self) -> None:
        if self._owns_connection and self.connection is not None:
            self.connection.close()
            self.connection = None

    def search(self, query: str, *, limit: int = 40, threshold: float = 0.18) -> dict[str, Any]:
        conn = self._open()
        if conn is None:
            return {
                "available": False,
                "complete": False,
                "authority": "development-narrative",
                "matches": [],
                "database": str(self.path),
            }
        result = search_narrative(conn, query, limit=limit, threshold=threshold)
        result["database"] = str(self.path)
        return result
