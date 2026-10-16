from __future__ import annotations

from difflib import SequenceMatcher
import json
from pathlib import Path
import re
from typing import Any, Optional


_TOKEN_RE = re.compile(r"[A-Za-z0-9_+'-]+")
DEFAULT_PATH = Path(".repo-index/narrative.json")


def _tokens(value: str) -> set[str]:
    return {token.lower() for token in _TOKEN_RE.findall(value) if len(token) > 1}


def _score(query: str, event: dict[str, Any]) -> float:
    q = query.strip().lower()
    query_tokens = _tokens(q)
    title = str(event.get("title", ""))
    text = str(event.get("text", ""))
    objects = " ".join(
        str(item)
        for key in ("touched_objects", "introduced_objects", "removed_objects")
        for item in event.get(key, [])
    )
    haystack = "\n".join((title, text, objects))
    haystack_tokens = _tokens(haystack)
    token_score = (
        len(query_tokens & haystack_tokens) / len(query_tokens)
        if query_tokens
        else 0.0
    )
    name_score = SequenceMatcher(None, q, title.lower()).ratio()
    exact = 1.0 if q and q in haystack.lower() else 0.0
    object_score = (
        len(query_tokens & _tokens(objects)) / len(query_tokens)
        if query_tokens and objects
        else 0.0
    )
    return min(1.0, 0.45 * token_score + 0.25 * object_score + 0.20 * name_score + 0.10 * exact)


class NarrativeCache:
    """Read the repo-history development narrative cache, if available.

    Narrative data guides discovery and archaeology only. It cannot establish
    theorem truth, proof validity, empirical truth, or promotion authority.
    """

    def __init__(self, root: Path, path: Optional[Path] = None) -> None:
        self.root = root.resolve()
        chosen = path or DEFAULT_PATH
        self.path = chosen if chosen.is_absolute() else self.root / chosen

    def _load(self) -> Optional[dict[str, Any]]:
        if not self.path.exists():
            return None
        try:
            payload = json.loads(self.path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            return None
        if payload.get("schema") != "dashi.repo-narrative.v1":
            return None
        return payload

    def search(self, query: str, *, limit: int = 40, threshold: float = 0.18) -> dict[str, Any]:
        payload = self._load()
        if payload is None:
            return {
                "available": False,
                "complete": False,
                "authority": "development-narrative",
                "matches": [],
                "path": str(self.path),
            }
        ranked = []
        for event in payload.get("events", []):
            if not isinstance(event, dict):
                continue
            score = _score(query, event)
            if score < threshold:
                continue
            item = dict(event)
            item["archaeology_score"] = score
            ranked.append(item)
        ranked.sort(
            key=lambda item: (
                -float(item.get("archaeology_score", 0.0)),
                -int(item.get("timestamp", 0) or 0),
                str(item.get("event_id", "")),
            )
        )
        source_status = payload.get("source_status", {})
        complete = bool(source_status.get("commit_history_complete") is True)
        return {
            "available": True,
            "complete": complete,
            "authority": "development-narrative",
            "may_establish_formal_fact": False,
            "may_establish_empirical_fact": False,
            "source_status": source_status,
            "matches": ranked[:limit],
            "path": str(self.path),
        }
