from __future__ import annotations

from difflib import SequenceMatcher
import re


_TOKEN_RE = re.compile(r"[A-Za-z0-9]+")
_CAMEL_RE = re.compile(r"(?<=[a-z0-9])(?=[A-Z])")


def _tokens(text: str) -> set[str]:
    expanded = _CAMEL_RE.sub(" ", text.replace("_", " ").replace(".", " "))
    return {item.lower() for item in _TOKEN_RE.findall(expanded) if len(item) > 1}


def _query_score(query: str, row: dict) -> float:
    """Cheap deterministic concept/name score; not semantic equivalence."""
    q = query.lower().strip()
    name = str(row.get("name", "")).lower()
    qualified = str(row.get("qualified_name", "")).lower()
    signature = str(row.get("signature", "")).lower()
    q_tokens = _tokens(query)
    haystack_tokens = _tokens(" ".join((row.get("name", ""), row.get("qualified_name", ""), row.get("signature", ""))))
    token_score = (
        len(q_tokens & haystack_tokens) / len(q_tokens | haystack_tokens)
        if q_tokens and haystack_tokens else 0.0
    )
    name_score = max(
        SequenceMatcher(None, q, name).ratio(),
        SequenceMatcher(None, q, qualified).ratio(),
    )
    substring = 1.0 if q and (q in name or q in qualified) else 0.0
    return min(1.0, 0.50 * name_score + 0.35 * token_score + 0.15 * substring)
