from __future__ import annotations

from dataclasses import dataclass
from difflib import SequenceMatcher
import hashlib
import re
from typing import Iterable, Optional, Tuple


_ROUND_RE = re.compile(r"Round(\d+)")
_IDENT_RE = re.compile(r"\b[A-Za-z_][A-Za-z0-9_']*\b")
_BINDER_RE = re.compile(r"([({])\s*([A-Za-z_][A-Za-z0-9_']*)\s*:\s*([^)}]+)([)}])")
_SPACE_RE = re.compile(r"\s+")


@dataclass(frozen=True)
class SymbolFingerprint:
    normalized_signature: str
    signature_sha256: str
    body_sha256: str


def stable_sha256(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _alpha_normalize_explicit_binders(text: str) -> str:
    mapping: dict[str, str] = {}
    counter = 0

    def replace(match: re.Match[str]) -> str:
        nonlocal counter
        opener, name, type_text, closer = match.groups()
        if name not in mapping:
            mapping[name] = f"v{counter}"
            counter += 1
        normalized_type = type_text
        for old, new in mapping.items():
            normalized_type = re.sub(rf"\b{re.escape(old)}\b", new, normalized_type)
        return f"{opener}{mapping[name]}:{normalized_type}{closer}"

    rewritten = _BINDER_RE.sub(replace, text)
    for old, new in mapping.items():
        rewritten = re.sub(rf"\b{re.escape(old)}\b", new, rewritten)
    return rewritten


def normalized_signature(signature: str) -> str:
    """Return a deterministic shallow signature form for discovery only."""
    text = re.sub(r"--[^\n]*", " ", signature)
    text = _alpha_normalize_explicit_binders(text)
    return _SPACE_RE.sub("", text).strip()


def normalized_body(body: str) -> str:
    text = re.sub(r"--[^\n]*", " ", body)
    return _SPACE_RE.sub("", text).strip()


def make_fingerprint(signature: str, body: str = "") -> SymbolFingerprint:
    normalized = normalized_signature(signature)
    return SymbolFingerprint(
        normalized_signature=normalized,
        signature_sha256=stable_sha256(normalized),
        body_sha256=stable_sha256(normalized_body(body)) if body else "",
    )


def classify_surface_role(module_name: str) -> str:
    if _ROUND_RE.search(module_name):
        return "historical_snapshot"
    lowered = module_name.lower()
    # Canonical Core ownership is structural and outranks incidental words such
    # as Receipt/Candidate in a declaration or module name.
    if ".core." in lowered or module_name.startswith("DASHI.Core."):
        return "canonical"
    if "validation" in lowered:
        return "validation"
    if "receipt" in lowered:
        return "receipt"
    if "candidate" in lowered:
        return "candidate"
    return "current"


def round_family(module_name: str) -> Tuple[Optional[str], Optional[int]]:
    match = _ROUND_RE.search(module_name)
    if match is None:
        return None, None
    number = int(match.group(1))
    family = module_name[: match.start()] + "Round#" + module_name[match.end() :]
    return family, number


def _token_set(value: str) -> set[str]:
    return {token.lower() for token in _IDENT_RE.findall(value)}


def _jaccard(left: Iterable[str], right: Iterable[str]) -> float:
    a = set(left)
    b = set(right)
    if not a or not b:
        return 0.0
    return len(a & b) / len(a | b)


def similarity_score(
    *,
    name_a: str,
    signature_a: str,
    refs_a: Iterable[str] = (),
    name_b: str,
    signature_b: str,
    refs_b: Iterable[str] = (),
) -> float:
    """Return a heuristic discovery score in [0, 1], never proof equivalence."""
    sig_a = normalized_signature(signature_a)
    sig_b = normalized_signature(signature_b)
    sig_ratio = SequenceMatcher(None, sig_a, sig_b).ratio() if sig_a and sig_b else 0.0
    sig_tokens = _jaccard(_token_set(sig_a), _token_set(sig_b))
    ref_ratio = _jaccard((item.lower() for item in refs_a), (item.lower() for item in refs_b))
    name_ratio = SequenceMatcher(None, name_a.lower(), name_b.lower()).ratio()
    score = 0.5 * sig_ratio + 0.25 * sig_tokens + 0.15 * ref_ratio + 0.10 * name_ratio
    return max(0.0, min(1.0, score))
