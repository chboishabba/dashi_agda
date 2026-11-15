"""Read-only fleet-native residual handoff preflight.

No scheduler, transport, corpus access, mutation, or authority promotion.
Caller must supply an independently resolved canonical thread ID. This module
does not infer identities from labels, titles, timestamps or SHA references.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping
import hashlib
import json


@dataclass(frozen=True)
class ResidualCandidate:
    canonical_thread_id: str
    consumer_ref: str
    residual_ref: str
    task_atom: str
    source_revision_ref: str
    source_digest: str


def _digest(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def preflight(candidate: ResidualCandidate, *, canonical_ids: set[str]) -> dict[str, Any]:
    """Produce bounded, non-authoritative ITIR operator candidate or explicit hold.

    Exact canonical identity must be supplied by the caller's trusted mapping.
    The returned object is NOT a verified proof or an executable dispatch.
    """
    reasons = []
    if not candidate.canonical_thread_id or candidate.canonical_thread_id not in canonical_ids:
        reasons.append("canonical_thread_unresolved")
    if not candidate.consumer_ref or not candidate.residual_ref:
        reasons.append("consumer_or_residual_missing")
    if not candidate.source_revision_ref or not candidate.source_digest:
        reasons.append("source_identity_incomplete")
    if not candidate.task_atom or len(candidate.task_atom) > 512:
        reasons.append("task_atom_missing_or_oversized")
    # No raw task atom or corpus text is emitted in this preflight receipt.
    receipt = {
        "schema": "dashi.fleet.residual_preflight.v1",
        "canonical_thread_id": candidate.canonical_thread_id,
        "consumer_ref": candidate.consumer_ref,
        "residual_ref": candidate.residual_ref,
        "source_revision_ref": candidate.source_revision_ref,
        "source_digest": candidate.source_digest,
        "task_atom_sha256": _digest(candidate.task_atom),
        "held_reasons": sorted(reasons),
        "review_only": True,
        "proof_verified": False,
        "dispatch_performed": False,
        "promotion": False,
    }
    receipt["receipt_sha256"] = _digest(json.dumps(receipt, sort_keys=True, separators=(",", ":")))
    return receipt


def operator_candidate(candidate: ResidualCandidate, *, canonical_ids: set[str]) -> dict[str, Any]:
    """Return the *candidate input* shape, not an ITIR execution result.

    A caller must use ITIR's existing operator_workflow to validate/inspect it.
    """
    check = preflight(candidate, canonical_ids=canonical_ids)
    if check["held_reasons"]:
        return {"state": "held", "preflight": check}
    return {
        "state": "candidate_only",
        "preflight": check,
        "operator_input": {
            "canonical_thread_id": candidate.canonical_thread_id,
            "task_atom": candidate.task_atom,
        },
    }
