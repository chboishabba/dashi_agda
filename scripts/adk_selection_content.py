from __future__ import annotations

import hashlib
import json
from typing import Sequence

import adk_pdb_cv_fixture as base

SELECTION_CONTENT_SCHEMA = "dashi.adk.selection_content.v1"


def canonical_selection_row(atom: base.Atom) -> str:
    try:
        mass = base.MASS[atom.element]
    except KeyError as exc:
        raise ValueError(f"no mass for element {atom.element!r}") from exc
    return "|".join(
        [
            str(atom.model),
            atom.chain,
            str(atom.residue),
            atom.resname,
            atom.name,
            atom.altloc,
            str(atom.serial),
            atom.element,
            f"{mass:.6f}",
            f"{atom.x:.3f}",
            f"{atom.y:.3f}",
            f"{atom.z:.3f}",
        ]
    )


def canonical_selection_rows(atoms: Sequence[base.Atom]) -> list[str]:
    return sorted(canonical_selection_row(atom) for atom in atoms)


def selection_content_packet(atoms: Sequence[base.Atom]) -> dict:
    rows = canonical_selection_rows(atoms)
    payload = "\n".join(rows).encode("utf-8")
    return {
        "schema": SELECTION_CONTENT_SCHEMA,
        "count": len(rows),
        "mass_source_doi": base.ATOMIC_MASS_DOI,
        "rows": rows,
        "payload_sha256": hashlib.sha256(payload).hexdigest(),
        "promotion_boundary": (
            "transparent selected-content payload only; row equality is direct "
            "content evidence for this canonicalisation policy, while hash equality "
            "alone is not treated as a formal equality proof or scientific authority"
        ),
    }


def same_selection_content(
    left: Sequence[base.Atom], right: Sequence[base.Atom]
) -> bool:
    return canonical_selection_rows(left) == canonical_selection_rows(right)


def packet_json(atoms: Sequence[base.Atom]) -> str:
    return json.dumps(selection_content_packet(atoms), sort_keys=True, indent=2) + "\n"
