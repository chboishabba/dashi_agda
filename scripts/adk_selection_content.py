from __future__ import annotations

import hashlib
import json
from typing import Sequence

import adk_pdb_cv_fixture as base

SELECTION_CONTENT_SCHEMA = "dashi.adk.selection_content.v1"
THREE_CV_CONTENT_SCHEMA = "dashi.adk.three_cv_selection_content.v1"

THREE_CV_SELECTIONS = {
    "theta1_lid_backbone": (base.THETA1_LID, "backbone"),
    "theta_hinge_backbone": (base.THETA1_HINGE, "backbone"),
    "theta_core_backbone": (base.THETA1_CORE, "backbone"),
    "theta2_nmp_backbone": (base.THETA2_NMP, "backbone"),
    "dln_lid_backbone": (base.DLN_LID, "backbone"),
    "dln_nmp_backbone": (base.DLN_NMP, "backbone"),
    "dln_lid_heavy": (base.DLN_LID, "heavy"),
    "dln_nmp_heavy": (base.DLN_NMP, "heavy"),
}


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


def three_cv_content_packet(atoms: Sequence[base.Atom]) -> dict:
    selections = {}
    for name, (spans, policy) in THREE_CV_SELECTIONS.items():
        selected = base.select_atoms(atoms, spans, policy)
        selections[name] = selection_content_packet(selected)
    return {
        "schema": THREE_CV_CONTENT_SCHEMA,
        "selection_schema": SELECTION_CONTENT_SCHEMA,
        "selection_order": sorted(THREE_CV_SELECTIONS),
        "selections": selections,
        "mass_source_doi": base.ATOMIC_MASS_DOI,
        "li_liu_ji_doi": base.LI_LIU_JI_DOI,
        "dln_source_atom_subset_resolved": False,
        "promotion_boundary": (
            "exact transparent content over the evaluator's eight named selection "
            "surfaces; dLN backbone/heavy remain distinct evaluator conventions and "
            "the packet does not create source authority or canonical PDB-byte parity"
        ),
    }


def same_three_cv_content(
    left: Sequence[base.Atom], right: Sequence[base.Atom]
) -> bool:
    return three_cv_content_packet(left)["selections"] == three_cv_content_packet(right)[
        "selections"
    ]


def packet_json(atoms: Sequence[base.Atom]) -> str:
    return json.dumps(selection_content_packet(atoms), sort_keys=True, indent=2) + "\n"


def three_cv_packet_json(atoms: Sequence[base.Atom]) -> str:
    return json.dumps(three_cv_content_packet(atoms), sort_keys=True, indent=2) + "\n"
