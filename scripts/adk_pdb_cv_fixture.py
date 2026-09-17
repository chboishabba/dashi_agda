from __future__ import annotations

from dataclasses import dataclass
import argparse
import hashlib
import json
import math
from pathlib import Path
from typing import Iterable, Sequence

MASS = {
    "H": 1.008,
    "C": 12.011,
    "N": 14.007,
    "O": 15.999,
    "P": 30.974,
    "S": 32.06,
    "MG": 24.305,
}
BACKBONE = {"N", "CA", "C", "O", "OXT"}

THETA1_LID = [(123, 155)]
THETA1_HINGE = [(161, 165)]
THETA1_CORE = [(1, 8), (79, 85), (104, 110), (190, 198)]
THETA2_NMP = [(50, 59)]
THETA2_CORE = THETA1_CORE
THETA2_HINGE = THETA1_HINGE
DLN_LID = [(122, 159)]
DLN_NMP = [(30, 59)]


@dataclass(frozen=True)
class Atom:
    serial: int
    name: str
    altloc: str
    resname: str
    chain: str
    residue: int
    x: float
    y: float
    z: float
    element: str


def _infer_element(name: str, explicit: str) -> str:
    element = explicit.strip().upper()
    if element:
        return element
    stripped = "".join(ch for ch in name if ch.isalpha()).upper()
    if stripped.startswith("MG"):
        return "MG"
    return stripped[:1]


def parse_pdb_text(text: str, chain: str, altloc_policy: str = "blank-or-A") -> list[Atom]:
    if altloc_policy != "blank-or-A":
        raise ValueError(f"unsupported altloc policy: {altloc_policy}")
    atoms: list[Atom] = []
    for line in text.splitlines():
        if not line.startswith(("ATOM  ", "HETATM")) or len(line) < 54:
            continue
        line_chain = line[21].strip()
        if line_chain != chain:
            continue
        altloc = line[16].strip()
        if altloc not in ("", "A"):
            continue
        try:
            serial = int(line[6:11])
            residue = int(line[22:26])
            x = float(line[30:38])
            y = float(line[38:46])
            z = float(line[46:54])
        except ValueError:
            continue
        name = line[12:16].strip()
        atoms.append(
            Atom(
                serial=serial,
                name=name,
                altloc=altloc,
                resname=line[17:20].strip(),
                chain=line_chain,
                residue=residue,
                x=x,
                y=y,
                z=z,
                element=_infer_element(name, line[76:78] if len(line) >= 78 else ""),
            )
        )
    return atoms


def parse_pdb_file(path: Path, chain: str, altloc_policy: str = "blank-or-A") -> list[Atom]:
    return parse_pdb_text(path.read_text(), chain=chain, altloc_policy=altloc_policy)


def _in_spans(residue: int, spans: Sequence[tuple[int, int]]) -> bool:
    return any(lo <= residue <= hi for lo, hi in spans)


def select_atoms(
    atoms: Iterable[Atom], spans: Sequence[tuple[int, int]], atom_policy: str
) -> list[Atom]:
    selected = [atom for atom in atoms if _in_spans(atom.residue, spans)]
    if atom_policy == "backbone":
        selected = [atom for atom in selected if atom.name in BACKBONE]
    elif atom_policy == "heavy":
        selected = [atom for atom in selected if atom.element != "H"]
    else:
        raise ValueError(f"unsupported atom policy: {atom_policy}")
    if not selected:
        raise ValueError(f"empty selection for spans={spans} policy={atom_policy}")
    return selected


def center_of_mass(atoms: Sequence[Atom]) -> tuple[float, float, float]:
    weighted: list[tuple[Atom, float]] = []
    for atom in atoms:
        try:
            mass = MASS[atom.element]
        except KeyError as exc:
            raise ValueError(f"no mass for element {atom.element!r}") from exc
        weighted.append((atom, mass))
    total = sum(mass for _, mass in weighted)
    if total == 0:
        raise ValueError("zero total mass")
    return tuple(
        sum(getattr(atom, axis) * mass for atom, mass in weighted) / total
        for axis in ("x", "y", "z")
    )


def distance(a: Sequence[float], b: Sequence[float]) -> float:
    return math.sqrt(sum((a[index] - b[index]) ** 2 for index in range(3)))


def angle_degrees(
    a: Sequence[float], vertex: Sequence[float], c: Sequence[float]
) -> float:
    u = [a[index] - vertex[index] for index in range(3)]
    v = [c[index] - vertex[index] for index in range(3)]
    norm_u = math.sqrt(sum(value * value for value in u))
    norm_v = math.sqrt(sum(value * value for value in v))
    if norm_u == 0 or norm_v == 0:
        raise ValueError("undefined angle for zero-length vector")
    cosine = sum(u[index] * v[index] for index in range(3)) / (norm_u * norm_v)
    cosine = max(-1.0, min(1.0, cosine))
    return math.degrees(math.acos(cosine))


def _com(
    atoms: Sequence[Atom], spans: Sequence[tuple[int, int]], policy: str = "backbone"
) -> tuple[float, float, float]:
    return center_of_mass(select_atoms(atoms, spans, policy))


def evaluate_adk_cv(atoms: Sequence[Atom]) -> dict:
    lid_theta = _com(atoms, THETA1_LID)
    hinge = _com(atoms, THETA1_HINGE)
    core = _com(atoms, THETA1_CORE)
    nmp_theta = _com(atoms, THETA2_NMP)

    lid_backbone = _com(atoms, DLN_LID, "backbone")
    nmp_backbone = _com(atoms, DLN_NMP, "backbone")
    lid_heavy = _com(atoms, DLN_LID, "heavy")
    nmp_heavy = _com(atoms, DLN_NMP, "heavy")

    return {
        "theta1_degrees": angle_degrees(lid_theta, hinge, core),
        "theta2_degrees": angle_degrees(nmp_theta, core, hinge),
        "dln_angstrom": {
            "domain_backbone": distance(lid_backbone, nmp_backbone),
            "domain_heavy": distance(lid_heavy, nmp_heavy),
        },
        "dln_source_atom_subset_resolved": False,
        "theta_atom_policy": "backbone",
        "dln_evaluator_conventions": ["domain_backbone", "domain_heavy"],
        "mass_convention": "abridged standard atomic weights; see DASHI attributed mass owner",
    }


def file_receipt(path: Path, chain: str, altloc_policy: str) -> dict:
    raw = path.read_bytes()
    atoms = parse_pdb_text(raw.decode("utf-8"), chain=chain, altloc_policy=altloc_policy)
    return {
        "path": str(path),
        "sha256": hashlib.sha256(raw).hexdigest(),
        "byte_count": len(raw),
        "chain": chain,
        "altloc_policy": altloc_policy,
        "selected_atom_count": len(atoms),
        "cv": evaluate_adk_cv(atoms),
    }


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Emit a deterministic same-object AdK PDB/CV fixture receipt."
    )
    parser.add_argument("pdb", type=Path)
    parser.add_argument("--chain", required=True)
    parser.add_argument(
        "--altloc-policy", default="blank-or-A", choices=["blank-or-A"]
    )
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    payload = json.dumps(
        file_receipt(args.pdb, args.chain, args.altloc_policy),
        sort_keys=True,
        indent=2,
    ) + "\n"
    if args.output:
        args.output.write_text(payload)
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
