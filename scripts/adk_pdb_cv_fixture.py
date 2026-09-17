from __future__ import annotations

from dataclasses import dataclass
import argparse
import hashlib
import json
import math
from pathlib import Path
from typing import Iterable, Sequence
from urllib.request import Request, urlopen

SCRIPT_VERSION = "0.1.0"
ARTIFACT_SCHEMA = "dashi.adk.pdb_cv_fixture.v1"
LI_LIU_JI_DOI = "10.1016/j.bpj.2015.06.059"
ATOMIC_MASS_DOI = "10.1515/pac-2019-0603"

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
    model: int = 1


def _infer_element(name: str, explicit: str) -> str:
    element = explicit.strip().upper()
    if element:
        return element
    stripped = "".join(ch for ch in name if ch.isalpha()).upper()
    if stripped.startswith("MG"):
        return "MG"
    return stripped[:1]


def parse_pdb_text(
    text: str,
    chain: str,
    altloc_policy: str = "blank-or-A",
    model: int = 1,
) -> list[Atom]:
    if altloc_policy != "blank-or-A":
        raise ValueError(f"unsupported altloc policy: {altloc_policy}")

    atoms: list[Atom] = []
    current_model = 1
    has_model_records = False

    for line_number, line in enumerate(text.splitlines(), 1):
        if line.startswith("MODEL"):
            has_model_records = True
            try:
                current_model = int(line[10:14].strip() or line.split()[1])
            except (ValueError, IndexError) as exc:
                raise ValueError(f"line {line_number}: malformed MODEL record") from exc
            continue
        if line.startswith("ENDMDL"):
            continue
        if not line.startswith(("ATOM  ", "HETATM")):
            continue

        effective_model = current_model if has_model_records else 1
        if effective_model != model:
            continue
        if len(line) < 54:
            raise ValueError(f"line {line_number}: truncated coordinate record")

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
        except ValueError as exc:
            raise ValueError(
                f"line {line_number}: malformed numeric coordinate record"
            ) from exc

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
                model=effective_model,
            )
        )

    if not atoms:
        raise ValueError(
            f"no atoms selected for model={model} chain={chain!r} "
            f"altloc_policy={altloc_policy}"
        )
    return atoms


def parse_pdb_file(
    path: Path,
    chain: str,
    altloc_policy: str = "blank-or-A",
    model: int = 1,
) -> list[Atom]:
    return parse_pdb_text(
        path.read_text(encoding="utf-8"),
        chain=chain,
        altloc_policy=altloc_policy,
        model=model,
    )


def _in_spans(residue: int, spans: Sequence[tuple[int, int]]) -> bool:
    return any(lo <= residue <= hi for lo, hi in spans)


def select_atoms(
    atoms: Iterable[Atom],
    spans: Sequence[tuple[int, int]],
    atom_policy: str,
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


def atom_manifest(atoms: Sequence[Atom]) -> dict[str, int | str]:
    rows = [
        "|".join(
            [
                str(atom.model),
                atom.chain,
                str(atom.residue),
                atom.resname,
                atom.name,
                atom.altloc,
                str(atom.serial),
                atom.element,
            ]
        )
        for atom in atoms
    ]
    payload = "\n".join(rows).encode("utf-8")
    return {
        "count": len(atoms),
        "sha256": hashlib.sha256(payload).hexdigest(),
    }


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
    a: Sequence[float],
    vertex: Sequence[float],
    c: Sequence[float],
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


def _selection(
    atoms: Sequence[Atom],
    spans: Sequence[tuple[int, int]],
    policy: str,
) -> tuple[list[Atom], tuple[float, float, float], dict[str, int | str]]:
    selected = select_atoms(atoms, spans, policy)
    return selected, center_of_mass(selected), atom_manifest(selected)


def evaluate_adk_cv(atoms: Sequence[Atom]) -> dict:
    _, lid_theta, lid_theta_manifest = _selection(atoms, THETA1_LID, "backbone")
    _, hinge, hinge_manifest = _selection(atoms, THETA1_HINGE, "backbone")
    _, core, core_manifest = _selection(atoms, THETA1_CORE, "backbone")
    _, nmp_theta, nmp_theta_manifest = _selection(atoms, THETA2_NMP, "backbone")

    _, lid_backbone, lid_backbone_manifest = _selection(atoms, DLN_LID, "backbone")
    _, nmp_backbone, nmp_backbone_manifest = _selection(atoms, DLN_NMP, "backbone")
    _, lid_heavy, lid_heavy_manifest = _selection(atoms, DLN_LID, "heavy")
    _, nmp_heavy, nmp_heavy_manifest = _selection(atoms, DLN_NMP, "heavy")

    return {
        "theta1_degrees": angle_degrees(lid_theta, hinge, core),
        "theta2_degrees": angle_degrees(nmp_theta, core, hinge),
        "dln_angstrom": {
            "domain_backbone": distance(lid_backbone, nmp_backbone),
            "domain_heavy": distance(lid_heavy, nmp_heavy),
        },
        "selection_manifests": {
            "theta1_lid_backbone": lid_theta_manifest,
            "theta_hinge_backbone": hinge_manifest,
            "theta_core_backbone": core_manifest,
            "theta2_nmp_backbone": nmp_theta_manifest,
            "dln_lid_backbone": lid_backbone_manifest,
            "dln_nmp_backbone": nmp_backbone_manifest,
            "dln_lid_heavy": lid_heavy_manifest,
            "dln_nmp_heavy": nmp_heavy_manifest,
        },
        "dln_source_atom_subset_resolved": False,
        "theta_atom_policy": "backbone",
        "dln_evaluator_conventions": ["domain_backbone", "domain_heavy"],
        "backbone_atom_names": sorted(BACKBONE),
        "mass_convention": "abridged standard atomic weights",
        "mass_source_doi": ATOMIC_MASS_DOI,
    }


def rcsb_pdb_url(pdb_id: str) -> str:
    return f"https://files.rcsb.org/download/{pdb_id.upper()}.pdb"


def download_rcsb_pdb(pdb_id: str, output: Path) -> str:
    url = rcsb_pdb_url(pdb_id)
    request = Request(url, headers={"User-Agent": "DASHI-AdK-fixture/1"})
    with urlopen(request) as response:
        payload = response.read()
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_bytes(payload)
    return url


def file_receipt(
    path: Path,
    chain: str,
    altloc_policy: str,
    model: int = 1,
    pdb_id: str | None = None,
) -> dict:
    raw = path.read_bytes()
    atoms = parse_pdb_text(
        raw.decode("utf-8"),
        chain=chain,
        altloc_policy=altloc_policy,
        model=model,
    )
    canonical_pdb_id = pdb_id.upper() if pdb_id else None
    return {
        "artifact_schema": ARTIFACT_SCHEMA,
        "script_version": SCRIPT_VERSION,
        "source_path": str(path),
        "source_sha256": hashlib.sha256(raw).hexdigest(),
        "source_byte_count": len(raw),
        "pdb_id": canonical_pdb_id,
        "pdb_deposition_doi": (
            f"10.2210/pdb{canonical_pdb_id}/pdb" if canonical_pdb_id else None
        ),
        "li_liu_ji_doi": LI_LIU_JI_DOI,
        "model": model,
        "chain": chain,
        "altloc_policy": altloc_policy,
        "selected_chain_atom_count": len(atoms),
        "cv": evaluate_adk_cv(atoms),
        "promotion_boundary": (
            "coordinate-derived executable receipt only; does not make evaluator "
            "convention source-paid, does not identify chemical microstate, "
            "force-field mechanics, kinetics, or formal proof authority"
        ),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Emit a deterministic same-object AdK PDB/CV fixture receipt."
    )
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--pdb", type=Path)
    source.add_argument("--pdb-id")
    parser.add_argument(
        "--expected-pdb-id",
        help="Attach the expected PDB identity when evaluating already-downloaded bytes.",
    )
    parser.add_argument("--model", type=int, default=1)
    parser.add_argument("--chain", required=True)
    parser.add_argument(
        "--altloc-policy",
        default="blank-or-A",
        choices=["blank-or-A"],
    )
    parser.add_argument("--download-path", type=Path)
    parser.add_argument("--output", type=Path)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    acquisition_url = None

    if args.pdb_id:
        pdb_path = args.download_path or Path(f"{args.pdb_id.upper()}.pdb")
        acquisition_url = download_rcsb_pdb(args.pdb_id, pdb_path)
        pdb_id = args.pdb_id
    else:
        pdb_path = args.pdb
        pdb_id = args.expected_pdb_id

    receipt = file_receipt(
        pdb_path,
        args.chain,
        args.altloc_policy,
        args.model,
        pdb_id,
    )
    receipt["acquisition_url"] = acquisition_url
    payload = json.dumps(receipt, sort_keys=True, indent=2) + "\n"

    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
