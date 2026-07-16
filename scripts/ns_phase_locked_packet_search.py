#!/usr/bin/env python3
"""Adversarial phase search for finite NS critical-packet recurrence.

This is intentionally a *counterexample search*, not evidence for a packet
barrier.  It builds reality-symmetric, divergence-free helical networks.  The
default is a three-target cyclic feedback graph:

    lower donors -> r_i -> s_i -> r_(i+1).

The ``s_i`` modes are shared by outlet and feedback triads, so their phases
cannot independently maximize every transfer.

With ``--backend gpu`` or ``--backend cpu``, the selected candidates are then
evolved under the sibling dashiCFD finite Galerkin solver and ranked by the
actual multi-window endpoint objective.  This can falsify a proposed uniform
contraction in the tested finite family; it cannot prove a universal
Navier--Stokes theorem.
"""

from __future__ import annotations

import argparse
import ast
import copy
import importlib.util
import json
import math
import itertools
import sys
import time
from pathlib import Path
from typing import Any

import numpy as np

from ns_critical_packet_phase_residence_audit import (
    component_dealias_mask,
    dyadic_shell_packets,
    frequency_grid,
    heat_continued_packet,
    leray_project,
    reconstructed_nonlinear_rhs,
    shell_dissipation,
    shell_nonlinear_rate,
)
from ns_triad_edge_depletion_audit import helical_basis


SCRIPT_NAME = "scripts/ns_phase_locked_packet_search.py"
DEFAULT_CFD_ROOT = Path("/home/c/Documents/code/dashiCFD")
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_phase_locked_packet_search_N32_20260716.json"
)

ROLE_TRANSFER_ROLES = ("target", "donor", "outlet", "feedback")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=32)
    parser.add_argument("--nu", type=float, default=1.0e-3)
    parser.add_argument("--dt", type=float, default=1.0e-3)
    parser.add_argument("--target-shell", type=int, default=2)
    parser.add_argument("--window-c", type=float, default=1.0)
    parser.add_argument("--windows", type=int, default=2,
                        help="complete viscous windows in the endpoint objective")
    parser.add_argument("--topology", choices=("cyclic-feedback", "donor-star"),
                        default="cyclic-feedback")
    parser.add_argument("--phase-samples", type=int, default=256)
    parser.add_argument("--phase-sample-index", type=int, default=None,
                        help=("evaluate exactly this deterministic sample from the --seed phase stream; "
                              "useful for externally staged endpoint screens"))
    parser.add_argument("--seed", type=int, default=20260716)
    parser.add_argument("--target-amplitude", type=float, default=3.0)
    parser.add_argument("--donor-amplitude", type=float, default=1.0)
    parser.add_argument("--feedback-amplitude", type=float, default=1.0)
    parser.add_argument("--outlet-amplitude", type=float, default=None,
                        help="raw upper-outlet-side amplitude; defaults to --feedback-amplitude")
    parser.add_argument("--role-shares", default=None,
                        help="critical-mass shares target,donor,outlet,feedback; four positive comma-separated numbers")
    parser.add_argument("--target-dominance-min", type=float, default=0.0,
                        help="reject sampled candidates below this initial target-packet dominance")
    parser.add_argument("--local-tightness-min", type=float, default=0.0,
                        help="reject sampled candidates below this initial local packet tightness")
    parser.add_argument("--role-share-min", type=float, default=0.0,
                        help="reject sampled candidates if any active role falls below this realised critical-mass share")
    parser.add_argument("--normalization", choices=("critical", "urms"), default="critical",
                        help="fix total finite H^(1/2) packet mass or physical-space urms")
    parser.add_argument("--critical-mass", type=float, default=1.0,
                        help="sum_j X_j imposed when --normalization critical")
    parser.add_argument("--target-urms", type=float, default=1.0)
    parser.add_argument("--top-candidates", type=int, default=1)
    parser.add_argument("--endpoint-prefilter-candidates", type=int, default=0,
                        help="number of static seeds to rank by a short evolved moving-packet objective")
    parser.add_argument("--endpoint-prefilter-window-c", type=float, default=0.0,
                        help="short viscous-window factor for endpoint preselection; zero disables it")
    parser.add_argument("--moving-packet-radius", type=int, default=1,
                        help="half-width L of the dynamically centred critical packet")
    parser.add_argument("--helicity-static-audit", action="store_true",
                        help="enumerate the reduced pure-mode-helicity factor tables; no CFD evolution")
    parser.add_argument("--helicity-static-case", type=int, default=None,
                        help="use this rank from the 64-case static audit, with each private block's top envelope choice")
    parser.add_argument("--backend", choices=("none", "cpu", "gpu"), default="none")
    parser.add_argument("--fft-backend", default="vkfft-vulkan")
    parser.add_argument("--save-every", type=int, default=100)
    parser.add_argument("--cfd-root", type=Path, default=DEFAULT_CFD_ROOT)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT)
    return parser.parse_args()


def authority() -> dict[str, bool]:
    return {
        "candidate_only": True,
        "empirical_non_promoting": True,
        "theorem_authority": False,
        "clay_authority": False,
        "promoted": False,
    }


def mode_index(mode: tuple[int, int, int], n: int) -> tuple[int, int, int]:
    """Physical mode ``(kx, ky, kz)`` to archive array order ``(z, y, x)``."""
    kx, ky, kz = mode
    return kz % n, ky % n, kx % n


def negate(mode: tuple[int, int, int]) -> tuple[int, int, int]:
    return tuple(-value for value in mode)


def donor_star_modes() -> tuple[tuple[int, int, int], list[tuple[int, int, int]]]:
    """A shared-target adjacent-shell donor star, all within N32 2/3 support."""
    target = (-8, 0, 0)
    donors = [(4, 3, 0), (4, 0, 3), (4, 3, 3), (4, 2, 4)]
    return target, donors


def network_spec(args: argparse.Namespace) -> dict[str, Any]:
    """Return an explicit finite graph in physical wavevector coordinates.

    The feedback graph is placed at ``N=32, j=2``.  Its targets have size
    four; the shared outlet/feedback modes have size above eight, while every
    coordinate remains in the componentwise 2/3-dealiased carrier.
    """
    if args.topology == "donor-star":
        target, donors = donor_star_modes()
        entries: list[dict[str, Any]] = [{
            "mode": target, "amplitude": args.target_amplitude, "helicity": 1,
            "fixed_phase": 0.0, "role": "target",
        }]
        triads: list[dict[str, Any]] = []
        for index, donor in enumerate(donors):
            partner = tuple(-target[axis] - donor[axis] for axis in range(3))
            entries.extend((
                {"mode": donor, "amplitude": args.donor_amplitude, "helicity": 1,
                 "role": f"donor-{index}"},
                {"mode": partner, "amplitude": args.donor_amplitude, "helicity": -1,
                 "role": f"donor-partner-{index}"},
            ))
            triads.append({"kind": "lower-donor", "modes": [donor, partner, target]})
        return {"kind": "shared-target adjacent-shell donor star", "targets": [target],
                "entries": entries, "triads": triads}

    targets = [(4, 0, 0), (0, 4, 0), (0, 0, 4)]
    donors = [
        [(-2, 1, 0), (-2, -1, 0)],
        [(1, -2, 0), (-1, -2, 0)],
        [(1, 0, -2), (-1, 0, -2)],
    ]
    # r_i + a_i + s_i = 0 and s_i + b_i + r_(i+1) = 0, cyclically.
    feedback = [
        {"a": (-10, -6, 0), "s": (6, 6, 0), "b": (-6, -10, 0)},
        {"a": (0, -10, -6), "s": (0, 6, 6), "b": (0, -6, -10)},
        {"a": (-6, 0, -10), "s": (6, 0, 6), "b": (-10, 0, -6)},
    ]
    outlet_amplitude = args.feedback_amplitude if args.outlet_amplitude is None else args.outlet_amplitude
    entries: list[dict[str, Any]] = [
        {"mode": target, "amplitude": args.target_amplitude, "helicity": 1,
         "fixed_phase": 0.0, "role": f"target-{index}"}
        for index, target in enumerate(targets)
    ]
    triads: list[dict[str, Any]] = []
    for index, (target, pair, link) in enumerate(zip(targets, donors, feedback, strict=True)):
        for local, mode in enumerate(pair):
            entries.append({"mode": mode, "amplitude": args.donor_amplitude,
                            "helicity": 1 if local == 0 else -1,
                            "role": f"donor-{index}-{local}"})
        entries.extend((
            {"mode": link["a"], "amplitude": outlet_amplitude, "helicity": -1,
             "role": f"outlet-side-{index}"},
            {"mode": link["s"], "amplitude": args.feedback_amplitude, "helicity": 1,
             "role": f"shared-outlet-{index}"},
            {"mode": link["b"], "amplitude": args.feedback_amplitude, "helicity": -1,
             "role": f"feedback-{index}"},
        ))
        triads.extend((
            {"kind": "lower-donor", "modes": [pair[0], pair[1], target]},
            {"kind": "upper-outlet", "modes": [target, link["a"], link["s"]]},
            {"kind": "feedback", "modes": [link["s"], link["b"], targets[(index + 1) % len(targets)]]},
        ))
    return {"kind": "three-target cyclic outlet-feedback graph", "targets": targets,
            "entries": entries, "triads": triads}


def validate_network(args: argparse.Namespace, network: dict[str, Any]) -> None:
    if args.n != 32:
        raise ValueError("the explicit experimental networks are currently calibrated only for N32")
    expected_shell = 3 if args.topology == "donor-star" else 2
    if args.target_shell != expected_shell:
        raise ValueError(f"{args.topology} requires --target-shell {expected_shell}")
    cutoff = args.n / 3.0
    for entry in network["entries"]:
        if max(abs(value) for value in entry["mode"]) > cutoff:
            raise ValueError(f"network mode escapes 2/3 carrier: {entry['mode']!r}")
    for triad in network["triads"]:
        total = tuple(sum(mode[axis] for mode in triad["modes"]) for axis in range(3))
        if total != (0, 0, 0):
            raise ValueError(f"invalid zero-sum network triad: {triad!r}")


def phase_graph_geometry(network: dict[str, Any]) -> dict[str, Any]:
    """Finite triad/mode incidence geometry of the designed feedback graph.

    This is deliberately only the combinatorial phase graph.  The physical
    channel offsets ``beta_e`` and their holonomies must be extracted from the
    exact helical interaction coefficients; a graph cycle alone is not a
    helical-frustration certificate.
    """
    modes = sorted({tuple(mode) for triad in network["triads"] for mode in triad["modes"]})
    mode_columns = {mode: index for index, mode in enumerate(modes)}
    incidence = np.zeros((len(network["triads"]), len(modes)), dtype=np.int64)
    nodes = [f"mode:{mode}" for mode in modes] + [f"triad:{index}" for index in range(len(network["triads"]))]
    parent = {node: node for node in nodes}

    def find(node: str) -> str:
        while parent[node] != node:
            parent[node] = parent[parent[node]]
            node = parent[node]
        return node

    tree_adjacency: dict[str, list[str]] = {node: [] for node in nodes}
    cycles: list[list[str]] = []

    def tree_path(start: str, goal: str) -> list[str]:
        frontier = [start]
        predecessor: dict[str, str | None] = {start: None}
        for node in frontier:
            if node == goal:
                break
            for neighbor in tree_adjacency[node]:
                if neighbor not in predecessor:
                    predecessor[neighbor] = node
                    frontier.append(neighbor)
        path = [goal]
        while path[-1] != start:
            previous = predecessor.get(path[-1])
            if previous is None:
                raise RuntimeError("cycle edge did not have a spanning-tree path")
            path.append(previous)
        return list(reversed(path))

    edge_count = 0
    for triad_index, triad in enumerate(network["triads"]):
        triad_node = f"triad:{triad_index}"
        for mode in triad["modes"]:
            mode = tuple(mode)
            incidence[triad_index, mode_columns[mode]] = 1
            mode_node = f"mode:{mode}"
            edge_count += 1
            left, right = find(triad_node), find(mode_node)
            if left != right:
                parent[left] = right
                tree_adjacency[triad_node].append(mode_node)
                tree_adjacency[mode_node].append(triad_node)
            else:
                cycles.append(tree_path(triad_node, mode_node) + [triad_node])
    component_count = len({find(node) for node in nodes})
    return {
        "mode_order": [list(mode) for mode in modes],
        "triad_mode_incidence_matrix": incidence.tolist(),
        "triad_mode_incidence_rank": int(np.linalg.matrix_rank(incidence.astype(np.float64))),
        "bipartite_vertex_count": len(nodes),
        "bipartite_edge_count": edge_count,
        "bipartite_component_count": component_count,
        "cycle_space_dimension": edge_count - len(nodes) + component_count,
        "cycle_basis": cycles,
        "helical_coupling_holonomy": {
            "status": "not_yet_computed",
            "reason": "requires exact complex helical-channel coefficients, not only triad/mode topology",
        },
    }


def signed_phase_constraint_geometry(network: dict[str, Any]) -> dict[str, Any]:
    """Audit whether this graph can impose a static phase-holonomy constraint.

    A selected helical channel has phase ``-phi_out + phi_left + phi_right
    + beta``.  In reality-reduced coordinates, with the first labelled triad
    mode used as output, ``phi(-p)=-phi(p)`` makes the coefficient row
    ``phi(p)+phi(q)+phi(r)``.  A topology-only holonomy requires a nontrivial
    left kernel of this row matrix.  Exact channel offsets beta are deliberately
    outside this structural audit.
    """
    modes = sorted({tuple(mode) for triad in network["triads"] for mode in triad["modes"]})
    mode_columns = {mode: index for index, mode in enumerate(modes)}
    rows = np.zeros((len(network["triads"]), len(modes)), dtype=np.int64)
    degrees = {mode: 0 for mode in modes}
    for triad_index, triad in enumerate(network["triads"]):
        for mode in triad["modes"]:
            mode = tuple(mode)
            rows[triad_index, mode_columns[mode]] += 1
            degrees[mode] += 1

    private_by_triad = [
        [tuple(mode) for mode in triad["modes"] if degrees[tuple(mode)] == 1]
        for triad in network["triads"]
    ]
    # A distinct private mode in every row supplies a diagonal nonzero minor.
    # This is an exact full-row-rank certificate for the present topology.
    private_elimination = all(private_by_triad)
    rank = len(network["triads"]) if private_elimination else int(
        np.linalg.matrix_rank(rows.astype(np.float64))
    )
    left_kernel_dimension = len(network["triads"]) - rank
    backbone = [mode for mode in modes if degrees[mode] > 1]
    leaves = [mode for mode in modes if degrees[mode] == 1]
    return {
        "coordinate_convention": (
            "reality-reduced phases: canonical labelled channel row is "
            "phi(p)+phi(q)+phi(r) after phi(-p)=-phi(p)"
        ),
        "mode_order": [list(mode) for mode in modes],
        "signed_phase_constraint_matrix": rows.tolist(),
        "constraint_count": len(network["triads"]),
        "mode_count": len(modes),
        "constraint_rank": rank,
        "left_kernel_dimension": left_kernel_dimension,
        "private_modes_by_triad": [[list(mode) for mode in row] for row in private_by_triad],
        "private_column_elimination_certificate": private_elimination,
        "shared_backbone_modes": [list(mode) for mode in backbone],
        "private_leaf_modes": [list(mode) for mode in leaves],
        "static_holonomy_conclusion": (
            "no topology-forced phase holonomy: every constraint has a private "
            "phase variable, so the rows are independent"
            if left_kernel_dimension == 0 else
            "a topology-level left kernel exists; select physical channels and "
            "their beta offsets before interpreting it as holonomy"
        ),
        "warning": (
            "This does not rule out dynamical relocking. It only rules out a "
            "static phase-frustration theorem from this graph alone."
        ),
    }


def helicity_factorisation_geometry(network: dict[str, Any]) -> dict[str, Any]:
    """Expose the pure-helicity search reduction implied by graph sharing."""
    degrees: dict[tuple[int, int, int], int] = {}
    for triad in network["triads"]:
        for mode in triad["modes"]:
            mode = tuple(mode)
            degrees[mode] = degrees.get(mode, 0) + 1
    backbone = sorted(mode for mode, degree in degrees.items() if degree > 1)
    blocks: list[dict[str, Any]] = []
    for triad_index, triad in enumerate(network["triads"]):
        leaves = [tuple(mode) for mode in triad["modes"] if degrees[tuple(mode)] == 1]
        blocks.append({
            "triad": triad_index,
            "kind": triad["kind"],
            "private_leaf_modes": [list(mode) for mode in leaves],
            "conditional_sign_choices": 2 ** len(leaves),
        })
    return {
        "pure_mode_helicity_model": "one sign per represented mode; reality fixes the negative partner",
        "backbone_modes": [list(mode) for mode in backbone],
        "backbone_assignment_count": 2 ** len(backbone),
        "full_assignment_count": 2 ** len(degrees),
        "local_leaf_blocks": blocks,
        "elimination_note": (
            "For each backbone assignment retain local Pareto alternatives over "
            "coupling magnitude, channel phase, desired-leg transfer sign, and "
            "helicity metadata; do not eliminate a leaf solely by magnitude."
        ),
        "global_helicity_flip": "not quotiented until endpoint-objective invariance is verified",
    }


def pure_helical_channel_coefficient(
    left: tuple[int, int, int], right: tuple[int, int, int], output_mode: tuple[int, int, int],
    left_sign: int, right_sign: int, output_sign: int,
) -> complex:
    """Geometric coefficient for one reality-compatible pure-helicity channel.

    ``output_mode`` is the represented positive/labelled mode.  The Fourier
    energy test mode is its negative, whose vector is the conjugate of the
    represented helical vector under the construction used by this script.
    Amplitude and modal phase factors are intentionally excluded.
    """
    left_vector = helical_basis(left)[0 if left_sign > 0 else 1]
    right_vector = helical_basis(right)[0 if right_sign > 0 else 1]
    output_vector = np.conjugate(helical_basis(output_mode)[0 if output_sign > 0 else 1])
    out = -np.asarray(output_mode, dtype=np.float64)
    left_k = np.asarray(left, dtype=np.float64)
    right_k = np.asarray(right, dtype=np.float64)
    nonlinear = 1j * (
        np.dot(right_k, left_vector) * right_vector
        + np.dot(left_k, right_vector) * left_vector
    )
    projected = nonlinear - out * np.dot(out, nonlinear) / np.dot(out, out)
    return complex(np.vdot(output_vector, projected))


def helicity_static_factor_audit(network: dict[str, Any]) -> dict[str, Any]:
    """Enumerate the 64 shared-mode sign cases and their local leaf factors.

    This is deliberately an envelope/compatibility audit.  It does not assert
    that independently optimal local channel phases are dynamically reachable.
    """
    entry_by_mode = {tuple(entry["mode"]): entry for entry in network["entries"]}
    degrees: dict[tuple[int, int, int], int] = {}
    for triad in network["triads"]:
        for mode in triad["modes"]:
            mode = tuple(mode)
            degrees[mode] = degrees.get(mode, 0) + 1
    backbone = sorted(mode for mode, degree in degrees.items() if degree > 1)
    default_signs = {mode: int(entry["helicity"]) for mode, entry in entry_by_mode.items()}
    desired = {"lower-donor": "feed-target", "upper-outlet": "avoid-target-loss", "feedback": "feed-next-target"}
    cases: list[dict[str, Any]] = []
    for backbone_values in itertools.product((-1, 1), repeat=len(backbone)):
        signs = dict(zip(backbone, backbone_values, strict=True))
        factors: list[dict[str, Any]] = []
        best_envelope = 0.0
        for triad_index, triad in enumerate(network["triads"]):
            left, right, output = (tuple(mode) for mode in triad["modes"])
            leaves = [mode for mode in (left, right, output) if degrees[mode] == 1]
            choices: list[dict[str, Any]] = []
            for leaf_values in itertools.product((-1, 1), repeat=len(leaves)):
                trial = signs | dict(zip(leaves, leaf_values, strict=True))
                coefficient = pure_helical_channel_coefficient(
                    left, right, output, trial[left], trial[right], trial[output]
                )
                amplitude_product = float(np.prod([entry_by_mode[mode]["amplitude"] for mode in (left, right, output)]))
                envelope = amplitude_product * abs(coefficient)
                choices.append({
                    "leaf_signs": {str(mode): trial[mode] for mode in leaves},
                    "helicity_triple": [trial[left], trial[right], trial[output]],
                    "coupling_magnitude": float(abs(coefficient)),
                    "coupling_phase": wrap_phase(float(np.angle(coefficient))),
                    "amplitude_weighted_envelope": envelope,
                })
            choices.sort(key=lambda row: float(row["amplitude_weighted_envelope"]), reverse=True)
            best_envelope += float(choices[0]["amplitude_weighted_envelope"])
            factors.append({
                "triad": triad_index,
                "kind": triad["kind"],
                "desired_transfer_role": desired[triad["kind"]],
                "local_leaf_modes": [list(mode) for mode in leaves],
                "choices": choices,
            })
        cases.append({
            "backbone_signs": {str(mode): signs[mode] for mode in backbone},
            "independently_maximized_envelope_sum": best_envelope,
            "local_factors": factors,
        })
    cases.sort(key=lambda row: float(row["independently_maximized_envelope_sum"]), reverse=True)
    return {
        "status": "static_geometric_factor_audit_only",
        "backbone_mode_count": len(backbone),
        "backbone_assignment_count": len(cases),
        "default_mode_signs": {str(mode): sign for mode, sign in default_signs.items()},
        "cases_ranked_by_independently_maximized_envelope_sum": cases,
        "warning": (
            "The ranking is an upper-envelope screen, not a phase optimization or "
            "an endpoint prediction. Local choices retain coupling phase because "
            "maximal magnitude alone can destroy network compatibility."
        ),
    }


def role_name(entry: dict[str, Any]) -> str:
    """Four physical allocation roles used by the endpoint search."""
    role = str(entry["role"])
    if role.startswith("target"):
        return "target"
    if role.startswith("donor"):
        return "donor"
    if role.startswith("outlet-side") or role.startswith("shared-outlet"):
        return "outlet"
    if role.startswith("feedback"):
        return "feedback"
    raise ValueError(f"unrecognised allocation role: {role!r}")


def role_by_reality_mode(network: dict[str, Any]) -> dict[tuple[int, int, int], str]:
    """Label both members of every designed reality pair by its allocation role."""
    labels: dict[tuple[int, int, int], str] = {}
    for entry in network["entries"]:
        role = role_name(entry)
        for mode in (tuple(entry["mode"]), negate(tuple(entry["mode"]))):
            previous = labels.get(mode)
            if previous is not None and previous != role:
                raise RuntimeError(f"designed mode {mode!r} belongs to incompatible roles")
            labels[mode] = role
    return labels


def parse_role_shares(text: str | None) -> dict[str, float] | None:
    if text is None:
        return None
    values = [float(value.strip()) for value in text.split(",")]
    names = ("target", "donor", "outlet", "feedback")
    if len(values) != len(names) or any(value <= 0.0 for value in values):
        raise ValueError("--role-shares requires four positive values: target,donor,outlet,feedback")
    total = float(sum(values))
    return {name: value / total for name, value in zip(names, values, strict=True)}


def dyadic_weight(mode: tuple[int, int, int]) -> float:
    magnitude = float(np.linalg.norm(np.asarray(mode, dtype=np.float64)))
    if magnitude <= 0.0:
        raise ValueError("the finite network must not contain the zero mode")
    return float(2 ** int(math.floor(math.log2(magnitude))))


def apply_role_mass_shares(network: dict[str, Any], requested: dict[str, float] | None) -> dict[str, Any]:
    """Rescale entries so the raw finite dyadic mass has the requested role shares.

    The final carrier is still normalized with ``normalise_critical_mass``.
    This construction uses the same dyadic shell weight as the packet ledger,
    rather than a handwritten conjugate-pair factor; realised shares are also
    emitted later as a check on the finite FFT convention.
    """
    if requested is None:
        return {"requested": None, "applied": False}
    by_role = {name: 0.0 for name in requested}
    for entry in network["entries"]:
        by_role[role_name(entry)] += dyadic_weight(tuple(entry["mode"])) * float(entry["amplitude"]) ** 2
    if any(value <= 0.0 for value in by_role.values()):
        raise ValueError("each requested allocation role must have nonzero raw support")
    for entry in network["entries"]:
        role = role_name(entry)
        entry["amplitude"] *= math.sqrt(requested[role] / by_role[role])
    return {
        "requested": requested,
        "applied": True,
        "pre_normalisation_role_weights": by_role,
        "construction": "role weights use the packet ledger's dyadic shell factor; final shares are recomputed from the finite carrier",
    }


def static_helicity_case_assignment(
    network: dict[str, Any], audit: dict[str, Any], rank: int,
) -> dict[str, Any]:
    """Apply one ranked backbone case and its local envelope-maximising leaves.

    This is only a deterministic seed constructor.  It deliberately does not
    collapse the audit's stored local Pareto alternatives into a theorem about
    phase compatibility or endpoint recurrence.
    """
    cases = audit["cases_ranked_by_independently_maximized_envelope_sum"]
    if rank < 0 or rank >= len(cases):
        raise ValueError(f"--helicity-static-case must be in [0, {len(cases) - 1}]")
    case = cases[rank]
    signs = {tuple(ast.literal_eval(mode)): int(sign) for mode, sign in case["backbone_signs"].items()}
    selected_factors: list[dict[str, Any]] = []
    for factor in case["local_factors"]:
        choice = factor["choices"][0]
        for mode, sign in choice["leaf_signs"].items():
            parsed = tuple(ast.literal_eval(mode))
            previous = signs.get(parsed)
            if previous is not None and previous != int(sign):
                raise RuntimeError("a purported private leaf received incompatible static signs")
            signs[parsed] = int(sign)
        selected_factors.append({
            "triad": factor["triad"],
            "kind": factor["kind"],
            "desired_transfer_role": factor["desired_transfer_role"],
            "selected_leaf_choice": choice,
        })
    for entry in network["entries"]:
        mode = tuple(entry["mode"])
        if mode not in signs:
            raise RuntimeError(f"static helicity construction omitted mode {mode!r}")
        entry["helicity"] = signs[mode]
    return {
        "rank": rank,
        "backbone_signs": case["backbone_signs"],
        "full_mode_signs": {str(mode): sign for mode, sign in sorted(signs.items())},
        "independently_maximized_envelope_sum": case["independently_maximized_envelope_sum"],
        "selected_local_envelope_choices": selected_factors,
        "warning": (
            "private leaves use each factor's largest-envelope alternative only; "
            "this is a reproducible seed, not a joint phase/share optimisation"
        ),
    }


def wrap_phase(angle: float) -> float:
    return float((angle + math.pi) % (2.0 * math.pi) - math.pi)


def helical_scalar(field_hat: np.ndarray, mode: tuple[int, int, int], sign: int) -> complex:
    basis = helical_basis(mode)[0 if sign > 0 else 1]
    return complex(np.vdot(basis, field_hat[(slice(None),) + mode_index(mode, field_hat.shape[1])]))


def channel_complex_contribution(
    field_hat: np.ndarray,
    out: tuple[int, int, int], left: tuple[int, int, int], right: tuple[int, int, int],
    out_sign: int, left_sign: int, right_sign: int,
) -> tuple[complex, complex, complex, complex]:
    """One exact complex helical term before taking its real energy part."""
    out_basis = helical_basis(out)[0 if out_sign > 0 else 1]
    left_basis = helical_basis(left)[0 if left_sign > 0 else 1]
    right_basis = helical_basis(right)[0 if right_sign > 0 else 1]
    out_scalar = helical_scalar(field_hat, out, out_sign)
    left_scalar = helical_scalar(field_hat, left, left_sign)
    right_scalar = helical_scalar(field_hat, right, right_sign)
    out_vector = out_scalar * out_basis
    left_vector = left_scalar * left_basis
    right_vector = right_scalar * right_basis
    out_k = np.asarray(out, dtype=np.float64)
    left_k = np.asarray(left, dtype=np.float64)
    right_k = np.asarray(right, dtype=np.float64)
    nonlinear = 1j * (
        np.dot(right_k, left_vector) * right_vector
        + np.dot(left_k, right_vector) * left_vector
    )
    projected = nonlinear - out_k * np.dot(out_k, nonlinear) / np.dot(out_k, out_k)
    return complex(np.vdot(out_vector, projected)), out_scalar, left_scalar, right_scalar


def static_modal_transfer(
    field_hat: np.ndarray, out: tuple[int, int, int], left: tuple[int, int, int], right: tuple[int, int, int],
) -> float:
    out_k = np.asarray(out, dtype=np.float64)
    left_k = np.asarray(left, dtype=np.float64)
    right_k = np.asarray(right, dtype=np.float64)
    left_vector = field_hat[(slice(None),) + mode_index(left, field_hat.shape[1])]
    right_vector = field_hat[(slice(None),) + mode_index(right, field_hat.shape[1])]
    out_vector = field_hat[(slice(None),) + mode_index(out, field_hat.shape[1])]
    nonlinear = 1j * (
        np.dot(right_k, left_vector) * right_vector
        + np.dot(left_k, right_vector) * left_vector
    )
    projected = nonlinear - out_k * np.dot(out_k, nonlinear) / np.dot(out_k, out_k)
    return -float(np.real(np.vdot(out_vector, projected)))


def designed_role_transfer_rate(field_hat: np.ndarray, network: dict[str, Any]) -> dict[str, Any]:
    """Conservative role-to-role ledger for the nine *designed* triads.

    A triad fixes only its three modal energy changes, not a unique pairwise
    donor allocation.  For each triad we therefore distribute a negative modal
    change to positive modal changes proportionally to the latter.  This gives
    an exact conservative transport ledger at the modal-transfer level while
    making the convention explicit.  It intentionally excludes all triads
    generated outside the designed network; support leakage and the full
    shell transfer remain separate telemetry.
    """
    roles = ROLE_TRANSFER_ROLES
    labels = role_by_reality_mode(network)
    matrix = {source: {target: 0.0 for target in roles} for source in roles}
    modal_net = {role: 0.0 for role in roles}
    triad_rows: list[dict[str, Any]] = []
    max_conservation_residual = 0.0
    for triad_index, triad in enumerate(network["triads"]):
        p, q, r = (tuple(mode) for mode in triad["modes"])
        modes = (p, q, r)
        # For p + q + r = 0, energy in the labelled p mode is tested at -p.
        transfers = np.asarray((
            static_modal_transfer(field_hat, negate(p), q, r),
            static_modal_transfer(field_hat, negate(q), r, p),
            static_modal_transfer(field_hat, negate(r), p, q),
        ), dtype=np.float64)
        triad_roles = tuple(labels[mode] for mode in modes)
        residual = float(np.sum(transfers))
        max_conservation_residual = max(max_conservation_residual, abs(residual))
        for role, transfer in zip(triad_roles, transfers, strict=True):
            modal_net[role] += float(transfer)
        gains = [(index, float(value)) for index, value in enumerate(transfers) if value > 0.0]
        losses = [(index, float(-value)) for index, value in enumerate(transfers) if value < 0.0]
        gain_total = float(sum(value for _, value in gains))
        loss_total = float(sum(value for _, value in losses))
        # Numerical residuals are retained rather than silently normalised.
        if gain_total > 0.0 and loss_total > 0.0:
            for donor_index, loss in losses:
                for receiver_index, gain in gains:
                    matrix[triad_roles[donor_index]][triad_roles[receiver_index]] += loss * gain / gain_total
        triad_rows.append({
            "triad": triad_index,
            "kind": triad["kind"],
            "modes": [list(mode) for mode in modes],
            "roles": list(triad_roles),
            "modal_transfers": [float(value) for value in transfers],
            "conservation_residual": residual,
            "positive_transfer": gain_total,
            "negative_transfer": loss_total,
        })
    return {
        "contract": (
            "designed-triad-only conservative donor-to-receiver allocation; "
            "losses are distributed to positive modal gains in proportion to gain"
        ),
        "roles": list(roles),
        "rate_matrix": matrix,
        "modal_net_rate_by_role": modal_net,
        "triad_rows": triad_rows,
        "max_triad_conservation_residual": max_conservation_residual,
    }


def integrated_role_transfer_ledger(history: list[dict[str, Any]]) -> dict[str, Any]:
    """Integrate gross designed-triad throughput over saved solver states.

    ``rate_matrix`` is nonnegative by construction: each instantaneous modal
    loss is allocated to the triad's positive modal gains.  Its integral is
    therefore a gross directed throughput, rather than a signed net role
    balance.  The latter remains available separately as ``modal_net``.
    """
    roles = ROLE_TRANSFER_ROLES
    if len(history) < 2:
        return {"status": "insufficient_checkpoints", "roles": list(roles)}
    times = np.asarray([row["time"] for row in history], dtype=np.float64)
    matrix = {source: {target: 0.0 for target in roles} for source in roles}
    modal_net = {role: 0.0 for role in roles}
    for source in roles:
        for target in roles:
            values = np.asarray([
                row["designed_role_transfer_ledger"]["rate_matrix"][source][target]
                for row in history
            ], dtype=np.float64)
            matrix[source][target] = float(np.trapezoid(values, times))
    for role in roles:
        values = np.asarray([
            row["designed_role_transfer_ledger"]["modal_net_rate_by_role"][role]
            for row in history
        ], dtype=np.float64)
        modal_net[role] = float(np.trapezoid(values, times))
    designed_target_rate = np.asarray([
        row["designed_role_transfer_ledger"]["modal_net_rate_by_role"]["target"]
        for row in history
    ], dtype=np.float64)
    full_target_rate = np.asarray([row["target_nonlinear_rate"] for row in history], dtype=np.float64)
    designed_target_absolute_activity = float(np.trapezoid(np.abs(designed_target_rate), times))
    full_target_absolute_activity = float(np.trapezoid(np.abs(full_target_rate), times))
    target_to_outlet = matrix["target"]["outlet"]
    outlet_to_feedback = matrix["outlet"]["feedback"]
    feedback_to_target = matrix["feedback"]["target"]
    intended_stages = (target_to_outlet, outlet_to_feedback, feedback_to_target)
    intended_max = max(intended_stages)
    intended_min = min(intended_stages)
    loop_ratio = feedback_to_target / target_to_outlet if target_to_outlet > 1.0e-30 else math.nan
    closure_fraction = (
        feedback_to_target / (feedback_to_target + target_to_outlet)
        if feedback_to_target + target_to_outlet > 1.0e-30 else math.nan
    )
    return {
        "contract": (
            "time integral of nonnegative designed-triad-only donor-to-receiver "
            "throughput; not a full convolution source attribution"
        ),
        "roles": list(roles),
        "integrated_matrix": matrix,
        "integrated_modal_net_by_role": modal_net,
        "feedback_to_target_over_target_to_outlet": loop_ratio,
        "feedback_loop_closure_fraction": closure_fraction,
        "intended_loop_balance": intended_min / intended_max if intended_max > 1.0e-30 else math.nan,
        "integrated_feedback_to_target": feedback_to_target,
        "integrated_target_to_outlet": target_to_outlet,
        "integrated_outlet_to_feedback": outlet_to_feedback,
        "intended_loop_stages": {
            "target_to_outlet": target_to_outlet,
            "outlet_to_feedback": outlet_to_feedback,
            "feedback_to_target": feedback_to_target,
        },
        "target_dynamics_capture": {
            "contract": (
                "absolute target-shell nonlinear activity captured by the nine designed triads; "
                "this is separate from the internally conservative designed-triad residual"
            ),
            "designed_target_absolute_activity": designed_target_absolute_activity,
            "full_target_absolute_activity": full_target_absolute_activity,
            "designed_over_full_absolute_activity": (
                designed_target_absolute_activity / full_target_absolute_activity
                if full_target_absolute_activity > 1.0e-30 else math.nan
            ),
        },
        "max_checkpoint_conservation_residual": max(
            float(row["designed_role_transfer_ledger"]["max_triad_conservation_residual"])
            for row in history
        ),
    }


def role_transfer_checkpoint_telemetry(
    history: list[dict[str, Any]], window_steps: int,
) -> list[dict[str, Any]]:
    """Prefix ledgers at each complete viscous-window checkpoint.

    Designed-triad conservation is expected to remain at roundoff even when
    the PDE populates unplanned modes.  The capture statistic, not that
    residual, detects when the intended graph stops describing the full
    target-shell nonlinear dynamics.
    """
    checkpoints: list[dict[str, Any]] = []
    for index, row in enumerate(history):
        # Quarter-window prefixes expose whether an apparent endpoint loop
        # closure was sustained or merely a transient burst.  ``window_steps``
        # is chosen by ceiling, so use an exact integer divisibility test and
        # omit fractional points only if the time grid cannot represent them.
        if index == 0 or (4 * int(row["step"])) % window_steps != 0:
            continue
        prefix = history[:index + 1]
        ledger = integrated_role_transfer_ledger(prefix)
        checkpoints.append({
            "step": int(row["step"]),
            "time": float(row["time"]),
            "designed_role_transfer": ledger,
        })
    return checkpoints


def helical_channel_phase_audit(field_hat: np.ndarray, network: dict[str, Any]) -> dict[str, Any]:
    """Expose the actual channel hypergraph behind any future holonomy claim.

    A row is ``-phi_out + phi_left + phi_right + beta``.  The coefficient
    phase ``beta`` is recovered from the exact complex channel contribution,
    after removing the three actual helical-amplitude phases.  This records
    the physical input needed for a weighted channel-cycle holonomy theorem;
    it does not select a preferred phase branch or claim a holonomy bound.
    """
    rows: list[dict[str, Any]] = []
    modal_checks: list[dict[str, float]] = []
    for triad_index, triad in enumerate(network["triads"]):
        p, q, r = (tuple(mode) for mode in triad["modes"])
        modal_specs = (("p", negate(p), q, r), ("q", negate(q), r, p), ("r", negate(r), p, q))
        for output_label, out, left, right in modal_specs:
            channel_sum = 0.0
            channel_envelope = 0.0
            for out_sign in (-1, 1):
                for left_sign in (-1, 1):
                    for right_sign in (-1, 1):
                        value, out_scalar, left_scalar, right_scalar = channel_complex_contribution(
                            field_hat, out, left, right, out_sign, left_sign, right_sign
                        )
                        channel_sum += -float(np.real(value))
                        channel_envelope += abs(value)
                        amplitude_product = abs(out_scalar * left_scalar * right_scalar)
                        if amplitude_product <= 1.0e-30:
                            continue
                        beta = wrap_phase(
                            float(np.angle(value))
                            - (-float(np.angle(out_scalar)) + float(np.angle(left_scalar)) + float(np.angle(right_scalar)))
                        )
                        rows.append({
                            "triad": triad_index,
                            "output": output_label,
                            "modes": [list(out), list(left), list(right)],
                            "helicities": [out_sign, left_sign, right_sign],
                            "phase_incidence": [-1, 1, 1],
                            "geometric_coefficient_phase_beta": beta,
                            "complex_term_phase": float(np.angle(value)),
                            "complex_term_magnitude": float(abs(value)),
                            "real_energy_term": -float(np.real(value)),
                        })
            direct = static_modal_transfer(field_hat, out, left, right)
            modal_checks.append({
                "triad": float(triad_index),
                "channel_sum": channel_sum,
                "direct_transfer": direct,
                "reconstruction_error": abs(channel_sum - direct),
                "channel_phase_saturation": abs(channel_sum) / channel_envelope if channel_envelope > 1.0e-30 else 0.0,
            })
    return {
        "active_channel_count": len(rows),
        "max_modal_reconstruction_error": float(max((row["reconstruction_error"] for row in modal_checks), default=0.0)),
        "modal_checks": modal_checks,
        "active_channels": rows,
        "holonomy_status": "channel_rows_extracted_but_weighted_cycle_holonomy_not_yet_selected",
        "warning": "A graph cycle alone does not determine an NS phase holonomy; any next holonomy audit must choose a channel weighting and a phase-preference branch.",
    }


def add_reality_symmetric_helical_mode(
    raw_hat: np.ndarray, mode: tuple[int, int, int], amplitude: float, phase: float, helicity: int,
) -> None:
    """Insert one mode and its conjugate exactly in physical component order."""
    basis = helical_basis(mode)[0 if helicity > 0 else 1]
    coefficient = amplitude * np.exp(1j * phase) * basis
    raw_hat[mode_index(mode, raw_hat.shape[0])] += coefficient
    raw_hat[mode_index(negate(mode), raw_hat.shape[0])] += np.conjugate(coefficient)


def normalise_urms(raw_hat: np.ndarray, target_urms: float) -> np.ndarray:
    velocity = np.fft.ifftn(raw_hat, axes=(0, 1, 2)).real
    urms = float(np.sqrt(np.mean(np.sum(velocity * velocity, axis=-1))))
    if urms <= 1.0e-30:
        raise ValueError("phase candidate has zero velocity")
    return raw_hat * (target_urms / urms)


def normalise_critical_mass(raw_hat: np.ndarray, critical_mass: float) -> np.ndarray:
    """Set ``sum_j 2^j ||P_j u||_2^2`` to one common finite-carrier scale."""
    _, norm = frequency_grid(raw_hat.shape[0])
    field_hat = np.moveaxis(raw_hat / float(raw_hat.shape[0] ** 3), -1, 0)
    max_shell = int(math.ceil(math.log2(float(np.max(norm)) + 1.0)))
    observed_mass = float(np.sum(dyadic_shell_packets(field_hat, norm, max_shell)))
    if observed_mass <= 1.0e-30:
        raise ValueError("phase candidate has zero critical packet mass")
    return raw_hat * math.sqrt(critical_mass / observed_mass)


def packet_max_shell(norm: np.ndarray) -> int:
    """Include every nonzero lattice mode in the finite carrier packet ledger."""
    return int(math.ceil(math.log2(float(np.max(norm)) + 1.0)))


def build_candidate(args: argparse.Namespace, network: dict[str, Any], phases: np.ndarray) -> np.ndarray:
    variable_entries = [entry for entry in network["entries"] if "fixed_phase" not in entry]
    if len(phases) != len(variable_entries):
        raise ValueError("one phase is required per non-fixed network mode")
    raw_hat = np.zeros((args.n, args.n, args.n, 3), dtype=np.complex128)
    phase_iter = iter(float(phase) for phase in phases)
    for entry in network["entries"]:
        phase = float(entry["fixed_phase"]) if "fixed_phase" in entry else next(phase_iter)
        add_reality_symmetric_helical_mode(
            raw_hat, entry["mode"], float(entry["amplitude"]), phase, int(entry["helicity"])
        )
    return (normalise_critical_mass(raw_hat, args.critical_mass)
            if args.normalization == "critical" else normalise_urms(raw_hat, args.target_urms))


def raw_to_field_hat(raw_hat: np.ndarray, wave: np.ndarray, norm_sq: np.ndarray) -> np.ndarray:
    n = raw_hat.shape[0]
    return leray_project(np.moveaxis(raw_hat / float(n ** 3), -1, 0), wave, norm_sq)


def realised_role_mass_shares(field_hat: np.ndarray, network: dict[str, Any]) -> dict[str, float]:
    """Recover role shares from the actual reality-paired finite carrier."""
    role_mass = {name: 0.0 for name in ("target", "donor", "outlet", "feedback")}
    for entry in network["entries"]:
        mode = tuple(entry["mode"])
        weight = dyadic_weight(mode)
        positive = field_hat[(slice(None),) + mode_index(mode, field_hat.shape[1])]
        negative = field_hat[(slice(None),) + mode_index(negate(mode), field_hat.shape[1])]
        role_mass[role_name(entry)] += weight * float(
            np.vdot(positive, positive).real + np.vdot(negative, negative).real
        )
    total = float(sum(role_mass.values()))
    if total <= 1.0e-30:
        raise ValueError("candidate has zero realised role mass")
    return {role: value / total for role, value in role_mass.items()}


def static_metrics(
    args: argparse.Namespace, raw_hat: np.ndarray, wave: np.ndarray, norm: np.ndarray,
    norm_sq: np.ndarray, network: dict[str, Any],
) -> dict[str, Any]:
    field_hat = raw_to_field_hat(raw_hat, wave, norm_sq)
    dealias = component_dealias_mask(wave, args.n)
    nonlinear_hat = reconstructed_nonlinear_rhs(field_hat, wave, norm_sq, dealias)
    packets = dyadic_shell_packets(field_hat, norm, packet_max_shell(norm))
    dissipations = shell_dissipation(field_hat, norm_sq, norm, packet_max_shell(norm))
    nonlinear_rates = shell_nonlinear_rate(field_hat, nonlinear_hat, norm, packet_max_shell(norm))
    target_packet = float(packets[args.target_shell])
    target_dissipation = float(dissipations[args.target_shell])
    target_nonlinear = float(nonlinear_rates[args.target_shell])
    total_packet = float(np.sum(packets))
    lower = max(0, args.target_shell - 1)
    upper = min(len(packets), args.target_shell + 2)
    return {
        "target_packet": target_packet,
        "target_packet_dominance": target_packet / float(np.max(packets)) if np.max(packets) > 0.0 else math.nan,
        "target_packet_local_tightness": float(np.sum(packets[lower:upper])) / total_packet if total_packet > 0.0 else math.nan,
        "target_nonlinear_rate": target_nonlinear,
        "target_viscous_rate": 2.0 * args.nu * target_dissipation,
        "initial_replenishment_ratio": target_nonlinear / (2.0 * args.nu * target_dissipation) if target_dissipation > 1.0e-30 else math.nan,
        "realised_role_critical_shares": realised_role_mass_shares(field_hat, network),
    }


def packet_shape_metrics(
    args: argparse.Namespace,
    field_hat: np.ndarray,
    norm: np.ndarray,
    network: dict[str, Any],
    reference_network_vector: np.ndarray | None,
) -> dict[str, Any]:
    """Packet and designed-network telemetry at one exact solver checkpoint.

    The three target phases are fixed at the three independent modes
    ``(4,0,0)``, ``(0,4,0)``, ``(0,0,4)``.  That removes the three translation
    phase gauges from the phase search.  The checkpoint telemetry additionally
    reports the full-field correlation maximised over discrete translations.
    It does not quotient lattice rotations; those are intentionally left for a
    later relative-periodic-orbit search.
    """
    packets = dyadic_shell_packets(field_hat, norm, packet_max_shell(norm))
    target = float(packets[args.target_shell])
    lower = max(0, args.target_shell - 1)
    upper = min(len(packets), args.target_shell + 2)
    total = float(np.sum(packets))
    dominant_shell = int(np.argmax(packets))
    moving_lower = max(0, dominant_shell - args.moving_packet_radius)
    moving_upper = min(len(packets), dominant_shell + args.moving_packet_radius + 1)
    moving_packet = float(np.sum(packets[moving_lower:moving_upper]))
    coordinates: list[np.ndarray] = []
    support_energy = 0.0
    all_energy = float(np.sum(np.abs(field_hat) ** 2))
    for entry in network["entries"]:
        for mode in (entry["mode"], negate(entry["mode"])):
            value = np.asarray(field_hat[(slice(None),) + mode_index(mode, args.n)], dtype=np.complex128)
            coordinates.append(value)
            support_energy += float(np.sum(np.abs(value) ** 2))
    vector = np.concatenate(coordinates)
    vector_norm = float(np.linalg.norm(vector))
    if reference_network_vector is None:
        correlation = 1.0
    else:
        reference_norm = float(np.linalg.norm(reference_network_vector))
        correlation = (float(abs(np.vdot(reference_network_vector, vector)) / (reference_norm * vector_norm))
                       if reference_norm > 1.0e-30 and vector_norm > 1.0e-30 else math.nan)
    return {
        "target_packet": target,
        "target_packet_dominance": target / float(np.max(packets)) if np.max(packets) > 0.0 else math.nan,
        "target_packet_local_tightness": float(np.sum(packets[lower:upper])) / total if total > 0.0 else math.nan,
        "shell_packets": [float(value) for value in packets],
        "dominant_shell": dominant_shell,
        "moving_packet": moving_packet,
        "moving_packet_fraction": moving_packet / total if total > 0.0 else math.nan,
        "designed_network_energy_fraction": support_energy / all_energy if all_energy > 1.0e-30 else math.nan,
        "support_leakage_fraction": 1.0 - support_energy / all_energy if all_energy > 1.0e-30 else math.nan,
        "network_correlation_direct": correlation,
        "_network_vector": vector,
    }


def translation_max_correlation(reference: np.ndarray, current: np.ndarray) -> float:
    """Correlation modulo the discrete torus translations of the full field.

    For a translation ``x0``, Fourier coefficients gain ``exp(i k . x0)``.
    The inverse FFT of the cross spectrum evaluates every discrete translation
    simultaneously, so this is exact on the finite N^3 Galerkin carrier.
    """
    reference_norm = float(np.linalg.norm(reference))
    current_norm = float(np.linalg.norm(current))
    if reference_norm <= 1.0e-30 or current_norm <= 1.0e-30:
        return math.nan
    cross_spectrum = np.sum(np.conjugate(reference) * current, axis=0)
    correlations = np.fft.ifftn(cross_spectrum) * float(reference.shape[1] ** 3)
    return float(np.max(np.abs(correlations)) / (reference_norm * current_norm))


def moving_packet_from_packets(packets: np.ndarray, radius: int) -> tuple[int, float]:
    centre = int(np.argmax(packets))
    return centre, float(np.sum(packets[max(0, centre - radius):min(len(packets), centre + radius + 1)]))


def heat_packet_ledger(
    initial_field: np.ndarray, norm_sq: np.ndarray, norm: np.ndarray, nu: float, delta_t: float,
) -> np.ndarray:
    return np.asarray([
        heat_continued_packet(initial_field, norm_sq, norm, shell, nu, delta_t)
        for shell in range(packet_max_shell(norm) + 1)
    ], dtype=np.float64)


def load_cfd_module(args: argparse.Namespace) -> Any:
    scripts_dir = args.cfd_root / "scripts"
    if not scripts_dir.is_dir():
        raise FileNotFoundError(f"missing dashiCFD scripts directory: {scripts_dir}")
    sys.path.insert(0, str(scripts_dir))
    spec = importlib.util.spec_from_file_location("dashi_make_truth_3d", scripts_dir / "make_truth_3d.py")
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load sibling finite-Galerkin solver")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def evolve_candidate(
    args: argparse.Namespace, network: dict[str, Any], raw_hat: np.ndarray,
    wave: np.ndarray, norm: np.ndarray, norm_sq: np.ndarray,
) -> dict[str, Any]:
    """Evolve one candidate and score every complete viscous-time window."""
    module = load_cfd_module(args)
    nominal_window_time = args.window_c * (2.0 ** (-2 * args.target_shell)) / args.nu
    window_steps = int(math.ceil(nominal_window_time / args.dt))
    actual_window_time = window_steps * args.dt
    steps = args.windows * window_steps
    actual_time = steps * args.dt
    _, kx, ky, kz, k2, _ = module.make_grid(args.n, 2.0 * math.pi)
    mask = module.component_dealias_mask(kx, ky, kz, args.n, 2.0 * math.pi)
    initial_field = raw_to_field_hat(raw_hat, wave, norm_sq)
    initial_shape = packet_shape_metrics(args, initial_field, norm, network, None)
    reference_network_vector = initial_shape.pop("_network_vector")
    initial_packet = float(initial_shape["target_packet"])
    initial_moving_packet = float(initial_shape["moving_packet"])
    heat_ledgers = [heat_packet_ledger(
        initial_field, norm_sq, norm, args.nu, window * actual_window_time
    ) for window in range(args.windows + 1)]
    heat_packets = [float(ledger[args.target_shell]) for ledger in heat_ledgers]
    heat_moving = [moving_packet_from_packets(ledger, args.moving_packet_radius) for ledger in heat_ledgers]
    history: list[dict[str, Any]] = []
    quarter_checkpoint_steps = {
        numerator * window_steps // 4
        for numerator in range(1, 4 * args.windows + 1)
        if (numerator * window_steps) % 4 == 0
    }

    def record(step: int, current_raw: np.ndarray) -> None:
        current_field = raw_to_field_hat(current_raw, wave, norm_sq)
        shape = packet_shape_metrics(args, current_field, norm, network, reference_network_vector)
        shape.pop("_network_vector")
        shape["translation_max_correlation_full_field"] = translation_max_correlation(initial_field, current_field)
        nonlinear = reconstructed_nonlinear_rhs(current_field, wave, norm_sq, component_dealias_mask(wave, args.n))
        dissipation = shell_dissipation(current_field, norm_sq, norm, args.target_shell)[args.target_shell]
        nonlinear_rate = shell_nonlinear_rate(current_field, nonlinear, norm, args.target_shell)[args.target_shell]
        role_ledger = designed_role_transfer_rate(current_field, network)
        history.append({"step": step, "time": step * args.dt, **shape,
                        "target_dissipation": float(dissipation),
                        "target_nonlinear_rate": float(nonlinear_rate),
                        "designed_role_transfer_ledger": role_ledger})

    if args.backend == "gpu":
        from vulkan_truth3d_backend import VulkanTruth3DBackend
        backend = VulkanTruth3DBackend(args.n, dt=args.dt, nu0=args.nu, length=2.0 * math.pi, fft_backend=args.fft_backend)
        try:
            backend.set_initial_u_hat(raw_hat)
            for step in range(steps + 1):
                if (step % args.save_every == 0 or step % window_steps == 0
                        or step in quarter_checkpoint_steps or step == steps):
                    record(step, np.asarray(backend.read_u_hat(), dtype=np.complex128))
                if step < steps:
                    backend.step()
        finally:
            backend.close()
    else:
        current_raw = raw_hat.copy()
        for step in range(steps + 1):
            if (step % args.save_every == 0 or step % window_steps == 0
                    or step in quarter_checkpoint_steps or step == steps):
                record(step, current_raw)
            if step < steps:
                current_raw = module.rk2_step(current_raw, kx, ky, kz, k2, mask, args.dt, args.nu)
    window_rows = [row for row in history if int(row["step"]) % window_steps == 0]
    ratios = [float(window_rows[index + 1]["target_packet"] / window_rows[index]["target_packet"])
              for index in range(len(window_rows) - 1)]
    moving_ratios = [float(window_rows[index + 1]["moving_packet"] / window_rows[index]["moving_packet"])
                     for index in range(len(window_rows) - 1)]
    log_score = (float(np.mean(np.log(moving_ratios)))
                 if moving_ratios and all(value > 0.0 for value in moving_ratios) else math.nan)
    times = np.asarray([row["time"] for row in history], dtype=np.float64)
    nonlinear_rates = np.asarray([row["target_nonlinear_rate"] for row in history], dtype=np.float64)
    dissipations = np.asarray([row["target_dissipation"] for row in history], dtype=np.float64)
    viscous_loss = float(2.0 * args.nu * np.trapezoid(dissipations, times))
    nonlinear_positive = float(np.trapezoid(np.maximum(nonlinear_rates, 0.0), times))
    nonlinear_negative = float(-np.trapezoid(np.minimum(nonlinear_rates, 0.0), times))
    role_transfer = integrated_role_transfer_ledger(history)
    role_transfer_checkpoints = role_transfer_checkpoint_telemetry(history, window_steps)
    final_packet = float(window_rows[-1]["target_packet"])
    final_moving_packet = float(window_rows[-1]["moving_packet"])
    final_dominant_shell = int(window_rows[-1]["dominant_shell"])
    heat_final_centre, heat_final_moving = heat_moving[-1]
    return {
        "steps": steps,
        "nominal_window_time": nominal_window_time,
        "actual_window_time": actual_window_time,
        "windows": args.windows,
        "actual_time": actual_time,
        "initial_packet": initial_packet,
        "heat_only_packets_exact_spectrum": heat_packets,
        "heat_only_shell_packets_exact_spectrum": [[float(value) for value in ledger] for ledger in heat_ledgers],
        "heat_only_moving_packet_centres": [int(centre) for centre, _ in heat_moving],
        "heat_only_moving_packets_exact_spectrum": [float(value) for _, value in heat_moving],
        "final_packet": final_packet,
        "endpoint_recurrence_ratio": final_packet / initial_packet,
        "endpoint_heat_compensated_ratio": final_packet / heat_packets[-1] if heat_packets[-1] > 1.0e-30 else math.nan,
        "window_recurrence_ratios": ratios,
        "initial_moving_packet": initial_moving_packet,
        "final_moving_packet": final_moving_packet,
        "moving_packet_recurrence_ratio": final_moving_packet / initial_moving_packet,
        "moving_packet_heat_compensated_ratio": (final_moving_packet / heat_final_moving
                                                   if heat_final_moving > 1.0e-30 else math.nan),
        "moving_window_recurrence_ratios": moving_ratios,
        "min_moving_window_recurrence_ratio": min(moving_ratios) if moving_ratios else math.nan,
        "initial_dominant_shell": int(window_rows[0]["dominant_shell"]),
        "final_dominant_shell": final_dominant_shell,
        "moving_packet_scale_displacement": final_dominant_shell - int(window_rows[0]["dominant_shell"]),
        "heat_final_dominant_shell": int(heat_final_centre),
        "min_window_recurrence_ratio": min(ratios) if ratios else math.nan,
        "mean_log_window_recurrence": log_score,
        "nonlinear_positive_over_viscous_loss": nonlinear_positive / viscous_loss if viscous_loss > 1.0e-30 else math.nan,
        "nonlinear_negative_over_viscous_loss": nonlinear_negative / viscous_loss if viscous_loss > 1.0e-30 else math.nan,
        "designed_role_transfer": role_transfer,
        "designed_role_transfer_checkpoints": role_transfer_checkpoints,
        "window_checkpoints": window_rows,
        "history": history,
    }


def main() -> None:
    args = parse_args()
    if (args.n < 24 or args.nu <= 0.0 or args.dt <= 0.0 or args.phase_samples <= 0
            or args.windows <= 0 or args.top_candidates <= 0):
        raise ValueError("n >= 24, positive nu/dt/windows/candidates, and phase-samples > 0 are required")
    if args.critical_mass <= 0.0 or args.target_urms <= 0.0:
        raise ValueError("critical-mass and target-urms must be positive")
    if args.moving_packet_radius < 0 or args.endpoint_prefilter_candidates < 0:
        raise ValueError("moving-packet-radius and endpoint-prefilter-candidates must be nonnegative")
    if args.phase_sample_index is not None and args.phase_sample_index < 0:
        raise ValueError("phase-sample-index must be nonnegative when supplied")
    if not (0.0 <= args.target_dominance_min <= 1.0 and 0.0 <= args.local_tightness_min <= 1.0
            and 0.0 <= args.role_share_min <= 0.25):
        raise ValueError("dominance/tightness minima must lie in [0,1] and role-share-min in [0,0.25]")
    network = network_spec(args)
    validate_network(args, network)
    requested_role_shares = parse_role_shares(args.role_shares)
    # The static envelope uses amplitude-weighted coupling factors.  Apply the
    # requested allocation before ranking helicity cases so each allocation
    # regime receives its own honest static seed ordering.
    role_allocation = apply_role_mass_shares(network, requested_role_shares)
    phase_geometry = phase_graph_geometry(network)
    signed_phase_geometry = signed_phase_constraint_geometry(network)
    helicity_geometry = helicity_factorisation_geometry(network)
    needs_helicity_audit = args.helicity_static_audit or args.helicity_static_case is not None
    helicity_static_audit = helicity_static_factor_audit(network) if needs_helicity_audit else {
        "status": "not_requested",
        "how_to_run": "pass --helicity-static-audit for the 64-backbone-case factor-table screen",
    }
    selected_helicity_seed = (
        static_helicity_case_assignment(network, helicity_static_audit, args.helicity_static_case)
        if args.helicity_static_case is not None else {"status": "default_entry_helicities"}
    )
    variable_dimension = sum("fixed_phase" not in entry for entry in network["entries"])
    wave, norm = frequency_grid(args.n)
    norm_sq = norm * norm
    rng = np.random.default_rng(args.seed)
    candidates: list[dict[str, Any]] = []
    # A staged external screen needs to evaluate an exact phase point rather
    # than repeatedly letting the static-inflow sort choose a different one.
    # Preserve the ordinary RNG stream, so index i is identical to sample i in
    # an unrestricted run with the same seed.
    sample_indices = range(args.phase_samples)
    if args.phase_sample_index is not None:
        if args.phase_sample_index >= args.phase_samples:
            raise ValueError("phase-sample-index must be smaller than --phase-samples")
        sample_indices = range(args.phase_sample_index + 1)
    for sample in sample_indices:
        phases = rng.uniform(-math.pi, math.pi, size=variable_dimension)
        if args.phase_sample_index is not None and sample != args.phase_sample_index:
            continue
        raw_hat = build_candidate(args, network, phases)
        metrics = static_metrics(args, raw_hat, wave, norm, norm_sq, network)
        # Role allocations are normalised by finite floating-point carrier
        # sums.  A requested exact floor can therefore round to, e.g.,
        # ``0.04999999999999999`` rather than ``0.05``.  The tolerance only
        # accepts machine-level representation error; it is not a relaxation
        # of the declared packet-admissibility contract.
        admissibility_tolerance = 1.0e-12
        admissible = (
            float(metrics["target_packet_dominance"]) >= args.target_dominance_min - admissibility_tolerance
            and float(metrics["target_packet_local_tightness"]) >= args.local_tightness_min - admissibility_tolerance
            and min(metrics["realised_role_critical_shares"].values())
            >= args.role_share_min - admissibility_tolerance
        )
        candidates.append({"sample": sample, "phases": [float(value) for value in phases],
                           "initial_admissible": admissible, **metrics})
    # Positive nonlinear inflow into the target shell is only the cheapest
    # first filter.  An optional short evolved prefilter then ranks those
    # seeds by the actual moving-packet endpoint objective before any full
    # viscous-window run.  Neither stage is global endpoint optimisation.
    candidates = [candidate for candidate in candidates if bool(candidate["initial_admissible"])]
    if not candidates:
        raise ValueError("no phase samples satisfy the declared target/tightness/role-share admissibility constraints")
    candidates.sort(key=lambda row: float(row["target_nonlinear_rate"]), reverse=True)
    selected = candidates[:args.top_candidates]
    prefilter_rows: list[dict[str, Any]] = []
    if args.backend != "none" and args.endpoint_prefilter_candidates > 0:
        if args.endpoint_prefilter_window_c <= 0.0:
            raise ValueError("--endpoint-prefilter-window-c must be positive when endpoint prefiltering is enabled")
        prefilter_args = copy.copy(args)
        prefilter_args.window_c = args.endpoint_prefilter_window_c
        prefilter_args.windows = 1
        for rank, candidate in enumerate(candidates[:args.endpoint_prefilter_candidates]):
            started = time.perf_counter()
            endpoint = evolve_candidate(
                prefilter_args, network, build_candidate(args, network, np.asarray(candidate["phases"])),
                wave, norm, norm_sq,
            )
            prefilter_rows.append({
                "rank_by_initial_inflow": rank,
                "sample": candidate["sample"],
                "phases": candidate["phases"],
                "endpoint_prefilter": endpoint,
                "elapsed_seconds": time.perf_counter() - started,
            })
        prefilter_rows.sort(
            key=lambda row: float(row["endpoint_prefilter"]["moving_packet_recurrence_ratio"]), reverse=True
        )
        selected_samples = {int(row["sample"]) for row in prefilter_rows[:args.top_candidates]}
        selected = [candidate for candidate in candidates if int(candidate["sample"]) in selected_samples]
    selected_phase_channel_audits = [
        {
            "sample": candidate["sample"],
            "phase_audit": helical_channel_phase_audit(
                raw_to_field_hat(build_candidate(args, network, np.asarray(candidate["phases"])), wave, norm_sq), network
            ),
        }
        for candidate in selected
    ]
    endpoint_rows: list[dict[str, Any]] = []
    if args.backend != "none":
        for rank, candidate in enumerate(selected):
            started = time.perf_counter()
            endpoint_rows.append({
                "rank_by_initial_inflow": rank,
                "sample": candidate["sample"],
                "phases": candidate["phases"],
                "static": {key: value for key, value in candidate.items() if key not in {"sample", "phases"}},
                "endpoint": evolve_candidate(
                    args, network, build_candidate(args, network, np.asarray(candidate["phases"])), wave, norm, norm_sq
                ),
                "elapsed_seconds": time.perf_counter() - started,
            })
        endpoint_rows.sort(
            key=lambda row: float(row["endpoint"]["min_moving_window_recurrence_ratio"]), reverse=True
        )
    payload = {
        "contract": "ns_phase_locked_packet_adversarial_search",
        "authority": authority(),
        "status": "ok",
        "topology": network | {
            "phase_dimension": variable_dimension,
            "constraints": "reality symmetric, divergence free helical modes, componentwise 2/3 dealiased N32 support, fixed amplitudes and declared global normalization",
            "translation_phase_gauge": "fixed phases of (4,0,0), (0,4,0), (0,0,4) remove the three translation gauges for the cyclic graph",
            "phase_graph_geometry": phase_geometry,
            "signed_phase_constraint_geometry": signed_phase_geometry,
            "helicity_factorisation_geometry": helicity_geometry,
            "helicity_static_factor_audit": helicity_static_audit,
            "selected_helicity_seed": selected_helicity_seed,
            "role_mass_allocation": role_allocation,
        },
        "objective": {
            "static_prefilter": "maximize initial nonlinear target-shell inflow only to seed an endpoint search",
            "endpoint": "maximize min_m P_L((m+1)T) / P_L(mT), where P_L follows the dominant shell and T = c * 2^(-2j) / nu",
            "secondary_endpoint": "maximize mean log moving-packet recurrence",
            "translation_quotient": "checkpoint correlation is maximised over discrete torus translations; lattice rotations are not quotiented",
            "warning": (
                "this version samples phase candidates and evolves only a staged prefiltered subset; "
                "it is not global endpoint optimization.  A selected static helicity case is an envelope seed, "
                "not a joint leaf-choice or mixed-polarization search."
            ),
        },
        "inputs": vars(args) | {"cfd_root": str(args.cfd_root), "output_json": str(args.output_json)},
        "static_candidates_ranked": candidates,
        "endpoint_prefilter_evolutions": prefilter_rows,
        "selected_phase_channel_audits": selected_phase_channel_audits,
        "endpoint_evolutions": endpoint_rows,
        "decision": "candidate-only adversarial search; any apparent recurrence is a finite numerical lead requiring independent reproduction, not a Navier--Stokes theorem.",
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(json.dumps(payload, indent=2, sort_keys=True, allow_nan=False) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2, sort_keys=True, allow_nan=False))


if __name__ == "__main__":
    main()
