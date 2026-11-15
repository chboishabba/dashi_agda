#!/usr/bin/env python3
"""Diagnostic seam derivation receipt over a toy body patch.

The runner exercises the SeaMeInIt seam pipeline shape:
fields -> seam costs -> seam topology -> panels -> flattening residuals
-> metric-correction operators -> allowances -> finished receipt.

It is intentionally diagnostic-only. The synthetic body, ROM, fabric, and
flattening model are fixtures, not production pattern evidence.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CLAIM_BOUNDARY = {
    "body_truth": False,
    "global_optimum": False,
    "isometry": False,
    "true_inverse": False,
    "manufacturing_authority": False,
    "seameinit_production_promotion": False,
}


@dataclass(frozen=True)
class Vertex:
    vid: int
    i: int
    j: int
    x: float
    y: float
    z: float


@dataclass(frozen=True)
class Edge:
    eid: int
    a: int
    b: int
    orientation: str


@dataclass(frozen=True)
class Face:
    vertices: tuple[int, int, int, int]


@dataclass(frozen=True)
class ReprojectionQuality:
    max_distance: float
    mean_distance: float
    edge_retention_ratio: float
    retained_edges: int
    source_edge_count: int


class ReprojectionCompatibilityError(ValueError):
    """Raised when source and target meshes fail geometric compatibility gates."""


def stable_hash(value: object) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode(
        "utf-8"
    )
    return hashlib.sha256(encoded).hexdigest()


def file_hash(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build_toy_patch(width: int, height: int) -> tuple[list[Vertex], list[Edge], list[Face]]:
    vertices: list[Vertex] = []
    for j in range(height):
        for i in range(width):
            u = i / (width - 1)
            v = j / (height - 1)
            x = 2.0 * u - 1.0
            y = 2.0 * v - 1.0
            z = 0.34 * math.exp(-2.2 * (x * x + 0.55 * y * y))
            vertices.append(Vertex(j * width + i, i, j, x, y, z))

    edges: list[Edge] = []
    eid = 0
    for j in range(height):
        for i in range(width):
            here = j * width + i
            if i + 1 < width:
                edges.append(Edge(eid, here, here + 1, "horizontal"))
                eid += 1
            if j + 1 < height:
                edges.append(Edge(eid, here, here + width, "vertical"))
                eid += 1

    faces = [
        Face((j * width + i, j * width + i + 1, (j + 1) * width + i + 1, (j + 1) * width + i))
        for j in range(height - 1)
        for i in range(width - 1)
    ]
    return vertices, edges, faces


def build_target_patch(
    source_vertices: list[Vertex],
    source_edges: list[Edge],
    source_faces: list[Face],
) -> tuple[list[Vertex], list[Edge], list[Face]]:
    """Build a nearby target fixture without assuming identical coordinates."""
    target_vertices = [
        Vertex(
            v.vid,
            v.i,
            v.j,
            v.x + 0.004 * v.y,
            v.y - 0.003 * v.x,
            v.z + 0.002 * (v.x * v.x + v.y * v.y),
        )
        for v in source_vertices
    ]
    target_edges = [Edge(e.eid, e.a, e.b, e.orientation) for e in source_edges]
    target_faces = [Face(face.vertices) for face in source_faces]
    return target_vertices, target_edges, target_faces


def vertex_distance(a: Vertex, b: Vertex) -> float:
    return math.sqrt(
        (a.x - b.x) * (a.x - b.x)
        + (a.y - b.y) * (a.y - b.y)
        + (a.z - b.z) * (a.z - b.z)
    )


def nearest_vertex_reprojection(
    source_vertices: list[Vertex],
    target_vertices: list[Vertex],
) -> tuple[dict[int, int], list[float]]:
    if not source_vertices:
        raise ReprojectionCompatibilityError("source mesh has no vertices")
    if not target_vertices:
        raise ReprojectionCompatibilityError("target mesh has no vertices")

    mapping: dict[int, int] = {}
    distances: list[float] = []
    for source_vertex in source_vertices:
        target_vertex = min(
            target_vertices,
            key=lambda candidate: (
                vertex_distance(source_vertex, candidate),
                candidate.vid,
            ),
        )
        mapping[source_vertex.vid] = target_vertex.vid
        distances.append(vertex_distance(source_vertex, target_vertex))
    return mapping, distances


def reprojection_quality(
    source_vertices: list[Vertex],
    source_edges: list[Edge],
    target_vertices: list[Vertex],
    target_edges: list[Edge],
) -> tuple[ReprojectionQuality, dict[int, int]]:
    mapping, distances = nearest_vertex_reprojection(source_vertices, target_vertices)

    target_edge_keys = {
        frozenset((edge.a, edge.b))
        for edge in target_edges
        if edge.a != edge.b
    }
    retained_edges = 0
    for edge in source_edges:
        mapped_a = mapping[edge.a]
        mapped_b = mapping[edge.b]
        if (
            mapped_a != mapped_b
            and frozenset((mapped_a, mapped_b)) in target_edge_keys
        ):
            retained_edges += 1

    source_edge_count = len(source_edges)
    edge_retention_ratio = (
        retained_edges / source_edge_count
        if source_edge_count
        else 1.0
    )
    quality = ReprojectionQuality(
        max_distance=max(distances),
        mean_distance=sum(distances) / len(distances),
        edge_retention_ratio=edge_retention_ratio,
        retained_edges=retained_edges,
        source_edge_count=source_edge_count,
    )
    return quality, mapping


def require_reprojection_compatible(
    quality: ReprojectionQuality,
    *,
    max_distance: float,
    mean_distance: float,
    min_edge_retention_ratio: float,
) -> None:
    if max_distance < 0.0:
        raise ValueError("max_distance threshold must be non-negative")
    if mean_distance < 0.0:
        raise ValueError("mean_distance threshold must be non-negative")
    if not 0.0 <= min_edge_retention_ratio <= 1.0:
        raise ValueError("min_edge_retention_ratio must be in [0, 1]")

    failures: list[str] = []
    if quality.max_distance > max_distance:
        failures.append(
            f"max_distance={quality.max_distance:.6f} > {max_distance:.6f}"
        )
    if quality.mean_distance > mean_distance:
        failures.append(
            f"mean_distance={quality.mean_distance:.6f} > {mean_distance:.6f}"
        )
    if quality.edge_retention_ratio < min_edge_retention_ratio:
        failures.append(
            "edge_retention_ratio="
            f"{quality.edge_retention_ratio:.6f} < {min_edge_retention_ratio:.6f}"
        )

    if failures:
        raise ReprojectionCompatibilityError(
            "incompatible source/target meshes: " + "; ".join(failures)
        )


def transfer_edges(
    selected_source_edges: list[int],
    source_edges: list[Edge],
    target_edges: list[Edge],
    vertex_mapping: dict[int, int],
) -> list[int]:
    source_by_id = {edge.eid: edge for edge in source_edges}
    target_by_key = {
        frozenset((edge.a, edge.b)): edge.eid
        for edge in target_edges
        if edge.a != edge.b
    }

    transferred: list[int] = []
    for source_edge_id in selected_source_edges:
        source_edge = source_by_id[source_edge_id]
        mapped_key = frozenset(
            (
                vertex_mapping[source_edge.a],
                vertex_mapping[source_edge.b],
            )
        )
        target_edge_id = target_by_key.get(mapped_key)
        if target_edge_id is None:
            raise ReprojectionCompatibilityError(
                "source seam edge "
                f"{source_edge_id} has no retained target edge after reprojection"
            )
        transferred.append(target_edge_id)
    return transferred


def gaussian(x: float, y: float, sx: float, sy: float) -> float:
    return math.exp(-((x * x) / (2.0 * sx * sx) + (y * y) / (2.0 * sy * sy)))


def projected_fields(vertices: list[Vertex]) -> dict[int, dict[str, float]]:
    fields: dict[int, dict[str, float]] = {}
    for v in vertices:
        reach_load = 0.55 + 0.35 * (v.y + 1.0) / 2.0
        twist_load = 0.25 * abs(v.x)
        pressure = gaussian(v.x - 0.10, v.y + 0.05, 0.38, 0.42)
        support = 1.0 if v.x < -0.05 else 0.15
        curvature = abs(v.z) + 0.08 * gaussian(v.x, v.y, 0.55, 0.50)
        tension = reach_load + twist_load + 0.20 * curvature
        shear = abs(v.x) * (0.30 + 0.40 * pressure)
        grain_sector6 = float(int(((math.atan2(v.y, v.x) + math.pi) / (2.0 * math.pi)) * 6.0) % 6)
        fields[v.vid] = {
            "tension": tension,
            "pressure": pressure,
            "shear": shear,
            "support": support,
            "curvature": curvature,
            "grain_sector6": grain_sector6,
        }
    return fields


def edge_costs(
    vertices: list[Vertex],
    edges: list[Edge],
    fields: dict[int, dict[str, float]],
) -> list[dict[str, Any]]:
    by_id = {v.vid: v for v in vertices}
    rows: list[dict[str, Any]] = []
    for edge in edges:
        va, vb = by_id[edge.a], by_id[edge.b]
        fa, fb = fields[edge.a], fields[edge.b]
        support_jump = abs(fa["support"] - fb["support"])
        tension_jump = abs(fa["tension"] - fb["tension"])
        risk = (
            0.45 * max(fa["pressure"], fb["pressure"])
            + 0.35 * max(fa["shear"], fb["shear"])
            + 0.20 * max(fa["curvature"], fb["curvature"])
        )
        natural = 0.85 * support_jump + 0.25 * tension_jump
        manufacturing = 0.08 if edge.orientation == "vertical" else 0.16
        uncertainty = 0.04 * abs(va.y + vb.y) / 2.0
        cost = risk - natural + manufacturing + uncertainty
        if max(fa["pressure"], fb["pressure"]) > 0.94:
            admissibility = "forbidden"
        elif cost > 0.55:
            admissibility = "risky"
        elif natural > risk:
            admissibility = "preferred"
        else:
            admissibility = "neutral"
        rows.append(
            {
                "edge_id": edge.eid,
                "a": edge.a,
                "b": edge.b,
                "orientation": edge.orientation,
                "risk_penalty": round(risk, 6),
                "natural_boundary_reward": round(natural, 6),
                "manufacturing_penalty": round(manufacturing, 6),
                "uncertainty_penalty": round(uncertainty, 6),
                "cost": round(cost, 6),
                "admissibility": admissibility,
            }
        )
    return rows


def select_seam_path(
    width: int,
    height: int,
    edge_rows: list[dict[str, Any]],
) -> list[int]:
    vertical_edges_by_column: dict[int, list[dict[str, Any]]] = {}
    for row in edge_rows:
        if row["orientation"] != "vertical":
            continue
        a = int(row["a"])
        col = a % width
        vertical_edges_by_column.setdefault(col, []).append(row)

    best_col = 1
    best_score = float("inf")
    for col, rows in vertical_edges_by_column.items():
        if col in (0, width - 1):
            continue
        if any(row["admissibility"] == "forbidden" for row in rows):
            continue
        score = sum(float(row["cost"]) for row in rows)
        center_bias = abs(col - (width - 1) / 2.0) * 0.04
        if score + center_bias < best_score:
            best_score = score + center_bias
            best_col = col
    return [int(row["edge_id"]) for row in vertical_edges_by_column[best_col]]


def panels_from_vertical_seam(
    width: int,
    height: int,
    selected_edges: list[int],
    edges: list[Edge],
) -> list[dict[str, Any]]:
    selected = {eid for eid in selected_edges}
    seam_columns = [edges[eid].a % width for eid in selected]
    cut_col = seam_columns[0] if seam_columns else width // 2
    left_vertices = [
        j * width + i for j in range(height) for i in range(cut_col + 1)
    ]
    right_vertices = [
        j * width + i for j in range(height) for i in range(cut_col + 1, width)
    ]
    return [
        {
            "panel_id": 0,
            "side": "left",
            "vertices": left_vertices,
            "topological_disk": True,
            "grain_direction": "warp",
        },
        {
            "panel_id": 1,
            "side": "right",
            "vertices": right_vertices,
            "topological_disk": True,
            "grain_direction": "weft",
        },
    ]


def panel_flattening_and_shaping(
    panel: dict[str, Any],
    vertices: list[Vertex],
    fields: dict[int, dict[str, float]],
    residual_threshold: float,
) -> dict[str, Any]:
    by_id = {v.vid: v for v in vertices}
    vids = list(panel["vertices"])
    curvature = sum(fields[vid]["curvature"] for vid in vids) / len(vids)
    pressure = sum(fields[vid]["pressure"] for vid in vids) / len(vids)
    shear = sum(fields[vid]["shear"] for vid in vids) / len(vids)
    area_residual = 0.08 * curvature + 0.025 * len(vids) / len(vertices)
    angle_residual = 0.05 * shear
    shear_residual = 0.12 * shear + 0.03 * pressure
    boundary_residual = 0.04 + 0.05 * max(abs(by_id[vid].z) for vid in vids)
    aggregate = area_residual + angle_residual + shear_residual + boundary_residual

    shaping_ops: list[dict[str, Any]] = []
    if aggregate > residual_threshold:
        after = aggregate * 0.58
        gain = aggregate - after
        description_cost = 0.035
        kind = "wedge_dart" if pressure < 0.55 else "split_panel"
        shaping_ops.append(
            {
                "kind": kind,
                "diagnostic_only": True,
                "orientation_sector6": 1 if panel["side"] == "left" else 4,
                "metric_residual_before": round(aggregate, 6),
                "metric_residual_after": round(after, 6),
                "mdl_gain": round(gain - description_cost, 6),
                "manufacturable": True,
                "manufacturing_method_required": "home_sewing",
            }
        )

    panel_out = {
        "panel_id": panel["panel_id"],
        "side": panel["side"],
        "vertex_count": len(vids),
        "face_count": max(1, len(vids) - 3),
        "topological_disk": panel["topological_disk"],
        "grain_direction": panel["grain_direction"],
        "flattening": {
            "method": "toy_xy_projection",
            "foldover_count": 0,
            "area_residual": round(area_residual, 6),
            "angle_residual": round(angle_residual, 6),
            "shear_residual": round(shear_residual, 6),
            "boundary_residual": round(boundary_residual, 6),
            "aggregate_residual": round(aggregate, 6),
        },
        "shaping_ops": shaping_ops,
    }
    return panel_out


def allowance_receipt(
    selected_edges: list[int],
    edge_rows: list[dict[str, Any]],
    has_shaping: bool,
) -> dict[str, Any]:
    selected = {eid for eid in selected_edges}
    allowances = {}
    asymmetric_edges = 0
    for row in edge_rows:
        if row["edge_id"] not in selected:
            continue
        base = 10.0
        extra = 2.0 if row["admissibility"] == "risky" else 0.75
        if has_shaping:
            extra += 1.25
            asymmetric_edges += 1
        allowances[str(row["edge_id"])] = round(base + extra, 3)
    return {
        "default_mm": 10.0,
        "edge_allowances_mm": allowances,
        "edge_allowance_hash": stable_hash(allowances),
        "asymmetric_edges": asymmetric_edges,
    }


def build_receipt(
    width: int,
    height: int,
    residual_threshold: float,
    max_reprojection_distance: float = 0.02,
    mean_reprojection_distance: float = 0.01,
    min_edge_retention_ratio: float = 0.99,
) -> dict[str, Any]:
    source_vertices, source_edges, source_faces = build_toy_patch(width, height)
    target_vertices, target_edges, target_faces = build_target_patch(
        source_vertices,
        source_edges,
        source_faces,
    )

    quality, vertex_mapping = reprojection_quality(
        source_vertices,
        source_edges,
        target_vertices,
        target_edges,
    )
    require_reprojection_compatible(
        quality,
        max_distance=max_reprojection_distance,
        mean_distance=mean_reprojection_distance,
        min_edge_retention_ratio=min_edge_retention_ratio,
    )

    source_fields = projected_fields(source_vertices)
    costs = edge_costs(source_vertices, source_edges, source_fields)
    selected_source = select_seam_path(width, height, costs)
    selected_target = transfer_edges(
        selected_source,
        source_edges,
        target_edges,
        vertex_mapping,
    )

    target_fields = projected_fields(target_vertices)
    panels0 = panels_from_vertical_seam(
        width,
        height,
        selected_target,
        target_edges,
    )
    panels = [
        panel_flattening_and_shaping(
            panel,
            target_vertices,
            target_fields,
            residual_threshold,
        )
        for panel in panels0
    ]
    has_shaping = any(panel["shaping_ops"] for panel in panels)
    allowances = allowance_receipt(selected_source, costs, has_shaping)

    field_projection = {
        str(vid): {k: round(v, 6) for k, v in values.items()}
        for vid, values in target_fields.items()
    }
    selected_cost_rows = [
        row for row in costs if row["edge_id"] in set(selected_source)
    ]
    blockers = ["synthetic_body", "toy_flattening", "no_real_fabric_validation"]

    payload: dict[str, Any] = {
        "benchmark": "seam_derivation_diagnostic",
        "status": "diagnostic_only",
        "claim_boundary": dict(CLAIM_BOUNDARY),
        "pipeline_order": [
            "input",
            "body_gate",
            "reprojection_gate",
            "field_summary",
            "seam_cost_graph",
            "panels",
            "allowances",
            "promotion",
        ],
        "input": {
            "body_fixture": "toy_ellipsoid_patch",
            "rom_fixture": "synthetic_reach_twist",
            "fabric_fixture": "woven_moderate_stretch",
            "fabrication_method": "home_sewing",
            "width": width,
            "height": height,
            "source_mesh_fixture": "toy_ellipsoid_patch",
            "target_mesh_fixture": "deterministic_nearby_patch",
        },
        "body_gate": {
            "gate": "diagnostic",
            "severity": 1,
            "reason": "synthetic fixture, not fitted body evidence",
        },
        "reprojection_gate": {
            "passed": True,
            "max_distance": round(quality.max_distance, 9),
            "mean_distance": round(quality.mean_distance, 9),
            "edge_retention_ratio": round(quality.edge_retention_ratio, 9),
            "retained_edges": quality.retained_edges,
            "source_edge_count": quality.source_edge_count,
            "thresholds": {
                "max_distance": max_reprojection_distance,
                "mean_distance": mean_reprojection_distance,
                "min_edge_retention_ratio": min_edge_retention_ratio,
            },
            "vertex_mapping_hash": stable_hash(vertex_mapping),
        },
        "field_summary": {
            "fields": ["tension", "pressure", "shear", "support", "curvature", "grain_sector6"],
            "vertex_count": len(target_vertices),
            "edge_count": len(target_edges),
            "face_count": len(target_faces),
            "field_hash": stable_hash(field_projection),
        },
        "seam_cost_graph": {
            "edge_count": len(source_edges),
            "forbidden_edges": sum(1 for row in costs if row["admissibility"] == "forbidden"),
            "risky_edges": sum(1 for row in costs if row["admissibility"] == "risky"),
            "preferred_edges": sum(1 for row in costs if row["admissibility"] == "preferred"),
            "selected_seam_edges": selected_target,
            "selected_source_seam_edges": selected_source,
            "selected_target_seam_edges": selected_target,
            "selected_seam_cost": round(sum(float(row["cost"]) for row in selected_cost_rows), 6),
            "cost_hash": stable_hash(costs),
        },
        "panels": panels,
        "allowances": allowances,
        "promotion": {
            "state": "diagnostic_only",
            "severity": 1,
            "blockers": blockers,
            "metric_residual_absorbed_or_diagnosed": True,
            "manufacturing_exports_generated": False,
        },
    }
    payload["receipt_hashes"] = {
        "harness_source_hash": file_hash(Path(__file__).resolve()),
        "artifact_schema_hash": stable_hash(
            {
                "benchmark": "str",
                "status": "diagnostic_only",
                "claim_boundary": "dict[str,bool]",
                "input": "dict",
                "body_gate": "dict",
                "reprojection_gate": "dict",
                "field_summary": "dict",
                "seam_cost_graph": "dict",
                "panels": "list[panel]",
                "allowances": "dict",
                "promotion": "dict",
                "receipt_hashes": "dict[str,sha256]",
            }
        ),
        "command_hash": stable_hash(
            {
                "width": width,
                "height": height,
                "residual_threshold": residual_threshold,
                "max_reprojection_distance": max_reprojection_distance,
                "mean_reprojection_distance": mean_reprojection_distance,
                "min_edge_retention_ratio": min_edge_retention_ratio,
            }
        ),
        "environment_hash": stable_hash({"python": platform.python_version()}),
        "artifact_hash": stable_hash(payload),
    }
    return payload


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--width", type=int, default=6)
    parser.add_argument("--height", type=int, default=5)
    parser.add_argument("--residual-threshold", type=float, default=0.105)
    parser.add_argument("--max-reprojection-distance", type=float, default=0.02)
    parser.add_argument("--mean-reprojection-distance", type=float, default=0.01)
    parser.add_argument("--min-edge-retention-ratio", type=float, default=0.99)
    parser.add_argument("--out-dir", type=Path)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.width < 3 or args.height < 3:
        raise SystemExit("width and height must both be at least 3")
    try:
        payload = build_receipt(
            args.width,
            args.height,
            args.residual_threshold,
            max_reprojection_distance=args.max_reprojection_distance,
            mean_reprojection_distance=args.mean_reprojection_distance,
            min_edge_retention_ratio=args.min_edge_retention_ratio,
        )
    except ReprojectionCompatibilityError as exc:
        raise SystemExit(str(exc)) from exc
    text = json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n"
    if args.out_dir is not None:
        args.out_dir.mkdir(parents=True, exist_ok=True)
        (args.out_dir / "seam_derivation_diagnostic_summary.json").write_text(
            text, encoding="utf-8"
        )
    print(text, end="")


if __name__ == "__main__":
    main()
