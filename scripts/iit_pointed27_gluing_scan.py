#!/usr/bin/env python3
from __future__ import annotations

import json
from itertools import product
from pathlib import Path

VALUES = (-1, 0, 1)
POINTS = tuple(product(VALUES, repeat=3))
FACES = (
    (0, -1), (0, 1),
    (1, -1), (1, 1),
    (2, -1), (2, 1),
)


def on_face(point: tuple[int, int, int], face: tuple[int, int]) -> bool:
    axis, sign = face
    return point[axis] == sign


def incident_faces(point: tuple[int, int, int]) -> tuple[tuple[int, int], ...]:
    return tuple(face for face in FACES if on_face(point, face))


def opposite(left: tuple[int, int], right: tuple[int, int]) -> bool:
    return left[0] == right[0] and left[1] != right[1]


def gluing_summary() -> dict:
    strata = {0: 0, 1: 0, 2: 0, 3: 0}
    for point in POINTS:
        strata[len(incident_faces(point))] += 1

    pair_overlaps = []
    for i, left in enumerate(FACES):
        for right in FACES[i + 1 :]:
            if opposite(left, right):
                continue
            overlap = tuple(
                point for point in POINTS
                if on_face(point, left) and on_face(point, right)
            )
            if overlap:
                pair_overlaps.append((left, right, overlap))

    corner_triples = []
    for fx in ((0, -1), (0, 1)):
        for fy in ((1, -1), (1, 1)):
            for fz in ((2, -1), (2, 1)):
                overlap = tuple(
                    point for point in POINTS
                    if on_face(point, fx) and on_face(point, fy) and on_face(point, fz)
                )
                corner_triples.append((fx, fy, fz, overlap))

    face_sizes = {
        str(face): sum(on_face(point, face) for point in POINTS)
        for face in FACES
    }

    return {
        "contract": "iit_pointed27_gluing_scan",
        "carrier_size": len(POINTS),
        "non_origin_count": len(POINTS) - 1,
        "strata": {
            "0_faces": strata[0],
            "1_face": strata[1],
            "2_faces": strata[2],
            "3_faces": strata[3],
        },
        "face_count": len(FACES),
        "each_face_size": min(face_sizes.values()),
        "face_sizes": face_sizes,
        "total_point_face_incidences": sum(len(incident_faces(point)) for point in POINTS),
        "pairwise_face_overlaps": len(pair_overlaps),
        "each_edge_overlap_size": min(len(overlap) for _, _, overlap in pair_overlaps),
        "corner_face_triples": len(corner_triples),
        "each_corner_triple_intersection_size": min(
            len(overlap) for *_faces, overlap in corner_triples
        ),
        "three_selected_cubie_choices": len(POINTS) ** 3,
        "active_face_choice_count_by_point": {
            str(point): len(incident_faces(point)) for point in POINTS
        },
        "boundary": {
            "selection_alone_determines_face_gluing": False,
            "geometry_alone_defines_an_iit_tpm": False,
            "cech_edge_transport_still_required": True,
            "corner_cocycle_still_required": True,
            "c3_recentring_is_canonical_geometric_symmetry": False,
        },
    }


def main() -> None:
    summary = gluing_summary()
    output = Path(__file__).with_name("data") / "outputs" / "iit_pointed27_gluing_scan.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
