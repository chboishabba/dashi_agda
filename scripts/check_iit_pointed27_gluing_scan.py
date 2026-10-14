#!/usr/bin/env python3
from __future__ import annotations

from iit_pointed27_gluing_scan import gluing_summary


def main() -> None:
    summary = gluing_summary()
    assert summary["carrier_size"] == 27
    assert summary["strata"] == {"0_faces": 1, "1_face": 6, "2_faces": 12, "3_faces": 8}
    assert summary["non_origin_count"] == 26
    assert summary["total_point_face_incidences"] == 54
    assert summary["face_count"] == 6
    assert summary["each_face_size"] == 9
    assert summary["pairwise_face_overlaps"] == 12
    assert summary["each_edge_overlap_size"] == 3
    assert summary["corner_face_triples"] == 8
    assert summary["each_corner_triple_intersection_size"] == 1
    assert summary["three_selected_cubie_choices"] == 19683
    assert summary["boundary"]["selection_alone_determines_face_gluing"] is False
    assert summary["boundary"]["geometry_alone_defines_an_iit_tpm"] is False
    print("IIT pointed-27 gluing scan: PASS")


if __name__ == "__main__":
    main()
