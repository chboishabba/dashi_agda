#!/usr/bin/env python3
from exceptional_e6_e8_hyperfabric import compute_receipt


def main() -> None:
    r = compute_receipt()

    assert r["e6"]["weyl_order"] == 51840
    assert r["e6"]["patch_orbits"] == {"H4": 36, "H3": 120, "H2": 270, "H1": 36}
    assert r["e6"]["patch_stabilizers"] == {"H4": 1440, "H3": 432, "H2": 192, "H1": 1440}
    assert r["e6"]["reflection_cores"] == {"H3": 216, "H2": 96}
    assert r["e6"]["incidence_edges"] == {"H4_H3": 360, "H3_H2": 1080, "H2_H1": 540}
    assert r["e6"]["complete_flags"] == 6480
    assert r["e6"]["complete_flag_stabilizer"] == 8
    assert r["e6"]["a2cube_subsystems"] == 40
    assert r["e6"]["h3_per_a2cube"] == 3
    assert r["e6"]["radical_null_line_indexes_a2cube"] is True
    assert r["e6"]["root_orthogonal_graph_is_KG_6_2"] is True

    assert r["e8"]["symplectic_projective_points"] == 40
    assert r["e8"]["symplectic_projective_lines"] == 40
    assert r["e8"]["root_orbits_order3"] == 80

    assert r["bridge"]["e6_null_to_e8_line_graph_isomorphic"] is True
    assert r["bridge"]["e6_null_to_e8_point_graph_isomorphic"] is False
    assert r["bridge"]["a2cube_to_e8_symplectic_line_graph_isomorphic"] is True


if __name__ == "__main__":
    main()
