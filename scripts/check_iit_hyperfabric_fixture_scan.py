#!/usr/bin/env python3
from __future__ import annotations

from iit_hyperfabric_fixture_scan import fixture_summary


def main() -> None:
    summary = fixture_summary()
    fixtures = summary["fixtures"]
    assert fixtures["open_xor_path"]["iit_4_0_2023"]["distinct_phi_s"] == [0.0]
    assert fixtures["closed_xor_cycle"]["iit_4_0_2023"]["distinct_phi_s"] == [2.0]
    assert fixtures["xor_grid_2x2"]["iit_4_0_2023"]["distinct_phi_s"] == [0.0, 0.5]
    assert fixtures["closed_trixor_cycle"]["iit_4_0_2023"]["distinct_phi_s"] == [3.169925001442]
    assert summary["partition_semantics"] == [
        "causal_graph_connection_partition",
        "stalk_restriction_partition",
        "global_section_partition",
    ]
    assert summary["boundary"]["these_partition_semantics_are_definitionally_identical"] is False
    assert summary["boundary"]["pants_seam_rewrites_hyperfabric_incidence_automatically"] is False
    print("IIT hyperfabric fixture scan: PASS")


if __name__ == "__main__":
    main()
