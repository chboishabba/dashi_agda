#!/usr/bin/env python3
"""Reference regression of original 27-cube X/Y dialectic -> Z interaction.

Source ownership: DASHI.Reasoning.TernaryComparisonSynthesisExact owns
Comparison9/SynthesisChoice27; the geometric role rechart is the
DASHI.Reasoning.DialecticXYInteractionZTransportExact adapter.

X, Y and Z refer to *dialectical positions*, never signed proposition
evidence, legal judgments or the three-cube T^9 evidence chart.
"""
import itertools
import json

ROLES = ("thesis", "antithesis", "synthesis")
GROUNDS = (
    "advice-consideration", "recovery-plan", "incremental-habitat",
    "comment-transmission", "approval-scope", "local-prestart",
    "improper-influence",
)

def encode(x, y, z):
    """Existing canonical TriTruth × TriTruth × TriTruth indexing."""
    return ROLES.index(x) * 9 + ROLES.index(y) * 3 + ROLES.index(z)

def decode(index):
    return (ROLES[index // 9], ROLES[(index // 3) % 3], ROLES[index % 3])

def verify():
    cells = list(itertools.product(ROLES, repeat=3))
    assert len(cells) == 27
    assert len({encode(*c) for c in cells}) == 27
    assert all(decode(encode(*c)) == c for c in cells)
    xy_plane = list(itertools.product(ROLES, repeat=2))
    assert len(xy_plane) == 9
    for x, y in xy_plane:
        column = [(x, y, z) for z in ROLES]
        assert len(column) == 3
        assert all(c[:2] == (x, y) for c in column)
        assert tuple(c[-1] for c in column) == ROLES
        assert [encode(*c) for c in column] == list(
            range(encode(x, y, "thesis"), encode(x, y, "thesis") + 3))
        # A proposed Z stage is not a function of XY without an explicit rule.
        assert column[0][:2] == column[2][:2]
        assert column[0][2] != column[2][2]
        # The given Z-stage path is only a possible within-column sequence.
        assert [c[2] for c in column] == list(ROLES)

    for x in ROLES:
        for y in ROLES:
            for z in ROLES:
                c = decode(encode(x, y, z))
                assert c[0] == x and c[1] == y and c[2] == z

    return {
        "status": "passed",
        "case_ground_count": len(GROUNDS),
        "xy_encounter_count_per_ground": len(xy_plane),
        "z_options_for_each_xy": len(ROLES),
        "possible_cells_per_ground": len(cells),
        "possible_cells_across_seven_grounds": len(GROUNDS) * len(cells),
        "current_actual_xyz_positions_established": False,
        "z_from_xy_without_mediation": False,
        "signed_claim_support_is_axis_coordinate": False,
        "triadic_face_paid": False,
        "court_merits_established": False,
        "agda_kernel_typechecked_here": False,
    }

if __name__ == "__main__":
    print(json.dumps(verify(), indent=2, sort_keys=True))
