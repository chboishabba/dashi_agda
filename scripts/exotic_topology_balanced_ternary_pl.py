#!/usr/bin/env python3
"""Real genus-zero 1->3 finite PL cobordism from TWO ordinary pants.

Exact prior-art owners:
  DASHI.Topology.TernaryCylinderPantsGeometryExact (composed 1->3);
  DASHI.Topology.TernaryPantsFrontierExact (ternary prefix / path);
  DASHI.Algebra.Trit / DASHI.Codec.BalancedTritBitFibre (neg/zero/pos);
  scripts/exotic_topology_pl_surface_gluings.py (literal triangles);
  scripts/exotic_topology_pl_frontier_lineage.py (marked frontiers);
  scripts/exotic_topology_pl_complement_components.py (old-subcomplex,
       exterior dual components and geometric child identification).

This file supplies the missing FINITE geometric consumer, not a second
pants library: first PANTS creates outputs '-1' and a temporary
continuation, then a second PANTS splits that continuation into 0,+1.
The temporary connecting circle is NOT an end, not balanced zero,
and does NOT survive as an outgoing frontier. The total cobordism has
four boundary circles (one incoming, three outgoing) and Euler -2.

The existing 369 digits are explicitly identified as:
  digit3 -> neg (-1) -> binary code 0,
  digit6 -> zero (0) -> binary code 10,
  digit9 -> pos (+1) -> binary code 11.
This is a CHOSEN code, not 3/6/9 arithmetic or a measure equality.
The resulting product Cantor topologies are homeomorphic; fair-bit
measure is not uniform ternary measure (negative digit mass 1/2,
zero and positive 1/4). No embedded 3D wildness or Richards end
homeomorphism is proven by this finite source.

Original literature: classical compact orientable surfaces, H. R.
Brahana (1921); infinite-surface classification Kerékjártó (1923),
Ian Richards (1963); coding theory is classical.
"""
from itertools import product, combinations
from fractions import Fraction
import json

from exotic_topology_pl_frontier_lineage import (
    mark_initial, attach,
)
from exotic_topology_pl_surface_gluings import (
    disk, sphere_with_holes, inspect, boundary_loops,
)
from exotic_topology_pl_complement_components import (
    verify_complement_components,
)

BRANCHES = (-1, 0, 1)
CODE = {-1: (0,), 0: (1, 0), 1: (1, 1)}
DIGIT369 = {-1: 3, 0: 6, 1: 9}
SIGN_INVERSION = {-1: 1, 0: 0, 1: -1}
CYCLIC_C3 = {-1: 0, 0: 1, 1: -1}


def encode_balanced_word(word):
    return tuple(bit for digit in word for bit in CODE[digit])


def decode_complete_binary_word(bits):
    out, i = [], 0
    while i < len(bits):
        if bits[i] == 0:
            out.append(-1)
            i += 1
        else:
            if i + 1 == len(bits):
                return None  # one unfinished '1' bit is NOT a full trit
            out.append(0 if bits[i + 1] == 0 else 1)
            i += 2
    return tuple(out)


def attach_one_ternary(stage, piece, parent):
    """Exactly two source-owned ordinary pants, one 3-output cobordism."""
    temporary = parent + ("continuation",)
    first, old_to_first = attach(
        stage, piece, parent, (parent + (-1,), temporary),
        with_transport=True,
    )
    assert temporary in first.frontier
    second, first_to_second = attach(
        first, piece, temporary, (parent + (0,), parent + (1,)),
        with_transport=True,
    )
    assert temporary not in second.frontier
    assert all(parent + (d,) in second.frontier for d in BRANCHES)
    old_to_second = {v: first_to_second[w] for v, w in old_to_first.items()}
    assert len(set(old_to_second.values())) == len(old_to_second)
    return second, old_to_second


def transition(stage, piece, with_transport=False):
    old_stage = stage
    parents = tuple(sorted(old_stage.frontier))
    # The old stage embeds through the COMPLETE sequence of two-pants
    # attachments at every old outgoing frontier; none of the
    # temporary branch circles is selected as a next-stage parent.
    full_embedding = {
        v: v for tri in old_stage.mesh.triangles for v in tri
    }
    for parent in parents:
        stage, embedding = attach_one_ternary(stage, piece, parent)
        full_embedding = {
            v: embedding[current] for v, current in full_embedding.items()
        }
    expected = {p + (d,) for p in parents for d in BRANCHES}
    assert set(stage.frontier) == expected
    receipt = verify_complement_components(
        old_stage, stage, full_embedding, "balanced_ternary"
    )
    assert receipt["components"] == len(parents)
    assert receipt["new_boundaries"] == 3 * len(parents)
    return ((stage, receipt, full_embedding) if with_transport
            else (stage, receipt))




def depth_three_cube_sibling_nonpromotion():
    """Finite same SET of 27 labels, DIFFERENT selected edge relations.

    Native cube source: Base369Ternary27HypervoxelFabricGeometryExact:
      an edge changes ONE coordinate by one step -1<->0<->1.
    Here 'sibling' is an OPTIONAL comparison of two depth-three
    paths with equal first TWO digits, not an intrinsic edge of the
    compact surface itself. These graph edges cannot be conflated.
    """
    vertices = list(product(BRANCHES, repeat=3))
    def ordered(u, v):
        return tuple(sorted((u, v)))
    grid = set()
    for v in vertices:
        for axis in range(3):
            for move in (-1, 1):
                nxt = list(v)
                nxt[axis] += move
                if nxt[axis] in BRANCHES:
                    grid.add(ordered(v, tuple(nxt)))
    siblings = set()
    for prefix in product(BRANCHES, repeat=2):
        kids = [prefix + (digit,) for digit in BRANCHES]
        for left, right in combinations(kids, 2):
            siblings.add(ordered(left, right))
    assert len(vertices) == 27
    assert len(grid) == 54
    assert len(siblings) == 27
    assert len(siblings.intersection(grid)) == 18
    assert len(siblings - grid) == 9
    assert len(grid - siblings) == 36
    assert ordered((0, 0, -1), (0, 0, 1)) in siblings - grid
    return {"same_underlying_label_count": 27,
            "native_cube_grid_edges": 54,
            "optional_parent_sibling_pairs": 27,
            "shared_pairs": 18,
            "sibling_non_grid_pairs": 9,
            "grid_non_sibling_pairs": 36,
            "cube_graph_equivalence_claim": False,
            "surface_homeomorphism_claim": False}

def audit(depth=3):
    assert 0 <= depth <= 4, "bounded exact finite source audit only"
    pants = sphere_with_holes(3)
    stage = mark_initial(disk(), [()])
    fixtures = []
    for n in range(depth + 1):
        stage_receipt = stage.verify((0, 3**n))
        all_words = set(product(BRANCHES, repeat=n))
        assert set(stage.frontier) == all_words
        # Every 369 word at the same trit depth decodes exactly; its
        # binary word can have a VARIABLE 1..2 bits per trit.
        for word in all_words:
            binary = encode_balanced_word(word)
            assert decode_complete_binary_word(binary) == word
            assert n <= len(binary) <= 2*n
        fixtures.append({
            "depth": n,
            "genus": stage_receipt["genus"],
            "boundary_count": stage_receipt["boundaries"],
            "all_boundary_words_exact": True,
            "vertex_links_verified": stage_receipt["vertex_links_verified"],
        })
        if n < depth:
            stage, receipt = transition(stage, pants)
            assert receipt["components"] == 3**n
            fixtures[-1]["new_attached_components"] = receipt["components"]
            fixtures[-1]["old_subcomplex_embedding"] = receipt["same_object_old_inclusion"]
    assert decode_complete_binary_word((1,)) is None
    assert all(SIGN_INVERSION[SIGN_INVERSION[t]] == t for t in BRANCHES)
    assert SIGN_INVERSION[0] == 0 and CYCLIC_C3[0] != 0
    assert SIGN_INVERSION != CYCLIC_C3
    assert sum((Fraction(1, 2**len(bits)) for bits in CODE.values()), Fraction()) == 1
    return {
        "family": "balanced_ternary_three_end_branching",
        "depth": depth,
        "stages": fixtures,
        "physical_pants_per_old_frontier": 2,
        "depth_three_label_graph_discriminator": depth_three_cube_sibling_nonpromotion(),
        "new_outgoing_boundaries_per_frontier": 3,
        "one_to_three_cobordism_euler": -2,
        "balanced_zero_fixed_by_sign_inversion": True,
        "sign_reflection_is_not_c3_rotation": True,
        "binary_to_ternary_measure_preservation_claim": False,
        "topological_infinite_end_space_homeomorphism_proved": False,
        "agda_or_lean_kernel_verified": False,
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
