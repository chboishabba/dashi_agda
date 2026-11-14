#!/usr/bin/env python3
"""Finite native pants-path adjacency versus 27-voxel one-trit adjacency.

The authored Agda graph module defines the pants adjacency independently
by one BranchSlot move (slot3<->slot6 or slot6<->slot9). This checker
confirms graph transport over ALL 27^2 ordered vertex pairs. It does
not assert smooth pants, physical Rubik motion, or proper colouring
from uniform interface paint.
"""
import itertools
import json

TRITS = (-1, 0, 1)
SLOTS = (3, 6, 9)
voxels = tuple(itertools.product(TRITS, repeat=3))
paths = tuple(itertools.product(SLOTS, repeat=3))
to_path = lambda v: tuple(3*(x+2) for x in v)
to_voxel = lambda p: tuple((x//3)-2 for x in p)

def cube_adj(a,b):
    return sum(x!=y for x,y in zip(a,b)) == 1 and sum(abs(x-y) for x,y in zip(a,b)) == 1

def pants_adj(a,b):
    return sum(x!=y for x,y in zip(a,b)) == 1 and sum(abs(x-y) for x,y in zip(a,b)) == 3

def main():
    assert len(voxels)==len(paths)==27
    assert {to_path(v) for v in voxels}==set(paths)
    assert all(to_voxel(to_path(v))==v for v in voxels)
    assert all(to_path(to_voxel(p))==p for p in paths)
    for a,b in itertools.product(voxels,repeat=2):
        assert cube_adj(a,b)==pants_adj(to_path(a),to_path(b))
    directed=sum(cube_adj(a,b) for a,b in itertools.product(voxels,repeat=2))
    assert directed==108
    assert directed//2==54
    # A constant colour function satisfies equality at two painted
    # interfaces, but is NEVER proper on the 27-grid.
    red=lambda _:0
    assert all(red(a)==red(b) for a,b in itertools.product(voxels,repeat=2))
    assert any(cube_adj(a,b) and red(a)==red(b) for a,b in itertools.product(voxels,repeat=2))
    # Unlike matching face paint, proper graph colouring demands unequal
    # colours on ADJACENT vertices. One explicit 3-colouring example
    # is the C3 sum mod 3 of the three path digits.
    colour=lambda v: sum(x+1 for x in v)%3
    assert all(not cube_adj(a,b) or colour(a)!=colour(b) for a,b in itertools.product(voxels,repeat=2))
    return {
        "result":"passed",
        "vertices":27,
        "ordered_vertex_pairs_checked":27**2,
        "directed_grid_steps":directed,
        "undirected_grid_edges":directed//2,
        "both_directions_graph_homomorphisms":True,
        "exact_vertex_roundtrip":True,
        "constant_face_paint_can_glue_locally":True,
        "constant_face_paint_is_proper_vertex_colouring":False,
        "three_colour_vertex_colouring_exists":True,
        "physical_pants_topology_or_legal_authority_established":False,
        "agda_kernel_checked":False
    }

if __name__=="__main__":
    print(json.dumps(main(),sort_keys=True,indent=2))
