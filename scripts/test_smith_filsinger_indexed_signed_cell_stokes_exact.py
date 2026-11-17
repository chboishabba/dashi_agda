#!/usr/bin/env python3
"""Exact rational per-cell signed face Stokes test.

The signed oriented work of each internal face is added at its source,
subtracted at its target. The net over all cells is zero for any valid
endpoint-indexed finite directed graph, independent of circulation.
This is NOT physical Maxwell integration or measured VI work.
"""
from fractions import Fraction as Q
from random import Random
import pytest
from test_smith_filsinger_indexed_face_incidence_exact import (
    Face, check_indexed
)
from test_smith_filsinger_finite_volume_face_incidence_exact import (
    mesh_faces_and_cells
)

def indexed_signed_cell_ledger(node_ids,faces,flux):
    assert len(faces)==len(flux)
    return {
      node:sum((a for face,a in zip(faces,flux) if face.source==node),Q(0))
          -sum((a for face,a in zip(faces,flux) if face.target==node),Q(0))
      for node in node_ids
    }

@pytest.mark.parametrize("nodes",[0,1,2,3,5,8,16,32])
def test_512_strict_meshes_exact_signed_cell_face_cancellation(nodes):
    rng=Random(668+nodes)
    for _ in range(64):
        edges=[]
        if nodes>1:
            for k in range(nodes*3):
                source=rng.randrange(nodes)
                target=(source+rng.randrange(1,nodes))%nodes
                edges.append((source,target,rng.randrange(25)))
        cells,_=mesh_faces_and_cells(nodes,edges,rng)
        faces=[Face(k+100,s,t,w) for k,(s,t,w) in enumerate(edges)]
        assert check_indexed(cells,list(range(nodes)),faces)
        signed_flux=[Q(rng.randrange(-17,18),rng.randrange(1,15))
                     for _ in faces]
        budget=indexed_signed_cell_ledger(list(range(nodes)),faces,signed_flux)
        assert sum(budget.values(),Q(0))==0

def test_strict_branch_redistributes_without_generation():
    f=[Face(11,0,1,2),Face(12,0,2,3)]
    x=indexed_signed_cell_ledger([0,1,2],f,[Q(7,5),Q(-11,3)])
    assert x[0]==Q(7,5)-Q(11,3)
    assert x[1]==-Q(7,5)
    assert x[2]==Q(11,3)
    assert sum(x.values(),Q(0))==0

def test_nontrivial_cycle_has_zero_total_signed_energy():
    f=[Face(1,0,1,1),Face(2,1,2,1),Face(3,2,0,1)]
    b=indexed_signed_cell_ledger([0,1,2],f,[Q(3,4)]*3)
    assert b=={0:Q(0),1:Q(0),2:Q(0)}

def test_per_cell_wrong_face_direction_is_detectable():
    f=[Face(7,0,1,3)]
    correct=indexed_signed_cell_ledger([0,1],f,[Q(9,7)])
    assert correct=={0:Q(9,7),1:Q(-9,7)}
    wrong={0:Q(9,7),1:Q(9,7)}
    assert sum(wrong.values(),Q(0))!=0

def test_no_source_energy_is_inferred_from_internal_flux():
    f=[Face(7,0,1,0)]
    b=indexed_signed_cell_ledger([0,1],f,[Q(4)])
    assert sum(b.values(),Q(0))==0
    assert b[0]>0 and b[1]<0
    # A nonzero internal field flux can circulate, but supplies no
    # independently verified exterior natural-work receipt.
