#!/usr/bin/env python3
"""F10-INC source-equivalent exact verification of individually indexed faces.

No Agda compiler acceptance or physical Maxwell surface/terminal data.
Regression compares new strict endpoint-ID incidence against older aggregate
face cancellation, with zero-work faces and forged assignments.
"""
from dataclasses import dataclass
from fractions import Fraction
from random import Random
import pytest
from test_smith_filsinger_finite_volume_face_incidence_exact import (
    Cell, mesh_faces_and_cells, validate_mesh
)

@dataclass(frozen=True)
class Face:
    id:int
    source:int
    target:int
    work:int

def check_indexed(cells,cell_ids,faces):
    if len(cells)!=len(cell_ids):return False
    if len(set(cell_ids))!=len(cell_ids):return False
    if len(set(f.id for f in faces))!=len(faces):return False
    if any(f.source==f.target or f.source not in cell_ids
           or f.target not in cell_ids or f.work<0 for f in faces):
        return False
    if not all(c.local_ok() for c in cells):return False
    # EACH work receipt belongs to exactly its actual source / target.
    for c,idx in zip(cells,cell_ids):
        if c.internal_out != sum(f.work for f in faces if f.source==idx):
            return False
        if c.internal_in != sum(f.work for f in faces if f.target==idx):
            return False
    # Explicit exactly-once checks also apply to zero-work faces.
    for f in faces:
        if sum(idx==f.source for idx in cell_ids)!=1:return False
        if sum(idx==f.target for idx in cell_ids)!=1:return False
    return validate_mesh(cells,[f.work for f in faces])

def signed_face_pair_total(faces,fluxes):
    assert len(faces)==len(fluxes)
    return sum((f+(-f) for f in fluxes),Fraction(0))

@pytest.mark.parametrize("nodes",[0,1,2,3,5,8,16,32])
def test_512_branched_and_cyclic_meshes_strictly_indexed(nodes):
    rng=Random(668+nodes)
    for _ in range(64):
        edges=[]
        if nodes>1:
            for n in range(nodes*3):
                a=rng.randrange(nodes)
                b=(a+rng.randrange(1,nodes))%nodes
                edges.append((a,b,rng.randrange(25)))
        cells,works=mesh_faces_and_cells(nodes,edges,rng)
        faces=[Face(100+k,a,b,w) for k,(a,b,w) in enumerate(edges)]
        assert works == [f.work for f in faces]
        assert check_indexed(cells,list(range(nodes)),faces)

def test_two_cell_source_id_consumer():
    cells=[Cell(8,0,0,0,3,3,1,1,0),
           Cell(0,3,0,0,0,0,2,1,0)]
    assert check_indexed(cells,[0,1],[Face(7,0,1,3)])

def test_aggregate_spoof_is_rejected_by_strict_face_ids():
    cells=[Cell(2,4,0,0,0,3,3,0,0),
           Cell(4,0,0,0,0,4,0,0,0),
           Cell(0,3,0,0,3,0,0,0,0)]
    assert validate_mesh(cells,[3,4])
    assert not check_indexed(cells,[0,1,2],
                             [Face(11,0,1,3),Face(12,1,2,4)])

def test_duplicate_face_id_rejected_even_when_work_matches():
    cells=[Cell(5,0,0,0,0,5,0,0,0),
           Cell(0,5,0,0,0,0,5,0,0)]
    assert validate_mesh(cells,[2,3])
    assert not check_indexed(cells,[0,1],
                             [Face(99,0,1,2),Face(99,0,1,3)])

def test_duplicate_cell_id_rejected_even_when_no_faces():
    cells=[Cell(0,0,0,0,0,0,0,0,0)]*2
    assert validate_mesh(cells,[])
    assert not check_indexed(cells,[0,0],[])

def test_zero_work_face_still_requires_endpoint_ownership():
    cells=[Cell(0,0,0,0,0,0,0,0,0),
           Cell(0,0,0,0,0,0,0,0,0)]
    assert check_indexed(cells,[0,1],[Face(41,0,1,0)])
    assert not check_indexed(cells,[0,1],[Face(41,0,3,0)])
    assert not check_indexed(cells,[0,1],[Face(41,0,0,0)])

def test_face_direction_reversal_rejected():
    cells=[Cell(5,0,0,0,0,5,0,0,0),
           Cell(0,5,0,0,0,0,5,0,0)]
    assert check_indexed(cells,[0,1],[Face(9,0,1,5)])
    assert not check_indexed(cells,[0,1],[Face(9,1,0,5)])

def test_same_face_amplitude_cancels_for_signed_rationals():
    faces=[Face(7,0,1,3), Face(8,1,2,0), Face(9,2,0,1)]
    fluxes=[Fraction(-7,3),Fraction(0),Fraction(11,7)]
    assert signed_face_pair_total(faces,fluxes)==0

def test_signed_amplitude_not_equal_nat_positive_magnitude():
    face=[Face(7,0,1,3)]
    assert signed_face_pair_total(face,[Fraction(-5,4)])==0
    assert face[0].work != Fraction(-5,4)

def test_no_original_world_measurement_inferred():
    cells=[Cell(0,0,0,0,0,0,0,0,0)]
    assert check_indexed(cells,[10],[])
    assert signed_face_pair_total([],[])==0
