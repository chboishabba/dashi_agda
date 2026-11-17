#!/usr/bin/env python3
"""Exact nonnegative finite-volume incidence model: branches and cycles.

A LOCAL cell equality and a matched face-incidence list are BOTH mandatory.
This is NOT a Yee/FDTD Maxwell solver nor a measured environmental source.
"""
from dataclasses import dataclass
from random import Random
import pytest

@dataclass(frozen=True)
class Cell:
    exterior_in:int
    internal_in:int
    driver:int
    initial:int
    exterior_out:int
    internal_out:int
    load:int
    loss:int
    final:int
    def local_ok(self):
        return min(vars(self).values())>=0 and (
            (self.exterior_in+self.internal_in)+(self.driver+self.initial)
            == (self.exterior_out+self.internal_out)
               +(self.load+self.loss+self.final))

def mesh_faces_and_cells(nodes, edges, rng):
    assert nodes>=0
    int_in=[0]*nodes
    int_out=[0]*nodes
    for src,dst,work in edges:
        assert 0<=src<nodes and 0<=dst<nodes and src!=dst and work>=0
        int_out[src]+=work
        int_in[dst]+=work
    cells=[]
    for k in range(nodes):
        drive,initial,load,loss,final=(rng.randrange(12) for _ in range(5))
        deficit=(int_out[k]+load+loss+final)-(int_in[k]+drive+initial)
        extin=max(deficit,0)
        extout=max(-deficit,0)
        cells.append(Cell(extin,int_in[k],drive,initial,
                          extout,int_out[k],load,loss,final))
    return cells,[w for _,_,w in edges]

def validate_mesh(cells,faces):
    if not all(c.local_ok() for c in cells):return False
    if sum(c.internal_in for c in cells)!=sum(faces):return False
    if sum(c.internal_out for c in cells)!=sum(faces):return False
    return (sum(c.exterior_in+c.driver+c.initial for c in cells)
            ==sum(c.exterior_out+c.load+c.loss+c.final for c in cells))

@pytest.mark.parametrize("nodes",[0,1,2,3,5,8,16,32])
def test_arbitrary_mesh_branch_and_cycle_face_cancellation(nodes):
    rng=Random(668+nodes)
    for repetition in range(64):
        count=nodes*3 if nodes>1 else 0
        edges=[]
        for _ in range(count):
            src=rng.randrange(nodes)
            dst=(src+rng.randrange(1,nodes))%nodes
            edges.append((src,dst,rng.randrange(25)))
        cells,faces=mesh_faces_and_cells(nodes,edges,rng)
        assert validate_mesh(cells,faces)

def test_nonempty_two_cell_original_agda_witness():
    cells=[Cell(8,0,0,0,3,3,1,1,0),
           Cell(0,3,0,0,0,0,2,1,0)]
    assert validate_mesh(cells,[3])

def test_mismatched_face_flux_fails_closed():
    rng=Random(7)
    cells,faces=mesh_faces_and_cells(4,[(0,1,3),(1,2,9)],rng)
    assert validate_mesh(cells,faces)
    assert not validate_mesh(cells,[faces[0],faces[1]+1])

def test_local_energy_forgery_not_accepted():
    cells=[Cell(8,0,0,0,3,3,1,1,0),
           Cell(0,3,0,0,0,0,3,1,0)]
    assert not validate_mesh(cells,[3])

def test_empty_mesh_zero_external_work():
    assert validate_mesh([],[])

def test_CFL_stability_does_not_prove_strict_physical_cone():
    physical_speed,dx,dt=1,4,1
    assert physical_speed*dt<=dx  # stable 1D Courant form
    assert dx>physical_speed*dt   # one-neighbor stencil has wider support

def test_source_free_internal_circulation_cannot_supply_load():
    # Two branches carry internal traffic with zero external, drive and
    # initial energy. This is not useful source work.
    cells=[Cell(0,5,0,0,0,5,0,0,0),
           Cell(0,5,0,0,0,5,0,0,0)]
    assert validate_mesh(cells,[5,5])
    assert sum(c.load for c in cells)==0

def test_aggregate_totals_not_a_per_cell_face_id_certificate():
    # A declared graph with edges 0->1 (3) and 1->2 (4) has actual
    # incoming per-cell [0,3,4]. Our aggregate-only mesh can instead
    # carry [4,0,3] with the same sum. The current theorem accepts both:
    # F10-INC must verify per-face/per-cell endpoint identity.
    cells=[Cell(2,4,0,0,0,3,3,0,0),
           Cell(4,0,0,0,0,4,0,0,0),
           Cell(0,3,0,0,3,0,0,0,0)]
    assert validate_mesh(cells,[3,4])
    actual_incoming=[0,3,4]
    assert [c.internal_in for c in cells]!=actual_incoming
