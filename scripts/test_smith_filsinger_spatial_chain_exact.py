#!/usr/bin/env python3
"""Independent exact integer checks for the Agda all-N spatial port chain.

Only source-equivalent model tests; these do NOT type-check Agda. One cell's
outgoing flux must exactly equal the next cell's incoming flux. No source work
is inferred from a phasor or electromagnetic signal observation.
"""
from dataclasses import dataclass
from random import Random
import pytest

@dataclass(frozen=True)
class Cell:
    incoming:int
    outgoing:int
    driver:int
    initial:int
    load:int
    loss:int
    final:int

    def valid(self):
        return (min(self.__dict__.values())>=0 and
            self.incoming+self.driver+self.initial ==
            self.outgoing+self.load+self.loss+self.final)

def random_chain(rng,n,start):
    flow=start
    cells=[]
    for _ in range(n):
        driver=rng.randint(0,50)
        stored=rng.randint(0,50)
        remaining=flow+driver+stored
        load=rng.randint(0,remaining)
        remaining-=load
        loss=rng.randint(0,remaining)
        remaining-=loss
        final=rng.randint(0,remaining)
        remaining-=final
        cell=Cell(flow,remaining,driver,stored,load,loss,final)
        assert cell.valid()
        cells.append(cell)
        flow=remaining
    return cells

def chain_balance(cells,start,end):
    if any(not cell.valid() for cell in cells):return False
    if not cells:return start==end
    if cells[0].incoming!=start or cells[-1].outgoing!=end:return False
    if any(a.outgoing!=b.incoming for a,b in zip(cells,cells[1:])):
        return False
    return (start+sum(c.driver+c.initial for c in cells) ==
            end+sum(c.load+c.loss+c.final for c in cells))

@pytest.mark.parametrize('n',[0,1,2,3,5,8,16,32,64])
def test_all_n_source_equivalent_spatial_balance(n):
    rng=Random(369+n)
    for start in range(0,10):
        for _ in range(10):
            cells=random_chain(rng,n,start)
            end=cells[-1].outgoing if cells else start
            assert chain_balance(cells,start,end)
            assert sum(c.load for c in cells)<=start+sum(c.driver+c.initial for c in cells)

def test_two_cell_agda_witness():
    c=[Cell(10,8,1,2,2,1,2),Cell(8,6,0,1,1,1,1)]
    assert chain_balance(c,10,6)
    assert sum(x.load for x in c)==3

def test_forged_shared_port_rejected():
    c=[Cell(10,8,1,2,2,1,2),Cell(8,6,0,1,1,1,1)]
    forged=[c[0],Cell(7,5,0,1,1,1,1)]
    assert not chain_balance(forged,10,5)

@pytest.mark.parametrize('n',[0,1,4,32])
def test_source_free_zero_stored_cannot_load(n):
    c=[Cell(0,0,0,0,0,0,0) for _ in range(n)]
    assert chain_balance(c,0,0)
    assert sum(x.load for x in c)==0

def test_storage_drawdown_does_not_count_as_replenishment():
    c=[Cell(0,0,0,9,8,1,0)]
    assert chain_balance(c,0,0)
    assert sum(x.load for x in c)==8
    assert c[0].initial!=c[0].final

def test_nonzero_outgoing_work_is_counted_not_hidden():
    c=[Cell(10,8,1,2,2,1,2)]
    assert chain_balance(c,10,8)
    assert c[0].outgoing>0
