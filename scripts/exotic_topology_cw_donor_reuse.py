#!/usr/bin/env python3
"""Exact cellular-chain donor audit for DASHI's existing finite CW work.

Classical CW chains (Whitehead/Hatcher); finite cellular CP1/S2 rational H2
already in ProjectiveLineCellularH2Exact and existing generic cochains in
FiniteCochainComplexExact. Independent exact chain arithmetic, NOT an Agda
kernel proof or a realisation of an arbitrary CW quotient topology.
"""
from dataclasses import dataclass
import json
import sympy as S
from sympy.matrices.normalforms import smith_normal_form
from sympy.polys.domains import ZZ

@dataclass(frozen=True)
class CW2:
    name: str
    n0: int
    n1: int
    n2: int
    boundary1: tuple[tuple[int,...],...]
    boundary2: tuple[tuple[int,...],...]
    expected_betti: tuple[int,int,int]
    expected_torsion_h1: tuple[int,...] = ()

    def verify(self):
        assert self.n0 >= 1 and self.n1 >= 0 and self.n2 >= 0
        d1=S.Matrix(self.n0,self.n1,lambda i,j:self.boundary1[i][j])
        d2=S.Matrix(self.n1,self.n2,lambda i,j:self.boundary2[i][j])
        assert all(x==0 for x in d1*d2),(self.name,'d1 d2 nonzero')
        r1,r2=d1.rank(),d2.rank()
        betti=(self.n0-r1, self.n1-r1-r2, self.n2-r2)
        assert betti==self.expected_betti,(self.name,betti,self.expected_betti)
        torsion=()
        if d1.is_zero_matrix:
            smith=smith_normal_form(d2,domain=ZZ)
            torsion=tuple(sorted(abs(int(smith[i,i])) for i in range(min(*smith.shape))
                                 if abs(int(smith[i,i]))>1))
            assert torsion==self.expected_torsion_h1,(self.name,torsion)
        else:
            assert not self.expected_torsion_h1
        return {'cells':(self.n0,self.n1,self.n2),'betti':betti,
                'h1_torsion':torsion,'d_squared_zero':True}

def zeros(rows,cols): return tuple(tuple(0 for _ in range(cols)) for _ in range(rows))

def single_vertex(name,n1,n2,d2,betti,torsion=()):
    return CW2(name,1,n1,n2,zeros(1,n1),
               tuple(tuple(row) for row in d2),betti,torsion)

def main():
    fixtures=[
      single_vertex('point',0,0,[],(1,0,0)),
      single_vertex('circle',1,0,[[]],(1,1,0)),
      single_vertex('sphere: existing CP1 donor',0,1,[],(1,0,1)),
      single_vertex('torus: [a,b] attaching degree zero',2,1,[[0],[0]],(1,2,1)),
      single_vertex('pinched torus: collapse primitive a',1,1,[[0]],(1,1,1)),
      single_vertex('real projective plane: attach degree two',1,1,[[2]],(1,0,0),(2,)),
      single_vertex('Moore space M(Z/3,1)',1,1,[[3]],(1,0,0),(3,)),
      single_vertex('pair of pants: spine',2,0,[[],[]],(1,2,0)),
      single_vertex('genus-one two-boundary cobordism spine',3,0,[[],[],[]],(1,3,0)),
      CW2('unit interval',2,1,0,((-1,),(1,)),((),),(1,0,0)),
      CW2('filled oriented triangle',3,3,1,
          ((-1,0,-1),(1,-1,0),(0,1,1)),((1,),(1,),(-1,)),(1,0,0)),
    ]
    result={f.name:f.verify() for f in fixtures}
    for family in ('cantor_tree','loch_ness_monster','jacobs_ladder'):
        for n in range(0,13):
            if family=='cantor_tree':genus,boundaries=0,2**n
            elif family=='loch_ness_monster':genus,boundaries=n,1
            else: genus,boundaries=2*n,2
            chi=2-2*genus-boundaries
            # Surface with boundary retracts to finite 1D CW spine of rank:
            rank=2*genus+boundaries-1
            assert 1-rank==chi
            if n in (0,1,6,12):
                result[f'{family}:depth{n}']={'genus':genus,'boundary_count':boundaries,
                    'cellular_graph_rank':rank,'euler':chi,'topological_retraction_proved':False}
    print(json.dumps({'result':result,
      'status':'PASS exact integer chain and torsion fixtures; CW topological realisation NOT claimed'},
      indent=2,sort_keys=True))

if __name__=='__main__':main()
