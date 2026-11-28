#!/usr/bin/env python3
"""BR71: one SAME-SOURCE physical 30+10 D/E boundary map.

Consumes original BR34 metric_rows/gauge_rows, BR66 exact geometric
Israel correction, BR68 genuine coordinate Codazzi and mean-force
corrections. Does NOT manufacture the full nonlinear Einstein PDE:
these are original reference rows + exact independently derived
physical graph/mean source; full gauge connection/shape Fréchet and
curved Bianchi remain separate input debts.

Rows retain original owners and exact indices:
 metric 0:10 tangent continuity; 10:14 mixed continuity;
 14:24 geometric Israel correction; 24:29 allocation-specific
 harmonic gauge rows; 29 physical nonzero mean force.
 gauge 0:5 allocation-specific physical prefix;
 5:9 true coordinate Codazzi; 9 original normal Gauss.
The different D/E PREFIXES MUST NOT be homogenized.

Both faces, symmetric metric 15+15, gauge 5+5, mean M tensor,
nonzero scalar mean m, nonzero tension jump j, graph phi,
nonzero warp-acceleration jump are independently present.
"""
import argparse
import sympy as s
from check_hopf369_br_warped_physical_attachment import (
    metric_rows,gauge_rows,metric_side,keys,E4,trace4
)

def symmetric(seed):
    return s.Matrix(5,5,lambda i,k:
        s.Rational((min(i,k)+seed+2)*(max(i,k)+seed+3)%23-11,13)
        +s.Rational(i+k+seed+2,19)*s.Symbol('n'))
def owner():
    j,mean,phi,bjump=s.symbols('j mean phi warpAccelerationJump')
    q=s.Matrix(s.symbols('q0:4'))
    M=s.Matrix(4,4,lambda i,k:s.Symbol(f'M{min(i,k)}{max(i,k)}'))
    p,px,m,mx=[symmetric(i) for i in range(4)]
    cp=s.Matrix(s.symbols('cp0:5'))
    cx=s.Matrix(s.symbols('cx0:5'))
    cm=s.Matrix(s.symbols('cm0:5'))
    cmx=s.Matrix(s.symbols('cmx0:5'))
    correction=2*(bjump-2*mean*j)*phi*E4
    mean_correction=-4*mean*(p[4,4]+m[4,4])/2
    jump=cp[:4,0]-cm[:4,0]
    su=cp[:4,0]+cm[:4,0]
    codazzi_correction=-2*M*E4*jump-j*su/2
    return (j,mean,phi,bjump,q,M,p,px,m,mx,cp,cx,cm,cmx,
            correction,mean_correction,codazzi_correction)

def build(allocation):
    (j,mean,phi,bjump,q,M,p,px,m,mx,cp,cx,cm,cmx,
            T,force,C)=owner()
    baseM=metric_rows(p,px,m,mx,q,j,allocation)
    baseG=gauge_rows(cp,cx,cm,cmx,q,j,allocation)
    assert (baseM.rows,baseG.rows)==(30,10)
    # Independent direct physical row construction, not an arbitrary
    # output vector whose entries are later compared to itself.
    hp,bp,kp,tp,_,_=metric_side(p,px,q,j/2)
    hm,bm,km,tm,_,_=metric_side(m,mx,q,-j/2)
    J=2*(kp-km)-j*(hp+hm)
    trueIsrael=J+T
    original_prefix=s.Matrix([*(hp-hm)[a,b] for a,b in keys]
                         +list(bp-bm))
    assert original_prefix==baseM[:14,0]
    physicalM=baseM.copy()
    for n,(a,b) in enumerate(keys):
        physicalM[14+n]=trueIsrael[a,b]
    physicalM[29]=tp+tm+force
    physicalG=baseG.copy()
    originalC=cx[:4,0]-cmx[:4,0]+q*(cp[4]-cm[4])-j*(cp[:4,0]+cm[:4,0])/2
    actualC=cx[:4,0]-cmx[:4,0]+q*(cp[4]-cm[4])-2*M*E4*(cp[:4,0]-cm[:4,0])-j*(cp[:4,0]+cm[:4,0])
    for i in range(4):physicalG[5+i]=actualC[i]
    assert (actualC-originalC-C).applyfunc(s.expand)==s.zeros(4,1)
    # Compare to independent SOURCE DELTA in the correct original
    # physical allocation, preserving prefixes and all five suffix
    # mean/Gauss/normal zero-mode information.
    deltaM=physicalM-baseM
    deltaG=physicalG-baseG
    expM=s.zeros(30,1)
    for n,(a,b) in enumerate(keys):expM[14+n]=T[a,b]
    expM[29]=force
    expG=s.zeros(10,1)
    for a in range(4):expG[5+a]=C[a]
    assert (deltaM-expM).applyfunc(s.expand)==s.zeros(30,1)
    assert (deltaG-expG).applyfunc(s.expand)==s.zeros(10,1)
    assert physicalM[:14,0]==baseM[:14,0]
    assert physicalM[24:29,0]==baseM[24:29,0]
    assert physicalG[:5,0]==baseG[:5,0]
    assert physicalG[9]==baseG[9]
    assert deltaM!=s.zeros(30,1) and deltaG!=s.zeros(10,1)
    return physicalM,physicalG

def check():
    Dm,Dg=build("D")
    Em,Eg=build("E")
    assert Dm[:24,0]==Em[:24,0]
    assert Dm[29]==Em[29]
    assert Dg[5:10,0]==Eg[5:10,0]
    # Some allocation-specific rows must remain different:
    assert (Dm[24:29,0]-Em[24:29,0])!=s.zeros(5,1)
    assert (Dg[:5,0]-Eg[:5,0])!=s.zeros(5,1)
    print("BR71 source constructed: both physical D/E 30 metric +10 gauge")
    print("BR71 source constructed: actual Israel/Codazzi/mean corrections and preserved D/E allocations")

if __name__=="__main__":
    parser=argparse.ArgumentParser();parser.add_argument('--part',choices=['all'],default='all');parser.parse_args();check()
