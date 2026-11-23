#!/usr/bin/env python3
"""OCT369 P0.13: L12 3c Mn face-centre geometry -> axial STF rank-3 tensor.
The all-out 120-degree spin texture is an explicit trial fixture, NOT a
verified physical PtMn3 domain or the paper's T1g octupole operator.
"""
import json
from itertools import product
import sympy as s
Q=s.Rational
V=s.Matrix
sites=[V([0,Q(1,2),Q(1,2)]),V([Q(1,2),0,Q(1,2)]),V([Q(1,2),Q(1,2),0])]
pt=V([0,0,0])
center=sum(sites,s.zeros(3,1))/3
pos=[v-center for v in sites]
spin=pos[:]
cycle=s.Matrix([[0,1,0],[0,0,1],[1,0,0]])
I=s.eye(3)
idx=list(product(range(3),repeat=3))
def tensor(rs,ms):
    raw=s.MutableDenseNDimArray.zeros(3,3,3)
    for r,m in zip(rs,ms):
        for i,j,k in idx:
            raw[i,j,k]+=sum(m[a]*r[b]*r[d] for a,b,d in
                ((i,j,k),(i,k,j),(j,i,k),(j,k,i),(k,i,j),(k,j,i)))/6
    tr=[sum(raw[i,j,j] for j in range(3)) for i in range(3)]
    T=s.MutableDenseNDimArray.zeros(3,3,3)
    for i,j,k in idx:
        T[i,j,k]=raw[i,j,k]-Q(1,5)*((i==j)*tr[k]+(i==k)*tr[j]+(j==k)*tr[i])
    return T
def shape(T):return tuple(T[i,j,k] for i,j,k in idx)
def rot(T,R):
    out=s.MutableDenseNDimArray.zeros(3,3,3)
    for i,j,k in idx:
        out[i,j,k]=sum(R[i,a]*R[j,b]*R[k,d]*T[a,b,d] for a,b,d in idx)
    return out
H=tensor(pos,spin)
checks=[]
def ok(label,test):
    assert test,label
    checks.append(label)
ok("L12 Pt and three Mn",len(sites)==3 and pt==V([0,0,0]))
ok("Mn in (111) plane",all(sum(v)==1 for v in sites))
ok("centroid",center==V([Q(1,3)]*3))
ok("net spin zero",sum(spin,s.zeros(3,1))==s.zeros(3,1))
ok("equal spin lengths",len({v.dot(v) for v in spin})==1)
ok("120 degree pair dot",all(spin[a].dot(spin[b])==-spin[a].dot(spin[a])/2
    for a in range(3) for b in range(a+1,3)))
ok("centred site sum zero",sum(pos,s.zeros(3,1))==s.zeros(3,1))
ok("C3 order and orientation",cycle**3==I and cycle.det()==1)
ok("C3 permutes Mn sites",set(tuple(cycle*v) for v in sites)==set(tuple(v) for v in sites))
ok("C3 permutes spins",set(tuple(cycle*v) for v in spin)==set(tuple(v) for v in spin))
ok("STF tensor nonzero",any(shape(H)))
ok("xyz component",H[0,1,2]==-Q(1,36))
ok("STF symmetry",all(H[i,j,k]==H[i,k,j]==H[j,i,k] for i,j,k in idx))
ok("STF trace",all(sum(H[i,j,j] for j in range(3))==0 for i in range(3)))
ok("C3 invariant tensor",shape(rot(H,cycle))==shape(H))
negative=tensor(pos,[-v for v in spin])
ok("time reversal negative",shape(negative)==tuple(-v for v in shape(H)))
ok("covariant rotation",shape(tensor([cycle*v for v in pos],[cycle*v for v in spin]))==shape(rot(H,cycle)))
ok("dipole zero, STF nonzero",sum(spin,s.zeros(3,1))==s.zeros(3,1) and H[0,1,2]!=0)
ok("axial inversion even",shape(tensor([-v for v in pos],spin))==shape(H))
ok("opposite-domain tensor cancellation",all(x+y==0 for x,y in zip(shape(H),shape(negative))))
ok("exact rational tensor",all(isinstance(v,s.Rational) for v in shape(H)))
receipt={
 "scope":"source-informed L12 sites and chosen 120-degree trial texture; no PtMn3 T1g or GR identification",
 "Mn_fractional_positions":[list(map(str,v)) for v in sites],
 "cluster_centroid":list(map(str,center)),
 "trial_spin_vectors_unnormalized":[list(map(str,v)) for v in spin],
 "tensor_definition":"STF(Sym sum_a spin_ai r_aj r_ak)",
 "tensor_xyz":str(H[0,1,2]),
 "tensor_norm_squared":str(sum(v*v for v in shape(H))),
 "passed":len(checks),"checks":checks,
 "real_material_spin_domain_paid":False,
 "published_T1g_operator_intertwiner_paid":False,
 "material_H_k_and_tunnel_transport_paid":False,
 "complete_Tmunu_and_gravitational_field_paid":False
}
if __name__=="__main__":print(json.dumps(receipt,indent=2,sort_keys=True))
