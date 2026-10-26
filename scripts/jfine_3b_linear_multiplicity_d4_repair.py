#!/usr/bin/env python3
"""Construct a D4 signed-monomial *multiplicity* repair over the existing H6.

Not an actual Monster D4 embedding or a 6.Suz representation. Changes ONLY
D4 action on the 90-dimensional linear multiplicity space, keeping the 729
Schrödinger fibre and all E/Heisenberg operators untouched.

CONDITIONAL source character targets: involutions 2A, product z*g class 6D
gives selected-zeta trace (4371-(-3))/3=1458. If r order4 has square2A,
its Monster class must be 4B; z*r belongs to the unique class 12G powering
to 4B and 3B, giving trace (51-(-3))/3=18.
Sources: Monster ATLAS power maps; Conway–Norton (1979) coefficients;
OEIS A007247 (4B q^1=52), A058485 (12G q^1=-2);
OEIS A007257 (6D q^1=-2); Breuer–Magaard–Wilson (2026).
"""
import json
from pathlib import Path
R=(1,0,4,2,5,3)
S=(0,1,3,2,5,4)
COUNT={'A1':23,'A2':5,'B1':13,'B2':13,'E':18}
def compose(x,y):return [(x[j][0],v*x[j][1]) for j,v in y]
def power(x,k):
    out=[(i,1) for i in range(len(x))]
    for _ in range(k):out=compose(x,out)
    return out
def trace(x):return sum(s for i,(j,s) in enumerate(x) if j==i)
def mulperm(p,q):return tuple(p[j] for j in q)
def permpow(p,k):
    out=tuple(range(len(p)))
    for _ in range(k):out=mulperm(p,out)
    return out
def perm_trace(p):
    found=set();n=0
    for i in range(len(p)):
        if i not in found:
            n+=1;j=i
            while j not in found:
                found.add(j);j=p[j]
    return 3**n
def model():
    r=[];s=[]
    for name,(rv,sv) in {'A1':(1,1),'A2':(1,-1),
                         'B1':(-1,1),'B2':(-1,-1)}.items():
        for _ in range(COUNT[name]):
            i=len(r);r.append((i,rv));s.append((i,sv))
    for _ in range(COUNT['E']):
        i=len(r);r.extend([(i+1,1),(i,-1)])
        s.extend([(i,1),(i+1,-1)])
    assert len(r)==len(s)==90
    I=[(i,1) for i in range(90)]
    assert power(r,4)==I and power(s,2)==I
    assert compose(s,compose(r,s))==power(r,3)
    assert permpow(R,4)==tuple(range(6)) and permpow(S,2)==tuple(range(6))
    assert mulperm(S,mulperm(R,S))==permpow(R,3)
    sector={'identity':I,'half':power(r,2),'quarter':r,
            'axis':s,'diagonal':compose(r,s)}
    fibre={'identity':tuple(range(6)),'half':permpow(R,2),
           'quarter':R,'axis':S,'diagonal':mulperm(R,S)}
    st={name:trace(m) for name,m in sector.items()}
    ht={name:perm_trace(p) for name,p in fibre.items()}
    pt={name:st[name]*ht[name] for name in sector}
    assert st=={'identity':90,'half':18,'quarter':2,'axis':18,'diagonal':18}
    assert ht=={'identity':729,'half':81,'quarter':9,'axis':81,'diagonal':81}
    assert pt=={'identity':65610,'half':1458,'quarter':18,'axis':1458,'diagonal':1458}
    chi={'A1':(1,1,1,1,1),'A2':(1,1,1,-1,-1),
         'B1':(1,1,-1,1,-1),'B2':(1,1,-1,-1,1),
         'E':(2,-2,0,0,0)}
    weights=(1,1,2,2,2)
    observations=tuple(st[name] for name in ('identity','half','quarter','axis','diagonal'))
    mult={k:sum(w*a*b for w,a,b in zip(weights,observations,v))//8
          for k,v in chi.items()}
    assert mult==COUNT
    return {'status':'exact_D4_signed_monomial_model_checked',
       'base_E_and_Heisenberg_fibre_action':'unchanged (imported existing JFine H6)',
       'S90_D4_irreps':mult,'S90_D4_trace':st,'H729_D4_trace':ht,
       'Pzeta_65610_D4_trace':pt,
       'source_2A_6D_trace':(4371+3)//3,
       'source_4B_12G_trace':(51+3)//3,
       'source_powers_verified_from_ATLAS':['6D^2=3B','6D^3=2A',
          '12G^4=3B','12G^3=4B','4B^2=2A'],
       'genuine_signed_monomial_generators':True,
       'full_inertia_6Suz_action_constructed':False,
       'actual_Monster_D4_subgroup_constructed':False,
       'external_quarter_trace_class_compatibility_only':True}
if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--receipt',type=Path)
    a=p.parse_args()
    output=json.dumps(model(),indent=2)+'\n'
    if a.receipt:a.receipt.write_text(output)
    print(output,end='')
