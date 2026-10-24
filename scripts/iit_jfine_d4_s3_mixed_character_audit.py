#!/usr/bin/env python3
"""Mixed D4(site) x S3(balanced-value) characters of the actual 3x3 jFine sheet.

Source: JFinePhaseQuotientFieldExact, PointedTernaryBulkExact,
IITJFineFourOneFourS3ZetaGaugeExact. Pointed marker MOVES under site D4.
Finite permutation-character evidence; not a Monster or IIT Phi proof.
"""
from __future__ import annotations
import hashlib
import json
import math
from collections import Counter
from itertools import permutations, product

ID=tuple(range(9))
R=(6,3,0,7,4,1,8,5,2)
S=(2,1,0,5,4,3,8,7,6)
CORNERS=(0,2,6,8)
EDGES=(1,3,5,7)

def compose(p,q):
    return tuple(p[q[i]] for i in range(9))

def ppow(p,k):
    x=ID
    for _ in range(k):
        x=compose(x,p)
    return x

def cycles(p):
    seen=set()
    ans=[]
    for i in range(9):
        if i in seen:
            continue
        cycle=[]
        j=i
        while j not in seen:
            seen.add(j)
            cycle.append(j)
            j=p[j]
        ans.append(cycle)
    return ans

def rows():
    result=[]
    for t,k in product(range(2),range(4)):
        p=compose(ppow(R,k),S if t else ID)
        cc=cycles(p)
        assert p[4]==4
        result.append((k,t,len(cc),sum(len(z)%2==0 for z in cc),
                       sum(len(z)==1 for z in cc)))
    return result

def d4char(k,t,name):
    if name=="E":
        return 0 if t else (2 if k==0 else -2 if k==2 else 0)
    er,es=((1,1),(1,-1),(-1,1),(-1,-1))[int(name[1:])]
    return er**k*es**t

def irreps(pointed):
    answer={}
    for dr,sr in product(("A0","A1","A2","A3","E"),("triv","sign","std")):
        numerator=0
        for k,t,ncycles,even,fixed_sites in rows():
            marker=(1+fixed_sites) if pointed else 1
            identity=marker*3**ncycles
            transposition=marker*3**even
            character=(2*identity if sr=="std" else
                       identity+(3 if sr=="triv" else -3)*transposition)
            numerator+=d4char(k,t,dr)*character
        assert numerator%48==0,(dr,sr,numerator)
        answer[dr+"."+sr]=numerator//48
    dimension=sum(v*(2 if k.startswith("E.") else 1)*
                  (2 if k.endswith(".std") else 1) for k,v in answer.items())
    assert dimension==(196830 if pointed else 19683)
    return answer

def rowcol72():
    group=set()
    for pr,pc,t in product(permutations(range(3)),
                            permutations(range(3)),range(2)):
        p=tuple(pr[j]*3+pc[i] if t else pr[i]*3+pc[j]
                for i in range(3) for j in range(3))
        group.add(p)
    assert len(group)==72 and R in group and S in group
    orders=Counter()
    burnside=0
    for p in group:
        cc=cycles(p)
        order=math.lcm(*(len(z) for z in cc))
        orders[order]+=1
        even=sum(len(z)%2==0 for z in cc)
        burnside+=3**len(cc)+3*3**even+(
            2*3**len(cc) if all(len(z)%3==0 for z in cc) else 0)
    assert orders=={1:1,2:21,3:8,4:18,6:24}
    assert burnside==36288 and burnside//432==84
    assert any(p[4]!=4 for p in group)
    return dict(sorted(orders.items())),burnside//432

def f9mul(x,y):
    a,b=x;c,d=y
    return ((a*c+2*b*d)%3,(a*d+b*c)%3)

def f9pow(x,n):
    v=(1,0)
    for _ in range(n):
        v=f9mul(v,x)
    return v

def audit():
    f=irreps(False)
    p=irreps(True)
    assert f=={
        "A0.triv":490,"A0.sign":464,"A0.std":954,
        "A1.triv":355,"A1.sign":356,"A1.std":711,
        "A2.triv":418,"A2.sign":410,"A2.std":828,
        "A3.triv":418,"A3.sign":410,"A3.std":828,
        "E.triv":800,"E.sign":820,"E.std":1620}
    assert p=={
        "A0.triv":4396,"A0.sign":4316,"A0.std":8712,
        "A1.triv":3856,"A1.sign":3884,"A1.std":7740,
        "A2.triv":4117,"A2.sign":4100,"A2.std":8217,
        "A3.triv":4117,"A3.sign":4100,"A3.std":8217,
        "E.triv":8162,"E.sign":8200,"E.std":16362}
    assert sum(S[i]==i for i in EDGES)==2
    assert sum(S[i]==i for i in CORNERS)==0
    assert p["A0.triv"]!=10*f["A0.triv"]
    orders,rowcol_orbits=rowcol72()
    assert f9pow((1,1),8)==(1,0) and f9pow((1,1),4)!=(1,0)
    result={
      "scope":"DASHI finite D4(site) x S3(value) permutations, NOT Monster/IIT/quantum",
      "source_fine_states":19683,
      "source_pointed_states":196830,
      "fine_irrep_multiplicities":f,
      "pointed_irrep_multiplicities":p,
      "fine_D4_by_valueS3_orbits":f["A0.triv"],
      "pointed_D4_by_valueS3_orbits":p["A0.triv"],
      "pointed_marker_moves":True,
      "D4_edge_corner_mirror_fixed_sites":[2,0],
      "D4_commutes_with_value_S3":True,
      "spatial_rowcol_S3_wreath_C2_order":72,
      "spatial_72_element_orders":orders,
      "spatial_72_by_valueS3_orbits":rowcol_orbits,
      "spatial_72_changes_distinguished_centre":True,
      "spatial_72_is_not_AGL1F9_72":True,
      "affine_F9_has_order8_element":True,
      "zeta_requires_characteristic_not3":True,
      "original_Monster_action_intertwined":False,
      "Agda_kernel_receipt":False
    }
    result["payload_sha256"]=hashlib.sha256(
        json.dumps(result,sort_keys=True).encode()).hexdigest()
    return result

if __name__=="__main__":
    print(json.dumps(audit(),indent=2,sort_keys=True))
