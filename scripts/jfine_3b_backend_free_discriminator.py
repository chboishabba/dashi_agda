#!/usr/bin/env python3
"""Backend-free exact JFine 3B representation-character fingerprint.

The mathematics is a consumer of existing DASHI finite-Heisenberg/Stone-von-
Neumann and IIT JFine 4+1+4 owners.  No Monster coordinate action is invented.
Computes actual traces of the CONSTRUCTED F3^6 Heisenberg fibre and geometric
D4 action on the 90 labels, including mixed-Weyl cyclotomic traces.

Primary representation theory: Serre, Linear Representations of Finite
Groups (1977); Barraclough--Wilson (2007) for Monster normalizer characters.
The source Monster 3B trace 53 and eigenspace dimension 65610 are sourced,
not independently proved by these enumerations.
"""
from fractions import Fraction
from itertools import product
import json

F3=range(3)
O=(0,)*6
Q=(1,0,4,2,5,3)
M=(0,1,3,2,5,4)

def compose(p,q): return tuple(p[i] for i in q)
def perm(v,p):return tuple(v[i] for i in p)
def power(p,k):
    out=tuple(range(len(p)))
    for _ in range(k):out=compose(out,p)
    return out

def elems():
    for k in range(4):
        for refl in (False,True):
            p=compose(power(Q,k),M) if refl else power(Q,k)
            def label(a,b,k=k,refl=refl):
                for _ in range(k):a,b=-b%3,a
                if refl:b=-b%3
                return a,b
            cl=('axis' if k%2==0 else 'diagonal') if refl else (
                'identity' if k==0 else 'half' if k==2 else 'quarter')
            yield (f"R^{k}" if not refl else f"M R^{k}",label,p,cl)

def fixed_p(p):
    seen=set();cc=0
    for i in range(len(p)):
        if i not in seen:
            cc+=1;j=i
            while j not in seen:
                seen.add(j);j=p[j]
    return 3**cc

def omega(b,u):return sum(x*y for x,y in zip(b,u))%3

def cyclotomic_trace(lab,p,a=O,b=O,t=0):
    # selected-zeta sector, with geometric operator after Weyl operator
    fixed_label=10*sum(lab(x,y)==(x,y) for x,y in product(F3,repeat=2))
    counts=[0,0,0]
    for u in product(F3,repeat=6):
        v=perm(tuple((x+y)%3 for x,y in zip(u,a)),p)
        if v==u:counts[(t+omega(b,u))%3]+=1
    return fixed_label*(counts[0]-counts[2]),fixed_label*(counts[1]-counts[2])

def d4_decompose(chi):
    # conjugacy-class order [1,r^2,{r,r^-1},reflection axis,diagonal]
    irreps={'A1':(1,1,1,1,1),'A2':(1,1,1,-1,-1),
            'B1':(1,1,-1,1,-1),'B2':(1,1,-1,-1,1),
            'E2':(2,-2,0,0,0)}
    size=(1,1,2,2,2)
    out={name:Fraction(sum(s*x*y for s,x,y in zip(size,chi,values)),8)
         for name,values in irreps.items()}
    assert all(x>=0 and x.denominator==1 for x in out.values())
    return {k:int(v) for k,v in out.items()}

def audit():
    # D4 presentation and exact symplectic-pairing preservation on six axes.
    # The geometric permutation lifts on the fibre therefore form a true
    # D4 representation: the associated selected geometric cocycle is 1.
    assert power(Q,4)==tuple(range(6))
    assert power(M,2)==tuple(range(6))
    assert compose(M,compose(Q,M))==power(Q,3)
    for p in (Q,M):
        for i in range(6):
            for j in range(6):
                ei=tuple(int(i==k) for k in range(6))
                ej=tuple(int(j==k) for k in range(6))
                assert omega(perm(ei,p),perm(ej,p))==int(i==j)
    elements=list(elems())
    assert len({p for _,_,p,_ in elements})==8
    classes=('identity','half','quarter','axis','diagonal')
    obs={};rows=[]
    for name,lab,p,cls in elements:
        chi90=10*sum(lab(a,b)==(a,b) for a,b in product(F3,repeat=2))
        chi729=fixed_p(p)
        triple=(chi90,chi729,chi90*chi729)
        assert cyclotomic_trace(lab,p)==(triple[2],0)
        if cls in obs:assert obs[cls]==triple
        obs[cls]=triple
        rows.append({'element':name,'class':cls,'chi90':chi90,'chi729':chi729,
                     'chi65610':triple[2]})
    vecs=[[obs[x][i] for x in classes] for i in (0,1,2)]
    mult=[d4_decompose(v) for v in vecs]
    assert mult[0]=={'A1':30,'A2':0,'B1':10,'B2':10,'E2':20}
    assert mult[1]=={'A1':144,'A2':63,'B1':99,'B2':99,'E2':162}
    assert mult[2]=={'A1':9540,'A2':7110,'B1':8280,'B2':8280,'E2':16200}
    for counts,dim in zip(mult,(90,729,65610)):
        assert sum((2 if k=='E2' else 1)*v for k,v in counts.items())==dim
    assert 3*729*729==3**13 and 531441+2*729**2==3**13
    assert 196883==65663+2*65610
    representatives={cl:next((lab,p) for _,lab,p,c in elements if c==cl) for cl in classes}
    cases=[
      ('identity',O,O,0,'identity'),
      ('central-z',O,O,1,'identity'),
      ('central-z2',O,O,2,'identity'),
      ('translation',(1,0,0,0,0,0),O,0,'identity'),
      ('modulation',O,(1,0,0,0,0,0),0,'identity'),
      ('mixed-weyl',(1,0,0,0,0,0),(1,0,0,0,0,0),0,'identity'),
      ('quarter-weyl',(1,0,0,0,0,0),O,0,'quarter'),
      ('axis-weyl',O,(0,0,1,0,0,0),1,'axis'),
      ('diag-weyl',(1,0,0,0,0,0),(0,1,0,0,0,0),2,'diagonal')]
    result=[]
    for name,a,b,t,cl in cases:
        chi=cyclotomic_trace(*representatives[cl],a,b,t)
        result.append({'case':name,'chi_coefficients_1_zeta':chi})
        if cl=='identity' and (a!=O or b!=O):assert chi==(0,0)
    assert result[1]['chi_coefficients_1_zeta']==(0,65610)
    assert result[2]['chi_coefficients_1_zeta']==(-65610,-65610)
    # Concrete negative control: twist the full D4 multiplicity action by
    # its determinant/sign character, leaving EVERY Heisenberg element fixed.
    # The E modules are literally identical but reflection traces change.
    # Therefore no D4-intertwiner exists between the two D4 extensions.
    sign=(1,1,1,-1,-1)
    twisted=[x*s for x,s in zip(vecs[2],sign)]
    twisted_mult=d4_decompose(twisted)
    assert twisted_mult=={'A1':7110,'A2':9540,'B1':8280,'B2':8280,'E2':16200}
    assert twisted!=vecs[2]
    return dict(status="exact integer/cyclotomic finite test passed",model="constructed geometric H6⋊D4 JFine action",
                mmgroup_required=False,D4_geometric_Weil_cocycle="trivial exact permutation lift",Heisenberg_order=3**13,
                central_fusion_3B_trace_sourced=53,
                Monster_c3_sector_dimensions=(65663,65610,65610),
                D4_class_order=classes,D4_char90=vecs[0],D4_char729=vecs[1],
                D4_char65610=vecs[2],D4_irreps90=mult[0],D4_irreps729=mult[1],
                D4_irreps65610=mult[2],D4_elements=rows,\n                same_E_different_D4_counterexample=dict(\n                  Heisenberg_action_identical=True,twist='orientation character of D4 on multiplicity',\n                  twisted_D4_character_65610=twisted,\n                  twisted_D4_irreps_65610=twisted_mult,\n                  exists_D4_intertwiner=False),
                exact_mixed_Weyl_traces=result,
                actual_Monster_N3B_same_action=False,
                actual_Monster_basis_intertwiner=False,
                actual_12_plus_78_identification=False)
if __name__=="__main__":print(json.dumps(audit(),indent=2))
