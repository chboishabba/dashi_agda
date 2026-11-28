from check_p0_signed_contrast_20261125 import cell,refine,ContinuationAllowance,canon,basis,accepts
from check_pnp_quadratic_phase import structured_contrast,recognize
from check_pnp_dual_syndrome_fourier import OMEGA
from itertools import product
from random import Random
from fractions import Fraction as Q
from collections import Counter

def force_chart(i):
    # Connected clauses, rank six, nullity ten. Disable optional producers
    # deliberately; this tests the exact-chart accounting branch, not a
    # claim that the ordinary portfolio must refuse this geometry.
    r=Random(3692828+i);n=16;rank=6;F=canon(tuple((j+1,(j+1)%n+1) for j in range(n)))
    cols=tuple(tuple(int(j==h) if j<rank else r.randrange(3) for h in range(rank))+(r.randrange(3),) for j in range(n));x=tuple(1 for _ in range(n));t=tuple(sum(c[j]*v for c,v in zip(cols,x))%3 for j in range(rank));o=i%3;w=Q((-1)**i)
    H=[0]*3
    for bits in product(range(2),repeat=n):
        if accepts(F,bits) and tuple(sum(c[j]*v for c,v in zip(cols,bits))%3 for j in range(rank))==t:H[(o+sum(c[-1]*v for c,v in zip(cols,bits)))%3]+=1
    delta=tuple(w*(3*h-sum(H)) for h in H);opt=dict(conditioned=False,component_width=None,boundary_width=None,syndrome_budget=0,normal_budget=0,dual_budget=0,phase_budget=0,mobius_budget=0,prefix_budget=0)
    cost=n*2**(n-len(basis(c[:-1] for c in cols)));C=Counter(fixtures=1,points=2**n)
    for splits in (0,4):
        for cap in (0,cost-1,cost*2):
            ledger=ContinuationAllowance(cap);root=cell(F,cols,t,o,tuple(range(n)),w,ledger=ledger,**opt)
            lo,hi,ds,done=refine([root],Q(0),splits,exact_probe_budget=cost*2,ledger=ledger,cell_options=opt)
            assert all(a<=x<=b for a,x,b in zip(lo,delta,hi)) and all(delta[d]>=0 for d in ds)
            assert ledger.left+sum(ledger.charges.values())==cap
            charged=ledger.charges.get('exact_chart',0)
            if cap==0:assert charged==0 and not ds
            if splits==0 and cap<cost:assert not ds and charged==0
            if cap==cost*2:assert ds and charged>0
            C['bounds']+=3;C['calls']+=1;C['charged_calls']+=bool(charged);C['reserved']+=charged;C['refusals']+=not ds;C['splits']+=done
    return C

def cubic(groups=2):
    # Groups of three original 8-bit truth-table gadgets, equated on all three
    # ternary input coordinates. Only first gadget per group contributes phase.
    enc=lambda a:(int(a==1),int(a==2));allowed={enc(x)+enc(y)+enc(z)+enc(x*y*z%3) for x,y,z in product(range(3),repeat=3)}
    F=[];cols=[];g=3*groups;r=6*groups
    for h in range(g):
        for bits in product(range(2),repeat=8):
            if bits not in allowed:F.append(tuple((8*h+j+1)*(1 if not b else -1) for j,b in enumerate(bits)))
        for j in range(8):
            col=tuple(((j%2+1)*(-1 if h%3==0 else 1))%3 if j<6 and z%3==j//2 and z//6==h//3 and (h%3==0 or z//3%2==h%3-1) else 0 for z in range(r))
            cols.append(col+((j%2+1) if h%3==0 and j>=6 else 0,))
    F=canon(F);cols=tuple(cols);t=(0,)*r;R=tuple(range(8*g));w=Q(1);H=[0]*3
    for x,y,z in product(range(3),repeat=3):H[x*y*z%3]+=1
    axis=tuple(H);H=[1,0,0]
    for _ in range(groups):H=[sum(H[j]*axis[(d-j)%3] for j in range(3)) for d in range(3)]
    delta=tuple(3*h-sum(H) for h in H);opts=dict(component_width=8,boundary_width=None,syndrome_budget=0,normal_budget=0,dual_budget=0,mobius_budget=0,prefix_budget=0,phase_budget=65536)
    ans=structured_contrast(F,cols,t,0,R,w,8,64,65536,degree_cap=3,phase_branch_cap=64);assert ans is not None and ans[0]==ans[1]==delta
    C=[]
    for cap,leaves,degree in ((0,64,3),(65536,3*groups-1,3),(65536,64,3),(65536,64,2)):
        ledger=ContinuationAllowance(cap);root=cell(F,cols,t,0,R,w,ledger=ledger,phase_leaf_cap=leaves,phase_degree=degree,**opts)
        assert root is not None and all(a<=x<=b for a,x,b in zip(root[-2],delta,root[-1]));assert ledger.left+sum(ledger.charges.values())==cap
        if cap and leaves==64 and degree==3:assert root[-2]==root[-1]==delta and ledger.phase_completed==1 and ledger.phase_leaves==3*groups
        if leaves==3*groups-1:assert ledger.phase_refused==1 and ledger.left==0
        if degree==2 and groups>1:assert ledger.phase_refused==1 and root[-2]!=root[-1]
        C.append(dict(cap=cap,leaf_cap=leaves,degree=degree,exact=root[-2]==root[-1],charges=ledger.charges,completed=ledger.phase_completed,refused=ledger.phase_refused,leaves=ledger.phase_leaves))
    # Degree four does not masquerade as cubic.
    T={x:OMEGA[x[0]*x[1]*x[2]*x[3]%3] for x in product(range(3),repeat=4)}
    assert recognize(T,4,lambda _:None,3) is None
    return dict(variables=len(R),rows=r,clauses=len(F),hist=H,contrast=delta,phase_work=ans[2]['work'],phase_leaves=ans[2]['phase_leaves'],ledgers=C)

if __name__=='__main__':
    C=Counter()
    for i in range(8):C.update(force_chart(i))
    print(dict(C),flush=True);print(cubic(),flush=True)
