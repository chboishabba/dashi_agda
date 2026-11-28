"""Dense planted sources: verify rank/width refusal, not an intrinsic width lower bound."""
from random import Random
from check_pnp_affine_normal_components import bits,canon,chart,Budget
from check_pnp_normal_boundary_join import value,tree
from check_pnp_separator_row_strata import build
from check_pnp_exact_cover_pair_hull import affine_disjunctive_close
from check_pnp_affine_normal_components import satisfies,Exhausted
from pathlib import Path
import hashlib,json,os,sys
HERE=Path(__file__).parent
out=Path(sys.argv[1]) if len(sys.argv)>1 else HERE/'width-checkpoint.json'
key=hashlib.sha256(b''.join((HERE/f).read_bytes() for f in (Path(__file__).name,'check_pnp_separator_row_strata.py','check_pnp_affine_normal_components.py','check_pnp_normal_boundary_join.py','check_pnp_exact_cover_pair_hull.py'))).hexdigest()
state=json.loads(out.read_text()) if out.exists() else {'key':key,'cases':[]}
assert state['key']==key
for m in (18,24,30,36):
    if any(c['m']==m for c in state['cases']):continue
    rng=Random(369+m);S=[]
    for _ in range(5):
        while True:
            p=list(range(m));rng.shuffle(p);T=[tuple(sorted(p[i:i+3])) for i in range(0,m,3)]
            if not set(T)&set(S):break
        S.extend(T)
    rng.shuffle(S)
    n=len(S);R=tuple(sum(1<<j for j,T in enumerate(S) if i in T) for i in range(m));P=canon((r,1) for r in R)
    # Original planted partition is used only to certify habitation, not to seed recovery.
    # After shuffling, regenerate its mask from the first partition in source order.
    rng0=Random(369+m);p=list(range(m));rng0.shuffle(p);plant={tuple(sorted(p[i:i+3])) for i in range(0,m,3)}
    cover=sum(1<<j for j,T in enumerate(S) if T in plant);assert all((cover&r).bit_count()==1 for r in R)
    u,V=chart(n,P);d=len(V);F=tuple(tuple((value(V,1<<j),u>>j&1) for j in bits(r)) for r in R)
    B=Budget(10**8);root,boundary,space=tree(d,F,B)
    def profile(node):
        mask,A,C=node;b=len(boundary(mask))
        if A is None:return len(space(mask)),b
        l,r=profile(A),profile(C);return max(l[0],r[0]),max(b,l[1],r[1])
    leaf,seam=profile(root);assert seam>4
    Q=Budget(10**8);assert build(n,R,P,Q,8,4) is None
    res=dict(n=n,m=m,rank=d,leaf=leaf,seam=seam,planted_cover=cover,cap=4,status='WIDTH_REFUSAL',tree_cost=sum(B.stats.values()),refusal_cost=sum(Q.stats.values()))
    B2=Budget(10**8)
    try:
        F0=tuple(tuple((1<<j,0) for j in bits(r)) for r in R);H,y=affine_disjunctive_close(n,F0,B2,P,depth=1,rounds=1)
        assert H is not None
        if y is not None:assert satisfies(y,P,()) and all((y&r).bit_count()==1 for r in R)
        res.update(lookahead='SAT' if y is not None else 'UNKNOWN',lookahead_rank=n-len(H),lookahead_cover=y,lookahead_cost=sum(B2.stats.values()))
    except Exhausted:res.update(lookahead='UNKNOWN_BUDGET',lookahead_cost=sum(B2.stats.values()))
    state['cases'].append(res);out.parent.mkdir(parents=True,exist_ok=True);tmp=out.with_suffix('.tmp');tmp.write_text(json.dumps(state,indent=2));os.replace(tmp,out);print(res,flush=True)
print('WIDTH_STRESS_PASS',len(state['cases']))
