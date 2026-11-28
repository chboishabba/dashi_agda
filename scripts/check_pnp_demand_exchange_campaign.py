"""Checkpointed shared-ledger exchange descent comparisons."""
import json,os,sys,hashlib
from pathlib import Path
from random import Random
from check_pnp_affine_normal_components import canon,chart,lift,Budget
from check_pnp_demand_exchange import descent
HERE=Path(__file__).parent
out=Path(sys.argv[1]) if len(sys.argv)>1 else HERE/'exchange-checkpoint.json'
key=hashlib.sha256(b''.join((HERE/f).read_bytes() for f in (Path(__file__).name,'check_pnp_demand_exchange.py','check_pnp_demand_strata.py','check_pnp_separator_row_strata.py','check_pnp_affine_normal_components.py','check_pnp_normal_boundary_join.py','check_pnp_exact_cover_pair_hull.py'))).hexdigest()
state=json.loads(out.read_text()) if out.exists() else {'key':key,'cases':[]}
assert state['key']==key
for seed in range(60):
    if any(c['seed']==seed for c in state['cases']):continue
    rng=Random(36950+seed);m=rng.choice((3,6,9));n=rng.randrange(3,10);S=[rng.sample(range(m),3) for _ in range(n)];R=tuple(sum(1<<j for j,T in enumerate(S) if i in T) for i in range(m));P=canon((r,1) for r in R)
    if P is None:continue
    u,V=chart(n,P);points=[lift(u,V,z) for z in range(1<<len(V))];T=[y for y in points if all((r&y).bit_count()==1 for r in R)];x=rng.choice(points);runs=[]
    for nodes in (0,8):
        B=Budget(100_000_000);H=[];y,done=descent(n,R,P,x,B,12,12,nodes,10_000_000,history=H,k_index=9)
        assert done and (y in T if T else y is None)
        assert len(H)<=(x.bit_count()-m//3)//2 and B.stats['demand_exchange_root']<=m*((x.bit_count()-m//3)//2)
        assert all(h[0]==9 and h[1]==t for t,h in enumerate(H))
        runs.append(dict(nodes=nodes,cover=y,steps=len(H),root_probes=B.stats['demand_exchange_root'],charged=sum(B.stats.values())))
    state['cases'].append(dict(seed=seed,n=n,m=m,rank=len(V),incumbent=x,runs=runs));out.parent.mkdir(parents=True,exist_ok=True);tmp=out.with_suffix('.tmp');tmp.write_text(json.dumps(state,indent=2));os.replace(tmp,out)
R=(7,7,7);P=canon(((7,1),));assert descent(3,R,P,7,Budget(100000),0,0,0,10000)==(None,False)
print('sources',len(state['cases']),'runs',sum(len(c['runs']) for c in state['cases']),'root_probes',sum(r['root_probes'] for c in state['cases'] for r in c['runs']),'steps',sum(r['steps'] for c in state['cases'] for r in c['runs']))
