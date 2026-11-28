"""Seeded calibration, not a general solver lower bound."""
from random import Random
from itertools import product
from collections import Counter
import json,sys
from check_pnp_compressed_boundary_portfolio import original
from check_pnp_hall_geometry import cnf_solver as prior
from check_pnp_frontier_resolution import accepts
from check_pnp_affine_accumulator import solve
CAP=200000
PROBE=3000000
STATES=4096

def threshold():
    rng=Random(3693302)
    for n in (12,20,32,48):
        for planted in (False,True):
            for i in range(8):
                w=tuple(rng.randrange(2) for _ in range(n));F=[]
                for _ in range(round(4.26*n)):
                    ids=rng.sample(range(n),3);c=tuple((j+1)*rng.choice((-1,1)) for j in ids)
                    if planted and not accepts((c,),w):c=(-c[0],)+c[1:]
                    F.append(c)
                yield n,planted,i,tuple(F)

def graph(n,seed):
    import networkx as nx
    for retry in range(100):
        G=nx.random_regular_graph(3,n,seed=seed+retry)
        if nx.is_connected(G):return tuple(sorted(tuple(sorted(e)) for e in G.edges()))
    raise RuntimeError('graph generation')

def substituted(v,E,odd):
    F=[]
    for i in range(v):
        ids=tuple(j for j,e in enumerate(E) if i in e);assert len(ids)==3
        scope=tuple(k for j in ids for k in (2*j,2*j+1))
        for a in product((0,1),repeat=6):
            if sum(a[j]*a[j+1] for j in (0,2,4))%2!=int(odd and i==0):
                F.append(tuple((j+1)*(1-2*b) for j,b in zip(scope,a)))
    return tuple(F)

def summary(q):
    return {k:q[k] for k in ('status','peak','observed_peak','completed_layers','stop','steps','width','entries','used','reserved','count') if k in q}

def test(F,n,truth=None):
    old=prior(F,n,(),(),CAP);normal=original(F,n,CAP,'normal',clip=None);rational=original(F,n,CAP,'rational',clip=None)
    for q in (old,normal,rational):
        if q['status']=='WITNESS':assert accepts(F,q['witness']) and truth is not False
        if truth is True:assert q['status']!='EMPTY'
    assert len({q['status'] for q in (old,normal,rational) if q['status']!='UNKNOWN'})<=1
    if normal['status']!='UNKNOWN' and rational['status']!='UNKNOWN':assert normal['count']==rational['count']
    return dict(prior=summary(old),normal=summary(normal),rational=summary(rational))

def probe(F,n,truth=None):
    q=solve((),(),n,F=F,cap=PROBE,max_states=STATES)
    if q['status']=='WITNESS':assert accepts(F,q['witness']) and truth is not False
    if truth is True:assert q['status']!='EMPTY'
    return summary(q)

def main():
    data=[]
    for n,planted,i,F in threshold():
        truth=True if planted else None
        if n==12:truth=any(accepts(F,x) for x in product((0,1),repeat=n))
        d=dict(family='threshold',n=n,m=len(F),planted=planted,index=i,truth=truth,**test(F,n,truth))
        if i<2:d['probe']=probe(F,n,truth)
        data.append(d)
    for v in (6,8,12,16):
        E=graph(v,3693700+v);n=2*len(E)
        for odd in (False,True):
            F=substituted(v,E,odd);assert accepts(F,(0,)*n)==(not odd)
            data.append(dict(family='and_tseitin',n=n,m=len(F),vertices=v,edges=E,odd=odd,truth=not odd,**test(F,n,not odd),probe=probe(F,n,not odd)))
    for n in (12,20,32,48):
        E=graph(n,3693800+n);F=tuple((i+1,j+1) for i,j in E)
        data.append(dict(family='graph_cnf',n=n,m=len(F),edges=E,truth=True,**test(F,n,True),probe=probe(F,n,True)))
    with open(sys.argv[1],'w') as out:json.dump(dict(cap=CAP,probe_cap=PROBE,state_cap=STATES,rows=data),out,indent=2)
    for family in ('threshold','and_tseitin','graph_cnf'):
        for n in sorted({d['n'] for d in data if d['family']==family}):
            D=[d for d in data if d['family']==family and d['n']==n]
            print(family,n,len(D),{k:dict(Counter(d[k]['status'] for d in D)) for k in ('prior','normal','rational')},'probe',[(d['probe']['status'],d['probe']['observed_peak'],d['probe']['completed_layers'],d['probe']['stop']) for d in D if 'probe' in d],flush=True)
if __name__=='__main__':main()
