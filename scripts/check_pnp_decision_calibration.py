"""Same-input decision comparison; graph expansion exact for small base graphs."""
from collections import Counter
from itertools import combinations
from random import Random
from time import perf_counter
from statistics import median
import json,sys,signal
import numpy as np
from check_pnp_compilation_calibration import threshold,graph,prior
from check_pnp_observation_lift import solve as lift,substituted,audit
from check_pnp_cdcl_baseline import solve as cdcl


def width(F,n):
    adj=[set() for _ in range(n)]
    for c in F:
        S={abs(l)-1 for l in c}
        for j in S:adj[j].update(S-{j})
    remaining=set(range(n));w=0
    while remaining:
        def score(j):
            N=adj[j]&remaining
            return sum(b not in adj[a] for a,b in combinations(sorted(N),2)),len(N),j
        j=min(remaining,key=score);N=adj[j]&remaining;w=max(w,len(N))
        for i in N:adj[i].update(N-{i})
        remaining.remove(j)
    return w


def expansion(v,E):
    A=np.zeros((v,v))
    for i,j in E:A[i,j]=A[j,i]=1
    eig=np.linalg.eigvalsh(A);h=min((sum(((mask>>i)^(mask>>j))&1 for i,j in E)/mask.bit_count(),mask) for mask in range(1,1<<v) if mask.bit_count()<=v//2)
    return dict(gap=float(3-eig[-2]),edge_expansion=h[0],minimizing_mask=h[1])


def timed(f):
    start=perf_counter()
    def alarm(*args):raise TimeoutError()
    old=signal.signal(signal.SIGALRM,alarm);signal.setitimer(signal.ITIMER_REAL,1)
    try:q=f()
    except TimeoutError:q=dict(status='UNKNOWN',reason='wall_timeout')
    finally:signal.setitimer(signal.ITIMER_REAL,0);signal.signal(signal.SIGALRM,old)
    return dict(q,wall_ms=(perf_counter()-start)*1000)


def run(F,n,truth):
    a=timed(lambda:prior(F,n,(),(),200000));b=timed(lambda:lift(F,n,cap=1000000));c=cdcl(F,n,timeout_ms=1000)
    for q in (a,b,c):
        if q['status']=='WITNESS':assert audit(F,q['witness']) and truth is not False
        if q['status']=='EMPTY':assert truth is not True
    assert len({q['status'] for q in (a,b,c) if q['status']!='UNKNOWN'})<=1
    def small(q):return {k:v for k,v in q.items() if k in ('status','wall_ms','used','reserved','route','reason','monomials','observations')}
    return dict(prior=small(a),lift=small(b),cdcl={k:v for k,v in c.items() if k!='witness'},min_fill_width=width(F,n))


def main():
    rows=[];rng=Random(3693801)
    for n,planted,i,F in threshold():rows.append(dict(family='threshold',n=n,m=len(F),planted=planted,index=i,**run(F,n,True if planted else None)))
    for v in (6,8,12,16):
        E=graph(v,3693700+v);g=expansion(v,E)
        for k,kind in ((2,'and'),(3,'majority'),(3,'random')):
            if kind=='and':T=((0,0,0,1),)*len(E)
            elif kind=='majority':T=(tuple(int(a.bit_count()>=2) for a in range(8)),)*len(E)
            else:
                T=tuple(tuple(a>>i&1 for i in range(8)) for a in (rng.randrange(1,255) for e in E))
            for odd in (False,True):
                F=substituted(v,E,T,k,odd);rows.append(dict(family=kind,n=k*len(E),v=v,m=len(F),odd=odd,edges=E,tables=T,**g,**run(F,k*len(E),not odd)))
    with open(sys.argv[1],'w') as f:json.dump(rows,f,indent=2)
    for kind in ('threshold','and','majority','random'):
        for n in sorted({r['n'] for r in rows if r['family']==kind}):
            D=[r for r in rows if r['family']==kind and r['n']==n]
            print(kind,n,{k:dict(Counter(r[k]['status'] for r in D)) for k in ('prior','lift','cdcl')},'solve_ms',round(median(r['cdcl']['solve_ms'] for r in D),3),'conflicts',[r['cdcl']['stats'].get('sat conflicts',0) for r in D],'width',[min(r['min_fill_width'] for r in D),max(r['min_fill_width'] for r in D)],flush=True)
if __name__=='__main__':main()
