from check_pnp_online_guarded_trace import execute
from random import Random
from collections import Counter
from pathlib import Path
import argparse,json

def literal(rules,v,limit):
    for k in range(limit):
        i=next((j for j,(g,d) in enumerate(rules) if all(a>=b for a,b in zip(v,g))),None)
        if i is None:return v,'halt',k
        v=tuple(a+b for a,b in zip(v,rules[i][1]))
    return v,'limit',limit

def case(i):
    r=Random(3692819+i);n=1+i%4;D=[tuple(r.randrange(-3,5) for _ in range(n)) for _ in range(1+i%6)];rules=[(tuple(max(0,-d) for d in V),V) for V in D];v=tuple(r.randrange(12) for _ in range(n));limit=i%128
    a,b,c=literal(rules,v,limit);x,y,s=execute(rules,v,limit,window=1+i%8,cache_cap=i%7);assert (a,b,c)==(x,y,s['raw_steps']),(i,rules,v,limit,(a,b,c),(x,y,s))
    return Counter(cases=1,**s)

def huge():
    # Rule 0 becomes enabled after exactly N repetitions of rule 1.
    N=10**12;rules=(((0,N),(0,-N)),((1,0),(-1,1)))
    # Explicit guards are allowed; these are reduced denominator guards.
    x,y,s=execute(rules,(N,0),N+1);assert (x,y)==((0,0),'limit') and s['raw_steps']==N+1 and s['jumps']>=1
    return s

def main():
    p=argparse.ArgumentParser();p.add_argument('--total',type=int,default=2048);p.add_argument('--batch',type=int,default=256);p.add_argument('--checkpoint',type=Path,required=True);a=p.parse_args();assert a.batch>0 and a.total>=0
    s=json.loads(a.checkpoint.read_text()) if a.checkpoint.exists() else dict(version=1,total=a.total,next=0,counts={});assert s['version']==1 and s['total']==a.total;c=Counter(s['counts'])
    for i in range(s['next'],min(a.total,s['next']+a.batch)):
        c.update(case(i));s.update(next=i+1,counts=dict(c));tmp=a.checkpoint.with_suffix('.tmp');tmp.write_text(json.dumps(s));tmp.replace(a.checkpoint)
    if s['next']==a.total:s['huge']=huge();a.checkpoint.write_text(json.dumps(s))
    print(json.dumps(s))
if __name__=='__main__':main()
