"""Compare gated/cooldown/savings policies to literal and prior runner."""
from random import Random
from collections import Counter
from pathlib import Path
from fractions import Fraction
from math import prod
import argparse,json
from check_pnp_gated_guarded_trace import execute_gated,valuation_adapter,relevant_two,repeat_suffixes
from check_pnp_online_guarded_trace import execute
from check_pnp_fractran_guarded_block import compile_block,jump

def literal(rules,v,limit):
    for k in range(limit):
        i=next((j for j,(g,d) in enumerate(rules) if all(a>=b for a,b in zip(v,g))),None)
        if i is None:return v,'halt',k
        v=tuple(a+b for a,b in zip(v,rules[i][1]))
    return v,'limit',limit

def case(i):
    r=Random(3692819+i);n=1+i%4;D=[tuple(r.randrange(-3,5) for _ in range(n)) for _ in range(1+i%6)];rules=[(tuple(max(0,-d) for d in V),V) for V in D];v=tuple(r.randrange(12) for _ in range(n));limit=i%128
    ref=literal(rules,v,limit);out=Counter(cases=1)
    # Same fixture/width/cache schedule as prior campaign.
    for name,run in [('old',execute),('gated',lambda *a,**kw:execute_gated(*a,**kw,admit=False)),('admitted',execute_gated)]:
        a,b,s=run(rules,v,limit,window=1+i%8,cache_cap=i%7)
        assert (a,b,s['raw_steps'])==ref,(i,name,ref,a,b,s)
        out.update({name+'_'+k:v for k,v in s.items()})
    # Direct cooldown semantic control: changing only irrelevant lanes
    # cannot alter the truth of the two-repetition guard predicate.
    p=tuple(r.randrange(len(rules)) for _ in range(1+i%4));B=compile_block(rules,p);I=relevant_two(B);v2=tuple(a if j in I else r.randrange(20) for j,a in enumerate(v))
    assert (jump(v,B,2) is None)==(jump(v2,B,2) is None);out['cooldown_controls']+=1
    return out

def controls():
    N=10**12;rules=(((0,N),(0,-N)),((1,0),(-1,1)))
    v,why,S=execute_gated(rules,(N,0),N+1);assert (v,why,S['raw_steps'],S['literal_steps'],S['jumps'])==((0,0),'limit',N+1,3,1)
    # Distinct phase tags, actual reduced fractions, zero repeat probes.
    P=(2,3,5,7,11,13,17,19,23,29,31,37,41);program=[Fraction(P[i+1],P[i]) for i in range(len(P)-1)]
    v,why,T=valuation_adapter(program,P[0],P,len(program)+1)
    assert why=='halt' and T['probes']==0 and prod(p**a for p,a in zip(P,v))==P[-1]
    return dict(huge=S,straight_line=T)

def main():
    p=argparse.ArgumentParser();p.add_argument('--total',type=int,default=2048);p.add_argument('--batch',type=int,default=256);p.add_argument('--checkpoint',type=Path,required=True);a=p.parse_args();assert a.batch>0 and a.total>=0
    s=json.loads(a.checkpoint.read_text()) if a.checkpoint.exists() else dict(version=1,total=a.total,next=0,counts={});assert s['version']==1 and s['total']==a.total;c=Counter(s['counts'])
    for i in range(s['next'],min(a.total,s['next']+a.batch)):
        c.update(case(i));s.update(next=i+1,counts=dict(c));tmp=a.checkpoint.with_suffix('.tmp');tmp.write_text(json.dumps(s));tmp.replace(a.checkpoint)
    if s['next']==a.total:s['controls']=controls();a.checkpoint.write_text(json.dumps(s))
    print(json.dumps(s))
if __name__=='__main__':main()
