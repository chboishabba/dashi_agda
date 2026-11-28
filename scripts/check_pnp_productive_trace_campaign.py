"""Restartable original-coordinate tests of the actual fallback owners."""
import argparse,json,os,time
from pathlib import Path
from random import Random
from functools import reduce
from check_pnp_affine_normal_components import Budget,canon,chart,satisfies
from check_pnp_capacity_geometry import violation_flats
from check_pnp_demand_strata import bounded_fold
from check_pnp_partial_quotient import solve as partial
from check_pnp_collective_fibre_escape import solve as collective
from check_pnp_fractran_trace import productive_trace
from check_pnp_aggregate_excess_demand import compile_excess_demand
from check_openai_shared_tseitin_parsimonious import eval_circuit

def case(i):
    rng=Random(36920261128+i);n=3+i%8;x=rng.randrange(1,1<<n)
    pool=[r for r in range(1,1<<n) if (r&x).bit_count()%2]
    R=tuple(rng.sample(pool,min(len(pool),1+i%6)))
    if i%4==0:
        R=tuple(r for r in R if not r>>(n-1)) or (x&-x,)
    H=canon(tuple((r,1) for r in R));caps=tuple(rng.choice((0,1,1,2,3)) for r in R)
    F=[]
    for _ in range(i%5):
        a,b=rng.sample(range(n),2);G=((1<<a,rng.randrange(2)),(1<<b,rng.randrange(2)))
        if satisfies(x,(),(G,)):F.append(G)
    F=tuple(F)
    phi=lambda z:sum(max(0,(r&z).bit_count()-c) for r,c in zip(R,caps))
    points=[z for z in range(1<<n) if satisfies(z,H,())]
    hard=[z for z in points if satisfies(z,(),F)];best=min(map(phi,hard));initial=phi(x)
    expected=sum(phi(z)==0 for z in points)
    B=Budget(10000000);count,y=bounded_fold(n,R,H,caps,B,leaf_cap=12,seam_cap=12)
    assert count==expected and (y is None)==(expected==0)
    if y is not None:assert y in points and phi(y)==0
    result={'mass':1,'mass_free':int(reduce(int.__or__,R,0)!=(1<<n)-1),'partial_sat':0,'partial_empty':0,'partial_unknown':0,'collective_sat':0,'collective_empty':0,'collective_unknown':0}
    F0=violation_flats(n,R,H,caps,Budget(10000000))+F
    assert all(satisfies(z,H,F0)==(z in hard and phi(z)==0) for z in points)
    for name,solver in [('partial',partial),('collective',collective)]:
        y,stats,done=solver(n,H,F0,2000000)
        if y is not None:assert done and y in hard and phi(y)==0;result[name+'_sat']=1
        elif done:assert best>0;result[name+'_empty']=1
        else:result[name+'_unknown']=1
    B=Budget(2000000);status,t,lower=productive_trace(n,R,H,caps,x,B,F,0,0,True)
    assert 0<=lower<=best
    if status=='SAT':assert initial==0 and t is None
    elif status=='MINIMUM':assert initial==best and t is None
    elif status=='IMPROVED':assert t['end'] in hard and phi(t['end'])<initial and t['decrease']==initial-phi(t['end'])
    else:assert status=='UNKNOWN' and t is None
    result['portfolio_'+status]=1
    result['demand_lane']=int(bool(B.stats['productive_demand']))
    result['demand_improved']=int(status=='IMPROVED' and bool(B.stats['productive_demand']))
    result['collective_lane']=int(bool(B.stats['exchange']))
    result['partial_lane']=int(bool(B.stats['block_chart']))
    _,V=chart(n,H);stall=initial>best and all(not satisfies(x^v,H,F) or phi(x^v)>=initial for v in V)
    result['basis_stall']=int(stall);result['basis_stall_improved']=int(stall and status=='IMPROVED')
    result['unknown_inhabited']=int(status=='UNKNOWN' and best==0)
    return result

def compiler_case(i):
    rng=Random(3692811+i);n=i%8
    R=tuple(rng.randrange(1<<n) for _ in range(i%5));caps=tuple(rng.randrange(n+2) for _ in R)
    bound=rng.randrange(-1,sum(r.bit_count() for r in R)+2);x=rng.randrange(1<<n)
    H=canon(tuple((r,(r&x).bit_count()%2) for r in [rng.randrange(1<<n)] if i%3==0))
    F=tuple((((1<<j),rng.randrange(2)),) for j in range(n) if rng.randrange(8)==0)
    N,Q,G,gates,out=compile_excess_demand(n,R,H,caps,bound,Budget(10000000),F)
    assert N==n+len(gates) and Q==H
    s={'cases':1,'points':0,'gate_flips':0,'small_all_aux':0,'accepted':0,'max_gates':len(gates)}
    for z in range(1<<n):
        inp=tuple(bool(z>>j&1) for j in range(n));aux=eval_circuit(n,gates,inp)
        y=z|sum(int(t)<<(n+j) for j,t in enumerate(aux))
        expected=satisfies(z,H,F) and sum(max(0,(z&r).bit_count()-c) for r,c in zip(R,caps))<=bound
        assert satisfies(y,Q,G)==expected;s['points']+=1;s['accepted']+=expected
        if expected:
            for j in range(len(gates)):
                assert not satisfies(y^(1<<(n+j)),Q,G);s['gate_flips']+=1
        if len(gates)<=5:
            assert sum(satisfies(z|(j<<n),Q,G) for j in range(1<<len(gates)))==int(expected);s['small_all_aux']+=1<<len(gates)
    return s

def lifted_controls():
    for n,R,H,caps,x,F in [(3,(7,),(),(1,),7,()),(3,(7,),((7,1),),(0,),7,(((1,0),),((2,0),),((4,0),)))]:
        initial=sum(max(0,(x&r).bit_count()-c) for r,c in zip(R,caps))
        N,Q,G,gates,out=compile_excess_demand(n,R,H,caps,initial-1,Budget(100000),F)
        truth=any(satisfies(z,H,F) and sum(max(0,(z&r).bit_count()-c) for r,c in zip(R,caps))<initial for z in range(1<<n))
        for solver in (partial,collective):
            y,stats,done=solver(N,Q,G,200000)
            if y is not None:assert truth and done and satisfies(y,Q,G)
            elif done:assert not truth
            if solver is collective:assert done and (y is not None)==truth
            print('lifted control',solver.__module__,N,len(G),truth,done,y,flush=True)

def main():
    p=argparse.ArgumentParser();p.add_argument('--checkpoint',required=True)
    p.add_argument('--mode',choices=('portfolio','compiler'),default='portfolio')
    p.add_argument('--total',type=int);p.add_argument('--batch',type=int,default=64)
    a=p.parse_args();path=Path(a.checkpoint)
    total=a.total if a.total is not None else (1024 if a.mode=='portfolio' else 512)
    if total<0 or a.batch<=0:raise ValueError('invalid batch')
    signature='pnp-fallback-v2-36920261128-'+a.mode
    state=json.loads(path.read_text()) if path.exists() else {'signature':signature,'next':0,'counts':{},'total':total}
    assert state['signature']==signature and state['total']==total
    stop=min(total,state['next']+a.batch);start=time.monotonic()
    path.parent.mkdir(parents=True,exist_ok=True)
    def save():
        tmp=path.with_suffix(path.suffix+'.tmp');tmp.write_text(json.dumps(state,indent=2)+'\n');os.replace(tmp,path)
    for i in range(state['next'],stop):
        r=(case if a.mode=='portfolio' else compiler_case)(i)
        for k,v in r.items():
            old=state['counts'].get(k,0);state['counts'][k]=max(old,v) if k=='max_gates' else old+v
        state['next']=i+1;save()
        if (i+1)%64==0:print('checkpoint',i+1,flush=True)
    if a.mode=='compiler' and state['next']==total and not state.get('lifted_controls'):
        lifted_controls();state['lifted_controls']='PASS';save()
    print(json.dumps(state,sort_keys=True));print('seconds',time.monotonic()-start)

if __name__=='__main__':main()
