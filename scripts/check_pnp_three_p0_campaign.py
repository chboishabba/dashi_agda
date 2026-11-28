"""Three P0 restartable regression, original owner imports (no fallback stubs).
For the full normal-space integration run --track unified --legacy.
Finite controls only; no universal endpoint claim.
"""
from collections import Counter
from itertools import product
from random import Random
from pathlib import Path
import argparse,json

HARD=((-8,-6,7),(-8,-5,1,4),(-5,-4,1,3),(-4,-1,5,7),(-1,4,6),(2,5,6))

def cnf(i,seed,n):
    r=Random(seed+i)
    return tuple(tuple((j+1)*r.choice((-1,1)) for j in r.sample(range(n),r.randrange(min(n,4)+1))) for _ in range(i%11))

def screen_case(i):
    from check_pnp_scale_gate import screen,potential,potential_bounds,Q
    from check_p0_signed_contrast_20261125 import canon,accepts
    n=i%9;F=canon(cnf(i,3692834,n));m=sum(accepts(F,x) for x in product((0,1),repeat=n))
    C=Counter(fixtures=1)
    for cap in (0,4096):
        s=screen(F,n,cap);l,u=s['mass'];assert l<=m<=u and s['reserved']<=cap
        for a in s['scales']:
            D=3**a['k'];v=potential(m,D);assert Q(a['lo'])<=v<=Q(a['hi'])
            if a['status']=='promised':assert v>Q(1,12)
            if a['status']=='below':assert v<=Q(1,12)
            C['scale_bounds']+=1
        if m:assert any(a['status']!='below' for a in s['scales'])
        C['exact_'+str(cap)]+=l==u
    return C

def autarky_case(i):
    from check_pnp_local_autarky import descend,reopen,canon,accepts
    n=i%9;F=canon(cnf(i,3692834,n));S=[x for x in product((0,1),repeat=n) if accepts(F,x)]
    s,x,G,p,w,R=descend(F,n,100000);Z=[x for x in product((0,1),repeat=n) if accepts(G,x)]
    assert bool(S)==bool(Z) and w<=100000
    for z in Z:assert reopen(F,n,p,z) in S
    im={reopen(F,n,p,z) for z in S};assert len(im)*(1<<len(p))>=len(S)
    assert x is None or x in S
    assert s!='EMPTY' or not S
    return Counter({s:1,'fixtures':1,'reopen':len(Z),'patches':len(R)})

def unified_case(i,legacy):
    from check_pnp_unified_endpoint import solve,classify,accepts
    r=Random(3692832)
    for j in range(i+1):
        n=j%7;F=tuple(tuple((k+1)*r.choice((-1,1)) for k in r.sample(range(n),r.randrange(min(n,3)+1))) for _ in range(j%10))
    S=[x for x in product((0,1),repeat=n) if accepts(F,x)]
    s,x,R=solve(F,n,65536,legacy=legacy)
    assert s=='WITNESS' if S else s=='EMPTY'
    assert x is None or x in S
    C=Counter({s:1,'fixtures':1})
    for a in R['attempts']:C['route_'+a['route']]+=1
    s,W,R=classify(F,n,65536,legacy=legacy)
    assert s==('EMPTY' if not S else 'SINGLETON' if len(S)==1 else 'MULTIPLE')
    assert all(x in S for x in W);C['class_'+s]+=1
    if legacy:
        # Exercise actual legacy route even when the default direct receiver exits.
        from check_p0_correlated_marginal_20261126 import portfolio
        y,done,route=portfolio(n,(),F,1048576)
        assert done and (y is not None)==bool(S)
        if y is not None:assert tuple((y>>k)&1 for k in range(n)) in S
        C['legacy_'+route]+=1
    return C

def stack_case(i):
    from check_pnp_stack_charged_run import candidate_exact,ChargedRunner
    from check_pnp_stack_fractran import compile_stack,source_next
    r=Random(3692835+i);q=1+i%3;a=1+i%3;blank=i%a
    rules=tuple((r.randrange(q),r.randrange(a),r.randrange(q),r.randrange(a),r.choice((-1,0,1))) for _ in range(i%8))
    M=compile_stack(q,a,blank,rules);one=lambda n,j:tuple(int(k==j) for k in range(n))
    bits=one(a,blank)+one(q,0)+one(q,q-1)+tuple(v for x,y,z,w,d in rules for v in one(q,x)+one(a,y)+one(q,z)+one(a,w)+one(3,d+1))
    c=(0,tuple(r.randrange(a) for _ in range(i%7)),tuple(r.randrange(a) for _ in range(1+i%7)));T=i%11
    R=candidate_exact(q,a,len(rules),bits,c[1],c[2],T,True);done=0
    for _ in range(T):
        z=source_next(M,c)
        if z is None:break
        c=z;done+=1
    assert R['configuration']==c and R['steps']==done and R['accepted']==(c[0]==q-1)
    assert R['halted']==(done<T) and R['terminal']==(source_next(M,c) is None)
    run=ChargedRunner(M);v=M.encode(*c);u,h,s=run.paid_step(v);w,k,t=run.step(v)
    assert (u,h,s['raw'])==(w,k,t['raw'])
    return Counter({R['status']:1,'fixtures':1,'steps':done,'terminal':R['terminal'],'step_equiv':1,'bit_weight':R['bit_weight']})

def seek_case(i):
    from check_pnp_cook_quadratic_seek import QuadraticCookSeek
    from check_pnp_cook_affine_seek_campaign import reference
    r=Random(3692831+i);T=i%5;w=1+i%3;R=1+i%2
    def clauses(N):return tuple(tuple((j,r.randrange(2)) for j in r.sample(range(N),r.randrange(min(N,4)+1))) for _ in range(i%4))
    D=QuadraticCookSeek(T,w,R,clauses(R+6*w),clauses(1+w),tuple(r.randrange(2) for _ in range(w)),tuple(r.randrange(2) for _ in range(w*(3+i%4))))
    want=reference(D);assert D.length()==len(want)
    for k,t in enumerate(want):assert D.token(k)==t
    return Counter(fixtures=1,tokens=len(want))

def equality_case(i):
    # A fixed paired-address schedule; only current pair and one accumulated
    # equality bit need persist besides the address counter. No hidden storage.
    n=1+i%7;A=list(product((0,1),repeat=n));rows=set();checks=0
    for x in A:
        row=[]
        for y in A:
            b=True
            for j in range(n):b=b and (x[j]==y[j])
            assert b==(x==y);row.append(b);checks+=1
        rows.add(tuple(row))
    assert len(rows)==2**n
    return Counter(fixtures=1,checks=checks,rows=len(rows))

def hard(legacy):
    from check_pnp_scale_gate import screened_search
    from check_pnp_unified_endpoint import solve,accepts
    out=[]
    for keep in (False,True):
        x,s,R=screened_search(HARD,8,9*1048576+4096,keep_low=keep)
        assert x is not None and accepts(HARD,x)
        out.append(dict(keep_low=keep,witness=x,screen=s,attempts=[dict(k=a['k'],status=a['status'],reserved=a['reserved'],queries=len(a['steps']),last=a['steps'][-1]) for a in R]))
    for local in (True,False):
        s,x,R=solve(HARD,8,65536,legacy=legacy,local=local,direct_options=dict(split_budget=0,cell_options=dict(conditioned=False,component_width=None)))
        assert s=='WITNESS' and accepts(HARD,x)
        out.append(dict(local=local,witness=x,attempts=R['attempts']))
    return out

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--track',choices=('screen','autarky','unified','stack','seek','equality'),required=True);p.add_argument('--total',type=int,required=True);p.add_argument('--batch',type=int,default=16);p.add_argument('--checkpoint',type=Path,required=True);p.add_argument('--legacy',action='store_true');p.add_argument('--hard',action='store_true');a=p.parse_args()
    assert a.batch>0 and a.total>=0
    s=json.loads(a.checkpoint.read_text()) if a.checkpoint.exists() else dict(track=a.track,total=a.total,legacy=a.legacy,next=0,counts={})
    assert (s['track'],s['total'],s['legacy'])==(a.track,a.total,a.legacy)
    C=Counter(s['counts']);case={'screen':screen_case,'autarky':autarky_case,'unified':lambda i:unified_case(i,a.legacy),'stack':stack_case,'seek':seek_case,'equality':equality_case}[a.track]
    for i in range(s['next'],min(a.total,s['next']+a.batch)):
        C.update(case(i));s.update(next=i+1,counts=dict(C));tmp=a.checkpoint.with_suffix('.tmp');tmp.write_text(json.dumps(s));tmp.replace(a.checkpoint)
    if a.hard and s['next']==a.total:s['hard']=hard(a.legacy);a.checkpoint.write_text(json.dumps(s))
    print(json.dumps(s))
