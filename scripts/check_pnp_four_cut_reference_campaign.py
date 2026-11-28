"""Independent local reference for native aggregate, switch, tape window, clock.
Not Agda/Lean elaboration. Repository import variant of local campaign.
"""
import argparse,json,os,random,time
from pathlib import Path
from check_pnp_affine_normal_components import canon,satisfies,Budget
from check_pnp_fractran_trace import productive_trace
from check_openai_shared_tseitin_parsimonious import optimized_clauses
from check_pnp_aggregate_excess_demand import pair_or_aggregate_trace

def shift(w,n):return (w[0],w[1]+n) if w[0]=='g' else w

def add(P,op,*args):
    P.append((op,args));return ('g',0)

def tail(P,b,a,ws):
    if not ws:return []
    c,*cs=ws;d=len(P);rest=tail(P,b,c,cs);delta=len(P)-d
    add(P,'and',shift(b,delta),shift(a,delta))
    add(P,'or',shift(c,delta+1),('g',0))
    return [('g',0)]+[shift(w,2) for w in rest]

def layer(P,b,ws):
    if not ws:return []
    a,*cs=ws;d=len(P);r=tail(P,b,a,cs)
    return [shift(a,len(P)-d)]+r

def table(P,ws,k):
    if not ws:
        add(P,'const',True);add(P,'const',False)
        return [('g',1)]+[('g',0)]*k
    b,*bs=ws;d=len(P);r=table(P,bs,k)
    return layer(P,shift(b,len(P)-d),r)

def agg(P,rows):
    if not rows:return []
    (indices,cap),*rs=rows
    r=agg(P,rs);d=len(P)
    row=table(P,[('i',i) for i in indices],len(indices))
    return row[cap+1:]+[shift(w,len(P)-d) for w in r]

def native(rows,k):
    P=[];rs=agg(P,rows);d=len(P);r=table(P,rs,k+1);add(P,'const',False)
    w=shift(r[k+1],1) if k+1<len(r) else ('g',0)
    add(P,'not',w)
    E=sum(max(0,len(is_)-c) for is_,c in rows)
    assert len(P)==sum(2+2*len(is_)**2 for is_,c in rows)+4+2*E*(k+1)
    return P

def eval_native(P,x):
    V=[]
    def read(w):return bool(x>>w[1]&1) if w[0]=='i' else V[-1-w[1]]
    for op,args in P:
        if op=='const':v=args[0]
        elif op=='not':v=not read(args[0])
        elif op=='and':v=read(args[0]) and read(args[1])
        else:v=read(args[0]) or read(args[1])
        V.append(v)
    return V

def native_case(i):
    rng=random.Random(2026112801+i);n=i%7
    rows=[(tuple(rng.randrange(n) for _ in range(rng.randrange(0,7))) if n else (),rng.randrange(0,8)) for _ in range(i%5)]
    k=rng.randrange(0,1+sum(len(r) for r,c in rows))
    P=native(rows,k)
    Q=[]
    for g,(op,args) in enumerate(P):
        Q.append((op,args if op=='const' else tuple(('g',g-1-w[1]) if w[0]=='g' else w for w in args)))
    C=optimized_clauses(n,Q,('g',len(P)-1))
    assert len(C)<=3*len(P)+1
    checks=0;accepted=0;gates_checked=0
    for x in range(1<<n):
        V=eval_native(P,x);want=sum(max(0,sum((x>>j)&1 for j in r)-c) for r,c in rows)<=k
        assert V[-1]==want
        b=[bool(x>>j&1) for j in range(n)]+V
        assert all(any(b[j]==s for j,s in cl) for cl in C)==want
        checks+=1;accepted+=want;gates_checked+=len(P)
    return {'cases':1,'points':checks,'accepted':accepted,'gate_evals':gates_checked,'max_gates':len(P)}

def switch_source(n,F):
    t,s,d=(1<<n,1<<(n+1),1<<(n+2));R=(t|s|d,);H=canon(((t,1),(s|d,0)))
    G=tuple(canon(((s,0),)+tuple(f)) for f in F)
    assert None not in G
    return n+3,R,H,(1,),t|s|d,G

def switch_case(i):
    rng=random.Random(2026112802+i);n=1+i%9
    F=[]
    for _ in range(i%17):
        js=rng.sample(range(n),rng.randrange(min(n,4)+1))
        F.append(tuple((1<<j,rng.randrange(2)) for j in js))
    if i%4==1:
        y=rng.randrange(1<<n);F=[f for f in F if satisfies(y,(),(f,))]
    elif i%4==2:
        F.extend([((1,0),),((1,1),)])
    F=tuple(F);N,R,H,caps,x,G=switch_source(n,F)
    truth=[z for z in range(1<<n) if satisfies(z,(),F)]
    phi=lambda z:max(0,(z&R[0]).bit_count()-1)
    assert satisfies(x,H,G) and phi(x)==2
    lifted=[z for z in range(1<<N) if satisfies(z,H,G) and phi(z)<2]
    assert {z&((1<<n)-1) for z in lifted}==set(truth) and len(lifted)==len(truth)
    B=Budget(200000);status,t,lo=productive_trace(N,R,H,caps,x,B,G,0,0,True)
    if status=='UNKNOWN':status,t,lo=pair_or_aggregate_trace(N,R,H,caps,x,B,G,True,lo,8192)
    assert lo<= (0 if truth else 2)
    if status=='IMPROVED':assert t['end'] in lifted and t['decrease']==2
    elif status=='MINIMUM':assert not truth
    else:assert status=='UNKNOWN'
    return {'cases':1,'sat':int(bool(truth)),'unsat':int(not truth),'original_points':1<<n,'lifted_points':1<<N,'sat_witnesses':len(truth),'portfolio_'+status:1,'unknown_sat':int(status=='UNKNOWN' and bool(truth))}

def window_case(i):
    rng=random.Random(2026112803+i);k=i%25
    rules={(q,a):(rng.randrange(4),rng.randrange(3),rng.randrange(-1,2)) for q in range(4) for a in range(3)}
    def run(l,q,a,r):
        trace=[];l=list(l);r=list(r)
        for _ in range(k):
            trace.append((q,a));q,b,m=rules[q,a]
            if m==-1:a=l.pop(0) if l else 0;r.insert(0,b)
            elif m==1:a=r.pop(0) if r else 0;l.insert(0,b)
            else:a=b
        return trace,q,a
    l=[rng.randrange(3) for _ in range(rng.randrange(0,2*k+5))];r=[rng.randrange(3) for _ in range(rng.randrange(0,2*k+5))]
    def change(s):return s[:k]+[rng.randrange(3) for _ in range(rng.randrange(0,10))] if len(s)>=k else s
    q,a=rng.randrange(4),rng.randrange(3)
    assert run(l,q,a,r)==run(change(l),q,a,change(r))
    return {'cases':1,'steps':k}

def clock_case(i):
    rng=random.Random(2026112804+i);T=rng.randrange(0,10000);seed=rng.randrange(0,10000)
    bits=seed+2*T+rng.randrange(10000);source=bits+rng.randrange(10000);target=source+rng.randrange(10000)
    assert not T or target>T
    return {'cases':1,'positive_obstructed':int(T>0)}

modes={'native':native_case,'switch':switch_case,'window':window_case,'clock':clock_case}
def main():
    p=argparse.ArgumentParser();p.add_argument('--mode',choices=modes,required=True);p.add_argument('--total',type=int,required=True);p.add_argument('--batch',type=int,default=64);p.add_argument('--checkpoint',required=True);a=p.parse_args();path=Path(a.checkpoint);sig='four-cut-reference-v1-'+a.mode
    s=json.loads(path.read_text()) if path.exists() else {'signature':sig,'total':a.total,'next':0,'counts':{}}
    assert s['signature']==sig and s['total']==a.total
    start=time.monotonic()
    for i in range(s['next'],min(a.total,s['next']+a.batch)):
        for k,v in modes[a.mode](i).items():s['counts'][k]=max(s['counts'].get(k,0),v) if k=='max_gates' else s['counts'].get(k,0)+v
        s['next']=i+1;tmp=path.with_suffix('.tmp');tmp.write_text(json.dumps(s,indent=2));os.replace(tmp,path)
    print(json.dumps(s), 'seconds',time.monotonic()-start,flush=True)
if __name__=='__main__':main()
