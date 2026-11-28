"""Local signed rank-two, cross-row, component and graph-parity acceptance.
Small truth enumerations are independent test oracles, never producer input.
"""
from check_pnp_signed_capacity_rank2 import *
from check_pnp_affine_normal_components import Budget,Exhausted
from check_pnp_signed_capacity_components import components,recover
from random import Random
from collections import Counter
from sympy import Matrix
from pathlib import Path
import json,sys,hashlib,os
rng=Random(3692712)

def ev(M,z):return sum(c*(-1 if (a&z).bit_count()%2 else 1) for a,c in M.items())

def row(n):
    cols=[(0,1)]
    for i in range(rng.randrange(2,7)):
        a=rng.randrange(1,1<<n);b=rng.randrange(2);cols.extend([(a,b)]*2)
    M={}
    for a,b in cols:add(M,0,1);add(M,a,1 if b else -1)
    return M,cols

def original(d,rows):
    H=[];R=[];n=d
    for _,cols in rows:
        mask=0
        for a,b in cols:
            H.append(((1<<n)^a,b));mask|=1<<n;n+=1
        R.append(mask)
    return n,tuple(R),canon(H)

def main():
    hist=Counter();examples={};effective=pointchecks=0
    for d in range(2,6):
        for _ in range(140):
            r=[row(d) for j in range(rng.randrange(1,4))];M=[m for m,_ in r];caps=[rng.choice(range(1,len(c)+1,2)) for _,c in r]
            B=Budget(100000000);P=portfolio(M,caps,B);D=set(directions(P,B));truth=[z for z in range(1<<d) if all(ev(m,z)<=2*c for m,c in zip(M,caps))]
            single,_,_=observe(portfolio(M,caps,B,False),B,1);joint,_,_=observe(P,B,1);Q,rec,k=observe(P,B,2)
            for X in (single,joint,Q):
                if X is None:assert not truth
                else:assert all(satisfies(z,X,()) for z in truth)
            hist['sources']+=1;hist['SAT' if truth else 'UNSAT']+=1;hist['unique']+=len(truth)==1
            if single==() and joint!=():hist['cross_row_gain']+=1;examples.setdefault('cross_row',(M,caps,truth,joint))
            if joint==() and Q!=():hist['rank2_gain']+=1;examples.setdefault('rank2',(M,caps,truth,Q))
            if joint==() and Q==():hist['rank2_stall']+=1
            if Q is None:hist['proved_empty_first']+=1
            n,R,H=original(d,r);u,V=chart(n,H);assert len(V)==d and [row_ledger(a,u,V) for a in R]==M
            points=[]
            for z in truth:
                x=u
                for i in bits(z):x^=V[i]
                points.append(x)
            K,y,reason=screen(n,R,H,caps,Budget(100000000));hist['screen_'+reason]+=1
            if K is None:assert not truth
            else:assert all(satisfies(x,K,()) for x in points)
            if reason=='stalled':
                hist['stalled_SAT' if truth else 'stalled_UNSAT']+=1
                status,y,w=recover(n,R,K,caps,Budget(100000000));assert status=='witness' and y in points
                hist['stalled_recovered']+=1
            if y is not None:
                assert y in points
                A=Matrix(len(R),n,lambda i,j:R[i]>>j&1)
                assert all(v<=c and v%2==1 for v,c in zip(A*Matrix([y>>j&1 for j in range(n)]),caps))
            status,x,w=components(d,M,caps,Budget(100000000));assert (status=='witness')==bool(truth);assert x is None or x in truth
            hist['all_components_exact']+=1
            if d<=4:
                for a,b in combinations(range(1,1<<d),2):
                    W=canon(((a,0),(b,0)));A=(W[0][0],W[1][0]);sub={0,a,b,a^b}
                    for v in product((0,1),repeat=2):
                        H=tuple(zip(A,v));E=canon(tuple((q,sum(((q>>(p.bit_length()-1))&1)*val for p,val in H)%2) for q in D&sub))
                        for m,c,p,src in P:
                            assert lower(restrict_ledger(m,H),p)==lower(restrict_ledger(m,E),p);effective+=1
                            for z in range(1<<d):
                                if satisfies(z,H,()):assert ev(m,z)==ev(restrict_ledger(m,H),z);pointchecks+=1
    for v in (4,6,8,12,16,24,32):
        edges=sorted({tuple(sorted((i,(i+1)%v))) for i in range(v)}|{(i,i+v//2) for i in range(v//2)})
        rows=tuple(sum(1<<j for j,e in enumerate(edges) if i in e) for i in range(v))
        assert canon(tuple((r,int(i==0)) for i,r in enumerate(rows))) is None
        H=canon(tuple((r,int(i<2)) for i,r in enumerate(rows)));assert H is not None and len(H)==v-1
        u,V=chart(len(edges),H);assert satisfies(u,tuple((r,int(i<2)) for i,r in enumerate(rows)),())
        hist['tseitin_odd']+=1;hist['tseitin_even']+=1
    for blocks in (2,4,8,16,32):
        M=[];caps=[]
        for j in range(blocks):
            a,b=1<<(2*j),1<<(2*j+1);M.append({0:12,a:4,b:4,a^b:2});caps.append(7)
        status,y,w=components(2*blocks,M,caps,Budget(100000000));assert status=='witness' and w==(2,)*blocks and all(ev(m,y)<=14 for m in M);hist['large_factor']+=1
        assert components(2*blocks,M,caps,Budget(100000000),width=1)[0]=='unknown';hist['width_refusal']+=1
        M.append({0:6});caps.append(1);assert components(2*blocks,M,caps,Budget(100000000))[0]=='empty';hist['large_no']+=1
    try:observe([({0:6,1:-2},1,1,(0,))],Budget(0))
    except Exhausted:hist['refusal_control']+=1
    else:raise AssertionError('expected refusal')
    here=Path(__file__).parent;files=sorted(here.glob('check_pnp_*.py'))
    key=hashlib.sha256(b''.join(p.name.encode()+b'\0'+p.read_bytes() for p in files)).hexdigest()
    receipt=dict(key=key,counts=dict(hist),effective=effective,pointchecks=pointchecks,examples=examples)
    if len(sys.argv)>1:
        path=Path(sys.argv[1]);path.parent.mkdir(parents=True,exist_ok=True);tmp=path.with_suffix('.tmp');tmp.write_text(json.dumps(receipt,indent=2));os.replace(tmp,path)
    print(receipt)
if __name__=='__main__':main()
