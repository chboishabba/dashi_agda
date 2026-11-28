"""R415-R418: exact live-carrier complement rewrites and guarded suffix obstruction."""
from itertools import combinations, product
from random import Random
from collections import Counter
from check_langlands_future_jet import rref, normalize, forget, add, violation, mask, valid, packed, frontier


def rewrite(A,p,B,q):
    if len(A)>len(B): A,p,B,q=B,q,A,p
    if len(A)==len(B):
        if tuple(a for a,b in A)!=tuple(a for a,b in B): return None
        k=next((i for i,(a,b) in enumerate(A) if b!=B[i][1]),None)
        if k is None: return None
        a,b=A[k]
        C=rref(tuple((u^a,v^b) if v!=B[i][1] else (u,v) for i,(u,v) in enumerate(A) if i!=k))
        delta={}
        add(delta,(),normalize(B,p)); add(delta,(),q)
        d=delta.get((),{})
        if set(d)-{0}: return None
        w=d.get(0,0); out=dict(p)
        if w:
            if b: out[0]=out.get(0,0)^w
            while a:
                i=a&-a; a^=i; out[i]=out.get(i,0)^w
        out=normalize(C,{i:v for i,v in out.items() if v})
        assert normalize(A,out)==p and normalize(B,out)==q
        return C,out,'parallel'
    if len(B)!=len(A)+1 or rref(A+B)!=B or normalize(B,p)!=q: return None
    a,b=next((a,b) for a,b in B if rref(A+((a,b),))!=A)
    C=rref(A+((a,1-b),)); assert C is not None
    return C,normalize(C,p),'complement'


def reduce_live(S,stats):
    while True:
        for A,B in combinations(S,2):
            stats['pair_tests']+=1
            r=rewrite(A,S[A],B,S[B])
            if r is not None: break
        else: return S
        C,p,kind=r; del S[A]; del S[B]; add(S,C,p); stats[kind]+=1


def contract(n,rows,f,cap=10000):
    stats=Counter(); B=rref(rows)
    if B is None: return 0,stats
    suffix=[0]*(len(f)+1)
    for j in range(len(f)-1,-1,-1): suffix[j]=suffix[j+1]|mask(f[j])
    S={B:normalize(B,{0:1,**{1<<i:1<<(i+1) for i in range(n)}})}; active=(1<<n)-1
    for j in range(-1,len(f)):
        T={}
        if j<0: T=S
        else:
            for B,p in S.items():
                add(T,B,p); C=rref(B+violation(f[j])); stats['attempts']+=2
                if C is not None: add(T,C,normalize(C,p))
        stats['raw_peak']=max(stats['raw_peak'],len(T))
        T=reduce_live(T,stats); keep=suffix[j+1]; dead=active&~keep; S={}
        for B,p in T.items():
            d=dead
            while d and p:
                i=d&-d; d^=i; B,p=forget(B,p,i)
            if p: add(S,B,p)
        S=reduce_live(S,stats); active=keep
        stats['peak']=max(stats['peak'],len(S))
        if len(S)>cap: return None,stats
    assert all(B==() and set(p)<={0} for B,p in S.items())
    return S.get((),{}).get(0,0),stats


def eval_packet(B,p,a):
    if not valid(a,B,()): return 0
    v=p.get(0,0)
    for i,w in p.items():
        if a&i: v^=w
    return v


def main():
    rng=Random(415); total=Counter(); outcomes=Counter()
    # A constant jump across parallel fibres is affine; a slope jump is not.
    A,B=((1,0),),((1,1),)
    assert rewrite(A,{2:1},B,{0:2,2:1})==((),{2:1,1:2},'parallel')
    assert rewrite(A,{2:1},B,{2:2}) is None
    # Pointwise verification of both rewrite laws on arbitrary affine packets.
    for n in range(1,7):
        for _ in range(80):
            A=rref(tuple((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(n))))
            if A is None: continue
            a=rng.randrange(1,1<<n); B=rref(A+((a,0),)); C=rref(A+((a,1),))
            if B is None or C is None: continue
            p=normalize(A,{i:rng.randrange(16) for i in [0]+[1<<j for j in range(n)]}); p={i:v for i,v in p.items() if v}
            for X,Y in ((A,B),(B,C)):
                u,v=normalize(X,p),normalize(Y,p); r=rewrite(X,u,Y,v); assert r is not None
                D,w,kind=r
                for x in range(1<<n): assert eval_packet(X,u,x)^eval_packet(Y,v,x)==eval_packet(D,w,x)
                total['pointwise_rewrites']+=1
    for n in range(1,8):
        for _ in range(40):
            rows=tuple((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(n+1)))
            f=[tuple(rng.choice((-1,1))*i for i in rng.sample(range(1,n+1),rng.randrange(min(3,n)+1))) for _ in range(rng.randrange(8))]
            ws=[a for a in range(1<<n) if valid(a,rows,f)]; ref=0
            for a in ws: ref^=1|(a<<1)
            for cs in (f,list(reversed(f)),rng.sample(f,len(f))):
                q,st=contract(n,rows,cs); assert q==ref==frontier(n,rows,cs)[0]; total['jet_checks']+=1
                total.update({k:st[k] for k in ('parallel','complement','pair_tests')})
            outcomes['empty' if not ws else 'unique' if len(ws)==1 else 'multi']+=1
    # All coordinates stay live across block clauses because the suffix reads them.
    for k in (1,2,4,8,16,32,64):
        n=2*k; f=[]
        for j in range(k):
            x,y=2*j+1,2*j+2
            f.extend((x,y) if b==(0,0) else (-x,y) if b==(1,0) else (x,-y) for b in ((0,0),(1,0),(0,1)))
        f.extend((i,i+1) for i in range(1,n)); f.append((n,1))
        q,st=contract(n,(),f,cap=3); a=(1<<n)-1
        assert q==1|(a<<1) and valid(a,(),f); assert st['peak']<=3
        assert packed(n,q>>1)==packed(n,a)
        old=frontier(n,(),f,cap=1000)
        if k>=8: assert old[0] is None
        else: assert old[0]==q
        print('late-read',n,'peak',st['peak'],'raw_peak',st['raw_peak'],'old_peak_or_cut',old[1],'pair_tests',st['pair_tests'])
        total['late_read']+=1
    # Guarded singleton: two reachable terms have suffix response difference equal to parity(G).
    for n in range(1,6):
        for _ in range(30):
            G=[tuple(rng.choice((-1,1))*i for i in rng.sample(range(1,n+1),rng.randrange(min(3,n)+1))) for _ in range(rng.randrange(7))]
            s,t,u=n+1,n+2,n+3; N=n+3
            suffix=[(-t,)]+[(-s,)+c for c in G]+[(s,-i) for i in list(range(1,n+1))+[u]]
            f=[(-s,),(-t,)]+suffix
            ws=[a for a in range(1<<n) if valid(a,(),G)]
            assert [a for a in range(1<<N) if valid(a,(),f)]==[0]
            q,_=contract(N,(),f); assert q==1
            p,_=contract(N,((1<<(s-1),1),),suffix); z,_=contract(N,((1<<(t-1),1),),suffix)
            assert p==((len(ws)%2)<<u) and z==0
            total['guarded_term_checks']+=1
    print(dict(total),dict(outcomes))


if __name__=='__main__': main()
