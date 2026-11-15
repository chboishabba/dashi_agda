#!/usr/bin/env python3
"""E2 independent source-wire native-bit verifier and polynomial NP receipts.

Source owners: Karp21NativeWholeBinaryGraphRuntimeExact, Karp21NativeWholeBinaryVerifierExact,
Karp21NativeWholeBinaryTypedAcceptanceExact, Karp21NativeOriginalSparseCertificateTightBoundExact.
No Agda kernel or E1 priority/FRACTRAN bit-TM clock is claimed.
"""
from itertools import product
from random import Random

class Tally:
    def __init__(self): self.work=0; self.max_width=0; self.max_history=0; self.max_edges=0
    def pay(self, units): self.work+=units
    def width(self, bits): self.max_width=max(self.max_width,len(bits))

def gamma(n):
    assert n >= 0
    b=bin(n+1)[2:]
    return tuple([0]*(len(b)-1)+[int(c) for c in b])
def signed_gamma(w): return gamma(2*w if w>=0 else -2*w-1)
def encode_graph(n,edges,W):
    w=gamma(n)+gamma(len(edges))
    for u,v,a in edges: w+=gamma(u)+gamma(v)+signed_gamma(a)
    return w+gamma(W)
def predle(a,T):
    a=list(a);T.width(a)
    for i,b in enumerate(a):
        T.pay(1)
        if b: a[i]=0;return tuple(a)
        a[i]=1
    return tuple(a)
def norm(a,T):
    a=list(a);T.pay(len(a));T.width(a)
    while a and a[-1]==0:a.pop()
    return tuple(a)
def less(a,b,T):
    a=norm(a,T);b=norm(b,T)
    T.pay(len(a)+len(b)+1)
    if len(a)!=len(b):return len(a)<len(b)
    for i in range(len(a)-1,-1,-1):
        T.pay(1)
        if a[i]!=b[i]: return a[i]<b[i]
    return False
def equal(a,b,T):return not less(a,b,T) and not less(b,a,T)
def anyone(a,T):T.pay(len(a));return any(a)
def add(a,b,T):
    T.width(a);T.width(b)
    out=[];carry=0
    for i in range(max(len(a),len(b))):
        T.pay(1)
        z=(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0)+carry
        out.append(z&1);carry=z>>1
    if carry:out.append(carry)
    T.width(out)
    return tuple(out)
def le_nat(n):return tuple(int(c) for c in bin(n)[2:][::-1]) if n else ()

def read_gamma(bits,pos,T):
    N=len(bits);k=0
    while pos+k<N and bits[pos+k]==0:T.pay(1);k+=1
    T.pay(1)
    if pos+k>=N or pos+2*k+1>N:return None
    payload=bits[pos+k:pos+2*k+1] # this is the n+1 bitstring, BE
    T.pay(len(payload));T.width(payload)
    return payload,pos+2*k+1

def read_nat_le(bits,pos,T):
    got=read_gamma(bits,pos,T)
    if got is None:return None
    successor_be,p=got
    return predle(successor_be[::-1],T),p

def read_signed(bits,pos,T):
    got=read_gamma(bits,pos,T)
    if got is None:return None
    successor_be,p=got
    T.pay(len(successor_be));T.width(successor_be)
    # For zigzag encoded n: n+1 is odd for w>=0, even for w<0.
    sign=1 if successor_be[-1] else -1
    magnitude=tuple(successor_be[:-1][::-1])
    return (sign,magnitude),p

def read_graph(word,T):
    N=len(word); a=read_nat_le(word,0,T)
    if a is None:return None
    n,p=a; a=read_nat_le(word,p,T)
    if a is None:return None
    m,p=a
    # B3/B4 source 3*m <= length(suffix): bit-level compare, no m allocation.
    max_m=(N-p)//3
    if less(le_nat(max_m),m,T): return None
    edges=[];prev=None
    fuel=N-p
    while anyone(m,T):
        if fuel==0:return None
        fuel-=1
        a=read_nat_le(word,p,T)
        if a is None:return None
        u,p=a
        a=read_nat_le(word,p,T)
        if a is None:return None
        v,p=a
        a=read_signed(word,p,T)
        if a is None:return None
        signed,p=a
        if not less(u,v,T) or not less(v,n,T):return None
        if prev is not None:
            x,y=prev
            if not (less(x,u,T) or (equal(x,u,T) and less(y,v,T))):return None
        edges.append((u,v,signed));T.max_edges=max(T.max_edges,len(edges))
        T.pay(len(u)+len(v)+len(signed[1])+1)
        prev=(u,v);m=predle(m,T)
    a=read_nat_le(word,p,T)
    if a is None:return None
    threshold,p=a
    if p!=N or not anyone(threshold,T):return None
    return n,edges,threshold

def verify(word,cert,stats=False):
    T=Tally();N=len(word);C=len(cert)
    parsed=read_graph(word,T)
    if parsed is None:return (False,T) if stats else False
    n,edges,threshold=parsed
    if C!=2*len(edges):return (False,T) if stats else False
    history=[];P=();M=();position=0
    for u,v,(sign,mag) in edges:
        a,b=cert[position:position+2];position+=2
        # Original source tests *both* prior-history consistency predicates
        # before mutating its chronological endpoint-history register.
        for vertex,label in ((u,a),(v,b)):
            for other,observed in history:
                if equal(vertex,other,T) and label!=observed:
                    return (False,T) if stats else False
        history=[(u,a),(v,b)]+history
        T.max_history=max(T.max_history,len(history))
        T.pay(len(u)+len(v)+2)
        if a!=b:
            if sign>0:P=add(P,mag,T)
            else:M=add(M,mag,T)
    # Original signed positive threshold: P >= M + W, no subtraction.
    result=not less(P,add(M,threshold,T),T)
    if stats:return result,T
    return result

def full_semantics(word,cert):
    # Independent integer reference mirroring original gamma/zigzag grammar,
    # Fin-free N21 endpoint consistency and signed sparse score.
    def rd(pos):
        if pos>=len(word):raise ValueError('EOF')
        k=0
        while pos+k<len(word) and word[pos+k]==0:k+=1
        if pos+2*k+1>len(word):raise ValueError('truncated gamma')
        v=0
        for bit in word[pos+k:pos+2*k+1]:v=2*v+bit
        return v-1,pos+2*k+1
    try:
        n,pos=rd(0);m,pos=rd(pos)
        if 3*m>len(word)-pos:return False
        edges=[];prev=None
        for _ in range(m):
            u,pos=rd(pos);v,pos=rd(pos);wz,pos=rd(pos)
            w=wz//2 if wz%2==0 else -(wz//2)-1
            if not (0<=u<v<n) or (prev is not None and (u,v)<=prev):return False
            prev=u,v;edges.append((u,v,w))
        W,pos=rd(pos)
        if pos!=len(word) or W<=0 or len(cert)!=2*m:return False
        history=[];score=0
        for (u,v,w),(a,b) in zip(edges,zip(cert[0::2],cert[1::2])):
            for vertex,label in ((u,a),(v,b)):
                for old,observed in history:
                    if vertex==old and label!=observed:return False
            history=[(u,a),(v,b)]+history
            if a!=b:score+=w
        return score>=W
    except ValueError:return False

# Elementary source-driven bit-width and memory accounting:
# n=|word|, c=|certificate|, S=1+n+c, m<=n/3 on parse success.
# Each endpoint/weight register width<=n, two ledgers each<=2n+2;
# each edge record <=3n+O(1), at most n edges; history<=2n entries.
# Thus all live bit storage incl. input, graph, history and ledger <=K*S^2.
# Each of at most n edge steps scans <=2n historical entries of width<=n,
# so primitive bit operations O(S^3); other scans O(S^3) on malformed
# inputs. A fixed multi-tape implementation with <=C*S^4 steps and
# <=C*S^2 visited squares compiles by the standard 1-tape track scan
# into at most A*S^8 steps; A is fixed, independent of input and cert.

def tests():
    # Source grammar positive/negative/zero weight, both label values, loops,
    # order, duplicate, huge vertex address, n exponentially larger than word.
    valid=[]
    for n in [0,1,2,3,4,5,100,2**20]:
        for edges in ([],[(0,1,-5)] if n>=2 else [] ,
                      [(0,1,7),(0,2,-9)] if n>=3 else []):
            for W in [1,2,4,9]:
                if edges and max(max(u,v) for u,v,_ in edges)>=n:continue
                valid.append(encode_graph(n,edges,W))
    rng=Random(90211)
    for _ in range(300):
        n=rng.randrange(2,25);m=rng.randrange(0,9)
        pairs=sorted(rng.sample([(u,v) for u in range(n) for v in range(u+1,n)],min(m,n*(n-1)//2)))
        es=[(u,v,rng.randrange(-1000,1001)) for u,v in pairs]
        valid.append(encode_graph(n,es,rng.randrange(1,500)))
    checked=0;success=0;maxwork=0;maxwidth=0
    for word in valid:
        # Valid graph with multiple exact/malformed certificate lengths.
        g=read_graph(word,Tally());assert g is not None
        m=len(g[1]);
        candidates=[(),(0,),(1,),tuple([0]*(2*m)),tuple([1]*(2*m)),tuple((i%2) for i in range(2*m)),tuple([0]*(2*m+1))]
        if m<=5: candidates+=list(product((0,1),repeat=2*m))
        for c in candidates:
            got,t=verify(word,c,True);exp=full_semantics(word,c)
            assert got==exp, (word,c,got,exp)
            if got:
                success+=1
                assert len(c)<=len(word) # source tight physical G3
                assert len(c)==2*m
            maxwork=max(maxwork,t.work);maxwidth=max(maxwidth,t.max_width)
            assert t.work <= 1000*(1+len(word)+len(c))**4
            checked+=1
        # Malformed: bits dropped/appended/flipped plus all prefix truncations
        corrupt=[word[:i] for i in range(len(word)+1)]+[word+(0,),word+(1,)]
        corrupt += [word[:j]+(1-b,)+word[j+1:] for j,b in enumerate(word)]
        for w in corrupt:
            for c in [(),(0,1),(1,0),(1,1),(0,0)]:
                got,t=verify(w,c,True);exp=full_semantics(w,c)
                assert got==exp,(w,c,got,exp)
                if got:assert len(c)<=len(w)
                assert t.work<=1000*(1+len(w)+len(c))**4
                checked+=1
    print('PASS original gamma(n+1), m budget, strict signed-graph parser and malformed suffix branches')
    print('PASS original sparse 2m certificate / chronological endpoint-history / signed threshold')
    print('PASS source typed/Fin-free semantic reference on',checked,'original word/certificate cases')
    print('PASS exact accepted certificate <= original graph word; accepted cases',success)
    print('PASS polynomial-width, operation envelopes for all exercised inputs; observed max work/width:',maxwork,maxwidth)
    print('THEOREM: classical standard fixed deterministic multi-tape bit verifier has O(S^4) steps and O(S^2) space,')
    print(' and can be simulated by fixed one-tape finite TM in O(S^8) steps. S=1+|word|+|certificate|.')
    print('FIREWALL: E1 exact selected priority/FRACTRAN machine clock, native typed Agda PR.InNP and kernel still OPEN')

if __name__=='__main__':tests()
