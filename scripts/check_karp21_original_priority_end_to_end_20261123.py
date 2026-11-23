#!/usr/bin/env python3
"""Original Karp N21: all-word gamma/zigzag graph -> binary first-enabled
priority (advance/finish/reject) -> signed two-lane ledger -> final decision.

E1 SOURCE semantic/bit-primitive regression, not compiled F1 physical finite
transition table or F4 complete TM head-motion/live-heap certificate.
Existing Agda owners: Karp21NativeWholeBinaryPriorityMachineExact,
Karp21NativeBinaryToOriginalRawMachineStepExact,
Karp21NativeWholeBinaryStepPotentialExact, and original raw graph syntax.
"""
from itertools import combinations, product
from random import Random

class Charges:
    def __init__(self):
        self.bits=self.heap=self.width=self.comparisons=self.rules=0
    def pay(self,n=1):self.bits+=n
    def size(self,*args):self.width=max(self.width,*map(len,args))

def le(n):
    assert n>=0
    return tuple((n>>i)&1 for i in range(n.bit_length()))
def val(a):return sum(b<<i for i,b in enumerate(a))
def signed(z):return z//2 if z%2==0 else -(z+1)//2
def gamma(z):
    a=tuple(map(int,bin(z+1)[2:]))
    return (0,)*(len(a)-1)+a
def encode(n,edges,T):
    word=gamma(n)+gamma(len(edges))
    for u,v,w in edges:
        word+=gamma(u)+gamma(v)+gamma(2*w if w>=0 else -2*w-1)
    return word+gamma(T)
def ref_gamma(word,pos):
    if pos>=len(word):return None
    j=0
    while pos+j<len(word) and word[pos+j]==0:j+=1
    if pos+2*j+1>len(word):return None
    v=0
    for b in word[pos+j:pos+2*j+1]:v=2*v+b
    return v-1,pos+2*j+1
def ref_parse(word):
    if any(type(b)!=int or b not in (0,1) for b in word):return None
    x=ref_gamma(word,0)
    if x is None:return None
    n,pos=x;x=ref_gamma(word,pos)
    if x is None:return None
    m,pos=x
    if 3*m+1>len(word)-pos:return None
    edges=[];prev=(-1,-1)
    for _ in range(m):
        fields=[]
        for _ in range(3):
            x=ref_gamma(word,pos)
            if x is None:return None
            y,pos=x;fields.append(y)
        u,v,z=fields
        if not 0<=u<v<n or (u,v)<=prev:return None
        edges.append((u,v,signed(z)));prev=(u,v)
    x=ref_gamma(word,pos)
    if x is None:return None
    T,end=x
    return (n,edges,T) if T>0 and end==len(word) else None
def independent_original(word,cert):
    parsed=ref_parse(word)
    if parsed is None or len(cert)!=2*len(parsed[1]) or any(type(x)!=int or x not in (0,1) for x in cert):
        return False
    _,edges,T=parsed
    seen={};score=0
    for (u,v,w),a,b in zip(edges,cert[::2],cert[1::2]):
        for vertex,bit in ((u,a),(v,b)):
            if vertex in seen and seen[vertex]!=bit:return False
            seen[vertex]=bit
        if a!=b:score+=w
    return score>=T
def native_gamma(word,pos,c):
    if pos>=len(word):return None
    j=0
    while pos+j<len(word):
        c.pay()
        if word[pos+j]==1:break
        j+=1
    if pos+j>=len(word) or pos+2*j+1>len(word):return None
    payload=word[pos+j:pos+2*j+1]
    c.pay(len(payload)+j+1);c.size(payload)
    v=0
    for bit in payload:v=2*v+bit
    return tuple(reversed(payload)),v-1,pos+2*j+1
def cmp(a,b,c):
    la,lb=le(a),le(b);c.size(la,lb)
    c.pay(2*(len(la)+len(lb)+1))
    return val(la)<val(lb)
def equal(a,b,c):
    la,lb=le(a),le(b);c.size(la,lb)
    c.pay(max(len(la),len(lb),1)+1)
    return la==lb
def add(a,b,c):
    c.size(a,b);carry=0;out=[]
    for i in range(max(len(a),len(b))):
        z=(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0)+carry
        out.append(z&1);carry=z>>1;c.pay(4)
    if carry:out.append(carry);c.pay()
    c.size(out)
    return tuple(out)
def native_parse(word,c):
    if any(type(b)!=int or b not in(0,1) for b in word):return None
    x=native_gamma(word,0,c)
    if x is None:return None
    nle,n,pos=x;x=native_gamma(word,pos,c)
    if x is None:return None
    mle,m,pos=x
    # ORIGINAL raw source has ONLY the 3*m suffix-length guard; no binomial(n,2) check.
    # Canonical strict ordered simple edges imply m<=n(n-1)/2 AFTER valid parsing.
    # Do not construct or charge a nonexistent n-squared integer register.
    # Bound m using ACTUAL remaining source length before any m-loop.
    if len(word)-pos<1 or cmp((len(word)-pos-1)//3,m,c):
        return None
    edges=[];prev=(-1,-1)
    for _ in range(m):
        fields=[]
        for _ in range(3):
            x=native_gamma(word,pos,c)
            if x is None:return None
            b,v,pos=x;fields.append((b,v))
        (ub,u),(vb,v),(zb,z)=fields
        if not cmp(u,v,c) or not cmp(v,n,c) or (u,v)<=prev:return None
        c.pay(len(ub)+len(vb)+len(zb)+3)
        prev=(u,v);edges.append((u,v,signed(z),ub,vb,zb))
    x=native_gamma(word,pos,c)
    if x is None:return None
    threshold,T,end=x
    if T<=0 or end!=len(word):return None
    c.heap=max(c.heap,len(word)+sum(len(e[3])+len(e[4])+len(e[5])+3 for e in edges))
    return n,edges,T

def first_enabled(word,cert):
    c=Charges();parsed=native_parse(word,c)
    if parsed is None or any(type(x)!=int or x not in (0,1) for x in cert):
        return False,(),c
    n,edges,T=parsed
    i=pos=0;history=[];positive=negative=();trace=[]
    while True:
        c.heap=max(c.heap,len(word)+len(cert)
            +sum(len(e[3])+len(e[4])+len(e[5])+3 for e in edges)
            +sum(len(le(u))+2 for u,label in history)+len(positive)+len(negative))
        if i<len(edges) and pos+1<len(cert):
            u,v,w,ub,vb,zb=edges[i];a,b=cert[pos:pos+2]
            valid=True
            # Actual original history: ONLY endpoints from previous edges.
            for older,label in history:
                c.comparisons+=2
                if equal(older,u,c) and label!=a:valid=False
                if equal(older,v,c) and label!=b:valid=False
            if valid:
                trace.append('advance');c.rules+=1
                history.insert(0,(v,b));history.insert(0,(u,a))
                if a!=b:
                    if w>=0:positive=add(positive,le(w),c)
                    else:negative=add(negative,le(-w),c)
                i+=1;pos+=2
                continue
        if i==len(edges) and pos==len(cert):
            c.pay(2*(len(positive)+len(negative)+T.bit_length()+2))
            ok=val(positive)>=val(negative)+T
            trace.append('finish' if ok else 'reject');c.rules+=1
            return ok,tuple(trace),c
        trace.append('reject');c.rules+=1
        return False,tuple(trace),c

def checks():
    rng=Random(20261123)
    total=accepted=malformed=0
    maxbits=maxheap=maxsteps=0
    def test(word,cert):
        nonlocal total,accepted,malformed,maxbits,maxheap,maxsteps
        got,trace,c=first_enabled(word,cert)
        assert got==independent_original(word,cert),(word,cert,trace)
        parsed=ref_parse(word)
        if parsed is None:
            assert not trace
            malformed+=1
        else:
            m=len(parsed[1])
            assert len(trace)<=m+1 and trace.count('advance')<=m
            assert all(x=='advance' for x in trace[:-1])
            assert trace[-1] in ('finish','reject')
            assert c.comparisons<=2*m*(m-1)
            S=1+len(word)+len(cert)
            assert c.bits<=100*S**4 and c.heap<=10*S**2
        total+=1;accepted+=got
        maxbits=max(maxbits,c.bits);maxheap=max(maxheap,c.heap)
        maxsteps=max(maxsteps,c.rules)
    for n in range(1,5):
        possible=list(combinations(range(n),2))
        for m in range(min(3,len(possible))+1):
            for selected in combinations(possible,m):
                for weights in product((-2,0,3),repeat=m):
                    edges=[(*uv,w) for uv,w in zip(selected,weights)]
                    for T in (1,2,5):
                        word=encode(n,edges,T)
                        for cert in product((0,1),repeat=2*m):test(word,cert)
                        for cert in [(),(0,),(0,1,0),(1,1,1,1,1,1,1)]:test(word,cert)
    for k in range(2,33):
        n=2**k;word=encode(n,[(0,n-1,-17)],1)
        for cert in [(0,1),(0,0),(1,0),(0,1,1),(),(1,)]:test(word,cert)
    for _ in range(95):
        n=rng.randrange(1,9);pairs=list(combinations(range(n),2))
        rng.shuffle(pairs)
        m=rng.randrange(min(4,len(pairs))+1)
        edges=sorted((u,v,rng.randrange(-8,9)) for u,v in pairs[:m])
        word=encode(n,edges,rng.randrange(1,10))
        for at in range(len(word)+1):test(word[:at],(0,)*(2*m))
        for at in range(len(word)):
            test(word[:at]+(1-word[at],)+word[at+1:],(0,)*(2*m))
        for tail in ((0,),(1,),(0,1),(1,1,0)):test(word+tail,(0,)*(2*m))
    print('PASS full original grammar + first-enabled source trace, invalid/malformed and signed decisions')
    print('cases',total,'accepted',accepted,'malformed',malformed,
          'max_bit_operations',maxbits,'max_heap_bits',maxheap,'max_priority_steps',maxsteps)
    print('SOURCE ONLY: terminal quotient correct; head-motion physical TableProgram/Agda F1-F4 still open')
if __name__=='__main__':checks()
