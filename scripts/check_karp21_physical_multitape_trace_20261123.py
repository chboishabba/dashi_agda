#!/usr/bin/env python3
"""N21 original gamma signed graph / chronological endpoint word through a
   local-head *instrumented* three-tape interpreter and terminal comparison.

   This is a concrete bit-cell/head movement and live-copy accounting reference,
   NOT a finite Agda TableProgram or an F3 kernel theorem. Host Python controls
   branch dispatch, tape offsets, loops and allocated register descriptors;
   these are explicitly counted as uncompiled control / pointer debt.
   All source operand bit reads, writes and revisits use local tape heads.
"""
from itertools import combinations,product
from random import Random

class Tape:
    def __init__(self,bits=()):
        self.cells=list(bits);self.head=0;self.steps=0;self.peak=len(self.cells)
    def seek(self,k):
        assert k>=0
        while self.head!=k:
            self.head+=1 if self.head<k else -1
            self.steps+=1
    def read(self):
        self.steps+=1
        return self.cells[self.head] if self.head<len(self.cells) else None
    def write(self,cell):
        self.steps+=1
        if self.head==len(self.cells):self.cells.append(cell)
        elif self.head<len(self.cells):self.cells[self.head]=cell
        else:raise AssertionError('nonlocal tape write')
        self.peak=max(self.peak,len(self.cells))
    def length_by_head(self,start):
        self.seek(start);n=0
        while self.read() is not None:
            self.head+=1;self.steps+=1;n+=1
        self.seek(start)
        return n

class Machine:
    def __init__(self,word,certificate):
        self.source=Tape(word);self.cert=Tape(certificate);self.work=Tape()
        self.pc=0;self.cc=0;self.history=[];self.trace=[];self.spans=[]
        self.comp=0;self.allocs=0;self.max_control_refs=0
    def put(self,bits):
        bits=tuple(bits);at=len(self.work.cells)
        self.work.seek(at)
        for bit in bits:
            assert bit in (0,1)
            self.work.write(bit);self.work.head+=1;self.work.steps+=1
        self.work.write(2);self.work.head+=1;self.work.steps+=1
        self.allocs+=1
        return (at,len(bits))
    def take(self,ref):
        a,n=ref;self.work.seek(a);out=[]
        for _ in range(n):
            z=self.work.read();assert z in (0,1)
            out.append(z);self.work.head+=1;self.work.steps+=1
        assert self.work.read()==2
        return tuple(out)
    def prefix(self):
        start=self.pc
        self.source.seek(self.pc);zeroes=0
        while True:
            z=self.source.read()
            if z is None:return None
            self.source.head+=1;self.source.steps+=1;self.pc+=1
            if z==1:break
            if z!=0:return None
            self.put((1,)) # source-original count tracked physically (one mark)
            zeroes+=1
        payload=[1]
        for _ in range(zeroes):
            z=self.source.read()
            if z is None or z not in (0,1):return None
            payload.append(z);self.source.head+=1;self.source.steps+=1;self.pc+=1
        bits=tuple(reversed(payload))
        self.spans.append((start,self.pc))
        return self.put(dec(bits))
    def certbit(self):
        self.cert.seek(self.cc);z=self.cert.read()
        if z is None or z not in (0,1):return None
        self.cc+=1
        return z
    def check(self,word,cert):
        if any(type(x)!=int or x not in (0,1) for x in word+cert):return False
        n=self.prefix();m=self.prefix()
        if n is None or m is None:return False
        nbits=self.take(n);mbits=self.take(m)
        remaining=self.source.length_by_head(self.pc)
        # EXACT raw source guard 3*m <= remaining, no phantom binomial(n,2).
        if lt(le(remaining),mul3(mbits)):return False
        before=None;edgewords=[];mcur=mbits
        # The m-loop decrements an original *binary* register.
        while mcur:
            fields=[self.prefix(),self.prefix(),self.prefix()]
            if any(f is None for f in fields):return False
            u,v,z=(self.take(x) for x in fields)
            if not (lt(u,v) and lt(v,nbits)):return False
            if before is not None and not (lt(before[0],u) or (eq(before[0],u) and lt(before[1],v))):return False
            edgewords.append((fields[0],fields[1],fields[2]))
            before=(u,v);mcur=dec(mcur)
            self.max_control_refs=max(self.max_control_refs,len(edgewords)*3)
        threshold=self.prefix()
        if threshold is None or not self.take(threshold):return False
        if self.source.length_by_head(self.pc)!=0:return False
        # Constructive BIDI: every original source bit is retained in one
        # and only one positional gamma token, including the terminal W.
        assert self.spans and self.spans[0][0]==0
        assert all(a[1]==b[0] for a,b in zip(self.spans,self.spans[1:]))
        assert self.spans[-1][1]==len(word)
        assert tuple(z for a,b in self.spans for z in word[a:b])==tuple(word)
        positive=self.put(());negative=self.put(())
        for uref,vref,zref in edgewords:
            a=self.certbit();b=self.certbit()
            if a is None or b is None:return False
            u,v,z=self.take(uref),self.take(vref),self.take(zref)
            for old,oldbit in self.history:
                self.comp+=2
                if eq(self.take(old),u) and oldbit!=a:return False
                if eq(self.take(old),v) and oldbit!=b:return False
            self.history.insert(0,(vref,b));self.history.insert(0,(uref,a))
            self.max_control_refs=max(self.max_control_refs,len(self.history)*2+len(edgewords)*3)
            if a!=b:
                sign=z[0] if z else 0
                magnitude=z[1:] if sign==0 else inc(z[1:])
                if sign==0:positive=self.put(add(self.take(positive),magnitude))
                else:negative=self.put(add(self.take(negative),magnitude))
            self.trace.append('advance')
        if self.cert.length_by_head(self.cc)!=0:return False
        # True endpoint-history reverse: unique chronological original
        # 2m certificate is reconstructed from physical tape-stored records.
        restored=[]
        for j in range(len(edgewords)-1,-1,-1):
            uref,vref,zref=edgewords[j]
            observed=self.history[2*(len(edgewords)-1-j):2*(len(edgewords)-j)]
            assert [x[0] for x in observed]==[uref,vref]
            restored.extend(x[1] for x in observed)
        cert_recovered=tuple(reversed([restored[j:j+2] for j in range(0,len(restored),2)]))
        cert_recovered=tuple(x for pair in cert_recovered for x in pair)
        assert cert_recovered==tuple(cert)
        accept=not lt(self.take(positive),add(self.take(negative),self.take(threshold)))
        self.trace.append('finish' if accept else 'reject')
        return accept
    def costs(self):
        moves=self.source.steps+self.cert.steps+self.work.steps
        heap=self.source.peak+self.cert.peak+self.work.peak
        # Conservatively account for *uncompiled* host cursors/ref descriptors
        # in logical bits. Their physical instruction cost remains unpaid.
        L=max(self.source.peak+self.cert.peak,1)
        control_bits=(self.max_control_refs+len(self.history)*2+self.allocs+8)*(L+1).bit_length()
        return moves,heap,control_bits,self.comp

def trim(bits):
    bits=list(bits)
    while bits and bits[-1]==0:bits.pop()
    return tuple(bits)
def le(n):
    assert n>=0
    return tuple((n>>j)&1 for j in range(n.bit_length()))
def dec(bits):
    bits=list(bits);carry=1
    for j in range(len(bits)):
        if not carry:break
        if bits[j]:bits[j]=0;carry=0
        else:bits[j]=1
    assert not carry # original gamma payload is strictly >=1
    return trim(bits)
def inc(bits):return add(bits,(1,))
def add(x,y):
    out=[];c=0
    for i in range(max(len(x),len(y))):
        s=(x[i] if i<len(x) else 0)+(y[i] if i<len(y) else 0)+c
        out.append(s&1);c=s>>1
    if c:out.append(c)
    return trim(out)
def mul3(x):return add(x,add(x,x))
def eq(x,y):return trim(x)==trim(y)
def lt(x,y):
    x,y=trim(x),trim(y)
    if len(x)!=len(y):return len(x)<len(y)
    return tuple(reversed(x))<tuple(reversed(y))
def val(x):return sum(v<<i for i,v in enumerate(x))
def gamma(z):
    b=bin(z+1)[2:];return tuple([0]*(len(b)-1)+[int(j) for j in b])
def graph(n,edges,W):
    out=gamma(n)+gamma(len(edges))
    for u,v,w in edges:out+=gamma(u)+gamma(v)+gamma(2*w if w>=0 else -2*w-1)
    return out+gamma(W)
def original(word,cert):
    if any(x not in (0,1) for x in word+cert):return False
    def g(p):
        if p>=len(word):return None
        j=0
        while p+j<len(word) and word[p+j]==0:j+=1
        if p+2*j+1>len(word):return None
        return int(''.join(str(x) for x in word[p+j:p+2*j+1]),2)-1,p+2*j+1
    a=g(0)
    if a is None:return False
    n,p=a;a=g(p)
    if a is None:return False
    m,p=a
    if 3*m>len(word)-p:return False
    edges=[];last=(-1,-1)
    for _ in range(m):
        row=[]
        for _ in range(3):
            a=g(p)
            if a is None:return False
            row.append(a[0]);p=a[1]
        u,v,z=row
        if not 0<=u<v<n or (u,v)<=last:return False
        edges.append((u,v,z//2 if z%2==0 else -(z+1)//2));last=(u,v)
    a=g(p)
    if a is None or a[0]<=0 or a[1]!=len(word) or len(cert)!=2*m:return False
    W=a[0];seen={};score=0
    for (u,v,w),x,y in zip(edges,cert[::2],cert[1::2]):
        for vert,label in [(u,x),(v,y)]:
            if vert in seen and seen[vert]!=label:return False
            seen[vert]=label
        if x!=y:score+=w
    return score>=W

def run():
    rng=Random(20261123);tests=0;accepted=0;maxsteps=maxheap=maxcontrol=0
    def test(w,c):
        nonlocal tests,accepted,maxsteps,maxheap,maxcontrol
        machine=Machine(w,c)
        got=machine.check(w,c);expected=original(w,c)
        assert got==expected,(w,c,got,expected,machine.trace)
        N=len(w)+len(c);steps,heap,ctrl,cnt=machine.costs()
        assert cnt<=2*(len(c)//2)**2
        assert heap+ctrl<=64*(N+1)**3
        assert steps<=64*(N+1)**5
        if machine.trace:assert machine.trace[-1] in ('finish','reject') or not got
        tests+=1;accepted+=got
        maxsteps=max(maxsteps,steps);maxheap=max(maxheap,heap);maxcontrol=max(maxcontrol,ctrl)
    for n in range(1,6):
        vertices=list(combinations(range(n),2))
        for m in range(min(2,len(vertices))+1):
            for edges in combinations(vertices,m):
                for weights in product((-3,2),repeat=m):
                    encoded=graph(n,[(*e,w) for e,w in zip(edges,weights)],1)
                    for cert in product((0,1),repeat=2*m):test(encoded,tuple(cert))
                    for v in ((),(0,),(1,1,1),(0,1,0,1,1)):
                        test(encoded,v)
    for j in range(2,19):
        n=2**j;w=graph(n,[(0,n-1,-21)],1)
        for c in ((0,0),(0,1),(1,0),(1,1),()):test(w,c)
    for _ in range(80):
        n=rng.randrange(1,8);pairs=list(combinations(range(n),2));rng.shuffle(pairs)
        edges=sorted((u,v,rng.randrange(-5,6)) for u,v in pairs[:rng.randrange(min(3,len(pairs))+1)])
        w=graph(n,edges,rng.randrange(1,8));c=tuple(rng.choice((0,1)) for _ in range(2*len(edges)))
        for k in range(len(w)+1):test(w[:k],c)
        for k in range(len(w)):
            test(w[:k]+(1-w[k],)+w[k+1:],c)
    # Longer same-original histories: interleaved repeated endpoints, signed
    # weights, and up to 16 edges rather than only 1/2-edge unit fixtures.
    for _ in range(300):
        n=rng.randrange(4,13)
        pairs=list(combinations(range(n),2));rng.shuffle(pairs)
        m=rng.randrange(min(16,len(pairs))+1)
        edges=sorted((u,v,rng.randrange(-200,201)) for u,v in pairs[:m])
        word=graph(n,edges,rng.randrange(1,50))
        cert=tuple(rng.randrange(2) for _ in range(2*m))
        test(word,cert)
    print('PASS physical local-head instrumented reference; cases',tests,'accepted',accepted,
          'max_actual_cell_operations',maxsteps,'max_live_tape_cells',maxheap,
          'max_uncompiled_controller_bits',maxcontrol)
    print('OWNERS: original gamma-all-length finite Agda table reused; full N21 control logic remains host-Python, not Agda finite table')
    print('OPEN: complete F1 finite program, F3 bounded-stuttering kernel, F2 all-program heap, F4 worst-case TM proof')
if __name__=='__main__':run()
