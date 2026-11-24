"""Bounded source-gain circuit and exact weighted streaming frontier (G143+)."""
from itertools import product
from random import Random
from sympy import symbols, expand

# Canonical width <=2 clauses, no repetitions; input is 2 literal bits then 8 selectors.
CLAUSES=((-1,), (1,), (-2,), (2,), (-1,-2), (-1,2), (1,-2), (1,2))
X=list(product((0,1),repeat=2))
MASK=[sum(1<<j for j,x in enumerate(X) if any(x[abs(l)-1]==(l>0) for l in c)) for c in CLAUSES]
def anchored(units):return bool(units&3 and units&12)
def score(q,alive,units,timeout):return int(bool(alive) if anchored(units) else bool(alive&(1<<(0 if timeout else q))))
def concrete(tab,clock,m,l):
    def run(mask):
        q=0;alive=15;units=mask&15
        for i in range(8):
            b=(mask>>i)&1
            if i<clock:q=tab[q][b]
            if b:alive &= MASK[i]
        s=score(q,alive,units,clock<8)
        j=(alive&-alive).bit_length()-1 if anchored(units) and alive else (0 if clock<8 else q)
        return s,X[j]
    a,x=run(m);b,y=run(m|(1<<l));return (1-a)*b,y

class Gates:
    def __init__(self):self.ops=[];self.cnf=[];self.cache={}
    def gate(self,op,*args):
        key=(op,args)
        if key in self.cache:return self.cache[key]
        z=11+len(self.ops);self.ops.append(key);self.cache[key]=z
        if op=='0':self.cnf.append((-z,))
        elif op=='1':self.cnf.append((z,))
        elif op=='!':a,=args;self.cnf.extend(((-z,-a),(z,a)))
        elif op=='&':a,b=args;self.cnf.extend(((-z,a),(-z,b),(z,-a,-b)))
        elif op=='|':a,b=args;self.cnf.extend(((z,-a),(z,-b),(-z,a,b)))
        return z
    def NOT(self,a):return self.gate('!',a)
    def AND(self,a,b):return self.gate('&',a,b)
    def OR(self,a,b):return self.gate('|',a,b)
    def fold(self,op,seq,identity):
        a=self.gate(str(identity))
        for b in seq:a=op(a,b)
        return a
    def lift(self,bits):
        a=[0]+list(bits)
        for op,vs in self.ops:
            v=[a[i] for i in vs]
            a.append(int(op=='1') if op in ('0','1') else 1-v[0] if op=='!' else v[0]&v[1] if op=='&' else v[0]|v[1])
        return a
    def sat(self,a):return all(any(a[abs(l)]==(l>0) for l in c) for c in self.cnf)

def compile_gain(tab,clock):
    g=Gates();zero=g.gate('0');one=g.gate('1')
    choose=[g.AND(1 if j&2 else g.NOT(1),2 if j&1 else g.NOT(2)) for j in range(4)]
    raw=list(range(3,11));ref=[g.OR(raw[i],choose[i]) if i<4 else raw[i] for i in range(8)]
    def run(bs):
        q=[one,zero,zero,zero]
        for b in bs[:min(clock,8)]:
            q=[g.fold(g.OR,(g.AND(q[i],b if t else g.NOT(b)) for i in range(4) for t in (0,1) if tab[i][t]==j),0) for j in range(4)]
        if clock<8:q=[one,zero,zero,zero]
        alive=[g.fold(g.AND,(g.NOT(bs[i]) for i in range(8) if not MASK[i]&(1<<j)),1) for j in range(4)]
        pin=g.AND(g.OR(bs[0],bs[1]),g.OR(bs[2],bs[3]))
        s=g.OR(g.AND(pin,g.fold(g.OR,alive,0)),g.AND(g.NOT(pin),g.fold(g.OR,(g.AND(a,b) for a,b in zip(q,alive)),0)))
        return s
    flag=g.AND(g.NOT(run(raw)),run(ref));g.cnf.append((flag,));return g,flag

# Exact transfer with source labels; every word has a single state path.
# State: chosen literal, parent and refined machine states, surviving assignment
# mask, explicit unit mask. Revised support is parent support intersect literal.
def step(tab,clock,k,s,b):
    if k<2:return (s[0]*2+b,0,0,15,0)
    i=k-2;l,q,r,A,U=s;t=b or i==l
    return (l,tab[q][b] if i<clock else q,tab[r][int(t)] if i<clock else r,A&MASK[i] if b else A,U|((1<<i) if b and i<4 else 0))
def accept(s,clock):
    l,q,r,A,U=s;return (1-score(q,A,U,clock<8))*score(r,A&MASK[l],U|(1<<l),clock<8)
def frontier(tab,clock,w,mod):
    initial=(0,0,0,15,0);rows=[{initial:1}];edges=[];support={initial:()}
    for k in range(10):
        nxt={};ed=[];new={}
        for s,v in rows[-1].items():
            for b in (0,1):
                t=step(tab,clock,k,s,b);ed.append((s,b,t));nxt[t]=(nxt.get(t,0)+v*w[k][b])%mod
                new.setdefault(t,support[s]+(b,))
        edges.append(ed);rows.append(nxt);support=new
    back={s:accept(s,clock) for s in rows[-1]};z=sum(v*back[s] for s,v in rows[-1].items())%mod
    witness=next((support[s] for s in back if back[s]),None);m=[[0,0] for _ in range(10)]
    for k in range(9,-1,-1):
        prev={s:0 for s in rows[k]}
        for s,b,t in edges[k]:
            c=w[k][b]*back[t];prev[s]=(prev[s]+c)%mod;m[k][b]=(m[k][b]+rows[k][s]*c)%mod
        back=prev
    assert back[initial]==z
    return z,m,witness,max(map(len,rows)),sum(map(len,edges))

rng=Random(369);cases=edges=unique=scalar=marg=neutral=0;maxwidth=maxedges=maxg=0
for i in range(12):
    tab=[[rng.randrange(4) for _ in range(2)] for _ in range(4)];clock=(0,4,8)[i%3]
    g,flag=compile_gain(tab,clock);maxg=max(maxg,len(g.ops))
    truth=[]
    for l in range(4):
        for m in range(256):
            bits=((l>>1)&1,l&1)+tuple((m>>j)&1 for j in range(8));v,y=concrete(tab,clock,m,l);a=g.lift(bits)
            assert a[flag]==v and g.sat(a)==bool(v);cases+=1
            if v:assert all(any(y[abs(t)-1]==(t>0) for t in c) for j,c in enumerate(CLAUSES) if (m|(1<<l))>>j&1);unique+=1
            truth.append((bits,v))
    for mod in (2,4,8,17):
        for rep in range(3):
            w=[[rng.randrange(mod),rng.randrange(mod)] for _ in range(10)] if rep else [[1,1] for _ in range(10)]
            z,ms,word,width,ec=frontier(tab,clock,w,mod);maxwidth=max(maxwidth,width);maxedges=max(maxedges,ec)
            want=0;wm=[[0,0] for _ in range(10)]
            for bits,v in truth:
                mass=v
                for k,b in enumerate(bits):mass=mass*w[k][b]%mod
                want=(want+mass)%mod
                for k,b in enumerate(bits):wm[k][b]=(wm[k][b]+mass)%mod
            assert (z,ms)==(want,wm);scalar+=1;marg+=20
            assert all((a+b)%mod==z for a,b in ms)
            assert (word is not None)==any(v for _,v in truth)
            if word:
                l=2*word[0]+word[1];m=sum(b<<i for i,b in enumerate(word[2:]));assert concrete(tab,clock,m,l)[0]
                neutral+=int(z==0)
print('compiled source comparisons',cases,'accepting lifts',unique,'scalar comparisons',scalar,'marginals',marg,'inhabited zero samples',neutral,'max gates',maxg,'max frontier',maxwidth,'max transitions',maxedges)
# Exact signed unit-face telescope over arbitrary weights.
a,b,c=symbols('a b c');assert expand(c-a-(-(a-a*b)+(c-a*b)))==0
print('symbolic residual 1/1')
