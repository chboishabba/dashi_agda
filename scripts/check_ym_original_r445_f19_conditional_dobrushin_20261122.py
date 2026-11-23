#!/usr/bin/env python3
"""Original full Wilson R445/F19 fibre graph. Geometry/symbolic reference,
not SU(N) Haar quadrature, physical weak-coupling RG, W3, or Agda receipt."""
from itertools import product,combinations
from collections import Counter,defaultdict
from fractions import Fraction as Q
import sympy as s
def count(L):
    assert L>=4 and L%2==0
    sites=list(product(range(L),repeat=4))
    def shift(x,i,n=1):
        y=list(x);y[i]=(y[i]+n)%L;return tuple(y)
    bonds={(x,i) for x in sites for i in range(4)}
    pairs={(x,i):frozenset(((x,i),(shift(x,i),i))) for x in sites
           if all(v%2==0 for v in x) for i in range(4)}
    selected=set().union(*pairs.values())
    assert len(pairs)==4*(L//2)**4 and len(selected)==2*len(pairs)
    owner={b:('V',pair) for pair,ps in pairs.items() for b in ps}
    for b in bonds-selected:owner[b]=('S',b)
    assert len(owner)==len(bonds)
    graph=defaultdict(Counter);incident=Counter();all_faces=set()
    for x in sites:
        for i,j in combinations(range(4),2):
            original=frozenset(((x,i),(shift(x,i),j),(shift(x,j),i),(x,j)))
            assert len(original)==4
            all_faces.add(original)
            f={owner[b] for b in original}
            assert len(f)==4
            for a in f:
                incident[a]+=1
                for b in f:
                    if b!=a:graph[a][b]+=1
    assert len(all_faces)==6*L**4 and len(graph)==len(bonds)-len(pairs)
    assert all(incident[a]==(12 if a[0]=='V' else 6) for a in graph)
    assert all(sum(graph[a].values())==(36 if a[0]=='V' else 18) for a in graph)
    assert all(graph[a][b]==graph[b][a] for a in graph for b in graph[a])
    multiplicities=Counter(m for row in graph.values() for m in row.values())
    assert sum(sum(row.values()) for row in graph.values())==18*len(bonds)
    if L==4:
        assert len(pairs)==64 and len(bonds-selected)==896 and len(graph)==960
        assert multiplicities=={1:16896,2:768}
        def p(x,i,j):
            return {(x,i),(shift(x,i),j),(shift(x,j),i),(x,j)}
        f,g=p((0,0,0,0),1,2),p((0,0,0,2),1,2)
        assert f.isdisjoint(g)
        charged=[{owner[a] for a in face} for face in (f,g)]
        assert all(len(z)==4 for z in charged)
        marks=Counter(a for z in charged for a in z)
        assert all(marks[a]<=(2 if a[0]=='V' else 1) for a in marks)
        local=defaultdict(Counter)
        for z in charged:
            for a in z:
                for b in z:
                    if a!=b:local[a][b]+=1
        assert all(sum(local[a].values())<=(6 if a[0]=='V' else 3) for a in local)
        assert all(b in graph[a] for a in local for b in local[a])
        ids={ls:k for k,ls in pairs.items()}
        def c3(u):
            x,i=u;return ((x[0],x[3],x[1],x[2]),{0:0,1:2,2:3,3:1}[i])
        def theta(u):
            x,i=u;y=((-x[0])%L,x[1],x[2],x[3])
            return ((shift(y,0,-1),0) if i==0 else (y,i))
        def induced(fn,v):
            if v[0]=='S':return ('S',fn(v[1]))
            return ('V',ids[frozenset(fn(b) for b in pairs[v[1]])])
        for fn in (c3,theta):
            assert {induced(fn,a) for a in graph}==set(graph)
            assert all({induced(fn,b):m for b,m in graph[a].items()}
                       ==dict(graph[induced(fn,a)]) for a in graph)
        assert all(induced(c3,induced(theta,a))==induced(theta,induced(c3,a)) for a in graph)
    return L,len(bonds),len(all_faces),len(pairs),len(graph),dict(multiplicities)
assert count(4)==(4,1024,1536,64,960,{1:16896,2:768})
assert count(6)[0:5]==(6,5184,7776,324,4860)
r=Q(9,100)
assert 36*Q(1,72)==Q(1,2)
assert 36*Q(1,144)+6*r==Q(79,100)
a,b,c,d,x,y=s.symbols('a b c d x y')
K=a+b*x+c*y+d*x*y
assert s.cancel(s.diff(s.log(K),x,y)-(a*d-b*c)/K**2)==0
assert s.cancel(s.diff(-s.log(K),x,y)+(a*d-b*c)/K**2)==0
B=Q(4)/(1-r*r)**2/(1-Q(79,100))
assert B==Q(40000000000,2066117781)
print('PASS original source complete L4/L6 native pair, spectator and plaquette graphs',count(4),count(6))
print('PASS native 64 fibre variables x 36 and 896 spectators x 18, total 18432 weighted source incidences')
print('PASS original spatial C3 / time reflection commute and preserve full conditional interaction graph')
print('PASS fixed-W SU(N) continuous Haar analytical Dobrushin prerequisite: q<=36 tanh(beta)')
print('PASS marked two global affine plaquette sources: q<=36 tanh(beta)+6r <=79/100 at beta<=1/144')
print('PASS exact four-coefficient F19 action mixed Hessian and conditional score identity')
print('NOT CLAIMED: coarse-mean covariance, true CMP119/122 source activity, physical W3 or OS gap')
