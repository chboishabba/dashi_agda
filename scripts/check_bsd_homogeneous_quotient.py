"""Finite regression for the literal homogeneous normalization, not elliptic H1."""
from itertools import product
nchecks=0
def ck(ok):
    global nchecks
    if not ok: raise RuntimeError('homogeneous quotient guard failed')
    nchecks+=1

for n,m,a in ((2,4,1),(2,8,7),(3,7,2),(4,5,2),(4,8,3)):
    G=range(n)
    act=lambda g,x: pow(a,g,m)*x%m
    delta=lambda q:tuple((act(g,q)-q)%m for g in G)
    def crossed(c):
        return all(c[(g+h)%n]==(c[g]+act(g,c[h]))%m for g,h in product(G,repeat=2))
    C=[(0,)+v for v in product(range(m),repeat=n-1) if crossed((0,)+v)]
    B={delta(q) for q in range(m)}
    ck(B<=set(C))
    def hom(c):return tuple(tuple((c[y]-c[x])%m for y in G) for x in G)
    def normalize(H):return H[0]
    def orbit(c):return frozenset(tuple((x+y)%m for x,y in zip(c,b)) for b in B)
    Q={orbit(c) for c in C}
    ck(len(Q)*len(B)==len(C))
    for c in C:
        H=hom(c)
        ck(normalize(H)==c)
        ck(all(H[(g+x)%n][(g+y)%n]==act(g,H[x][y]) for g,x,y in product(G,repeat=3)))
        ck(all((H[y][z]-H[x][z]+H[x][y])%m==0 for x,y,z in product(G,repeat=3)))
        ck((orbit(c)==orbit(tuple(0 for _ in G)))==(c in B))
        for d in C:
            e=tuple((x-y)%m for x,y in zip(c,d))
            ck((orbit(c)==orbit(d))==(e in B))
    for q in range(m):
        b=tuple(act(g,q) for g in G)
        ck(hom(delta(q))==tuple(tuple((b[y]-b[x])%m for y in G) for x in G))
    print('finite model',n,m,a,'cycles',len(C),'boundaries',len(B),'quotient',len(Q))
print(f'{nchecks}/{nchecks} exact homogeneous quotient controls PASS')
