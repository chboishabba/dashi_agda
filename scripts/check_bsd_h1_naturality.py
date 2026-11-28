"""Finite exact H1 controls, including restriction and coefficient maps.
Not an elliptic arithmetic H1 computation or a native kernel receipt.
"""
from itertools import product
checks=0

def ck(ok):
    global checks
    if not ok: raise AssertionError('H1 naturality failed')
    checks+=1

def data(n,m,a):
    assert pow(a,n,m)==1
    def add(x,y): return tuple((u+v)%m for u,v in zip(x,y))
    def sub(x,y): return tuple((u-v)%m for u,v in zip(x,y))
    def delta(q): return tuple((pow(a,g,m)-1)*q%m for g in range(n))
    def crossed(c): return all(c[(g+h)%n]==(c[g]+pow(a,g,m)*c[h])%m for g,h in product(range(n),repeat=2))
    C=[(0,)+v for v in product(range(m),repeat=n-1) if crossed((0,)+v)]
    B={delta(q) for q in range(m)}
    def cls(c): return frozenset(add(c,b) for b in B)
    return C,B,cls,sub

# H -> G: h |-> step*h. Coefficient map x |-> mult*x, possibly
# noninjective, nontrivial or zero. Check group/action compatibility.
for n,m,a,k,l,b,step,mult in [(4,8,3,2,4,1,2,1),(4,8,3,4,4,3,1,1),(2,8,7,4,16,15,1,2),(3,7,2,3,7,2,1,3),(2,8,7,2,4,3,1,0)]:
    ck(k*step%n==0 and m*mult%l==0)
    ck(all(mult*pow(a,step*h,m)*x%l==pow(b,h,l)*mult*x%l for h in range(k) for x in range(m)))
    C,B,cls,sub=data(n,m,a); D,E,cld,sud=data(k,l,b)
    def F(c):return tuple(mult*c[step*h%n]%l for h in range(k))
    ck(all(F(c) in D for c in C));ck(all(F(c) in E for c in B))
    for c in C:
        hc=lambda x,y:(c[y]-c[x])%m
        d=F(c)
        ck(all((d[y]-d[x])%l==mult*hc(step*x%n,step*y%n)%l for x,y in product(range(k),repeat=2)))
        for e in C:
            ck((cls(c)==cls(e))==(sub(c,e) in B))
            if cls(c)==cls(e):ck(cld(F(c))==cld(F(e)))
    # Exact induced map composition with identity and class-zero reflection
    # only in the forward direction (restriction need not be injective).
    ck(all(F(c) in E for c in C if c in B))
    print('model',n,m,a,'->',k,l,b,'classes',len({cls(c) for c in C}),len({cld(c) for c in D}))

print(f'{checks}/{checks} exact H1 naturality controls PASS')
