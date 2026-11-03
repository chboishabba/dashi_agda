#!/usr/bin/env python3
from fractions import Fraction
import itertools, json

TRITS=(-1,0,1)

def t5_relative():
    return [x for x in itertools.product(TRITS, repeat=5)
            if not (x[0]==x[1]==x[2]==x[3]==x[4])]

def rot5(x): return x[1:]+x[:1]
def neg(v): return tuple(-x for x in v)
def g10_t(x): return neg(rot5(x))

def e8_roots():
    out=[]
    for i,j in itertools.combinations(range(8),2):
        for si in (-2,2):
            for sj in (-2,2):
                v=[0]*8; v[i]=si; v[j]=sj; out.append(tuple(v))
    for s in itertools.product((-1,1), repeat=8):
        if sum(x<0 for x in s)%2==0:
            out.append(tuple(s))
    return out

SIMPLE=(
 (1,-1,-1,-1,-1,-1,-1,1),
 (2,2,0,0,0,0,0,0),
 (-2,2,0,0,0,0,0,0),
 (0,-2,2,0,0,0,0,0),
 (0,0,-2,2,0,0,0,0),
 (0,0,0,-2,2,0,0,0),
 (0,0,0,0,-2,2,0,0),
 (0,0,0,0,0,-2,2,0),
)

def reflect(v,a):
    d=sum(x*y for x,y in zip(v,a))
    return tuple(Fraction(x)-Fraction(d,4)*Fraction(y) for x,y in zip(v,a))

def cox(v):
    w=tuple(Fraction(x) for x in v)
    for a in SIMPLE: w=reflect(w,a)
    return w

def power(f,x,n):
    y=x
    for _ in range(n): y=f(y)
    return y

def make_g10_e(c6_action): return lambda v: neg(c6_action(v))

def orbit(f,x):
    out=[]; y=x
    while y not in out:
        out.append(y); y=f(y)
    return out

def orbit_partition(xs,f):
    seen=set(); out=[]
    for x in xs:
        if x not in seen:
            o=orbit(f,x); out.append(o); seen.update(o)
    return out

def build_equivariant_bijection(ts,rs,g10_e):
    treps=sorted(min(o) for o in orbit_partition(ts,g10_t))
    rreps=sorted(min(o) for o in orbit_partition(rs,g10_e))
    m={}
    for tr,rr in zip(treps,rreps):
        x,y=tr,rr
        for _ in range(10):
            m[x]=y; x=g10_t(x); y=g10_e(y)
    return m

def hamming(x,y): return sum(a!=b for a,b in zip(x,y))
def dot(x,y): return sum(a*b for a,b in zip(x,y))

def main():
    ts=t5_relative(); roots=e8_roots()
    rs=[tuple(Fraction(x) for x in r) for r in roots]
    assert len(ts)==240
    assert len(roots)==len(set(roots))==240
    assert sum(0 in r for r in roots)==112
    assert sum(0 not in r for r in roots)==128
    assert all(dot(r,r)==8 for r in roots)

    rootset=set(rs)
    cperm={r:cox(r) for r in rs}
    assert set(cperm.values())==rootset
    def cpow(r,n):
        y=r
        for _ in range(n): y=cperm[y]
        return y
    assert all(cpow(r,30)==r for r in rs)
    assert all(cpow(r,k)!=r for r in rs for k in range(1,30))

    c6perm={r:cpow(r,6) for r in rs}
    c6=lambda r: c6perm[r]
    assert all(power(c6,r,5)==r for r in rs)
    assert all(power(c6,r,k)!=r for r in rs for k in range(1,5))
    assert all(power(rot5,x,5)==x for x in ts)
    assert all(power(rot5,x,k)!=x for x in ts for k in range(1,5))

    g10_e=make_g10_e(c6)
    t5o=orbit_partition(ts,rot5); e5o=orbit_partition(rs,c6)
    t10o=orbit_partition(ts,g10_t); e10o=orbit_partition(rs,g10_e)
    assert len(t5o)==len(e5o)==48 and all(len(o)==5 for o in t5o+e5o)
    assert len(t10o)==len(e10o)==24 and all(len(o)==10 for o in t10o+e10o)

    m=build_equivariant_bijection(ts,rs,g10_e)
    assert len(m)==240 and len(set(m.values()))==240
    assert all(m[rot5(x)]==c6(m[x]) for x in ts)
    assert all(m[neg(x)]==neg(m[x]) for x in ts)
    assert all(m[g10_t(x)]==g10_e(m[x]) for x in ts)

    by_hamming={}; witness=None
    for i,x in enumerate(ts):
        for y in ts[i+1:]:
            h=hamming(x,y); ip=dot(m[x],m[y])
            if h in by_hamming and by_hamming[h][0]!=ip:
                ip0,x0,y0=by_hamming[h]
                witness={"hamming":h,"e8_inner_product_a":int(ip0),
                         "e8_inner_product_b":int(ip),"x":x0,
                         "y_a":y0,"y_b":y}
                break
            by_hamming.setdefault(h,(ip,x,y))
        if witness: break
    assert witness is not None

    print(json.dumps({
      "t5_relative_count":240,"e8_root_count":240,
      "e8_integer_family":112,"e8_half_family":128,
      "coxeter_order":30,"rotation_c5_orbits":48,
      "coxeter6_c5_orbits":48,"c10_orbits_each":24,
      "equivariant_bijection":True,"rotation_intertwining":True,
      "negation_intertwining":True,
      "hamming_does_not_determine_e8_inner_product":True,
      "non_isometry_witness":witness}, indent=2, default=list))

if __name__=='__main__': main()
