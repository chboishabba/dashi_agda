#!/usr/bin/env python3
"""Exact finite model for source-owned #1244 invariant-cylinder direct-limit SETOID.

Previous code owners: AlexanderHornedNativeTernaryFibreActionExact and
AlexanderHornedDepthTwoFiveOrbitFibreExact; Stacks Project Tag 08ZW
for the classical profinite/finite-discrete factorization background.
New explicit finite common-refinement/restriction check, 2026-10-28.
NOT Agda kernel verification, topological continuity, wild geometry or
a same-object quaternion/Monster/Spin bridge.
"""
from itertools import product
from random import Random

TRITS=(-1,0,1)
def words(n):
    if type(n) is not int or n<0 or n>7:
        raise ValueError("bounded nonnegative finite address depth required")
    return tuple(product(TRITS,repeat=n))

def reflect(w):
    return tuple(-v for v in w)

def orbit(w):
    w=tuple(w)
    return min(w, reflect(w))

def orbits(n):
    return tuple(sorted({orbit(w) for w in words(n)}))

def project_orbit(w):
    if not w:
        raise ValueError("root has no parent")
    return orbit(w[:-1])

def zero_child(w):
    return orbit(w+(0,))

def field(n, values):
    os=orbits(n)
    if len(values)!=len(os) or any(type(v) is not int or v not in (0,1,2) for v in values):
        raise ValueError("invalid invariant C3 phase table")
    return n, dict(zip(os,values))

def pullback(f):
    n,m=f
    return (n+1,{o:m[project_orbit(o)] for o in orbits(n+1)})

def restrict_zero(f):
    n,m=f
    if n==0:
        raise ValueError("cannot restrict root invariant field")
    return (n-1,{o:m[zero_child(o)] for o in orbits(n-1)})

def lift_to(f,k):
    if type(k) is not int or k<f[0] or k>7:
        raise ValueError("target must refine source")
    while f[0]<k:
        f=pullback(f)
    return f

def add(a,b):
    k=max(a[0],b[0])
    aa=lift_to(a,k)[1];bb=lift_to(b,k)[1]
    return k,{o:(aa[o]+bb[o])%3 for o in orbits(k)}

def inverse(a):
    n,m=a
    return n,{o:(-m[o])%3 for o in orbits(n)}

def same_eventually(a,b):
    k=max(a[0],b[0])
    return lift_to(a,k)[1]==lift_to(b,k)[1]

def eval_end(f, end_prefix):
    n,m=f
    if len(end_prefix)<n:
        raise ValueError("finite end sample must extend the field depth")
    return m[orbit(end_prefix[:n])]

def sample(n,rng):
    return field(n,[rng.randrange(3) for _ in orbits(n)])

def check():
    rng=Random(20261028)
    counts={}
    for n in range(7):
        assert len(orbits(n))==(3**n+1)//2
        assert len(orbits(n))*2==len(words(n))+1  # Burnside: one sign-fixed zero word
        assert len({zero_child(o) for o in orbits(n)})==len(orbits(n))
        counts[n]=dict(cells=3*3**n,orbits=len(orbits(n)),
                       invariant_fields=3**len(orbits(n)))
    assert [counts[n]['orbits'] for n in range(5)]==[1,2,5,14,41]
    assert [counts[n+1]['orbits']-counts[n]['orbits'] for n in range(5)]==[
        3**n for n in range(5)]
    assert counts[2]['invariant_fields']==243
    assert counts[3]['invariant_fields']==3**14

    # Prove split injection at EVERY invariant phase table for n<=2.
    exhaustive=0
    for n in range(3):
        os=orbits(n)
        for vals in product(range(3),repeat=len(os)):
            f=field(n,vals)
            assert restrict_zero(pullback(f))==f
            assert same_eventually(f,pullback(f))
            exhaustive+=1
    assert exhaustive==3+9+243

    # Actual common-depth laws and the direct-limit equality relation.
    checked=0
    for depth_a in range(5):
        for depth_b in range(5):
            for _ in range(80):
                a,b=sample(depth_a,rng),sample(depth_b,rng)
                c=sample(rng.randrange(5),rng)
                assert same_eventually(add(a,b),add(b,a))
                assert same_eventually(add(add(a,b),c),add(a,add(b,c)))
                assert same_eventually(add(a,inverse(a)),field(0,(0,)))
                assert same_eventually(add(inverse(a),a),field(0,(0,)))
                assert same_eventually(add(a,pullback(b)),add(a,b))
                assert same_eventually(add(pullback(a),b),add(a,b))
                # Equality on infinite ends iff equality at common depth.
                k=max(depth_a,depth_b)
                finite_samples=words(k)
                equality_on_all_ends=all(
                    eval_end(a,w)==eval_end(b,w) for w in finite_samples)
                assert equality_on_all_ends==same_eventually(a,b)
                checked+=1
    assert checked==2000
    # The invariant subgroup does NOT equal all 3^27 addresswise phases.
    assert 3**len(orbits(2))==3**5 != 3**27
    # False descent: restricting then pulling back loses child-dependent data.
    k=orbits(2)
    witness=field(2,[1 if o==(-1,0) else 0 for o in k])
    assert pullback(restrict_zero(witness))!=witness
    return {"status":"PASS","ranks_by_depth":{k:v['orbits'] for k,v in counts.items()},
            "exhaustive_invariant_fields":exhaustive,
            "common_depth_cases":checked,
            "depth2_orbit_fibre_group":3**5,
            "finite_stage_exact":"common-depth equality iff all finite-end extensions"}

if __name__=="__main__":
    print(check())
