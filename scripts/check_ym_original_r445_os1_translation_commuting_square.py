#!/usr/bin/env python3
"""Source-native R445 / OS1 finite time translation commuting-square audit.

Exact reduced noncommutative free words, no commuting-link assumption.
Fine time C4, coarse time C2; original even-origin positive two-link block.
Coarse one-step = fine TWO-step. The fixed finite coarse torus is NOT an
all-time continuum OS1 carrier. No physical RP/Hamiltonian proof here.
"""
from itertools import product
D = 4
COARSE = tuple(product(range(2), repeat=D))
FINE = tuple(product(range(4), repeat=D))

def step(x,a,n,k=1):
    y=list(x); y[a]=(y[a]+k)%n
    return tuple(y)
def reflect(x,n):
    y=list(x); y[0]=(-y[0])%n
    return tuple(y)
def link(x,a):
    return (((x,a),1),)
def inv(w):
    return tuple((v,-sgn) for v,sgn in reversed(w))
def mul(*ws):
    out=[]
    for w in ws:
        for e in w:
            if out and out[-1][0]==e[0] and out[-1][1]==-e[1]:
                out.pop()
            else:
                out.append(e)
    return tuple(out)
def fine_tau(k, field):
    return lambda x,a: field(step(x,0,4,k),a)
def coarse_tau(k, field):
    return lambda x,a: field(step(x,0,2,k),a)
def fine_r(field):
    def val(x,a):
        y=reflect(x,4)
        return inv(field(step(y,0,4,-1),0)) if a==0 else field(y,a)
    return val
def coarse_r(field):
    def val(x,a):
        y=reflect(x,2)
        return inv(field(step(y,0,2,-1),0)) if a==0 else field(y,a)
    return val
def block(field):
    def val(x,a):
        y=tuple(2*z for z in x)
        return mul(field(y,a),field(step(y,a,4),a))
    return val

def check():
    original=link
    source=block(original)
    comparisons=0
    for k in range(-4,5):
        fine_then_block=block(fine_tau(2*k,original))
        coarse_then_shift=coarse_tau(k,source)
        for x in COARSE:
            for axis in range(D):
                assert fine_then_block(x,axis)==coarse_then_shift(x,axis)
                comparisons+=1
    assert comparisons==576
    reflect_then_block=block(fine_r(original))
    block_then_reflect=coarse_r(source)
    assert all(reflect_then_block(x,a)==block_then_reflect(x,a)
               for x in COARSE for a in range(D))
    dihedral=0
    for k in range(-4,5):
        a=fine_r(fine_tau(2*k,original))
        b=fine_tau(-2*k,fine_r(original))
        for x in FINE:
            for axis in range(D):
                assert a(x,axis)==b(x,axis)
                dihedral+=1
        ac=coarse_r(coarse_tau(k,source))
        bc=coarse_tau(-k,coarse_r(source))
        assert all(ac(x,axis)==bc(x,axis) for x in COARSE for axis in range(D))
    assert dihedral==9216
    # An odd fine step shifts the original even-origin gauge blocks off
    # the source-selected native pairs. It is NOT a coarse single step.
    odd=block(fine_tau(1,original))
    wrong=coarse_tau(1,source)
    mismatches=sum(odd(x,a)!=wrong(x,a) for x in COARSE for a in range(D))
    assert mismatches==64
    # The finite coarse translation has period two; t and t+2 are
    # indistinguishable here, so an unbounded OS1 time metric CANNOT
    # be read from this fixed C2 carrier.
    assert all(coarse_tau(2,source)(x,a)==source(x,a)
               for x in COARSE for a in range(D))
    print("PASS original source B T_f^(2k) = T_c^k B: 576/576")
    print("PASS original source B theta_f = theta_c B: 64/64")
    print("PASS reflection/translation dihedral: 9216/9216")
    print("NEGATIVE odd fine-step translation fails: 64/64 mismatches")
    print("FINITE C2 alias t=t+2: no unbounded OS1 time from fixed block")
    print("OPEN Agda native Fin-coordinate kernel, CMP119 actual physical")
    print("OPEN E1/OS H and physical-time uniform D1/D2")
if __name__=="__main__":
    check()
