#!/usr/bin/env python3
"""Exact rational 3-4-5 Fourier witness for the proposed R815/W2 payment.

This is a literal finite-cube *evaluator*, independent of the rational
Agda R408 trajectory and uninhabited global helical-projector-law record.
It evaluates the R230/R692 coherent-work convention and the R515 dyadic
critical production/viscous rate.  A negative initial value is evidence
against the auxiliary universal signed W2 payment, NOT against NS itself.

All active velocity/forcing modes have Pythagorean integer lengths, so the
helical projections appearing in the nonzero work have rational entries.
"""
from __future__ import annotations
from fractions import Fraction
from itertools import product
from functools import lru_cache
from sympy import I, Matrix, Rational, S, conjugate, expand, simplify, sqrt
import json

CUT = 4
MODES = frozenset(product(range(-CUT, CUT + 1), repeat=3)) - {(0, 0, 0)}
ZERO = Matrix([0, 0, 0])
SEEDS = {
    (3, 0, 0): Matrix([0, 2+2*I, -2-I]),
    (0, 4, 0): Matrix([2+2*I, 0, 2+2*I]),
    (3, 4, 0): Matrix([6*I, -Rational(9, 2)*I, -2+2*I]),
}

def neg(k): return tuple(-z for z in k)
def sub(k,p): return tuple(x-y for x,y in zip(k,p))
def add(k,p): return tuple(x+y for x,y in zip(k,p))
def weight(k): return 2 ** ((max(map(abs,k))-1).bit_length())
def project(k,v):
    m=Matrix(k)
    return v-m*(m.dot(v)/m.dot(m))

def snapshot():
    u={}
    for k,v in SEEDS.items():
        u[k]=v
        u[neg(k)]=v.applyfunc(conjugate)
    assert all(Matrix(k).dot(v)==0 for k,v in u.items())
    assert all(u[neg(k)]==v.applyfunc(conjugate) for k,v in u.items())
    @lru_cache(None)
    def force(k):
        if k not in MODES: return ZERO
        raw=ZERO
        for p,v in u.items():
            q=sub(k,p)
            if q in u: raw+=v.dot(Matrix(q))*u[q]
        return -I*project(k,raw)
    active=set(u)
    for p in u:
        for q in u:
            k=add(p,q)
            if k in MODES: active.add(k)
    # Every mode whose nonzero velocity/force is used has rational |k|.
    norms={k:sqrt(sum(z*z for z in k)) for k in active}
    assert all(length.is_Rational for length in norms.values())
    @lru_cache(None)
    def hel(k,forc,sign):
        v=force(k) if forc else u.get(k,ZERO)
        if v==ZERO:return ZERO
        kv=Matrix(k)
        return (project(k,v)+sign*I*kv.cross(v)/norms[k])/2
    comm=S.Zero
    product_rule=S.Zero
    for k in active:
        mixed=ZERO
        comm_cell=ZERO
        product_cell=ZERO
        for p in active:
            q=sub(k,p)
            if q not in active:continue
            pplus=hel(p,False,1)
            qminus=hel(q,False,-1)
            fplus=hel(p,True,1)
            mixed+=pplus.cross(qminus)
            comm_cell+=fplus.cross(qminus)-hel(p,True,-1).cross(hel(q,False,1))
            product_cell+=fplus.cross(qminus)+pplus.cross(hel(q,True,-1))
        if mixed!=ZERO:
            comm+=sum(conjugate(mixed[j])*comm_cell[j] for j in range(3))
            product_rule+=sum(conjugate(mixed[j])*product_cell[j] for j in range(3))
    comm=simplify(2*expand(comm).as_real_imag()[0])
    product_rule=simplify(2*expand(product_rule).as_real_imag()[0])
    prod=simplify(2*sum(
        weight(k)*expand(sum(conjugate(v[j])*force(k)[j] for j in range(3))).as_real_imag()[0]
        for k,v in u.items()))
    diss=simplify(sum(weight(k)*sum(z*z for z in k)*
        sum(conjugate(v[j])*v[j] for j in range(3)) for k,v in u.items()))
    rate=simplify(6*(12*comm-prod+diss))
    assert comm==Rational(-557627,125)
    assert product_rule==comm
    assert prod==0
    assert diss==15834
    assert rate==Rational(-28273644,125)<0
    assert all(x.is_Rational for x in [comm,product_rule,prod,diss,rate])

    # Global conservative component sup-norm bootstrap on all 728 cube modes.
    # The inequalities are purely rational and do not numerically integrate.
    n=len(MODES)
    M,U0=12,6
    assert n==728
    # |P_k|_row <=4, |H^pm_k|_row <=3, |k_j|<=4, |k|^2<=48.
    P,H,cross,dot,lap=4,3,2,12,48
    F=P*n*dot*M*M
    FL=P*n*2*dot*M
    ode=F+lap*M
    hu,huL,hf,hfL=H*M,H,H*F,H*FL
    mixed=n*cross*hu*hu
    mixedL=n*cross*2*hu*huL
    comm_bound=n*2*cross*hf*hu
    commL=n*2*cross*(hfL*hu+hf*huL)
    WL=2*n*3*(mixedL*comm_bound+mixed*commL)
    prodL=2*n*3*(F+M*FL)
    dissL=n*3*lap*2*M
    rateL=6*(12*WL+prodL+dissL)
    initial_integer_margin=226189
    T=min(Fraction(M-U0,2*ode),Fraction(initial_integer_margin,2*rateL*ode))
    assert T>0 and U0+ode*T<M
    assert rate < -initial_integer_margin
    assert rateL*ode*T<=Fraction(initial_integer_margin,2)
    assert -initial_integer_margin+rateL*ode*T <= -Fraction(initial_integer_margin,2)
    # This is a mathematical finite-ODE short-time enclosure conditional
    # on the polynomial vector field and rate matching the live physical packet.
    return {
        "schema":"ns_r828_rational_345_seed.v1",
        "cube_radius":CUT,"nonzero_cube_modes":n,
        "nonzero_initial_modes":{str(k):list(map(str,v)) for k,v in SEEDS.items()},
        "active_helicity_mode_count":len(active),
        "active_helicity_norms":{str(k):str(v) for k,v in sorted(norms.items())},
        "commutator_work":str(comm),"product_rule_work":str(product_rule),
        "critical_production":str(prod),"critical_dissipation":str(diss),
        "combined":str(12*comm),"canonical_signed_rate":str(rate),
        "rate_is_negative":bool(rate<0),
        "ode_component_bound":ode,"rate_lipschitz_bound":rateL,
        "short_time_rational":str(T),
        "rate_bound_on_short_time":str(-Fraction(initial_integer_margin,2)),
        "integral_is_strictly_negative_under_exact_ode_interpretation":True,
        "R408_global_helical_projector_laws_constructed":False,
        "R408_trajectory_same_object_weld_kernel_certified":False,
        "Clay_solution_claim":False,
    }

if __name__=="__main__":
    print(json.dumps(snapshot(),indent=2))
