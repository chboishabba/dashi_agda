#!/usr/bin/env python3
"""Dual-phase 1458 Heisenberg/D4 anti-similitude finite MODEL.

Classical Weyl/Schrodinger construction on chosen F3^6 basis; consumes
#1250 MIXED8 pointed729 and #1098 D4 source representation TYPE.
Actual ATLAS generators, 6.Suz selected78, Monster Hom and IIT are NOT
identified. Mirror exchanges zeta/zeta^2; never treat it as a linear
operator preserving one 729 sector. Source authors BW07/BMW24 retained.
"""
import json
from itertools import product
from collections import Counter
import monster3b_mixed8_ordered_E3_pointed729_bidi as chart

E=chart.E
Q=tuple(product(E,repeat=3))
PHASES=(1,2)
UNIT=tuple(tuple(tuple(int(2*j+k==i) for k in range(2))
                 for j in range(3)) for i in range(6))

def plus(q,v):
    return tuple(tuple((a+b)%3 for a,b in zip(x,y))
                 for x,y in zip(q,v))

def dot(q,w):
    return sum(a*b for x,y in zip(q,w) for a,b in zip(x,y))%3

def apply_q(q,g):
    return tuple(g(x) for x in q)

def phase_multiplier(g):
    return 1 if g is chart.r else 2

def on_state(st,g):
    s,p=st
    return (s*phase_multiplier(g)%3,
            chart.encode729(*apply_q(chart.decode729(p),g)))

def inverse_on_state(st,g):
    for _ in range(3 if g is chart.r else 1):
        st=on_state(st,g)
    return st

def translated(st,v):
    s,p=st
    return (s,chart.encode729(*plus(chart.decode729(p),v)))

def modulation(st,w):
    s,p=st
    return s*dot(chart.decode729(p),w)%3

def check():
    addrs={chart.encode729(*q):q for q in Q}
    assert len(addrs)==729
    states=tuple((s,p) for s in PHASES for p in addrs)
    assert len(states)==1458
    n=Counter()
    for st in states:
        s,p=st
        assert chart.decode729(p)==addrs[p]
        r=on_state(st,chart.r)
        m=on_state(st,chart.m)
        assert on_state(m,chart.m)==st
        assert on_state(on_state(on_state(r,chart.r),chart.r),chart.r)==st
        assert on_state(on_state(m,chart.r),chart.m)==inverse_on_state(st,chart.r)
        n["D4_relations"]+=3
        half=on_state(r,chart.r)
        assert half[0]==s
        assert half[1]==chart.encode729(*tuple(
            tuple((-a)%3 for a in e) for e in addrs[p]))
        n["halfturn"]+=1
        for g in (chart.r,chart.m):
            gs=on_state(st,g)
            lam=phase_multiplier(g)
            assert gs[0]==lam*s%3
            n["central_multiplier"]+=1
            for u in UNIT:
                gu=apply_q(u,g)
                assert on_state(translated(st,u),g)==translated(gs,gu)
                n["translation_covariance"]+=1
                gw=gu if lam==1 else tuple(tuple((-a)%3 for a in e) for e in gu)
                assert modulation(st,u)==modulation(gs,gw)
                n["modulation_covariance"]+=1
        for v in UNIT:
            assert translated(translated(translated(st,v),v),v)==st
            n["translation_order_three"]+=1
            for w in UNIT:
                assert modulation(translated(st,v),w)==(
                    modulation(st,w)+s*dot(v,w))%3
                n["weyl_pairs"]+=1
    assert n==dict(D4_relations=4374,halfturn=1458,
                   central_multiplier=2916,translation_covariance=17496,
                   modulation_covariance=17496,
                   translation_order_three=8748,weyl_pairs=52488)
    traces=dict(r=sum(on_state(st,chart.r)==st for st in states),
                r2=sum(on_state(on_state(st,chart.r),chart.r)==st for st in states),
                m=sum(on_state(st,chart.m)==st for st in states))
    assert traces==dict(r=2,r2=2,m=0)
    central={p for p in addrs if p[0]=="central"}
    fixed=sum({chart.encode729(*plus(addrs[p],v)) for p in central}==central
              for v in Q)
    assert fixed==9
    return dict(schema="monster3b-pointed729-two-phase-anti-similitude-model-v1",
        dimension=1458,sector_dimensions=[729,729],
        identity_character=1458,nonidentity_centre_character=-729,
        source_type_D4_character_traces=traces,
        D4_irrep_multiplicities=dict(A1=183,A2=183,B1=182,B2=182,E=364),
        checks=dict(n),check_total=sum(n.values()),
        preserving_nine_translations=fixed,moving_nine_translations=720,
        mirror_exchanges_phases=True,
        actual_ATLAS_generator_words_selected=False,
        genuine_6Suz78_family_selected=False,
        source_Monster_Hom_proved=False,IIT_observable_transport_proved=False,
        Agda_kernel_checked=False,status="EXACT_FINITE_DUAL_PHASE_MODEL_ONLY")

if __name__=="__main__":
    print(json.dumps(check(),indent=2,sort_keys=True))
