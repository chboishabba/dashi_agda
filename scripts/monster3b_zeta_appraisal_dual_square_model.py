#!/usr/bin/env python3
"""Finite chosen-chart consumer of the MERGED zeta/appraisal commuting square.

Original owners (reused): Monster3BCentralCharacterInertiaExact,
Base369Monster3BActualMultiplicitySliceAppraisalBidiExact and
Base369AppraisalHeisenbergMonomialActionBidiExact (merged #695).
#1098 owns AtlasRep source normalizer, #1250 source character matcher.
IbrahimZeta54AlbertPair53SnowballAttributionBidiExact is a DIFFERENT
54/53 carrier square and is not conflated with this Monster model.
Finite model only: NO actual source phase recognition, Monster Hom,
kernel theorem, actual 6.Suz 78 selection or IIT physical semantics.
"""
import json
from itertools import product
import monster3b_mixed8_ordered_E3_pointed729_bidi as chart

Q=tuple(product(chart.E,repeat=3))
UNIT=tuple(tuple(tuple(1 if 2*j+k==i else 0 for k in range(2))
                 for j in range(3)) for i in range(6))

def add(x,v):
    return tuple(tuple((a+b)%3 for a,b in zip(u,w)) for u,w in zip(x,v))

def dot(x,v):
    return sum(a*b for u,w in zip(x,v) for a,b in zip(u,w))%3

def on_q(q):
    return tuple(chart.m(x) for x in q)

def neg_q(q):
    return tuple(tuple((-x)%3 for x in pair) for pair in q)

def evaluate(s,q,mu):
    assert s in (1,2) and q in Q and 0<=mu<90
    return s,chart.encode729(*q),mu

def mirror_actual(st):
    s,address,mu=st
    return (-s)%3,chart.encode729(*on_q(chart.decode729(address))),mu

def translation_actual(st,v):
    s,address,mu=st
    return s,chart.encode729(*add(chart.decode729(address),v)),mu

def modulation_exponent(st,v):
    s,address,_=st
    return s*dot(chart.decode729(address),v)%3

def verify():
    diagram=translation=modulation=swap=0
    for s,mu,q in product((1,2),range(90),Q):
        source=evaluate(s,q,mu)
        target=evaluate((-s)%3,on_q(q),mu)
        assert mirror_actual(source)==target
        diagram+=1
        assert mirror_actual(source)[0]!=s
        swap+=1
        for v in UNIT:
            assert mirror_actual(translation_actual(source,v))==translation_actual(target,on_q(v))
            translation+=1
            assert modulation_exponent(source,v)==modulation_exponent(target,neg_q(on_q(v)))
            modulation+=1
    assert (diagram,translation,modulation,swap)==(131220,787320,787320,131220)
    return dict(schema="monster3b-zeta-appraisal-90-slice-dual-phase-conditional-model-v1",
        states=1458*90,appraisal_square_checks=diagram,
        translation_square_checks=translation,modulation_square_checks=modulation,
        mirror_changes_phase_checks=swap,
        total_checks=diagram+translation+modulation+swap,
        actual_source_inverter_word_selected=False,
        actual_plus_minus_sector_recognitions_supplied=False,
        same_source_Monster_Hom_selected=False,agda_kernel_checked=False,
        status="FINITE_CONDITIONAL_TWO_PHASE_SQUARE_ONLY")

if __name__=="__main__":
    print(json.dumps(verify(),indent=2,sort_keys=True))
