#!/usr/bin/env python3
"""Finite Weyl-action transport through the selected MIXED8 pointed729 codec.

Consumes the existing chosen E^3 finite chart. This phase-preserving
cotangent-model D4 lift is NOT the actual ATLAS mirror: original #1098
source mirror inverts the Heisenberg centre zeta, swapping phase sectors.
The 729 Schr translations move the central nine-point projector except
for the nine inner-plane translations. No full Monster Hom asserted.
"""
import json
from itertools import product
import monster3b_mixed8_ordered_E3_pointed729_bidi as codec

E=codec.E
F=range(3)
X=tuple(product(E,repeat=3))
TO_ADDR={x:codec.encode729(*x) for x in X}
FROM_ADDR={p:x for x,p in TO_ADDR.items()}
assert len(TO_ADDR)==len(FROM_ADDR)==729


def plus(x,y):
    return tuple(tuple((a+b)%3 for a,b in zip(u,v)) for u,v in zip(x,y))


def dot(x,y):
    return sum(a*b for u,v in zip(x,y) for a,b in zip(u,v))%3


def translated(address,v):
    return TO_ADDR[plus(FROM_ADDR[address],v)]


def modulated_phase(address,w):
    return dot(FROM_ADDR[address],w)


UNIT=[]
for i in range(6):
    e=[[0,0],[0,0],[0,0]]
    e[i//2][i%2]=1
    UNIT.append(tuple(map(tuple,e)))
UNIT=tuple(UNIT)


def verify():
    for p in FROM_ADDR:
        for i in range(6):
            v=UNIT[i]
            assert translated(translated(translated(p,v),v),v)==p
        for v in UNIT:
            for w in UNIT:
                # M_w T_v = zeta^(w.v) T_v M_w on basis ket |x>.
                assert modulated_phase(translated(p,v),w)==(
                    modulated_phase(p,w)+dot(v,w))%3
        for g in (codec.r,codec.m):
            gp=codec.target_action(p,g)
            for v in UNIT:
                gv=tuple(g(x) for x in v)
                assert codec.target_action(translated(p,v),g)==translated(gp,gv)
                # The chosen r,m are orthogonal on this MODEL E^3.
                assert modulated_phase(gp,gv)==modulated_phase(p,v)

    central={p for p in FROM_ADDR if p[0]=="central"}
    assert len(central)==9
    n_preserved=sum({translated(p,v) for p in central}==central for v in X)
    assert n_preserved==9
    return {
      "schema":"monster3b-mixed8-pointed729-weyl-transport-v1",
      "model_basis_size":729,
      "translation_generators":6,
      "modulation_generators":6,
      "weyl_generator_pair_checks":729*36,
      "D4_model_covariant_generator_checks":729*2*6,
      "central_nine_projector_preserving_translations":9,
      "central_nine_projector_moving_translations":720,
      "chosen_D4_model_lift_central_phase_preserving":True,
      "actual_ATLAS_D4_mirror_central_phase_inverting":True,
      "same_source_normalizer_lift_established":False,
      "actual_Monster_Hom_constructed":False,
      "Agda_kernel_verified":False,
      "status":"FINITE_WEYL_MODEL_ONLY"
    }


if __name__=="__main__":
    print(json.dumps(verify(),sort_keys=True,indent=2))
