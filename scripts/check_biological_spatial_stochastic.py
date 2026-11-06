#!/usr/bin/env python3
"""P1/P2 independent finite checks of minimal phenotype classes and 3-D coupling.

The source-writer owns the Agda proofs. This fixture checks finite
computation, not kernel acceptance, genome physics, or tissue calibration.
"""
from __future__ import annotations

from itertools import product
from collections import defaultdict
import random

from check_biological_history_future_quotient import (
    ACTIONS, BiologicalState, all_states, project, update, coarse_step
)

POINTS = list(product((-1,0,1),repeat=3))


def x_neighbor(p):
    x,y,z=p
    return (0 if x else 1,y,z)


def neighbors(p):
    return [q for q in POINTS if sum(abs(a-b) for a,b in zip(q,p))==1]


def refine_minimal_morphology():
    states=list(all_states())
    labels={s:int(s.morphology) for s in states}
    steps=0
    history=[]
    while True:
        signatures={
            s:(labels[s],tuple(labels[update(a,s)] for a in ACTIONS))
            for s in states
        }
        classes={key:i for i,key in enumerate(sorted(set(signatures.values())))}
        new={s:classes[signatures[s]] for s in states}
        count=len(set(new.values()))
        history.append(count)
        # Comparing partition *relations* rather than numeric colours avoids
        # accidental relabelings that could look like non-stabilization.
        consistent=all((labels[x]==labels[y])==(new[x]==new[y])
                       for x in states for y in states)
        if consistent:
            return steps, len(set(labels.values())), history
        labels=new
        steps+=1
        if steps>64:
            raise AssertionError("finite partition exceeded state bound")


def signal_local(field,p):
    x=field[p]
    neighbor=field[x_neighbor(p)]
    return x.genome and x.memory and neighbor.junction and x.environment


def coupled_step(field,action):
    # Simultaneous old-field update, no in-place sequential mutation.
    if action=="signal":
        return {
            p:BiologicalState(x.genome,x.marker,x.memory,x.junction,
                              x.environment,signal_local(field,p))
            for p,x in field.items()
        }
    return {p:update(action,x) for p,x in field.items()}


def coarse_coupled_step(field,action):
    if action=="signal":
        out={}
        for p,code in field.items():
            g,h,j,e,m=code
            j_neighbor=field[x_neighbor(p)][2]
            out[p]=(g,h,j,e,g and h and j_neighbor and e)
        return out
    return {p:coarse_step(action,code) for p,code in field.items()}


def check():
    assert len(POINTS)==27
    edges=sum(len(neighbors(p)) for p in POINTS)
    assert edges==108 and edges//2==54
    for p in POINTS:
        n=x_neighbor(p)
        assert n in POINTS
        assert sum(abs(a-b) for a,b in zip(p,n))==1
    depth,count,history=refine_minimal_morphology()
    assert 2<=count<=64 and depth<=64
    print("Minimal morphology future quotient:", count,
          "classes, stabilization depth",depth,"history",history)

    # Both fine stochastic branches produce same coarse future code and
    # weights 1/2 + 1/2 normalize without loss.
    for x in all_states():
        for action in ACTIONS:
            result=update(action,x)
            flipped=BiologicalState(
                result.genome,not result.marker,result.memory,result.junction,
                result.environment,result.morphology)
            assert project(result)==project(flipped)
            assert project(result)==coarse_step(action,project(x))
            mass={project(result):0.5,project(flipped):0.5}
            assert sum(mass.values())==1
    rng=random.Random(20261106)
    states=list(all_states())
    for _ in range(80):
        field={p:rng.choice(states) for p in POINTS}
        cf={p:project(x) for p,x in field.items()}
        actions=[rng.choice(ACTIONS) for _ in range(4)]
        for action in actions:
            field=coupled_step(field,action)
            cf=coarse_coupled_step(cf,action)
            assert {p:project(x) for p,x in field.items()}==cf

    print("PASS: actual 3x3x3 nonperiodic coupling; randomized full-field traces")
    print("PASS: rank-bounded morphology quotient refinement and coarse stochastic mass")
    print("NO AGDA KERNEL / EMPIRICAL BIOLOGY ACCEPTANCE ASSERTED")


if __name__=="__main__":
    check()
