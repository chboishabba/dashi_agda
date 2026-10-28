#!/usr/bin/env python3
"""Exact five-orbit wave-operator DOMAIN transport on 3 named C3 labels.

Reuses source-owned #1244 anchored-word normalization and five native
H-orbit operator labels. This checks finite slot/evaluation semantics
only, not physical wave PDE dynamics or Zipf probability preservation.
"""
from itertools import product
from alexander_horned_s3_word_sign_orbit_transport_exact import (
    relative,sign_orbit,transform,rgs
)

SLOTS={
    (0,0):"origin",
    (1,0):"axisFirst",
    (0,1):"axisSecond",
    (1,1):"diagonal",
    (1,2):"antiDiagonal",
}
SLOT_ORDER=tuple(SLOTS.values())
PATTERN_TO_SLOT={
    (0,0,0):"origin",
    (0,0,1):"axisSecond",
    (0,1,0):"axisFirst",
    (0,1,1):"diagonal",
    (0,1,2):"antiDiagonal",
}
def orbit_of_word(w):
    if len(w)!=3 or any(type(v) is not int or v not in range(3) for v in w):
        raise ValueError("three C3 named tokens required")
    return SLOTS[sign_orbit(relative(w))]

def evolve(operators,fields,w):
    slot=orbit_of_word(w)
    multiplier,offset=operators[slot]
    return (multiplier*fields[slot]+offset)%3

def check():
    all_words=tuple(product(range(3),repeat=3))
    assert {rgs(w):orbit_of_word(w) for w in all_words}==PATTERN_TO_SLOT
    operators=dict(zip(SLOT_ORDER, ((0,2),(1,0),(2,1),(2,0),(1,2))))
    checked=0
    for vals in product(range(3),repeat=5):
        phase=dict(zip(SLOT_ORDER,vals))
        for w in all_words:
            output=evolve(operators,phase,w)
            assert output==(
                operators[orbit_of_word(w)][0]*phase[orbit_of_word(w)] +
                operators[orbit_of_word(w)][1])%3
            for shift,sign in product(range(3),(-1,1)):
                assert evolve(operators,phase,transform(w,shift,sign))==output
                checked+=1
    assert checked==243*27*6==39366
    return {"status":"PASS","named_word_patterns":5,
            "five_orbit_fields":243,"affine_s3_operator_checks":checked,
            "boundary":"equality-pattern wave slot only, not physical or statistical identity"}

if __name__=="__main__":
    print(check())
