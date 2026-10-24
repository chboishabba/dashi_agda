#!/usr/bin/env python3
"""Regression for source-driven 6.Suz degree78 family selection gates.

Synthetic character-table receipts ONLY: exercises selection/ambiguity, C2
fidelity and the distinction between source-selected 78 and Nebe's Sym²78.
Does not claim a real GAP/CTblLib run or any Monster class position.
Primary theory: Barraclough--Wilson (2007) Section 5.1 allows ANY
eta in Irr(6.Suz); source occurrence must select the candidate.
"""
from dataclasses import dataclass
from itertools import product
import json, argparse
from pathlib import Path

@dataclass(frozen=True)
class Candidate:
    label: str
    faithful: bool
    c2_trace: int
    restricts_to_two_78: bool
    main_splits_113724: bool
    unique_main_quotient_descent: bool
    monster_multiplicity: int

def selected(families):
    surviving = []
    for f in families:
        if f.c2_trace not in (-78, 78):
            raise ValueError("central involution trace cannot be non-scalar")
        if f.faithful and f.c2_trace != -78:
            raise ValueError("faithful 6.Suz 78 must have central -1")
        if (f.restricts_to_two_78 and f.main_splits_113724
                and f.unique_main_quotient_descent
                and f.monster_multiplicity > 0):
            surviving.append(f)
    if len(surviving) != 1:
        raise ValueError(f"ambiguous/unpaid source selection: {len(surviving)}")
    f = surviving[0]
    c2 = -12 + f.c2_trace
    return {"selected_label": f.label, "faithful78": f.faithful,
            "selected_c2_trace": c2, "sym2_c2_trace": 66,
            "necessary_c2_compatible_with_sym2": c2 == 66,
            "suzuki_equivalence_proved": False}

def run():
    f = Candidate("faithful-78ab", True, -78, True, True, True, 1)
    nf = Candidate("nebe-78", False, 78, True, True, True, 1)
    distract = Candidate("different-78", False, 78, True, False, True, 0)
    fa = selected([f,distract])
    na = selected([nf,distract])
    assert fa["selected_c2_trace"] == -90 and not fa["necessary_c2_compatible_with_sym2"]
    assert na["selected_c2_trace"] == 66 and na["necessary_c2_compatible_with_sym2"]
    for bad in ([f,nf], [distract], [], [f,f]):
        try:selected(bad)
        except ValueError:pass
        else:raise AssertionError("accepted ambiguous or absent source occurrence")
    try:selected([Candidate("false-faithful", True, 78,True,True,True,1)])
    except ValueError:pass
    else:raise AssertionError("accepted impossible faithful positive-C2 character")
    assert 66 - (-90) == 156 == 2*78
    centre=[]
    z=[(1,0),(0,1),(-1,-1)]
    for a,faithful in product((1,2),(False,True)):
        # Choose same C3 as the 12, so a C3 test cannot separate families.
        C3=(90*z[a][0],90*z[a][1])
        trace=-90 if faithful else 66
        centre.append(dict(phase=a,faithful78=faithful,c3=C3,
                           norm_c3=C3[0]**2-C3[0]*C3[1]+C3[1]**2,
                           centre_c2=trace))
    assert all(x["norm_c3"]==8100 for x in centre)
    # Two 78-row candidates may share all tested central C2/C3 values
    # while differing on an ordinary NONCENTRAL class. Therefore matching
    # centre and cyclotomic norm cannot replace all-class equality.
    same_centre_sym2 = (78, 78, 78, 78, 6)
    same_centre_other = (78, 78, 78, 78, 8)
    assert same_centre_sym2[:4] == same_centre_other[:4]
    assert same_centre_sym2 != same_centre_other
    # The producer's conjugate outer family has two class-function matches
    # for both Sym² and dual Sym², or none; a single isolated match fails.
    def source_full_character_equal(direct_count, dual_count):
        if direct_count not in (0,2) or dual_count not in (0,2):
            raise ValueError("partial or excess conjugate-pair match")
        return direct_count == dual_count == 2
    assert source_full_character_equal(2,2)
    assert not source_full_character_equal(0,0)
    assert not source_full_character_equal(2,0)
    for d,v in [(1,2),(2,1),(-1,0),(4,2)]:
        try: source_full_character_equal(d,v)
        except ValueError: pass
        else: raise AssertionError("accepted invalid full-character counts")
    # Equal-centre phase pairs: both nontrivial families admit two matches;
    # a trivial-centre candidate cannot align with faithful 12.
    for p in (1,2):
        faithful_12 = [p, (-p)%3]
        same_phase_78 = [p, (-p)%3]
        trivial_78 = [0,0]
        assert sum(int(a==b) for a in faithful_12 for b in same_phase_78)==2
        assert sum(int(a==b) for a in faithful_12 for b in trivial_78)==0
    return dict(status="LOCAL_SYNTHETIC_SELECTION_AND_CENTRAL_CHARACTER_PASS",
                faithful_path=fa,nonfaithful_path=na,
                expected_negative_controls=5,
                phase_examples=centre,
                source_full_character_synthetic_control=True,
                common729_C3_equal_phase_synthetic_control=True,
                source_genuine_Monster_receipt_present=False,
                gap_executed=False,agda_kernel_verified=False)

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--receipt",type=Path)
    args=p.parse_args();report=json.dumps(run(),indent=2)+"\n"
    if args.receipt:args.receipt.write_text(report)
    print(report,end="")
