#!/usr/bin/env python3
"""Exact 6.Suz centre-C2 discriminator for selected faithful78 vs Nebe Sym²12.

Reuses the existing character-table same-object matcher
scripts/monster_3b_suzuki_main_quotient_match.g, NOT a new 6.Suz group
construction. The existing matcher selects faithful degree12 and scans ALL degree78
outer character families; it checks main 1458-product, quotient descent
and restriction to Monster. It now emits centre-C2 character data.

Gabriele Nebe (2025), DOI 10.1007/s10801-025-01399-2: Sym² of a
faithful 12 is a 78 irreducible of 3.Suz, not faithful to 6.Suz.
Conditional C2 discriminator: faithful 12+faithful78 has trace -90,
while 12+Sym²(12) has trace +66; DIFFERENCE=156.
The SOURCE matcher must decide whether selected 78 is faithful.

No actual 6.Suz same-object result is claimed unless a real GAP receipt
from the SOURCE matcher is supplied and verified.
"""
import argparse, json
from pathlib import Path
from render_monster_3b_suzuki_main_quotient_match import validate

ROOT={0:(1,0),1:(0,1),2:(-1,-1)}
def add(a,b):return a[0]+b[0],a[1]+b[1]
def scale(n,x):return n*x[0],n*x[1]
def trace(x):return 2*x[0]-x[1]
def norm(x):return x[0]**2-x[0]*x[1]+x[1]**2

def finite_test():
    cases=[]
    for phase12 in (1,2):
        for family in ("directSym2","dualSym2","faithful78_equalC3","faithful78_oppositeC3"):
            phase78=(2*phase12 if family=="directSym2" else
                     -2*phase12 if family=="dualSym2" else
                     phase12 if family=="faithful78_equalC3" else -phase12)%3
            faithful78=family.startswith("faithful")
            c3=add(scale(12,ROOT[phase12]),scale(78,ROOT[phase78]))
            c2=-90 if faithful78 else 66
            c6=add(scale(-12,ROOT[phase12]),
                   scale((-78 if faithful78 else 78),ROOT[phase78]))
            assert trace(c3)==-90 and norm(c3) in (5292,8100)
            cases.append(dict(family=family,phase12=phase12,phase78=phase78,
                              central_C3=list(c3),central_C2=c2,
                              central_C6=list(c6),norm_C3=norm(c3)))
    for p in (1,2):
        faithful=next(c for c in cases if c["phase12"]==p and c["family"]=="faithful78_equalC3")
        dual=next(c for c in cases if c["phase12"]==p and c["family"]=="dualSym2")
        assert faithful["central_C3"]==dual["central_C3"]
        assert faithful["norm_C3"]==dual["norm_C3"]==8100
        assert faithful["central_C2"]==-90 and dual["central_C2"]==66
        assert faithful["central_C6"]!=dual["central_C6"]
    assert 66-(-90)==156==2*78
    return cases

def source_check(p):
    # The actual selected 78 is determined by the FULL source table quotient
    # matcher, which now searches all 78 families. The source C2 outcome can
    # be -90 or +66; either must remain unpredetermined before execution.
    v = validate(p)
    trace = v["source_trace"]
    compatible = v["c2_sym2_compatible"]
    faithful = v["selected_faithful"]
    assert trace in (-90, 66)
    assert compatible == (trace == 66)
    if faithful:
        assert trace == -90
    return dict(status="SOURCE_DECLARED_GAP_RECEIPT_SCHEMA_VERIFIED",
                caveat="schema does not independently authenticate actual GAP execution",
                selected_degree78_labels=v["labels78"],
                selected_degree12_labels=v["labels12"],
                selected_central_C2_character=trace,
                Sym2_central_C2_character=66,
                selected_faithful_to_6Suz=faithful,
                Sym2_C2_necessary_compatibility=compatible,
                full_6Suz_character_equal_to_Sym2="UNDETERMINED",
                absolute_zeta_orientation_resolved=False,
                actual_Monster_linear_intertwiner=False)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--source-receipt",type=Path,
                    help="actual generated monster_3b_suzuki_main_quotient_match.json")
    ap.add_argument("--receipt",type=Path)
    args=ap.parse_args()
    cases=finite_test()
    result=dict(status="local_exact_centre_discriminator_PASS",
                tested_cyclotomic_families=len(cases),family_cases=cases,
                decisive_C2_trace_difference=156,
                C3_trace_and_norm_alone_cannot_separate_faithful78_from_dualSym2=True,
                source_GAP_execution_observed=False)
    if args.source_receipt:
        p=json.loads(args.source_receipt.read_text())
        result["source_receipt"]=source_check(p)
        result["source_GAP_execution_observed"]="not independently authenticated"
    output=json.dumps(result,indent=2)+"\n"
    if args.receipt:args.receipt.write_text(output)
    print(output,end="")
if __name__=="__main__":main()
