#!/usr/bin/env python3
"""Independent finite reference for #1460 original TSVF->(3,1)->KK/OS seams.

Recreates original native finite 3-state/2-stage history semantics and the
original four-axis Boolean signature classifier. Does NOT construct a
physical causal metric, time generator, postselected Hilbert or Clay YM.
"""
from itertools import product

STATES=(-1, 0, +1)

def conjugate(x): return -x
def reverse_history(h): return (conjugate(h[1]), conjugate(h[0]))
def action(h): return abs(h[0]-h[1])
def classify_probe(bit): return "temporal" if bit else "spatial"
def selected_hidden(choice): return (0, choice)
def actual_smoothing(choice): return choice
def observed_terminal(level, choice):
    return actual_smoothing(choice) if level == 2 else None
def observed_record(level, choice): return ("quiet", observed_terminal(level, choice))
def shift_arrow(_): return 0  # literal ShiftLorentzEmergenceInstance.ShiftArrow _ = zero

def main():
    histories=list(product(STATES, repeat=2))
    for h in histories:
        assert reverse_history(reverse_history(h)) == h
        assert action(reverse_history(h)) == action(h)
    assert selected_hidden(-1) != selected_hidden(+1)
    assert action(selected_hidden(-1)) == action(selected_hidden(+1)) == 1
    for choice in (-1,+1):
        assert actual_smoothing(choice) == selected_hidden(choice)[1]
        assert observed_record(0,choice) == ("quiet",None)
        assert observed_record(1,choice) == ("quiet",None)
        assert observed_record(2,choice) == ("quiet",choice)
    assert observed_record(0,-1) == observed_record(0,+1)
    assert observed_record(2,-1) != observed_record(2,+1)
    assert (observed_record(2,-1)[0], None) == (observed_record(2,+1)[0], None)

    all_probes=list(product((False,True), repeat=4))
    matches=0
    for probe, kk_probe in product(all_probes, repeat=2):
        if tuple(map(classify_probe,probe)) == tuple(map(classify_probe,kk_probe)):
            assert probe == kk_probe
            matches += 1
    assert matches == 16
    unique=[p for p in all_probes if sum(p)==1]
    assert len(unique)==4
    for p in unique:
        assert tuple(map(classify_probe,p)).count("temporal") == 1
        assert tuple(map(classify_probe,p)).count("spatial") == 3
    # Merely matching (3,1) counts leaves four distinct selected axes.
    assert unique[0] != unique[1] and sum(unique[0])==sum(unique[1])==1

    for state in product(STATES,repeat=4):
        assert shift_arrow(state)==0
    assert shift_arrow(selected_hidden(-1))==shift_arrow(selected_hidden(+1))

    print(f"PASS: {len(histories)} original history reversal/action cases")
    print("PASS: 2 original boundary choices, 3 filtration levels, early/late noninjectivity")
    print(f"PASS: {len(all_probes)} four-axis probes; {matches} same-sign agreements force identical probes")
    print(f"PASS: {len(unique)} unique directions; same signature counts ALONE rejected")
    print("PASS: 81 original 1+3 ternary shift arrow states all constant zero")
    print("REFERENCE ONLY: not Agda kernel, physical (3,1), KK, OS or Clay")

if __name__=="__main__":
    main()
