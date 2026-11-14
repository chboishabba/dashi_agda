#!/usr/bin/env python3
"""Exact symbolic NV axial energy projection; NOT calibrated device dynamics.

Donor mathematical model: dashi_agda PR #1238, NVSpinOneAxialExact.agda
Physical model H_e = D S_z^2 + gamma B S_z (electron only).
Source-specific nuclear control cannot be inferred from this projection.
Adaptation/test: Johl Brown with OpenAI assistance, 2026-10-26.
"""
from fractions import Fraction as F

def electron_axial_energies(D, gamma, B):
    return (D + gamma*B, F(0), D - gamma*B)  # m_s = +1,0,-1

def candidate_projection(energies, choices=(0, 1)):
    assert len(energies) == 3 and len(choices) == 2
    assert all(0 <= x < 3 for x in choices) and choices[0] != choices[1]
    return tuple(energies[x] for x in choices)

def run():
    for D in [F(-3,2), F(0), F(5,3)]:
        for gamma in [F(0), F(1,4), F(7,3)]:
            for B in [F(-4), F(0), F(2)]:
                E = electron_axial_energies(D,gamma,B)
                assert E[0] - E[2] == 2*gamma*B
                Er = electron_axial_energies(D,gamma,-B)
                assert (Er[0],Er[1],Er[2]) == (E[2],E[1],E[0])
                for i in range(3):
                    for j in range(i+1,3):
                        assert candidate_projection(E,(i,j)) == (E[i],E[j])
    # Explicit counterexample to conflating chosen ket0/ket1 with ± branches.
    E = electron_axial_energies(F(3),F(2),F(0))
    assert E[0] == E[2] and E[0] != E[1]
    assert candidate_projection(E) == (F(3),F(0))
    print("PASS: axial spin-1 projection (27 parameter cases), branch exchange, typed interpretation gate")

if __name__ == "__main__":
    run()
