#!/usr/bin/env python3
"""Exact finite passive cascade energy identity; model, not device proof."""
import sympy as s

def exact_cascade_energy(n):
    k,t=s.symbols("k t",positive=True)
    stages=[s.exp(-k*t)*(k*t)**j/s.factorial(j) for j in range(n+1)]
    for j,e in enumerate(stages):
        incoming=k*stages[j-1] if j else 0
        assert s.simplify(s.diff(e,t)-(incoming-k*e))==0
    total=s.Add(*stages)
    assert s.simplify(s.diff(total,t)+k*stages[-1])==0
    return True

if __name__=="__main__":
    for n in (0,1,4,18,20):
        assert exact_cascade_energy(n)
        print(f"PASS cascade N={n}: d(sum(E))/dt=-k E_terminal")
