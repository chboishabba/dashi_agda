#!/usr/bin/env python3
"""SAXON Q architectural arithmetic and *ideal* Grover model.

Analysis: Johl Brown and OpenAI assistant (2026-10-26).
Experimental work: Gemsheim et al., arXiv:2609.13022 (2026).
This is NOT a simulation of calibrated SAXON Q pulses or validation of hardware.
"""
from fractions import Fraction

def claimed_capacity(cores: int, qubits_per_core: int, quantum_link=False):
    assert cores > 0 and qubits_per_core > 0
    return {"aggregate": cores * qubits_per_core,
            "native_width_bound_classical_only": None if quantum_link else qubits_per_core}

def grover_amplitudes(total: int, marked: int, iterations: int):
    """Exact amplitudes after scaling every basis amplitude by sqrt(total)."""
    assert 0 < marked <= total and iterations >= 0
    good, bad = Fraction(1), Fraction(1)
    for _ in range(iterations):
        flipped_good = -good
        mean = (marked * flipped_good + (total - marked) * bad) / total
        good, bad = 2 * mean - flipped_good, 2 * mean - bad
    return good, bad

def grover_probability(total: int, marked: int, iterations: int) -> Fraction:
    """Exact two-amplitude Grover recurrence over uniform real amplitudes.
    Returns exact probability; no trigonometry or floating-point rounding.
    """
    good, _ = grover_amplitudes(total, marked, iterations)
    return marked * good**2 / total

def test_exact() -> None:
    assert claimed_capacity(16, 8) == {"aggregate":128, "native_width_bound_classical_only":8}
    assert claimed_capacity(32, 16) == {"aggregate":512, "native_width_bound_classical_only":16}
    assert claimed_capacity(2, 5) == {"aggregate":10, "native_width_bound_classical_only":5}
    assert claimed_capacity(16, 8, quantum_link=True)["native_width_bound_classical_only"] is None
    assert grover_probability(8, 1, 2) == Fraction(121, 128)
    assert grover_probability(8, 2, 1) == Fraction(1)
    # Exact normalization over each full 8-outcome distribution.
    for marked in (1, 2, 3, 4, 5, 6, 7, 8):
        for steps in range(5):
            p = grover_probability(8, marked, steps)
            assert 0 <= p <= 1, (marked, steps, p)
            a, b = grover_amplitudes(8, marked, steps)
            assert marked * a*a + (8-marked) * b*b == 8
            assert p + Fraction(8-marked, 8) * b*b == 1
    # Compare a finite-qubit ideal circuit with full complex amplitudes
    # for all 8 possible marked singleton indices (permutation symmetry).
    for target in range(8):
        z = [Fraction(1) for _ in range(8)]
        for _ in range(2):
            z[target] = -z[target]
            mean = sum(z) / 8
            z = [2*mean-v for v in z]
        assert z[target]*z[target]/8 == Fraction(121,128)
        assert sum(v*v for v in z) == 8
    print("PASS: exact ideal Grover and classical-only architectural counting")
    
if __name__ == "__main__":
    test_exact()
