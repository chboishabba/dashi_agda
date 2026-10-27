#!/usr/bin/env python3
"""Source-attributed exact ideal Jones/Stokes readout and phase-code margins.

Glauser, Vonk, Seda et al., Nature 655, 87-92 (2026), Methods 23-29.
The finite idealized input/reference fields below are synthetic exact Gaussians;
they are not measured photon counts, instrumental read noise, or SI power.
"""
import json
from fractions import Fraction as F
from itertools import combinations
from check_fourier_pixel_exact import z, add, mul, conj, norm2

I = z(0, 1)
ONE = z(1)
MINUS = z(-1)
MINUS_I = z(0, -1)


def half(q):
    return q / 2


def multiply_i(field):
    return mul(I, field)


def ideal_stokes(ax, ay):
    xy = mul(conj(ax), ay)
    return (norm2(ax) + norm2(ay), norm2(ax) - norm2(ay),
            2 * xy[0], 2 * xy[1])


def recorded_stokes(ax, ay):
    ix, iy = half(norm2(ax)), half(norm2(ay))
    def interference(phase):
        return half(norm2(add(ax, mul(ay, phase))))
    i0, i90, i180, i270 = [interference(x) for x in [ONE, I, MINUS, MINUS_I]]
    return (2 * (ix + iy), 2 * (ix - iy), i0 - i180, i270 - i90)


def margin_checks():
    # (x,y) from the four-state ideal interference script.
    codewords = [(4, 2), (2, 4), (0, 2), (2, 0)]
    distances = [max(abs(u-v) for u, v in zip(a, b)) for a,b in combinations(codewords, 2)]
    min_distance = min(distances)
    assert min_distance == 2
    # Triangle inequality: if each coordinate is corrupted by strictly < 1,
    # an observation can belong to at most one codeword radius-<1 ball.
    assert min_distance >= 2
    clipped = [(min(1, a), min(1, b)) for a,b in codewords]
    assert len(set(clipped)) < len(codewords)
    return {"codeword_min_linf_distance":min_distance,
            "ideal_noise_radius_exclusive": "1",
            "codewords_unique_before_clipping": len(set(codewords)),
            "codewords_unique_after_clip_at_one": len(set(clipped))}


def main():
    tests = [(z(1), z(0)), (z(0), z(1)),
             (z(1), z(1)), (z(1), z(0, 1)),
             (z(F(3,2), F(1,3)), z(F(-2,3), F(5,4))),
             (z(0), z(0)), (z(F(1,2), F(2,5)), z(F(1,3), F(-1,4)))]
    for ax, ay in tests:
        expected = ideal_stokes(ax, ay)
        measured = recorded_stokes(ax, ay)
        assert measured == expected
        s0,s1,s2,s3 = expected
        assert s0*s0 == s1*s1+s2*s2+s3*s3
        assert ideal_stokes(multiply_i(ax), multiply_i(ay)) == expected
    # Incoherently mixed polarization is not the same as a pure Jones field.
    horizontal = ideal_stokes(z(1), z(0))
    vertical = ideal_stokes(z(0), z(1))
    mixture = tuple((a+b)/2 for a,b in zip(horizontal, vertical))
    assert mixture == (1, 0, 0, 0)
    assert mixture[0]**2 > sum(s*s for s in mixture[1:])
    print(json.dumps({"scope":"synthetic exact rational coherent Jones fields",
          "methods_25_to_29_recovered_on_fixtures":len(tests),
          "jones_pure_state_quadratic_identity":True,
          "global_quarter_turn_phase_invariant":True,
          "incoherent_mixture_not_pure_jones_state":True,
          "four_state_identifiability":margin_checks()},indent=2,sort_keys=True))


if __name__ == '__main__':
    main()
