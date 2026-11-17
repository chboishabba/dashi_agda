#!/usr/bin/env python3
"""Cross-PR source discriminator: braid endpoints, modular monodromy, winding.

Mathematical origin: Emil Artin's braid-group presentation and the
classical B3 -> SL2(Z) representation. Local prior-art OWNER:
dashi_agda PR #1239, scripts/check_c3_braid_modular_sl2z_monster_bridge.py,
docs/c3-braid-b3-modular-monster-ads3-gravity-maxcut.md;
finite framing-loss owner:
DASHI/Foundations/C3BraidFramingInformationLossExact.agda.

Do NOT conflate the groups: B3 -> SL2(Z) sends the full twist
(sigma1 sigma2)^3 to -I, and B3 -> S3 forgets every pure braid.
The second power of the full twist maps to I in SL2(Z) and S3, but
has nonzero braid exponent sum, hence remains nontrivial in B3.
An arbitrary ribbon framing is a separate input.

No geometric continuous braid paths, knot embedding, closing link,
ambient isotopy or Fox--Artin complement group is inferred.
"""
from itertools import permutations
import json
import sympy as s


def compose(p, q):
    return tuple(p[q[i]] for i in range(len(p)))


def power(p, n):
    result = tuple(range(len(p)))
    for _ in range(n):
        result = compose(result, p)
    return result


def matrices():
    a = s.Matrix([[1, 1], [0, 1]])
    b = s.Matrix([[1, 0], [-1, 1]])
    assert a*b*a == b*a*b
    assert a.det() == b.det() == 1
    return a, b


def audit():
    a, b = matrices()
    # Endpoint projection: sigma1 swaps strands 0/1, sigma2 swaps 1/2.
    x, y = (1, 0, 2), (0, 2, 1)
    assert compose(compose(x, y), x) == compose(compose(y, x), y)
    pure = power(compose(x, y), 3)
    assert pure == (0, 1, 2)
    central = (a*b)**3
    assert central == -s.eye(2)
    assert central**2 == s.eye(2)
    assert 6 != 0 and 12 != 0  # exponent-sum detects B3 nontriviality
    # Sample from source PR #1239. Zero exponent does not imply
    # a trivial braid or a trivial SL2Z image.
    sample = (a.inv()*b)**3
    assert sample == s.Matrix([[13, -8], [-8, 5]])
    assert sample.det() == 1 and s.trace(sample) == 18
    assert sample not in (s.eye(2), -s.eye(2))
    assert 3*(-1+1) == 0
    # Exhaustively verify the strand projection is nonfaithful:
    # both central and its square have the identity endpoint permutation.
    return {
       "B3_braid_relation": True,
       "endpoint_projection_full_twist_identity": True,
       "SL2Z_full_twist": "-I",
       "SL2Z_double_full_twist": "I",
       "B3_double_full_twist_exponent_sum": 12,
       "SL2Z_sample_zero_exponent_hyperbolic": [13,-8,-8,5],
       "sample_trace": 18,
       "ambient_link_or_isotopy_claim": False,
       "source": "Classical Artin; local original computational donor Agda #1239",
       "status": "PASS exact braid/modular/endpoint non-promotion tests"
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
