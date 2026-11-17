#!/usr/bin/env python3
"""Exact F81/F9 norm / inverse / projective audit (DASHI).
Original source field chart: iit_jfine_selected_punctured79_audit.py
Original projective chart: iit_projective_f9_pointed80_audit.py
Independent computation: /mnt/data/f81_f9_norm_inversion_audit.py.
NOT an Agda kernel receipt, Monster representation or physical claim.
"""
from __future__ import annotations
from collections import Counter
from itertools import product
from hashlib import sha256
import json
from iit_jfine_selected_punctured79_audit import ZERO, ONE, add, multiply, power

FIELD = tuple(product(range(3), repeat=4))

def audit():
    units = tuple(a for a in FIELD if a != ZERO)
    f9 = tuple(a for a in FIELD if power(a, 9) == a)
    f9units = tuple(a for a in f9 if a != ZERO)
    normone = tuple(a for a in units if power(a, 10) == ONE)
    assert (len(FIELD), len(units), len(f9), len(f9units), len(normone)) == (81,80,9,8,10)

    assert all(power(a,81) == a for a in FIELD)
    assert all(power(a,80) == ONE and multiply(a,power(a,79)) == ONE for a in units)
    assert all(power(power(a,79),79) == a for a in units)
    assert all(power(a,10) in f9units for a in units)
    assert all(power(a,8) in normone for a in units)
    assert all(power(multiply(a,s),8) == power(a,8) for a in units for s in f9units)
    fibres = Counter(power(a,8) for a in units)
    assert len(fibres) == 10 and set(fibres.values()) == {8}
    assert set(fibres) == set(normone)

    # Frobenius_9 is conjugation over F9; Norm(x)=x*x^9=x^10.
    assert all(power(z,9) == power(z,79) for z in normone)
    assert all(multiply(power(a,9),power(power(a,10),7)) == power(a,79) for a in units)

    two_fixed={a for a in units if power(a,79) == a}
    assert two_fixed == {ONE,(2,0,0,0)}
    assert {a for a in normone if power(a,9) == a} == two_fixed

    gen=next(a for a in normone if all(power(a,k)!=ONE for k in (1,2,5)))
    assert len({power(gen,k) for k in range(10)}) == 10
    order5=power(gen,2)
    first={power(order5,k) for k in range(5)}
    second={multiply(gen,power(order5,k)) for k in range(5)}
    assert len(first)==5 and len(second)==5 and first.isdisjoint(second)
    assert first|second == set(normone)

    visited=set()
    involution_orbits=[]
    for a in normone:
        if a in visited: continue
        orbit={a,power(a,79)}
        visited.update(orbit)
        involution_orbits.append(orbit)
    assert Counter(map(len,involution_orbits)) == Counter({1:2, 2:4})

    report = {
        "contract": "iit_f81_f9_norm_inversion_exact_finite",
        "source": "scripts/iit_jfine_selected_punctured79_audit.py",
        "field_elements_checked":81, "units_checked":80,
        "base_field":3, "extension_field":81,
        "q_minus_two_inverse_exponent":79,
        "81_minus_79_equals_3_minus_1":True,
        "gap_not_universal_p_minus_one_rule":True,
        "inverse_fixed_units": ["+1","-1"],
        "subfield_F9_elements":9,"subfield_F9_units":8,
        "norm_exponent":10,"relative_frobenius_exponent":9,
        "quotient_to_norm_one_exponent":8,
        "norm_one_group_size":10,"uniform_scalar_fibre_size":8,
        "projective_reconstruction_checked_on_all_80":True,
        "norm_one_frobenius_equals_inverse":True,
        "inverse_via_conjugate_over_norm":True,
        "order5_two_orbits":[5,5],
        "inverse_involution_orbits": {"fixed":2, "pairs":4},
        "Agda_concrete_field_checked":False,
        "IIT_phi_or_physical_correspondence":False,
    }
    digest=json.dumps(report,sort_keys=True,separators=(",",":")).encode()
    report["payload_sha256"]=sha256(digest).hexdigest()
    return report

if __name__=="__main__":
    print(json.dumps(audit(),indent=2,sort_keys=True))
