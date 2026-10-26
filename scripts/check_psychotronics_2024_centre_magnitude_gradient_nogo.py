#!/usr/bin/env python3
"""Exact local Maxwell-vacuum counterexample to inferring |B| gradient
from the 2024 Rodin paper's centre-field Table II alone.

Original source: A.D. Ramirez-Galindo et al., Revista Mexicana de Fisica
70 e030901 (2024), DOI 10.31349/RevMexFis.70.030901, Table II.
Original 2024 measurements remain credited to those authors.

Case-specific mathematical analysis by Johl Brown with OpenAI ChatGPT
assistance. These fields are SYNTHETIC LOCAL POLYNOMIALS, not original
Rodin/Helmholtz coil data, not actual source current distributions, and
not empirical evidence for or against a 60-percent biological effect.
"""
from __future__ import annotations
import argparse
import json
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product

Z = Q(0)
SOURCE_TABLE = (
    {"current_A": "1.60", "B_center_mT": "4.13"},
    {"current_A": "1.25", "B_center_mT": "3.05"},
    {"current_A": "0.60", "B_center_mT": "1.16"},
)
SOURCE_DOI = "10.31349/RevMexFis.70.030901"
SOURCE_URL = "https://www.scielo.org.mx/scielo.php?pid=S0035-001X2024000300006&script=sci_arttext"

@dataclass(frozen=True)
class LocalAffineMagneticField:
    """B(r)=c+M r. c in mT, M in mT/m; Cartesian x,y,z in m."""
    centre: tuple[Q,Q,Q]
    jacobian: tuple[tuple[Q,Q,Q], tuple[Q,Q,Q], tuple[Q,Q,Q]]

    def value(self, x: Q, y: Q, z: Q) -> tuple[Q,Q,Q]:
        r = (x, y, z)
        return tuple(self.centre[i] + sum(self.jacobian[i][j]*r[j] for j in range(3))
                     for i in range(3))

    def divergence(self) -> Q:
        return sum(self.jacobian[i][i] for i in range(3))

    def curl(self) -> tuple[Q,Q,Q]:
        m=self.jacobian
        return (m[2][1]-m[1][2], m[0][2]-m[2][0], m[1][0]-m[0][1])

    def magnitude_gradient_at_centre(self) -> tuple[Q,Q,Q]:
        """Exact grad|B| at centre where centre vector=(0,0,b), b>0."""
        if self.centre[0]!=Z or self.centre[1]!=Z or self.centre[2]<=Z:
            raise ValueError("only b>0 along z; general magnitude requires sqrt")
        return self.jacobian[2]

def matching_vacuum_pair(b: Q, g: Q) -> tuple[LocalAffineMagneticField,LocalAffineMagneticField]:
    """Two local source-free fields at same point with different gradients.

    B0=(0,0,b); B1=(g*z,0,b+g*x).
    Both have div B=0 and curl B=0 in a local current-free region.
    B1 is not an asserted globally finite-energy experimental source.
    """
    if b <= Z or g <= Z:
        raise ValueError("requires positive centre magnitude and contrast gradient")
    null = (Z,Z,Z)
    constant=LocalAffineMagneticField((Z,Z,b), (null,null,null))
    gradient=LocalAffineMagneticField(
        (Z,Z,b),((Z,Z,g),null,(g,Z,Z))
    )
    assert constant.value(Z,Z,Z)==gradient.value(Z,Z,Z)==(Z,Z,b)
    assert constant.divergence()==gradient.divergence()==Z
    assert constant.curl()==gradient.curl()==(Z,Z,Z)
    assert constant.magnitude_gradient_at_centre()==(Z,Z,Z)
    assert gradient.magnitude_gradient_at_centre()==(g,Z,Z)
    return constant,gradient

def witness() -> dict:
    demonstrations=[]
    for row in SOURCE_TABLE:
        b=Q(row["B_center_mT"])
        constant,gradient=matching_vacuum_pair(b,Q(1,1))
        demonstrations.append({
            "published_original_current_A":row["current_A"],
            "published_original_centre_mT":row["B_center_mT"],
            "hypothetical_uniform_grad_abs_B_mT_per_m":["0","0","0"],
            "hypothetical_nonuniform_grad_abs_B_mT_per_m":["1","0","0"],
            "both_vacuum_divergence_zero":True,
            "both_vacuum_curl_zero":True,
            "centre_values_equal":constant.centre==gradient.centre,
        })
    return {
        "original_owner":"Ramirez-Galindo et al. (2024)",
        "original_DOI": SOURCE_DOI,
        "source_locator": SOURCE_URL,
        "original_Table_II_not_a_3D_gradient_table": True,
        "all_hypothetical_fields_local_only": True,
        "actual_2024_3D_measured_map_not_tested": True,
        "paper_2024_did_perform_3D_mapping": True,
        "biological_60percent_superiority_established": False,
        "synthetic_same_centre_different_gradient_pairs": demonstrations,
    }

def self_test() -> dict:
    count=0
    for row, gradient in product(SOURCE_TABLE, (Q(1,10),Q(1),Q(10),Q(100))):
        b=Q(row["B_center_mT"])
        u,v=matching_vacuum_pair(b,gradient)
        assert u.value(Q(1,5),Z,Z)==u.centre
        assert v.value(Q(1,5),Z,Z)==(gradient*Z,Z,b+gradient*Q(1,5))
        count+=1
    for b,g in ((Z,Q(1)),(Q(-1),Q(1)),(Q(1),Z),(Q(1),Q(-2))):
        try: matching_vacuum_pair(b,g)
        except ValueError: count+=1
        else: raise AssertionError("invalid synthetic field constraints passed")
    try:
        LocalAffineMagneticField((Q(1),Z,Z), ((Z,Z,Z),)*3).magnitude_gradient_at_centre()
    except ValueError: count+=1
    else: raise AssertionError("invalid direction accepted")
    assert count==17
    witness()
    return {"valid_local_vacuum_pairs":12,"invalid_inputs_rejected":5,
            "total_cases":count,"synthetic_only":True,"original_Rodin_raw_data_acquired":False}

def main() -> None:
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--self-test",action="store_true")
    a=p.parse_args()
    r=witness()
    if a.self_test: r["self_test"]=self_test()
    print(json.dumps(r,indent=2,sort_keys=True))

if __name__=="__main__":
    main()
