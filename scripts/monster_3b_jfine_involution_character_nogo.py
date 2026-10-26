#!/usr/bin/env python3
"""Exact no-GAP/no-mmgroup Monster selected-3B geometric D4 obstruction.

ORIGINAL scholarship: Conway–Norton (1979); Ford–McKay–Norton (1994);
Breuer–Magaard–Wilson, Monster ordinary character verification (2026).
Source data: ATLAS Monster power-up relationships and the following OEIS
transcriptions of McKay–Thompson q-series. OECD/OEIS data is not assigned
credit for the original Monster character theory.

T_g(q)=q^-1+(1+chi_196883(g))*q+..., constant q^0 is irrelevant.
Only classes 6B,6D,6E square into Monster class 3B; their cubes are
2B,2A,2B, respectively. This is the source-power-map filter.
"""
import json
from fractions import Fraction
from pathlib import Path

SOURCE_2={"2A":4371,"2B":275}
SOURCE_6_Q1={"6A":79,"6B":78,"6C":15,"6D":-2,"6E":6,"6F":28}
SOURCE_6_OEIS={
    "6A":"A007254","6B":"A007255","6C":"A007256",
    "6D":"A007257","6E":"A007258","6F":"A007259",
}
ATLAS_3B_6_PAIRS={"6B":"2B","6D":"2A","6E":"2B"}
ATLAS_URL="https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/M"

def audit():
    six={c:q-1 for c,q in SOURCE_6_Q1.items()}
    assert six=={"6A":78,"6B":77,"6C":14,"6D":-3,"6E":5,"6F":27}
    overcomplete=[]
    for a,v2 in SOURCE_2.items():
        for b,v6 in six.items():
            t=Fraction(v2-v6,3)
            overcomplete.append({"two":a,"six":b,"trace":str(t),"integral":t.denominator==1})
    allowed={}
    for six_class,two_class in ATLAS_3B_6_PAIRS.items():
        t=Fraction(SOURCE_2[two_class]-six[six_class],3)
        assert t.denominator==1
        allowed[two_class+"/"+six_class]=int(t)
    assert allowed=={"2B/6B":66,"2A/6D":1458,"2B/6E":90}
    assert 810 not in allowed.values() and 2430 not in allowed.values()
    # Half-turn geometry=810; each geometric reflection=2430.
    # An intertwiner into actual W_zeta would force one of those values.
    return dict(status="mathematical_involution_character_no_go",
      actual_2A_2B_character=SOURCE_2, six_q1=SOURCE_6_Q1,
      six_character=six, oeis_transcriptions=SOURCE_6_OEIS,
      monster_ATLAS_power_source=ATLAS_URL,
      phase_preserving_order2_trace_candidates=allowed,
      exact_involution_allowed_values=sorted(set(allowed.values())),
      jfine_geometric_half_turn=810,jfine_geometric_reflections=2430,
      geometric_D4_intertwiner_possible=False,
      source_H6_E_isotypy_disproved=False,
      arbitrary_linear_D4_normalizer_extension_disproved=False,
      original_authorship=["Conway & Norton (1979)","Ford, McKay & Norton (1994)",
                           "Breuer, Magaard & Wilson (2026)"],
      method="Tr(W_zeta,g)=(chi_196883(g)-chi_196883(zg))/3, g^2=z^3=1, [z,g]=1",
      source_mathematics_not_reverified_from_GAP=True)
if __name__=="__main__":
    result=audit()
    import argparse
    p=argparse.ArgumentParser()
    p.add_argument("--receipt",type=Path)
    args=p.parse_args()
    blob=json.dumps(result,indent=2)+"\n"
    if args.receipt:args.receipt.write_text(blob)
    print(blob,end="")
