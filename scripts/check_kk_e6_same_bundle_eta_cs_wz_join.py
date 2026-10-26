#!/usr/bin/env python3
"""Exact same-object E6 27 global-consumer join; fail-closed regression.

Original prior art: classical Atiyah-Singer spin index and complex line
clutching; Slansky (1981) E6 branching; Scrucca et al (2002) and
von Gersdorff-Quirós (2003) local orbifold anomaly; Dai-Freed
(1994), Witten-Yonekura (2019/2020) global eta/inflow.
Selected source implementations: Agda E6 #1106 and physical KK #1241.
This join: Johl Brown with OpenAI ChatGPT assistance.

The witness is one and the SAME faithful parity-even H quotient bundle
over the spin SIX-fold X=(S2)^3, represented by three independent S2
clutch paths per SU3 factor, with common diagonal Z3 deck p=1.
A nonzero signed half-index is simultaneously accompanied by a
topologically nontrivial Chi33 line whose sections MUST vanish.
This does not compute eta, torsion, quantum CS, or any extended WZ
functional. Previous 2+1D SU2 CS level receipts cannot be imported as
5D spin CS quantization.
"""
from contextlib import redirect_stdout
from fractions import Fraction
from pathlib import Path
import io
import runpy

ROOT=Path(__file__).resolve().parents[1]
def owner(rel, *exports):
    f=ROOT/rel
    assert f.is_file(), f"missing source owner: {rel}"
    buf=io.StringIO()
    with redirect_stdout(buf):
        out=runpy.run_path(str(f))
    for name in exports:
        assert name in out, (rel,name)
    assert "PASS" in buf.getvalue(), (rel,buf.getvalue())
    return out

clutch=owner("scripts/check_kk_e6_orbifold_even_quotient_s2_clutch.py",
             "parity_even_lift_weights","chi33_line_winding")
index=owner("scripts/check_kk_e6_orbifold_index_even_universal_trace.py",
            "selected_indexes","fixture")
factor=owner("scripts/check_kk_e6_chi33_full_cartan_anomaly_factor.py",
             "D","Q","six_index_density")
local=owner("scripts/check_kk_e6_orbifold_cs_wz_anomaly_transfer.py",
            "I6","X4","remaining")
fractions=owner("scripts/check_kk_e6_z3_fractional_instanton_mixed_wz.py",
                "Bsq")

fixture=index["fixture"]
assert len(fixture)==3
for sphere in fixture:
    assert len(sphere)==3
    assert {p for p,m,n in sphere}=={1}  # actual common deck

winding=tuple(clutch["chi33_line_winding"](
    1, fixture[d][1][1],fixture[d][1][2],
    fixture[d][2][1],fixture[d][2][2]) for d in range(3))
assert winding==(Fraction(0),Fraction(0),Fraction(-1))
assert all(x.denominator==1 for x in winding)
# A nonzero first Chern class on S2 prevents a nonzero global section
# of Chi33; this is classical clutching theory, not proven by Python.
assert any(winding)
signed=index["selected_indexes"](fixture)
assert signed==-12 and signed/2==-6
assert sum([index["full"]])==0
# Re-use the ACTUAL local source, not duplicated coefficients.
assert local["remaining"]==(local["I6"],0)
assert local["X4"].expand().coeff(local["c2c"])==2
assert fractions["Bsq"]==2
assert factor["linear"]==8*factor["D"]
assert factor["cubic"].expand()==(4*factor["D"]*factor["Q"]).expand()

# Explicitly inspect the original QFT, 5D, and eta TARGET owners.
# Merely existing with those names is NOT an actual 5D eta functional.
owners=(
 ("DASHI/Physics/QFT/FermionicLoopCSShiftReceipt.agda",
  "candidate/conditional bookkeeping"),
 ("DASHI/Physics/QFT/BulkBoundarySU3Receipt.agda",
  "2+1D boundary candidate"),
 ("DASHI/Physics/Closure/KTheoryNovikovReceiptSurface.agda",
  "globalAnomalyEtaInvariantTarget"),
 ("DASHI/Physics/Gravity/KKMinkowskiChernSimonsFiveDConsumerExact.agda",
  "threeFormIsNotFiveForm"),
 ("DASHI/Physics/Gravity/KKE6OrbifoldCSWZTransferConsumerExact.agda",
  "globallyIntegralSpinQuotientCSTransferCertified = false"),
)
for rel,marker in owners:
    f=ROOT/rel
    assert f.is_file(), f"missing prior typed owner: {rel}"
    assert marker in f.read_text(encoding="utf-8"), (rel,marker)

print("PASS exact owner imports and original 2+1D/5D/eta authority separation")
print("PASS SAME parity-even nonliftable H-bundle on spin (S2)^3")
print("PASS selected Chi33 line degrees",winding,"forcing zero")
print("PASS same-bundle signed 27 index",signed,"half-index",signed/2)
print("PASS full H anomaly polynomial factor through Chi33 Chern class")
print("PASS local source endpoint polynomial cancellation only")
print("OPEN 5D regulated eta/Pfaffian on H bundle and quantum CS descent")
print("OPEN patched/defect-completed WZ on forced Chi33-zero sector")
