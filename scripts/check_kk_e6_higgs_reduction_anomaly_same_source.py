#!/usr/bin/env python3
"""Actual-owner join: connected Higgs reduction K and vanishing free anomaly.

Original math: Lie-group fibration exact homotopy sequence, first Chern
class and 6D spin Atiyah-Singer index (not original to this script).
Original selected physical action: first-Tits 27 #1106, KK/orbifold
#1241. New same-H reduction and consumer joining authored by Johl Brown
with OpenAI ChatGPT assistance. No fabricated global quantum payment.

H=(SU3c x U2L x U2R)/Z3diag, chi33(h)=det(U_R)/det(U_L).
pi1(H)=Z<A> + Z<R>; chi_*=-projection_A (primitive).
By exact homotopy, K=ker chi is connected and pi1(K)=Z<R>.
The quotient lifting/deck class R mod3 is STILL surjective on K.
The selected signed anomaly ch1 and ch3 have a Chi33 factor; their
rational classes vanish on BK. This only pays the UNBROKEN K free
anomaly, not full H gauge transformations, torsion eta or WZ defects.
"""
import contextlib
import io
from pathlib import Path
import runpy

ROOT=Path(__file__).resolve().parents[1]

def import_verified(relative, fields):
    f=ROOT/relative
    assert f.is_file(), f
    stream=io.StringIO()
    with contextlib.redirect_stdout(stream):
        result=runpy.run_path(str(f))
    assert "PASS" in stream.getvalue(), (relative,stream.getvalue())
    assert all(k in result for k in fields)
    return result

top=import_verified("scripts/check_kk_e6_h_pi1_charge_deck.py",
                    ("coordinates","higgs_kernel_loop","deck","chi_degree","A","R"))
anomaly=import_verified("scripts/check_kk_e6_chi33_full_cartan_anomaly_factor.py",
                        ("linear","cubic","D","Q","six_index_density",
                         "r1","l0","l1","r0","s"))

chi=top["chi_degree"]
assert chi(top["A"])==-1 and chi(top["R"])==0
# Primitive surjective character: connected K, one free pi1 generator,
# by the CLASSICAL long exact sequence for K -> H -> U(1).
for y in range(-120,121):
    p,dL,dR=top["higgs_kernel_loop"](y)
    hloop=top["coordinates"](p,dL,dR)
    assert hloop==(0,y)
    assert chi(hloop)==0 and top["deck"](hloop)==y%3
# One genuine nonliftable p=1 K loop, not an imaginary finite Z3
# torsion element of pi1(H). L and R component paths are IDENTICAL,
# so the actual Chi33 transition is identically 1 along the equator.
assert top["higgs_kernel_loop"](1)==(1,-1,-1)
assert top["coordinates"](*top["higgs_kernel_loop"](1))==(0,1)

s=anomaly["s"]
D=anomaly["D"]
Q=anomaly["Q"]
linear=anomaly["linear"]
cubic=anomaly["cubic"]
density=anomaly["six_index_density"]
assert s.expand(linear-8*D)==0
assert s.expand(cubic-4*D*Q)==0
# K imposes det(U_L)=det(U_R), or l2-r2=0 in Chern roots.
restriction={anomaly["r1"]:anomaly["l0"]+anomaly["l1"]-anomaly["r0"]}
assert s.expand(D.subs(restriction))==0
assert s.expand(linear.subs(restriction))==0
assert s.expand(cubic.subs(restriction))==0
assert s.expand(density.subs(restriction))==0
assert s.expand(Q.subs(restriction))!=0  # proper, nontrivial restriction

print("PASS source primitive Chi33 character and 241 representative K loops")
print("PASS K connected with pi1(K)=Z using external exact homotopy theorem")
print("PASS K Higgs reduction preserves all 3 nonliftable Z3 deck classes")
print("PASS source signed ch1, ch3 and free spin-six index vanish when pulled to BK")
print("OPEN torsion eta/bordism on K and full H gauge transformations")
print("OPEN actual stable nonzero Chi33 Higgs source / defect-complete H WZ")
print("OPEN full 5D interval theory, Earth matter source, LARES-2 prediction")
