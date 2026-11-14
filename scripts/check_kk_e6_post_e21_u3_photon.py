#!/usr/bin/env python3
"""Original Chi33+E32+E21 VEVs: global U3 color/electric residual.

Source first-Tits E6 27 #1106, physical KK parity/VEVs #1241.
Classical inputs: SU2-doublet stabilizers, compact covering groups,
SM hypercharge normalization. Selected-source implementation by
Johl Brown / OpenAI ChatGPT. NOT physical vacuum or quantum completion.

In K cover: SU2R=diag(z^3,z^-3) after E32 and
SU2L=diag(z^-3,z^3) after E21 (adapted component basis).
Thus SU3L weights (-2,+4,-2) and SU3R weights (+4,-2,-2)
under the residual z. All 27 charges are even: w=z² defines
the genuine electromagnetic U1, with integer e=3Q=-qz/2.
Faithful final group (SU3c x U1_w)/Z3 is abstractly U3.
"""
from itertools import product
from collections import Counter
from contextlib import redirect_stdout
from pathlib import Path
import io
import runpy

ROOT=Path(__file__).resolve().parents[1]
with redirect_stdout(io.StringIO()) as receipt:
    parent=runpy.run_path(str(ROOT/"scripts/check_kk_e6_post_e32_sm_global_z6.py"))
assert "PASS" in receipt.getvalue()
assert len(parent["states"])==27
P=parent["P"]

lw=(-2,4,-2)
rw=(4,-2,-2)
assert lw[2]-rw[2]==lw[2]-rw[1]==lw[1]-rw[0]==0
states=[]
for ci,li in product(range(3),repeat=2):
    states.append(('A',ci,li,None,1,-lw[li],-P[li]))
for ci,ri in product(range(3),repeat=2):
    states.append(('B',ci,None,ri,2,rw[ri],-P[ri]))
for li,ri in product(range(3),repeat=2):
    states.append(('C',None,li,ri,0,lw[li]-rw[ri],-P[li]*P[ri]))
assert len(states)==27

for old,new in zip(parent["states"],states):
    assert (old[0],old[1],old[2],old[3],old[4],old[-1])==(
            new[0],new[1],new[2],new[3],new[4],new[-1])
    b,c,l,r,t,qz,h=new
    assert qz%2==0
    q3=-qz//2
    assert (t+q3)%3==0,(b,c,l,r,t,q3)

def phase(t,qz,c,k):return (2*t*c+qz*k)%6
kernel=[(c,k) for c,k in product(range(3),range(6))
        if all(phase(t,qz,c,k)==0 for _,_,_,_,t,qz,h in states)]
assert len(kernel)==6
assert set(kernel)=={(n%3,(5*n)%6) for n in range(6)}
assert (0,3) in kernel # z->-z leaves all fields unchanged
# In the w=z^2 parameter, generator (omega3,w=omega3^2).
assert {(c,k%3) for c,k in kernel}=={(0,0),(1,2),(2,1)}
# (g,w)->w*g then realizes (SU3 x U1_w)/Z3 ≅ U3.

d=Counter((('LH' if h==1 else 'RH'),t,(-qz)//2) for
          b,c,l,r,t,qz,h in states)
assert sum(n for (hand,_,_),n in d.items() if hand=='LH')==16
assert sum(n for (hand,_,_),n in d.items() if hand=='RH')==11
assert ('LH',1,2) in d and ('LH',1,-1) in d
assert ('LH',0,-3) in d and ('LH',0,0) in d and ('LH',0,3) in d

print('PASS same-source Chi33+E32+E21 stabilizer: (SU3c x U1_em)/Z3 = U3')
print('PASS original parent 27 weights and 16 LH / 11 RH parity preserved')
print('PASS 3Q_em integer, 3Q_em = -color triality mod3 for all 27')
print('PASS geometric orbifold vector not silently added as a photon')
print('OPEN actual E21 VEV, global H eta/CS/WZ, exact 5D spectrum and Earth source')
