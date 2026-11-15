#!/usr/bin/env python3
"""Original Chi33+E32 stabilizer: global SM Z6 and 16+11 source audit.

Source owners: E6 first-Tits 27 #1106; physical KK parity/VEVs
#1241. Classical: SU2 fundamental-doublet stabilizer, covering kernels,
faithful Standard Model Z6 quotient. Selected-source computation by
Johl Brown with OpenAI assistance; NOT a UV anomaly-free action.

After Chi33, K=(SU3c x SU2L x SU2R x U1_z)/Z6.
For E32=(1,3L-singlet,bar3R-second-doublet) nonzero,
AR=diag(z^3,z^-3); its stabilizer is
S=(SU3c x SU2L x U1_z)/Z6 with 6Y=-q_z.
This requires the VEV as a physical input: not a source-potential proof.
"""
from itertools import product
from collections import Counter
from contextlib import redirect_stdout
from pathlib import Path
import io
import runpy

ROOT=Path(__file__).resolve().parents[1]
with redirect_stdout(io.StringIO()) as receipt:
    prior=runpy.run_path(str(ROOT/"scripts/check_kk_e6_orbifold_gs_anomaly_factor.py"))
assert "PASS" in receipt.getvalue()
assert len(prior["states"])==27
P=prior["P"]
assert P==(-1,-1,1)

def zweight(index): return 1 if index<2 else -2
rweights=(4,-2,-2)
assert zweight(2)-rweights[1]==0    # E32
assert zweight(2)-rweights[2]==0    # Chi33
assert zweight(1)-rweights[0]==-3   # E21: 6Y=+3

states=[]
for ci,li in product(range(3),repeat=2):
    states.append(('A',ci,li,None,1,int(li<2),-zweight(li),-P[li]))
for ci,ri in product(range(3),repeat=2):
    states.append(('B',ci,None,ri,2,0,rweights[ri],-P[ri]))
for li,ri in product(range(3),repeat=2):
    states.append(('C',None,li,ri,0,int(li<2),
                   zweight(li)-rweights[ri],-P[li]*P[ri]))
assert len(states)==27
for entry,old in zip(states,prior["states"]):
    name,ci,li,ri,t,sl,q,h=entry
    assert h==old["sign"] and old["l"]==li and old["r"]==ri

def phase(t,s,q,c,l,k): return (2*t*c+3*s*l+q*k)%6
kernel=[]
for c,l,k in product(range(3),range(2),range(6)):
    if all(phase(t,sl,q,c,l,k)==0 for _,_,_,_,t,sl,q,h in states):
        kernel.append((c,l,k))
assert len(kernel)==6
assert set(kernel)=={(n%3,n%2,(5*n)%6) for n in range(6)}
assert all((q-2*t-3*sl)%6==0 for _,_,_,_,t,sl,q,h in states)

# A true LEFT/RIGHT splitting of the SAME original orbifold 27.
# q_z=-6Y in this covering convention. The 11 RH modes are 10+1
# vectorlike exotics, not a second chiral SM generation.
expected=Counter({
 ('LH','3','2',1):6,('LH','bar3','1',-4):3,
 ('LH','bar3','1',2):3,('LH','1','2',-3):2,
 ('LH','1','1',6):1,('LH','1','1',0):1,
 ('RH','3','1',-2):3,('RH','bar3','1',2):3,
 ('RH','1','2',3):2,('RH','1','2',-3):2,
 ('RH','1','1',0):1})
actual=Counter()
for b,ci,li,ri,t,sl,q,h in states:
    color=('3' if t==1 else 'bar3' if t==2 else '1')
    weak='2' if sl else '1'
    actual[('LH' if h==1 else 'RH',color,weak,-q)]+=1
assert actual==expected,(actual-expected,expected-actual)
assert sum(n for (hand,*_),n in actual.items() if hand=='LH')==16
assert sum(n for (hand,*_),n in actual.items() if hand=='RH')==11

# The residual Z6 element gamma=(omega3,-I2,z=-omega3)
# respects the E32 stabilizer, because z^3=-1 on gamma.
assert all((3*(5*n)-3*n)%6==0 for n in range(6))
print('PASS Chi33+E32 residual faithful (SU3c x SU2L x U1)/Z6')
print('PASS imported original source states: 16 LH SM weights plus 11 RH exotic weights')
print('PASS conventional hypercharge 6Y=-q_z and every 27 weight descends')
print('PASS E21 is a weak doublet with 6Y=+3; nonzero E32 reduces SU2R')
print('OPEN E21 source vacuum, full H eta/CS/WZ, interval spectrum and Earth source')


# The source IR Standard-Model subgroup is perturbatively anomaly-free
# SEPARATELY in its 16 LH sector and 11 RH exotic sector (which pairs
# into vectorlike charge conjugates). Use one SU3/SU2 fundamental Dynkin
# normalization consistently; SU3^2 U1 counts m/3 color multiplets,
# SU2^2 U1 counts m/2 weak doublets.
intermediate=[
 ('LH',1,1,1,6),('LH',2,0,-4,3),('LH',2,0,2,3),
 ('LH',0,1,-3,2),('LH',0,0,6,1),('LH',0,0,0,1),
 ('RH',1,0,-2,3),('RH',2,0,2,3),
 ('RH',0,1,3,2),('RH',0,1,-3,2),('RH',0,0,0,1)]
for hand in ('LH','RH'):
    grp=[(t,s,q,m) for h,t,s,q,m in intermediate if h==hand]
    assert sum(m for t,s,q,m in grp)==(16 if hand=='LH' else 11)
    assert sum(m*q for t,s,q,m in grp)==0
    assert sum(m*q**3 for t,s,q,m in grp)==0
    assert sum((m//3)*q for t,s,q,m in grp if t)==0 # SU3²U1
    assert sum((m//2)*q for t,s,q,m in grp if s)==0 # SU2²U1
    assert sum(m*(1 if t==1 else -1) for t,s,q,m in grp if t)==0 # SU3³
    assert sum(m//2 for t,s,q,m in grp if s)%2==0
print('PASS IR SM chiral 16 and RH exotic 11: separate local anomaly sums vanish')
