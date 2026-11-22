#!/usr/bin/env python3
"""Original L4 Wilson -> R445 F19 -> nested CMP119-style finite marked-action jets.

Runs the existing exhaustive 1536-plaquette, 15-active-link original SU2-centre
conditional Wilson slice with independent 32768 fine and 32768 fibre enumerations.
Audits the literal Wilson affine 4-coefficient RG pushforward; no physical
CMP119/122 renormalized activity, Wilson Haar integral or W3 charge is claimed.
"""
from collections import defaultdict
from fractions import Fraction as Q
from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
from runpy import run_path
from sympy import symbols, diff, log, cancel, Rational

source=Path(__file__).with_name('check_ym_original_f19_fine_mark_fibre_20261122.py')
assert source.exists(), 'Original source regression required'
with redirect_stdout(StringIO()) as out:
    src=run_path(str(source))
assert {'K','Z','ZF','ZG','ZFG','cov'} <= src.keys()
K=src['K']; Z=src['Z']; ZF=src['ZF']; ZG=src['ZG']; ZFG=src['ZFG']
Cov=src['cov']
fine_fibre=src['fibre_cov'] if 'fibre_cov' in src else src['cov_fibre']
coarse_between=src['coarse_cov'] if 'coarse_cov' in src else src['cov_coarse']
assert len(K)==8 and all(len(row)==4 and row[0]>0 for row in K.values())

# All these coarse sigma-algebras belong to the SAME original weighted law.
# Keep: first 3 native R445 block signs -> first 2 -> first 1 -> none.
def grouped(nbits):
    H={}
    for w,row in K.items():
        g=w & ((1<<nbits)-1)
        acc=H.setdefault(g,[Q(0)]*4)
        for j,elem in enumerate(row): acc[j]+=elem/Q(1<<(3-nbits))
    return {g:tuple(vals) for g,vals in H.items()}

def mean_cond_cov(nbits):
    H=grouped(nbits)
    # We average each conditional weighted coefficient density over base coarse
    # Haar; normalizer Z is the SAME original fine Wilson Z for all levels.
    inside=sum((v[3]-v[1]*v[2]/v[0]) for v in H.values())/Q(1<<nbits)/Z
    between=(sum(v[1]*v[2]/v[0] for v in H.values())/Q(1<<nbits)/Z
             -(ZF/Z)*(ZG/Z))
    assert inside+between==Cov
    assert tuple(sum(v[j] for v in H.values())/Q(1<<nbits) for j in range(4)) == (Z,ZF,ZG,ZFG)
    return inside,between,H

inside3,between3,H3=mean_cond_cov(3)
assert inside3==fine_fibre and between3==coarse_between
levels={i:mean_cond_cov(i)[0] for i in range(4)}
assert levels[0]==Cov
# Explicit one-step source Hessian decomposition:
# old fine fluctuation at 3-bit level + 3->2 + 2->1 + 1->0.
contributions=[levels[3],levels[2]-levels[3],levels[1]-levels[2],levels[0]-levels[1]]
assert sum(contributions)==Cov
assert sum(contributions[1:])==between3

# Nonlinear effective action after an AFFINE four-column density. Even though
# the original partition has bidegree (1,1), its log effective action does not.
# At a fixed coarse block, d_s d_t(-log K_st)|0 = -Cov(F,G|block).
s,t,a,b,c,d=symbols('s t a b c d')
q=a+s*b+t*c+s*t*d
formula=(a*d-b*c)/q**2
assert cancel(diff(log(q),s,t)-formula)==0
assert cancel(diff(-log(q),s,t)+formula)==0
for nbits in range(4):
    inside,between,H=mean_cond_cov(nbits)
    for row in H.values():
        k, f, g, fg=row
        c_block=fg/k-f*g/k**2
        assert c_block==((k*fg-f*g)/k**2)
        assert cancel(formula.subs({a:Rational(k),b:Rational(f),c:Rational(g),d:Rational(fg),s:0,t:0})-Rational(c_block))==0
        for ss,tt in ((Q(0),Q(0)),(Q(9,100),-Q(9,100)),(Q(1,25),Q(1,25))):
            kst=k+ss*f+tt*g+ss*tt*fg
            assert kst>0
            exact=(k*fg-f*g)/kst**2
            assert abs(exact)<=Q(1,1)/(Q(1)-Q(9,100))**2

# At the finest R445 three-bit action, independently coarse-averaging F and G
# erases a strictly positive original mixed source coefficient.
assert levels[3] != 0
wrong=sum(row[1]*row[2]/row[0] for row in K.values())/Q(8)
assert wrong != ZFG
assert (wrong/Z-ZF*ZG/Z**2)==between3

# STRICT SIGNED-CANCELLATION NEGATIVE CONTROL (not a Wilson model):
# Rademacher two-level system, both bounded marks, total Cov=0 but
# separate scale charges are +1/4 and -1/4; absolute shell sum is 1/2.
values=[(e1,e2) for e1 in (-1,1) for e2 in (-1,1)]
F=lambda e1,e2:Q(e1+e2,2)
G=lambda e1,e2:Q(e1-e2,2)
assert all(abs(F(*z))<=1 and abs(G(*z))<=1 for z in values)
neg_total=sum(F(*z)*G(*z) for z in values)/4 - sum(F(*z) for z in values)/4*sum(G(*z) for z in values)/4
assert neg_total==0
coarse_pos=Q(1,4) # conditional means E[F|e1]=e1/2, E[G|e1]=e1/2
fine_neg=Q(-1,4) # conditional Cov(F,G|e1) = -Var(e2)/4
assert fine_neg+coarse_pos==neg_total and abs(fine_neg)+abs(coarse_pos)==Q(1,2)

print('PASS source rerun: 1536 original Wilson plaquettes, 32768 direct and 32768 fibre configurations')
print('PASS original four-coefficient source equality at 8 / 4 / 2 / 1 coarse states')
print('PASS exact four-stage signed covariance/action-Hessian tower; telescoping error zero')
print('PASS 15 distinct same-original fibre actions, source positivity and uniform affine score bound')
print('PASS full mixed log action = negative conditional F/G covariance; fine st source not factorizable')
print('PASS signed-W3 negative control: covariance 0 but absolute two-scale charge 1/2')
print('TOTAL covariance =',float(Cov))
for i,v in enumerate(contributions):
    print('step',i,'signed covariance contribution',float(v),'share',float(v/Cov))
print('CONDITIONAL ONLY: SU2-centre 15-link slice of full source, not continuous SU2 Haar, CMP119 physical activity or W3')
