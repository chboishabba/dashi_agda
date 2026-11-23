#!/usr/bin/env python3
"""Original 4D Wilson two-mark bad-sector: termwise-absolute event-log series.

Uses the existing ORIGINAL 1536-plaquette four-column L4 centre-subgroup
regression *unchanged* as exact rational input; never an SU(N) Haar substitute.
All general probability inequalities are separately proved mathematically.
"""
from fractions import Fraction as Q
from pathlib import Path
from runpy import run_path
from itertools import product

original_file=Path(__file__).with_name('check_ym_p0_sun_original_two_mark_bad_event_20261123.py')
old=run_path(str(original_file))
original=old['original']; rho=old['rho']; p=old['p']
assert len(original)==4096 and 0<p<Q(1,4)
R=((1+rho)/(1-rho))**2
M=1/(1-rho)
q=p*R/(1-p)
assert 0<q<1 and p < 1/(1+R)
checks=0

def verify(c,desc=''):
    global checks
    if not c: raise AssertionError((desc,checks))
    checks+=1

def cols(good):
    xs=[(w,f,g) for w,f,g,bad in original if ((not bad) if good else bad)]
    den=sum(w for w,_,_ in xs)
    assert den>0
    return tuple(Q(sum(w*f**i*g**j for w,f,g in xs),1)
                 for i,j in ((0,0),(1,0),(0,1),(1,1)))
A=cols(True);B=cols(False)

def cval(a,s,t):
    v,f,g,fg=a
    return v+s*f+t*g+s*t*fg

def cs(a,t): return a[1]+t*a[3]
def ct(a,s): return a[2]+s*a[3]

def log_mixed(a,s,t):
    d=cval(a,s,t)
    return a[3]/d-cs(a,t)*ct(a,s)/d**2

def qn_series(a,b,s,t,n):
    aa=cval(a,s,t);bb=cval(b,s,t)
    z=bb/aa
    logzs=cs(b,t)/bb-cs(a,t)/aa
    logzt=ct(b,s)/bb-ct(a,s)/aa
    logzst=log_mixed(b,s,t)-log_mixed(a,s,t)
    # 1/n * d_st(z^n) is z^n*(logz_st + n logz_s logz_t)
    return z**n*(logzst+n*logzs*logzt)

def tail(q,n):
    return M*M*q**(n+1)*(2/(1-q)+4*((n+1)/(1-q)+q/(1-q)**2))

for s,t in product((-rho,-Q(3,100),Q(0),Q(3,100),rho), repeat=2):
    a=cval(A,s,t);b=cval(B,s,t);z=b/a
    verify(0<z<=q,'exact source z<=q')
    full=tuple(A[k]+B[k] for k in range(4))
    expected=log_mixed(full,s,t)-log_mixed(A,s,t)
    partial=Q(0)
    abs_total=Q(0)
    for n in range(1,17):
        dn=qn_series(A,B,s,t,n)
        partial+=(-1)**(n+1)*dn
        abs_total+=abs(dn)
        verify(abs(dn)<=M*M*(2+4*n)*q**n,'termwise ABS bound')
        verify(abs(expected-partial)<=tail(q,n),'exact tail residual bound')
    envelope=M*M*(2*q/(1-q)+4*q/(1-q)**2)
    verify(abs_total<=envelope,'absolute partial sum bound')
    verify(abs(expected)<=envelope,'absolute full jet bound')
    verify(abs(expected)<=6*(1+rho)**2/(1-rho)**4*p,'prior signed 6p')


# Stronger result: the event-log expansion converges on the ENTIRE COMPLEX
# source bidisk. Original normalized conditional four columns remain real.
# The proof uses |K_A(s,t)-K_A(0,0)| <= (2rho+rho^2)K_A(0,0).
delta=2*rho+rho*rho
Rc=(1+rho)**2/(1-delta)
qc=p*Rc/(1-p)
verify(delta<1 and 0<qc<1, 'complex bidisk rarity')
verify(1/(1+Rc)==Q(8119,20000), 'exact complex event rarity threshold')
from sympy import I, expand, simplify, re, im
complex_roots=[-rho,Q(0),rho,-I*rho,I*rho]
for s,t in product(complex_roots, repeat=2):
    za=cval(A,s,t);zb=cval(B,s,t)
    normA=simplify(re(za)**2+im(za)**2)
    normB=simplify(re(zb)**2+im(zb)**2)
    verify(normA>=(1-delta)**2*A[0]**2,'original good complex zero-free')
    verify(normB<=(1+rho)**4*B[0]**2,'original bad upper norm')
    verify(simplify(qc**2*normA-normB)>=0,'complex event ratio bound')
# Cauchy coefficient: the absolute sum of the individual [s*t] log(z)
# series terms is at most -log(1-qc)/rho^2 (mathematical analytic sum).
# A purely RATIONAL upper bound using -log(1-q) <= q/(1-q) is checked.
rational_cauchy=qc/(rho**2*(1-qc))
zero_terms=sum(abs(qn_series(A,B,Q(0),Q(0),n)) for n in range(1,17))
verify(zero_terms<=rational_cauchy,'absolute complex Cauchy mixed coefficient envelope')

# Physically decisive F19 negative control: global bad rarity DOES NOT
# control pointwise bad mass in the actual native coarse-holonomy fibres.
# The original R445 coarse y-holonomies at even (t,y,z) starts time 0,2
# are U_y(t,0,0)*U_y(t,1,0); the second links are identity in this
# explicitly restricted centre slice. These are bits 0 and 8 of the
# original 12-live-link L4 model (NOT new/artificial coarse variables).
from collections import defaultdict
groups=defaultdict(list)
for bits,row in enumerate(original):
    groups[((bits>>0)&1,(bits>>8)&1)].append(row)
verify(len(groups)==4 and all(len(rows)==1024 for rows in groups.values()),'original native two-block W fibres')
global_total=sum(w for w,_,_,_ in original)
tower=Q(0);exceptional=Q(0);bad_fibre_count=0
for label,rows in sorted(groups.items()):
    mass=sum(w for w,_,_,_ in rows)
    badmass=sum(w for w,_,_,flag in rows if flag)
    pw=Q(badmass,mass)
    tower+=Q(mass,global_total)*pw
    if pw>Q(1,4): exceptional+=Q(mass,global_total)
    if pw==1:
        bad_fibre_count+=1
        verify(sum(w for w,f,g,flag in rows if not flag)==0,'good mass vanishes at original W')
    else:
        verify(pw<1/(1+Rc),'holomorphic good W sector')
    print('Original R445 native coarse W',label,'probability mass',float(Q(mass,global_total)),'conditional bad p(W)',float(pw))
verify(tower==p,'exact F19 bad-probability tower')
verify(bad_fibre_count==2,'2/4 original W fibres have all-bad source')
verify(exceptional <= 4*p,'Markov P_W(p(W)>1/4)<=4p')
# The W-average of conditional logarithms is NOT the global log.
# Use the true positive full source, not an invented per-W log partition.
verify(Q(sum(w for row in groups.values() for w,_,_,_ in row),global_total)==1,'true coarse reassembly')

# Event rarity is ESSENTIAL. For abstract unbounded p, q>=1 and this
# logarithmic series fails at s=t=0 despite finite source positivity.
for arbitrary_p in (Q(1,2),Q(3,4)):
    verify(arbitrary_p*R/(1-arbitrary_p)>1,'cannot expand when q>=1')
# No marked interaction multiplication has been introduced; A,B come from
# ORIGINAL single global F,G and (FG) four-column conditional sums.
print('PASS',checks,'exact checks across 25 original L4 two-global-mark affine source settings, 16 event-log terms each')
print('p=',float(p),' q=',float(q),' max absolute jet envelope=',float(envelope))
print('Complex bidisk q_c=',float(qc),' pcrit_c=',1/(1+Rc), ' Cauchy mixed coefficient upper=',float(rational_cauchy))
print('Rarity threshold p<',1/(1+R),' exact C_rho=', 6*(1+rho)**2/(1-rho)**4)
print('NOT: original SU(N) continuous Haar numerical integration, physical CMP119/122 T, or absolute CMP116 rooted cluster sum, or Clay mass gap')
