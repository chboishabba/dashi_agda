#!/usr/bin/env python3
"""Finite Wilson source -> marked Mayer polymers, with strict failure gates.

Universal theorem: for any finite original SU(N) Wilson product-Haar source,
expand each e^(beta t_p)=1+f_p and use the TWO GLOBAL insertion labels
(1+sF)(1+tG), then Haar integrals over disjoint LINK supports factor.
Canonical overlapping-link components define one and the same labelled polymer
partition function, with cross-polymer insertions retained.

Finite exact test: six literal plaquette words on a 4D periodic unit cube,
with true independent product Haar on its twelve links for the center subgroup
{+I,-I} of SU(2). This is NOT full SU(2) Haar/continuum or the KP W3 bound.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations
from sympy import Symbol, factor, simplify, pi, sin, sqrt, exp, integrate, Rational

L=4; dim=4; o=(0,)*dim
def shift(x,j):
    y=list(x); y[j]=(y[j]+1)%L; return tuple(y)
def plaquette(x, m, n):
    return ((x,m,1),(shift(x,m),n,1),
            (shift(x,n),m,-1),(x,n,-1))
# Six oriented faces of an actual original unit cube in the 0,1,2 axes.
faces=[]
for m,n in combinations(range(3),2):
    k=next(j for j in range(3) if j not in (m,n))
    faces.extend((plaquette(o,m,n),plaquette(shift(o,k),m,n)))
assert len(faces)==6
links=sorted(set((x,j) for face in faces for x,j,_ in face))
assert len(links)==12
bit={link:i for i,link in enumerate(links)}
def mask(face):
    x=0
    for site,j,sgn in face: x ^= 1<<bit[site,j]
    return x
face_masks=tuple(map(mask,faces))
assert len(set(face_masks))==6
assert all(m.bit_count()==4 for m in face_masks)
assert not (face_masks[0]&face_masks[1]) # opposite faces are link-disjoint
assert not __import__('functools').reduce(lambda a,b:a^b,face_masks,0)
assert all(sum(bool(m&(1<<i)) for m in face_masks)==2 for i in range(12))

# Literal source event labels 0..5: six actual Wilson plaquette factors;
# 6 and 7: one source factor s*F, t*G on two OPPOSITE cube faces.
label_masks=face_masks+(face_masks[0],face_masks[1]); nlabels=8
assert label_masks[6]==label_masks[0] and label_masks[7]==label_masks[1]
label_adj=[{j for j in range(nlabels) if j!=i and label_masks[i]&label_masks[j]}
           for i in range(nlabels)]

# For beta=log 2, e^(beta chi)=2^chi = 5/4 + (3/4)chi;
# f_p=2^chi-1 = 1/4 + (3/4)chi; center-Haar link characters
# integrate to 1 for XOR mask=0, else to 0.
a,b=Q(1,4),Q(3,4)
# coefficients of 1,s,t,s*t, indexed by flags (0..3) for source labels.
def activity(S):
    terms={(0,0):Q(1)} # (character XOR mask, source flags)
    for i in S:
        nxt=defaultdict(Q)
        if i<6:
            for (m,f),value in terms.items():
                nxt[(m,f)]+=value*a
                nxt[(m^label_masks[i],f)]+=value*b
        else:
            flag=1<<(i-6)
            for (m,f),value in terms.items():
                assert not (f&flag)
                nxt[(m^label_masks[i],f|flag)]+=value
        terms=nxt
    return tuple(terms.get((0,i),Q(0)) for i in range(4))

def components(S):
    pending=set(S); chunks=[]
    while pending:
        root=min(pending);pending.remove(root); comp={root};frontier=[root]
        while frontier:
            u=frontier.pop()
            for v in sorted(label_adj[u]&pending):
                pending.remove(v);comp.add(v);frontier.append(v)
        chunks.append(tuple(sorted(comp)))
    return tuple(chunks)

def multiply(A,B):
    out=[Q(0)]*4
    for i,x in enumerate(A):
        for j,y in enumerate(B):
            if not i&j:out[i|j]+=x*y
    return tuple(out)

sets=[tuple(i for i in range(nlabels) if bits>>i&1) for bits in range(1<<nlabels)]
connected={S:activity(S) for S in sets if S and len(components(S))==1}
assert connected
bad=0
rhs=[Q(0)]*4; observed=[Q(0)]*4
for S in sets:
    direct=activity(S)
    predicted=(Q(1),Q(0),Q(0),Q(0))
    for C in components(S): predicted=multiply(predicted,connected[C])
    if direct!=predicted:bad+=1
    for i in range(4):
        observed[i]+=direct[i];rhs[i]+=predicted[i]
assert bad==0 and tuple(rhs)==tuple(observed)

# Independently enumerate all 2^12 center-Haar link values to check the
# *actual* literal original cube source, no polymer expansion used here.
full=[Q(0)]*4
for linkbits in range(1<<len(links)):
    f=[-1 if (linkbits&m).bit_count()%2 else 1 for m in face_masks]
    w=Q(1)
    for x in f:w*=Q(2)**x
    for i,val in enumerate((1,f[0],f[1],f[0]*f[1])):
        full[i]+=w*val
full=tuple(x/Q(1<<len(links)) for x in full)
assert full==tuple(observed)

# Closed 6-face Bianchi relation: no other XOR relation among these six
# face characters; exact SU2-center cube partition is known analytically.
for bits in range(1,1<<6):
    val=0
    for i in range(6):
        if bits>>i&1:val^=face_masks[i]
    assert (val==0)==(bits==63)
t=Symbol('t',positive=True)
cov_expected=t**4*(1-t**2)**2/(1+t**6)**2
t0=Q(3,5)
Z,ZF,ZG,ZFG=full
cov=ZFG/Z-(ZF/Z)*(ZG/Z)
assert cov==Q(cov_expected.subs(t,__import__('sympy').Rational(3,5)))
assert cov>0
assert not (label_masks[6]&label_masks[7]) # disjoint Wilson supports

# Check exact finite logarithmic mixed jet and connected-cluster sign.
s,u=__import__('sympy').symbols('s u')
Zpoly=Z+s*ZF+u*ZG+s*u*ZFG
assert simplify(__import__('sympy').diff(__import__('sympy').log(Zpoly),s,u).subs({s:0,u:0})-cov)==0

# Important negative control at large beta: simple plaquette activity in
# original high-temperature/Mayer decomposition fails the pre-existing 1/16
# pointwise base-activity budget already at beta=log 2 in center-Haar case.
plaq_activity=connected[(0,)][0]
assert plaq_activity==a and plaq_activity>Q(1,16)

# SU(2) full Haar (NOT center-subgroup) genuine activity obstruction.
# One plaquette holonomy has Haar law, since its four link variables are
# independent Haar and all other link factors integrate out. Its normalized
# trace is cos(theta), with density (2/pi) sin(theta)^2 dtheta.
theta=Symbol('theta',real=True)
cap=simplify(integrate(2*sin(theta)**2/pi,(theta,0,pi/3)))
assert simplify(cap-(Rational(1,3)-sqrt(3)/(4*pi)))==0
assert float(cap)>1/6 # follows exactly from sqrt(3)<2 and pi>3
# For beta>=16, original microscopic plaquette activity
# w_p=E_Haar[e^(beta*cos theta)-1] >= cap*e^(beta/2)-1,
# so it cannot uniformly meet existing source KP rho_base=1/16.
assert float(cap*exp(8)-1)>1/16
print('PASS: exact full SU2 Haar positive-trace cap =',cap)
print('NO-GO: original full-SU2 microscopic Mayer singleton activity grows at least as cap*exp(beta/2)-1')
print('PASS: 6 native original 4D Wilson cube plaquettes / 12 original links')
print('PASS:',len(sets),'exact labelled subsets; canonical connected support decomposition')
print('PASS:',len(connected),'connected labelled polymer activities with global F/G insertions')
print('PASS: original center-Haar source == finite Mayer hard-core gas, all 4 mark coefficients',full)
print('PASS: independent',1<<len(links),'original link-Haar assignments')
print('PASS: opposite supports disjoint; genuine positive connected mixed log jet =',cov)
print('PASS: full 6-face Bianchi XOR and exact tanh(beta) formula')
print('NO-GO: unrenormalized plaquette activity',plaq_activity,'> KP base 1/16')
print('SCOPE: finite center SU2 subgroup Haar, NOT full SU2 Haar or continuum W3 estimate')
