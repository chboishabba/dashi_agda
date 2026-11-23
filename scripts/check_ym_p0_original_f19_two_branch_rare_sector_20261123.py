#!/usr/bin/env python3
"""YM mass gap P0: exact original F19 two-Hessian-branch rare-sector cut.

Analytic theorems work for full positive SU(N) Wilson/Haar, any coarse map.
Fixture is the prior ORIGINAL 4D L4 all-1536-plaquette Wilson-action script:
only 12 original links varied over the SU2 centre, remaining 1012 frozen.
Not a continuous-Haar quadrature or an absolute CMP116 polymer shell.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
from runpy import run_path

d=run_path(str(Path(__file__).with_name(
    "check_ym_p0_sun_original_two_mark_bad_event_20261123.py")))
records=d["original"]
rho=Q(9,100)
assert len(records)==4096
compressed=defaultdict(int)
for bits,(wt,f,g,bad) in enumerate(records):
    # Original two even-start y-positive R445 holonomies:
    # two independently varied native link bits 0 and 8.
    W=((bits>>0)&1,(bits>>8)&1)
    compressed[(W,f,g,bad)]+=wt
rows=[(*key,wt) for key,wt in compressed.items()]
total=sum(r[-1] for r in rows)
p=Q(sum(w for W,f,g,b,w in rows if b),total)
assert p==d["p"] and 0<p<Q(1,4)
checks=0

def verify(cond):
    global checks
    assert cond
    checks+=1

def calc(sub,s,t):
    den=sum(w*(1+s*f)*(1+t*g) for W,f,g,b,w in sub)
    if den==0: return None
    ex=sum(w*f*(1+t*g) for W,f,g,b,w in sub)/den
    ey=sum(w*g*(1+s*f) for W,f,g,b,w in sub)/den
    exy=sum(w*f*g for W,f,g,b,w in sub)/den
    return den,ex,ey,exy-ex*ey

def branches(sub,s,t):
    Z,x,y,c=calc(sub,s,t)
    groups=defaultdict(list)
    for row in sub:groups[row[0]].append(row)
    inside=Q(0);meanx=Q(0);meany=Q(0);meanxy=Q(0)
    for W,group in groups.items():
        result=calc(group,s,t)
        if result is None:continue
        z,a,b,v=result
        inside+=z*v/Z
        meanx+=z*a/Z
        meany+=z*b/Z
        meanxy+=z*a*b/Z
    between=meanxy-meanx*meany
    verify(inside+between==c and meanx==x and meany==y)
    return c,inside,between

good=[r for r in rows if not r[3]]
bad=[r for r in rows if r[3]]
verify(len(good)>0 and len(bad)>0)
M=1/(1-rho)
R=((1+rho)/(1-rho))**2
for s,t in product((-rho,-Q(3,100),Q(0),Q(3,100),rho),repeat=2):
    c,inside,between=branches(rows,s,t)
    ca,insa,betwa=branches(good,s,t)
    ptilt=calc(bad,s,t)[0]/calc(rows,s,t)[0]
    verify(ptilt<=R*p)
    verify(abs(c-ca)<=6*M*M*ptilt)
    verify(abs(inside-insa)<=6*M*M*ptilt)
    verify(abs(between-betwa)<=12*M*M*ptilt)
    verify(abs(inside-insa)<=6*M*M*R*p)
    verify(abs(between-betwa)<=12*M*M*R*p)

# Weighted source-absolute fibre event-log coefficients at the origin.
nuW=defaultdict(list)
for row in rows:nuW[row[0]].append(row)
alpha=Q(1,4)
abslog=Q(0);exceptional=Q(0);exccurv=Q(0);checktower=Q(0)
for W,rr in sorted(nuW.items()):
    mass=calc(rr,Q(0),Q(0))[0]
    br=[x for x in rr if x[3]]
    ar=[x for x in rr if not x[3]]
    pW=Q(sum(x[-1] for x in br),mass)
    checktower+=Q(mass,total)*pW
    if pW>alpha:
        exceptional+=Q(mass,total)
        exccurv+=Q(mass,total)*abs(calc(rr,Q(0),Q(0))[3])
        continue
    local=Q(0)
    if br:
        za,maF,maG,ca=calc(ar,Q(0),Q(0))
        zb,mbF,mbG,cb=calc(br,Q(0),Q(0))
        z=zb/za
        for n in range(1,25):
            term=z**n*((cb-ca)+n*(mbF-maF)*(mbG-maG))
            verify(abs(term)<=z**n*(2+4*n))
            local+=abs(term)
    verify(local<=16*pW)
    abslog+=Q(mass,total)*local
verify(checktower==p)
verify(exceptional<=4*p and exccurv<=exceptional)
verify(abslog<=16*p and abslog+exccurv<=20*p)
verify(sum(1 for rr in nuW.values() if all(x[3] for x in rr))==2)
print("PASS",checks,"exact original 4D Wilson R445/F19 two-branch and termwise-absolute rare-sector checks")
print("P(original bad)=",float(p),"weighted event-log abs=",float(abslog),
      "exceptional coarse mass=",float(exceptional))
print("At sources |s|,|t|<=9/100: |delta within|<=C_rho*p, |delta between|<=2*C_rho*p.")
print("At zero: weighted abs log good-fibre charges <=16p; exceptional curvature <=4p.")
print("NOT physical CMP119 constrained T, CMP116 individual renormalized spatial activities, or YM mass gap.")
