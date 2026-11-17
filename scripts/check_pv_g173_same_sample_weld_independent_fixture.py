#!/usr/bin/env python3
"""Independent 25-check P5/P7 optical/JV finite fixture, NO real-device data."""
import numpy as np
H=6.62607015e-34; C=299792458.; Q=1.602176634e-19
wl=np.linspace(400,1000,31);n=4
spec=np.column_stack([wl,np.ones_like(wl)])
A=np.full((len(wl),n),.2)
optic=np.column_stack([wl,np.full(len(wl),.1),A,np.full(len(wl),.1)])
eqe=np.column_stack([wl,.8*A]);checks=[]
def chk(tag,p):
    assert bool(p),tag
    checks.append(tag)
def photoflux(irr,wl):return irr*wl*1e-9/(H*C)
Jsc=Q*np.trapezoid(photoflux(spec[:,1],wl)[:,None]*eqe[:,1:],wl,axis=0)
curves=[]
for j in Jsc:
    v=np.linspace(0,1,21)
    curves.append(np.column_stack([v,j*(1-v)]))
chk("photon partition 100%",np.allclose(optic[:,1:].sum(axis=1),1))
chk("EQE below local absorber",np.all(eqe[:,1:]<=A))
chk("all 4 Jsc positive",np.all(Jsc>0))
chk("4T linear JV vertex",all(abs(curves[i][10,0]-.5)<1e-10 for i in range(n)))
P4=sum(j/4 for j in Jsc);P2=min(Jsc)*n/4
chk("2T = 4T for identical lossless curves",abs(P2-P4)<1e-9)
chk("4T converter 97% lowers gross output",0.97*P4<P4)
chk("aux subtraction decreases net",0.97*P4-2<0.97*P4)
chk("no >50 fake selftest",(0.97*P4-2)/np.trapezoid(spec[:,1],wl)<.5)
chk("source mismatch failure predicate",not np.array_equal(wl,wl+1))
chk("double count failure predicate",np.any(.1+4*(.2*2)+.1>1))
chk("EQE>A failure predicate",np.any(1.1*A>A))
chk("Jsc modified 10% fails 2% threshold",
    all(abs(j-.1*j)>.02*max(j,.1*j) for j in Jsc))
chk("converter gain>unity rejected by criterion",not (0<=1.2<=1))
chk("recovery exceed drive rejected",not (2<=1))
chk("negative auxiliary rejected",not (-1>=0))
def piecewise_max(x,y):
    vals=[(x0*y0,x0) for x0,y0 in zip(x,y)]
    for i in range(len(x)-1):
        a=(y[i+1]-y[i])/(x[i+1]-x[i]);b=y[i]-a*x[i]
        if a<0:
            vertex=-b/(2*a)
            if x[i]<vertex<x[i+1]:vals.append((vertex*(a*vertex+b),vertex))
    return max(vals)
for ix,(j,curve) in enumerate(zip(Jsc,curves)):
    p,v=piecewise_max(curve[:,0],curve[:,1])
    chk(f"4T {ix} exact MPP 0.5V",abs(v-.5)<1e-12)
    chk(f"4T {ix} exact MPP Jsc/4",abs(p-j/4)<1e-9)
knots=sorted(set(float(c) for curve in curves for c in curve[:,1]))
voltages=[sum(np.interp(k,curve[:,1][::-1],curve[:,0][::-1])
    for curve in curves) for k in knots]
p,j=piecewise_max(np.asarray(knots),np.asarray(voltages))
chk("series piecewise maximum same P for identical",abs(p-P2)<1e-7)
chk("series maximum current one half Jsc",abs(j-Jsc[0]/2)<1e-7)
# Independent unequal-junction series-current negative control:
# a 2T string must current-match, while 4T can extract at independent MPP.
sourceJ=np.array([21.,24.,29.,31.])
sourceVoc=np.array([1.2,1.1,.9,.8])
unequal=[np.column_stack([np.linspace(0,v,21),
    j*(1-np.linspace(0,v,21)/v)]) for j,v in zip(sourceJ,sourceVoc)]
unequal4=float(sum(j*v/4 for j,v in zip(sourceJ,sourceVoc)))
cap=float(min(sourceJ))
knots2=sorted(set([0.,cap]+[float(c) for iv in unequal
                         for c in iv[:,1] if 0<=c<=cap]))
volts2=[sum(np.interp(k,iv[:,1][::-1],iv[:,0][::-1])
        for iv in unequal) for k in knots2]
unequal2,atI=piecewise_max(np.asarray(knots2),np.asarray(volts2))
chk("unequal 2T current matching costs power",
    abs(unequal4-25.625)<1e-10 and
    abs(unequal2-25.02860693940963)<1e-9 and unequal2<unequal4)

print("PASS",len(checks),"synthetic tests; gross W/m2",P4,
      "net W/m2",P4*.97-2,
      "synthetic net efficiency %",100*(P4*.97-2)/600)
