"""Independent quadrature comparison of two weak layer forms on original clocks.
Manufactured smooth history, not original trajectory or interval proof.
"""
import json
import numpy as np
from scipy.optimize import brentq
from numpy.polynomial.legendre import leggauss


def run(n):
    F=lambda b:np.arcsinh(1/b)-np.sqrt(1+b*b)
    b=lambda t:brentq(lambda x:F(x)-F(1)-t,.07,1.01,xtol=1e-15)
    v=lambda b:-b/np.sqrt(1+b*b)
    a=lambda b:b/(1+b*b)**2
    c=[1.]
    for j in range(24):c.append(c[-1]*(j-1.5)*(j+2.5)/((j+1)*(j+.5)))
    c=np.array(c);d=np.arange(1,len(c))*c[1:];p=(1.5-np.arange(len(c)))*c;ss=(np.arange(1,len(c))-.5)*c[1:]
    q,w=leggauss(n);theta=np.pi*(q+1)/2;u=np.cos(theta);wt=w/2
    rows=[]
    for name,start,end in [('E',0.,.01),('R',2.644,2.659159198154073)]:
        t=(end-start)*(q+1)/2+start;z=b(end);xi=np.array([b(s) for s in t]);tau=end-t;vel=v(xi);acc=a(xi)
        # Integrate velocity and acceleration rather than subtract nearly equal endpoints.
        q8,w8=leggauss(8);u8=(q8+1)/2;w8=w8/2;bb=np.array([[b(s+dt*u) for u in u8] for s,dt in zip(t,tau)])
        dz=tau*(v(bb)@w8);N=tau*tau*(a(bb)@((1-u8)*w8));assert np.max(abs(dz-(z-xi)))<1e-13
        L=tau-vel*dz;C=N/L;Cs=((1-vel*vel)*N-acc*(tau*tau-dz*dz))/(L*L)
        D=np.sqrt(tau*tau-dz*dz);eta=(D[:,None]**2*(1-u[None,:]**2))/(4*z*xi[:,None]);A=np.polynomial.polynomial.polyval(eta,c);Ap=np.polynomial.polynomial.polyval(eta,d);B0=np.polynomial.polynomial.polyval(eta,p);S1=np.polynomial.polynomial.polyval(eta,ss)
        # F(s,r)=(elapsed/h)^2*(1+.1r+.3r^2), smooth flat value at start.
        r=1.2+D[:,None]*u;fac=((t-start)/(end-start))[:,None];f=fac**2*(1+.1*r+.3*r*r);ft=2*fac/(end-start)*(1+.1*r+.3*r*r);frr=fac**2*.6
        time=A*(C[:,None]*ft+(Cs+1.5/xi)[:,None]*f)-(1+C*vel)[:,None]*eta*Ap/xi[:,None]*f
        rad=N[:,None]*(1-u*u)*frr+(B0/xi[:,None]+N[:,None]/(2*z*xi[:,None])*S1)*f
        # normalized angular integration 1/pi, then dt
        T=float((end-start)/2*np.dot(w,time@wt));R=float((end-start)/2*np.dot(w,rad@wt));assert abs(T-R)<2e-13
        rows.append(dict(collar=name,n=n,time_form=T,radial_form=R,absolute_difference=abs(T-R),scope='manufactured history on original clock; no actual source trajectory'))
    return rows
if __name__=='__main__':print(json.dumps(run(64)+run(128),indent=2))
