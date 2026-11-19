"""Reduced reciprocal KK magnetic-bias mode: fixed initial energy, no pump budget trick.
Not a calibrated YBCO mode or full spatial solver. c=hbar=1 in derivation.
"""
import numpy as np
import sympy as s
from scipy.linalg import eigh
from scipy.integrate import solve_ivp

def symbolic():
    x,y,g,B,k,M=s.symbols('x y g B k M',real=True)
    V=s.exp(g*y)*(B+k*x)**2/2+M*M*y*y/2-k*B*x-g*B*B*y/2
    H=s.hessian(V,(x,y)).subs({x:0,y:0})
    assert s.simplify(H[0,1]-g*B*k)==0
    assert s.simplify(H.det()-k*k*(M*M-g*g*B*B/2))==0
    print('Hessian',H,'det',s.factor(H.det()))

def transfer(w,m,h,T=100,damping=0):
    K=np.array([[w*w,h],[h,m*m]])
    ev,U=eigh(K); assert min(ev)>0
    t=np.linspace(0,T,4001)
    z0=np.array([0.,0.,np.sqrt(2),0.,0.]) # unit initial EM energy
    def rhs(t,z):
        x=z[:2]; v=z[2:4]; return np.r_[v,-K@x-damping*v,damping*(v@v)]
    sol=solve_ivp(rhs,(0,T),z0,t_eval=t,rtol=2e-10,atol=2e-12); assert sol.success
    x,v=sol.y[:2],sol.y[2:4]; E=(np.sum(v*v,axis=0)+np.sum(x*(K@x),axis=0))/2
    err=max(abs(E+sol.y[4]-1)); assert err<2e-7
    scalar=(v[1]**2+m*m*x[1]**2)/2
    return max(scalar),err

def main():
    symbolic()
    for h in (.1,.02,.004):
        for m in (.8,1.,1.2):
            a,e=transfer(1,m,h); b,f=transfer(1,m,h,damping=.02)
            print(f'h={h:g} m={m:g} undamped={a:.9g} damped={b:.9g} ledger={max(e,f):.3g}')
    assert transfer(1,1,0)[0]==0
    for h in (.001,.0005): print('weak',h,transfer(1,1,h)[0])
    G=6.67430e-11;c=299792458.;mu0=1.25663706212e-6
    kB=np.sqrt(24*np.pi*G/(mu0*c**4)); rate=c*kB/np.sqrt(2) # h/omega = g B in canonical units; kB=sqrt(2)*? see text
    # kB^2=6 u/M^2=3 B^2/M^2; canonical g=sqrt(6)/M -> g B=sqrt(2)*kB
    rate=c*np.sqrt(2)*kB
    print('1T ideal mixing h/omega s^-1',rate,'first transfer time s',np.pi/rate,'27.5s fraction leading order',(rate*27.5/2)**2)
if __name__=='__main__':main()
