"""Axial geodesic comparator from original G3 second jets; not vacuum evolution."""
import numpy as np
import sympy as s
from scipy.integrate import solve_ivp


def exact():
    # Axial base metric -dt²+g(t,z) dz², circle phi, A=A_z dz.
    g,gt,gz,p,pt,pz,A,At,k,v,u=s.symbols('g gt gz p pt pz A At k v u',real=True)
    # affine velocities u=dt/ds, v=dz/ds; F_tz=At.
    du=-gt*v*v/2-k*At*v-k*k*pt/p**3
    dv=(-gt*u*v-gz*v*v/2-k*At*u+k*k*pz/p**3)/g
    norm=-u*u+g*v*v+k*k/p**2
    dn=s.diff(norm,u)*du+s.diff(norm,v)*dv+(gt*u+gz*v)*v*v-2*k*k*(pt*u+pz*v)/p**3
    assert s.simplify(dn)==0
    print('PASS affine KK normalization and signed electric force')


def numerical(e=.25):
    # Original P0T radial profile, normalized at R=64. No interval certificate.
    sol=solve_ivp(lambda r,y:[y[1],-16*e*e*y[0]/(3*(1+r*r)**4)],(0,64),(0,1),rtol=2e-12,atol=2e-14,dense_output=True)
    assert sol.success
    N=sol.y[1,-1]
    def jet(z):
        r=abs(z); u,v=sol.sol(r); p=u/(r*N) if r>1e-6 else (1-8*e*e*r*r/9)/N
        h=(v/u-1/r)*np.sign(z) if r>1e-6 else -16*e*e*z/9
        b2=64*e*e/(1+z*z)**4
        hr=h/z if abs(z)>1e-6 else -16*e*e/9
        gdd=-b2/2-8*hr-6*h*h
        pdd=(-7*b2/12+h*h)/p
        # On axis curl B0_z=32/(1+z²)^3, radial grad cross B0=0.
        Add=-32*e/(p*p*(1+z*z)**3)
        return np.array([p*p,p,2*e/(1+z*z)**1]),np.array([gdd,pdd,Add])
    def geom(t,z):
        a,b=jet(z); d=1e-5
        ap,bp=jet(z+d); am,bm=jet(z-d)
        return a+.5*t*t*b,t*b,(ap-am+.5*t*t*(bp-bm))/(2*d)
    def run(k,end):
        p=jet(0)[0][1]; u0=np.sqrt(1+k*k/p**2)
        def rhs(t,Y):
            z,u,v=Y; (g,p,A),(gt,pt,At),(gz,pz,Az)=geom(t,z)
            assert g>0 and p>0 and u>0
            du=-gt*v*v/2-k*At*v-k*k*pt/p**3
            dv=(-gt*u*v-gz*v*v/2-k*At*u+k*k*pz/p**3)/g
            return [v/u,du/u,dv/u]
        S=solve_ivp(rhs,(0,end),(0,u0,0),rtol=1e-10,atol=1e-12,t_eval=np.linspace(0,end,21))
        assert S.success
        err=max(abs(-u*u+geom(t,z)[0][0]*v*v+k*k/geom(t,z)[0][1]**2+1) for t,(z,u,v) in zip(S.t,S.y.T))
        assert err<1e-7
        return S.y[0,-1],err
    for end in (.01,.02,.04):
        p,ep=run(1,end); m,em=run(-1,end); z,ez=run(0,end)
        assert abs(p+m)<1e-10 and abs(z)<1e-12
        print('t',end,'z(+k)',p,'z(-k)',m,'norm error',max(ep,em,ez))
    print('PASS second-jet axial comparator; no Einstein residual bound')

if __name__=='__main__':
    exact(); numerical()
