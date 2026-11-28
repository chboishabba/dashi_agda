"""F8 all-sector frozen collar work and full-clock rank-one algebra.
Analytic bounds in the roadmap; no physical exterior or variable-time theorem.
"""
from fractions import Fraction as Q
import sympy as S


def exact():
    s,k,b,K,h,m=S.symbols('s k b K h m',real=True)
    a=3*b+h; al=3*b+h/2; d=s*s+a*s+k*k+3*b*b
    u=S.Matrix([[-s/2-al,S.I*k,-3*s/2]])
    c=K*S.Matrix([10*s+6*h+6*b,6*S.I*k,2*s-6*b])/d
    D=2*K*k*k+24*K*b*b-3*K*(h+b)*(h+6*b)
    assert S.cancel((u*c)[0]+8*K-D/d)==0
    I=S.eye(3); F=m+8*K-D/d
    assert ((m*I-c*u)*(I+c*u/F)/m-I).applyfunc(S.cancel)==S.zeros(3)
    # Full lower-order Israel stress clock part from density and pressure.
    dr=K*(s-3*b); dp=K*(s+h+3*b)
    assert S.expand(c[0]*d-4*dr-6*dp)==0
    assert S.expand(c[2]*d-2*dr)==0
    g,tau,ks=S.symbols('gamma tau ks',real=True)
    z=g+S.I*tau; Z=g*g+tau*tau+ks*ks; w=z*z+ks*ks
    assert S.expand(S.re(S.conjugate(z)*w)-g*Z)==0
    dc=w+a*z+3*b*b
    assert S.expand(S.im(dc)-(2*g+a)*tau)==0
    assert S.expand(S.re(S.conjugate(z)*S.conjugate(dc))-(g*(Z-4*tau*tau+3*b*b)+a*(g*g-tau*tau)))==0
    # |s²+c² k²|² - gamma² (|s|²+c² k²) >= 0.
    q=S.symbols('q',nonnegative=True)
    assert S.expand((g*g-tau*tau+q)**2+4*g*g*tau*tau-g*g*(g*g+tau*tau+q)-((q-tau*tau)**2+g*g*(tau*tau+q)))==0
    # Exact rational budgets for a deliberately conservative damping threshold.
    gamma=10**12
    assert Q(10000,gamma)<Q(1,2)
    assert Q(80003,gamma)<Q(1,100)
    assert Q(7*80000*362+7*3*362+100000*400,gamma)<Q(1,2)
    assert Q(4*100000*5,gamma)<Q(1,2)
    print('12 exact grouped checks PASS')

if __name__=='__main__':exact()


def diagnostic():
    import numpy as np
    from check_f8_optical_collar_dtn import dtn
    from check_f8_coupled_collar import operator, transfer, boundary, ids
    fun=operator(); worst=0.; defect=0.; cases=0
    ti=[i for i,(a,b) in enumerate(ids) if b<4]; ni=ids.index((4,4))
    for t in (1.,3.,12.):
        b=1/t; beta=np.sqrt(1+b*b); K=b*b/(3*beta)-b**4/12
        h=(-b**3*(2+b*b)/(3*beta**3)+b**5/3)/K
        for z,k in ((40+0j,0.),(40+100j,100.),(40+180j,100.),(40+100j,180.),(40+100j,np.sqrt(3)*100)):
            q=k*k; w=z*z+q; Z=abs(z)**2+q
            m,mass=dtn(t,k,w); dc=w+(3*b+h)*z+3*b*b
            D=2*K*q+24*K*b*b-3*K*(h+b)*(h+6*b)
            F=m+8*K-D/dc
            assert (z.conjugate()*m).real>=z.real*np.sqrt(Z)*(1-1e-5)
            assert (z.conjugate()*m).real>=z.real*Z*mass*(1-1e-5)
            if z.imag: assert F.imag*z.imag>0
            N=boundary(t,z,np.array([k,0.,0.]),transfer(fun,t,z,np.array([k,0.,0.]),256))
            # Exact block Schur elimination, compare to unreduced 15-row solve.
            f=np.arange(1,16)*(1+.3j); known=[i for i in range(15) if i not in ti+[ni]]
            rhs=f-N[:,known]@f[known]; S=N[np.ix_(ti,ti)]-np.outer(N[ti,ni],N[ni,ti])/N[ni,ni]
            y=np.zeros(15,complex); y[known]=f[known]
            y[ti]=np.linalg.solve(S,rhs[ti]-N[ti,ni]*rhs[ni]/N[ni,ni]); y[ni]=(rhs[ni]-N[ni,ti]@y[ti])/N[ni,ni]
            ref=np.linalg.solve(N,f)
            worst=max(worst,np.max(abs(N@y-f))/np.max(abs(f)))
            defect=max(defect,np.max(abs(ref-y))/max(1,np.max(abs(ref))))
            assert np.allclose(ref,y,rtol=1e-8,atol=1e-8); cases+=1
    print(cases,'actual frozen collar sector diagnostics PASS; max residual',worst,'Schur relative defect',defect)


if __name__=='__main__':diagnostic()
