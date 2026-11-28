"""F8 original-characteristic high-time commutator without normal derivative loss.

R_t=N R_n+S_R, L_t=-N L_n+S_L. Reconstruct each R_n,t^j
and L_n,t^j from time jets one order higher, lower source/time
jets and positive original lapse. No free mixed normal jet.
Still requires true characteristic energy and source estimates.
"""
from math import comb
import sympy as s


def reconstruct(N,Y,S,sign,order=5):
    if sign not in (-1,1) or not N or N[0]==0:
        raise ValueError('nonzero lapse and characteristic sign required')
    if len(N)<order+1 or len(Y)<order+2 or len(S)<order+1:
        raise ValueError('missing time or source jets')
    normal=[]
    for r in range(order+1):
        lower=sum(comb(r,j)*N[j]*normal[r-j] for j in range(1,r+1))
        normal.append(s.factor(sign*(Y[r+1]-S[r])/N[0]-lower/N[0]))
    return normal


def exact():
    t,n=s.symbols('t n',real=True)
    T=s.Rational(21,20);Z=s.Rational(1,4)
    N=2+t/3+n/5+t*n/7
    R=1+t+n+3*t*t*n+4*t**7*n*n
    L=2-t+2*n+t**3*n+5*t**6*n*n
    ev=lambda x:s.expand(x.subs({t:T,n:Z}))
    nj=[ev(s.diff(N,t,j)) for j in range(6)]
    for Y,sign in ((R,1),(L,-1)):
        S=s.diff(Y,t)-sign*N*s.diff(Y,n)
        ys=[ev(s.diff(Y,t,j)) for j in range(7)]
        ss=[ev(s.diff(S,t,j)) for j in range(6)]
        got=reconstruct(nj,ys,ss,sign)
        assert all(s.simplify(got[j]-ev(s.diff(Y,n,t,j)))==0 for j in range(6))
        assert len(got)==6 and all(s.simplify(v).is_finite for v in got)
        bad=list(ss);bad[0]+=1
        changed=reconstruct(nj,ys,bad,sign)
        assert s.simplify(changed[0]-got[0]+sign/nj[0])==0
    t0=s.symbols('t0',positive=True)
    a=s.sinh(s.asinh(t0)-n)
    Nphys=s.cosh(s.asinh(t0)-n)/s.sqrt(1+t0*t0)
    assert s.simplify(s.diff(a,t0)-Nphys)==0
    W,V,H,src,Nn=s.symbols('W V H src Nn')
    SR=src+Nn*W;SL=src-Nn*W
    assert s.simplify(SR-SL-2*Nn*W)==0
    print('PASS F8 transport time6 normal-jet elimination, both R/L signs, original source split')

if __name__=='__main__':exact()
