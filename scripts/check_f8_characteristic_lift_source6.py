"""F8 lifted characteristic time-six forcing uses only original Pi0..Pi7.

The incoming lift chi=1-2n preserves both physical boundaries and adds
no independent source. At differentiated order six, the unique highest
source derivative is -chi*q7 in the lifted L equation, q=12 Pi.
"""
import sympy as s


def exact():
    t,n=s.symbols('t n',real=True)
    N=s.Function('N')(t);a=s.Function('a')(t)
    c=s.Function('c')(t);Nn=s.Function('Nn')(t)
    H,R,l,q=s.symbols('H R l q',real=True)
    k=s.symbols('k',real=True);chi=1-2*n
    L=l+q*chi;W=(R+L)/2;V=(R-L)/2
    src=(Nn-3*N*c/a)*V-3*N/a*W-N*k*k*H/a**2
    SR=s.expand(src+Nn*W)
    SL=s.expand(src-Nn*W)
    AH=s.diff(N*W,q);AR=s.diff(SR,q);AL=s.diff(SL,q)
    assert s.simplify(AH-N*chi/2)==0
    assert s.simplify(AR-3*N*(c-1)*chi/(2*a))==0
    assert s.simplify(AL-(-Nn+3*N*(c-1)/(2*a))*chi)==0
    qfun=s.Function('q')(t)
    fH=AH*qfun
    fR=AR*qfun
    fL=AL*qfun-s.diff(qfun,t)*chi-N*qfun*s.diff(chi,n)
    qj=s.symbols('q0:9',real=True)
    poly=sum(qj[j]*(t-1)**j/s.factorial(j) for j in range(9))
    F6=[s.diff(f,t,6).subs({
         s.diff(qfun,t,j):s.diff(poly,t,j) for j in range(1,9)})
         .subs(qfun,poly).subs(t,1) for f in (fH,fR,fL)]
    assert all(not z.has(qj[8]) for z in F6)
    assert s.simplify(s.diff(F6[0],qj[7]))==0
    assert s.simplify(s.diff(F6[1],qj[7]))==0
    assert s.simplify(s.diff(F6[2],qj[7])+chi)==0
    assert s.simplify(F6[2].subs({x:0 for x in qj[:7]}).diff(qj[7])+chi)==0
    print('PASS original F8 lifted m6 forcing uses Pi0..Pi7 only; unique -chi q7 coefficient')

if __name__=='__main__':exact()
