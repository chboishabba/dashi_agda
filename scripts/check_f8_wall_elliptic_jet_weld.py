"""F8: original scalar_chart_trace normal inverse extended to time jets 0..5.
Reverse GN L H=F twice in n, retaining F,F_n and original Israel N1.
This is an ALTERNATE graph route, not a certified tangential energy estimate.
"""
from math import comb
import sympy as s

def inverse(H,N1,F,Fn,coeff,order=5):
    """Reconstruct N2 and N3 through time order 5, without 1/k.
    Requires H0..H7, N1_0..7 (prescribed original Neumann), F0..5
    and Fn0..5. Coefficients are time-jet arrays at one wall time.
    """
    if any(len(seq)<order+1 for seq in (F,Fn)) or len(H)<order+3 or len(N1)<order+3:
        raise ValueError('missing tangential or source graph jets')
    keys=('A','B','C','At','Bn','An','Atn','Bnn','Cn')
    if any(len(coeff[key])<order+1 for key in keys):
        raise ValueError('missing GN coefficient time derivatives')
    if coeff['B'][0]==0:raise ValueError('degenerate normal principal symbol')
    N2=[];N3=[]
    for j in range(order+1):
        v=F[j]+sum(comb(j,i)*(coeff['A'][i]*H[j-i+2]+coeff['At'][i]*H[j-i+1]
                 -coeff['Bn'][i]*N1[j-i]+coeff['C'][i]*H[j-i]) for i in range(j+1))
        v-=sum(comb(j,i)*coeff['B'][i]*N2[j-i] for i in range(1,j+1))
        N2.append(s.expand(v/coeff['B'][0]))
        w=Fn[j]+sum(comb(j,i)*(coeff['An'][i]*H[j-i+2]
                 +coeff['A'][i]*N1[j-i+2]+coeff['Atn'][i]*H[j-i+1]
                 +coeff['At'][i]*N1[j-i+1]-coeff['Bnn'][i]*N1[j-i]
                 -2*coeff['Bn'][i]*N2[j-i]+coeff['Cn'][i]*H[j-i]
                 +coeff['C'][i]*N1[j-i]) for i in range(j+1))
        w-=sum(comb(j,i)*coeff['B'][i]*N3[j-i] for i in range(1,j+1))
        N3.append(s.expand(w/coeff['B'][0]))
    return N2,N3

def coefficients(A,B,C,t,n,t0,n0,order=5):
    base={'A':A,'B':B,'C':C,'At':s.diff(A,t),'Bn':s.diff(B,n),
          'An':s.diff(A,n),'Atn':s.diff(A,t,n),'Bnn':s.diff(B,n,2),'Cn':s.diff(C,n)}
    return {key:[s.diff(expr,t,j).subs({t:t0,n:n0}) for j in range(order+1)]
            for key,expr in base.items()}

def exact():
    t,n,k=s.symbols('t n k',real=True)
    A=2+t+n+t*n;B=3+2*t+3*n+t*n;C=k*k*(1+t+n*n)
    H=sum((j+1)*t**j for j in range(8)) + n*sum((j+3)*t**j for j in range(8)) + n*n*sum((j+2)*t**j for j in range(6))/2 + n**3*sum((j+1)*t**j for j in range(6))/6
    F=-s.diff(A*s.diff(H,t),t)+s.diff(B*s.diff(H,n),n)-C*H
    t0=s.Rational(2,3);n0=s.Integer(0);k0=s.Rational(7,3)
    ev=lambda e:s.expand(e.subs({t:t0,n:n0,k:k0}))
    cs=coefficients(A,B,C,t,n,t0,n0,5)
    cs={key:[ev(val) for val in values] for key,values in cs.items()}
    h=[ev(s.diff(H,t,j)) for j in range(8)]
    n1=[ev(s.diff(H,n,t,j)) for j in range(8)]
    f=[ev(s.diff(F,t,j)) for j in range(6)]
    fn=[ev(s.diff(F,n,t,j)) for j in range(6)]
    q,r=inverse(h,n1,f,fn,cs)
    assert all(s.simplify(q[j]-ev(s.diff(H,n,2,t,j)))==0 for j in range(6))
    assert all(s.simplify(r[j]-ev(s.diff(H,n,3,t,j)))==0 for j in range(6))
    T=s.symbols('T',positive=True)
    a=s.sinh(s.asinh(T)-n);N=s.cosh(s.asinh(T)-n)/s.sqrt(1+T*T)
    AA=a**3/N;BB=N*a**3;CC=N*a*k*k
    assert s.simplify(BB.subs(n,0)-T**3)==0
    assert s.simplify(s.diff(BB,n).subs(n,0)+T**4/s.sqrt(1+T*T)+3*T*T*s.sqrt(1+T*T))==0
    assert s.simplify((AA/BB).subs(n,0)-1)==0
    f1=list(f);f1[0]+=1
    q1,_=inverse(h,n1,f1,fn,cs)
    assert s.simplify(q1[0]-q[0]-1/cs['B'][0])==0
    fn1=list(fn);fn1[0]+=1
    _,r1=inverse(h,n1,f,fn1,cs)
    assert s.simplify(r1[0]-r[0]-1/cs['B'][0])==0
    try:inverse(h[:7],n1,f,fn,cs)
    except ValueError:pass
    else:raise AssertionError('missing H7 admitted')
    print('PASS 12 exact normal inverse jet comparisons (N2,N3), actual GN wall, off-shell F/Fn controls')
    print('OPEN: 7th tangential time graph, Pi7 Neumann compatibility, source F_n and physical trace')

if __name__=='__main__':exact()
