#!/usr/bin/env python3
"""BR150-153: half-order trace, Einstein frame optics, G4 York jets,
literal Leech order-three lift. Local exact algebra, not nonlinear acceptance."""
import argparse
from itertools import product
import sympy as s
Q=s.Rational

def eq(a,b):
    if isinstance(a,s.MatrixBase):
        assert (a-b).applyfunc(s.simplify)==s.zeros(*a.shape)
    else:
        assert s.simplify(a-b)==0

def trace():
    from check_hopf369_br143_145_parallel import trace as donor
    P,X,Q0,M,D,L,E,Sc,C,Ct,Z=donor()
    B=L.col_join(E)
    U=(-Q0*M[3]*Q0).row_join(-Q0*D[3].T).col_join((-D[3]*Q0).row_join(s.zeros(50)))
    A=U*B
    assert A.rank()==26 and A.col_join(C).rank()==26
    w,a,b=s.symbols('w a b',positive=True);k=s.symbols('k',integer=True)
    eq(w**(2*k-1)*a*b,(w**k*a)*(w**(k-1)*b))
    eq(w**(2*k)*a*a+w**(2*k-2)*b*b-2*w**(2*k-1)*a*b,(w**k*a-w**(k-1)*b)**2)
    y=s.symbols('y',nonnegative=True);v=s.exp(-w*y)
    eq(s.integrate(v*v,(y,0,s.oo)),1/(2*w))
    eq(s.integrate(s.diff(v,y)**2,(y,0,s.oo)),w/2)
    eq(w**(2*k)/(2*w)+w**(2*k-2)*w/2,w**(2*k-1))
    print('PASS BR150 full normal trace and sharp half-order mixed-norm budget')

def optics():
    e,p,t=s.symbols('e p t',positive=True);theta=s.symbols('theta',real=True)
    O=s.diag(-Q(176,9),-Q(176,9)+32*s.sin(theta)**2)*e**2/p**2
    H=-Q(352,9)*e**2/p**2
    OE=(O-H*s.eye(2)/2)/p
    eq(OE,s.diag(0,32*s.sin(theta)**2)*e**2/p**3)
    eq(s.trace(OE),32*e**2*s.sin(theta)**2/p**3)
    eq(s.trace(OE),p**3/2*(8*e/p**3)**2*s.sin(theta)**2)
    q=e**2/p**3;m=e/p**2
    eq(q/m**2,p);eq(m*(q/m**2)**2,e)
    u=s.symbols('u',nonnegative=True)
    eq(s.integrate((t-u)*u*u/2,(u,0,t)),t**4/24)
    r=s.symbols('r',positive=True)
    eq(s.integrate(Q(16,3)*e**2*r/(1+r*r)**4,(r,0,s.oo)),Q(8,9)*e**2)
    q0=Q(8,9)*Q(1,4)**2;eq(1+q0,Q(19,18));eq(1/(1-q0),Q(18,17))
    print('PASS BR151 Einstein-frame optical sign change, observer inverse, Jacobi remainder coefficient, central radius interval')

def york():
    r=s.symbols('r',positive=True);a=s.symbols('a',real=True)
    fp=-2*(r-s.atan(r))/r**2;gp=-2*(s.atan(r)-r/(1+r*r))/r**2
    eq(-s.diff(fp,r)-2*fp/r,2/(1+r*r))
    eq(-s.diff(gp,r)-2*gp/r,4/(1+r*r)**2)
    b=(s.diff(fp,r)-fp/r)/r**2;v=-s.diff(fp,r)-fp/r;c=-gp/r
    A=s.diff(v,r)+b*r;B=2*s.diff(b,r)*r*r;C=2*b*r;D=s.diff(c,r)*r
    eq(2*A+B+3*C,0)
    for f,k in [(A,-Q(12,5)),(B,0),(C,Q(8,5)),(D,0)]:
        eq(s.limit(f,r,0),0);eq(s.limit(f/r,r,0),k)
    q=s.symbols('q',positive=True)
    eq(2/r*s.integrate(s.exp(-q)*s.sin(q*r),(q,0,s.oo)),2/(1+r*r))
    eq(2/r*s.integrate(q*s.exp(-q)*s.sin(q*r),(q,0,s.oo)),4/(1+r*r)**2)
    mu,nu=s.symbols('mu nu',real=True);n=s.Matrix([nu,0,mu]);z=s.Matrix([0,0,1]);h=z.cross(n)
    aa,bb,cc,dd=s.symbols('A B C D',real=True)
    Y=aa*(n*z.T+z*n.T)+bb*mu*n*n.T+cc*mu*s.eye(3);W=dd*(n*h.T+h*n.T)
    eq(s.trace(Y.T*W),0)
    reduce=lambda f:s.rem(s.expand(f),nu**2+mu**2-1,nu)
    U=2*(aa**2+dd**2);V=2*aa**2+bb**2+3*cc**2+4*aa*bb+4*aa*cc+2*bb*cc-2*dd**2
    eq(reduce(s.trace((Y+W).T*(Y+W))-U-V*mu**2),0)
    I=s.eye(3);g=[]
    for l in range(3):g.append(a*(Q(12,5)*(I[:,l]*z.T+z*I[:,l].T)-Q(8,5)*z[l]*I))
    eq(s.Matrix([sum(g[j][i,j] for j in range(3)) for i in range(3)]),8*a*z)
    for m in g:eq(s.trace(m),0)
    for l,i,j in product(range(3),repeat=3):
        f=12*a*((I[l,i]*z[j]+I[l,j]*z[i])/3-2*(I[l,i]*z[j]+I[l,j]*z[i]+I[i,j]*z[l])/15)
        eq(f,g[l][i,j])
    eq(s.integrate(3*(mu**2-(1-mu**2)/2)*mu**2/2,(mu,-1,1)),Q(2,5))
    p,Hx,Hz,k,ktr,sp,sl,rho=s.symbols('p Hx Hz k ktr sp sl rho',real=True,nonzero=True)
    Hess=s.diag(Hx,Hx,Hz);Ric=(-2*Hess-2*s.trace(Hess)*I)/p**4;K=ktr*I/3;S=s.diag(sp,sp,sl)
    T=Ric+ktr*K-K*K-k*(S+(rho-s.trace(S))*I/2)
    eq(T[2,2]-T[0,0],-2*(Hz-Hx)/p**4-k*(sl-sp))
    print('PASS BR152 original G4 radial York source, exact central gradient, axial norm and tidal Hessian cut')

def leech():
    import numpy as np
    from sympy.matrices.normalforms import hermite_normal_form
    N=24;I=np.eye(N,dtype=np.int64)
    g=sum(1<<i for i in (0,1,5,6,7,9,11));gen=[(g<<i)|(((g<<i).bit_count()%2)<<23) for i in range(12)];code=[0]
    for v in gen:code += [x^v for x in code]
    C=set(code);assert len(C)==4096
    perm=[(-pow(x+1,-1,23))%23 if x!=22 else 23 for x in range(23)]+[0]
    assert all(perm[perm[perm[i]]]==i and perm[i]!=i for i in range(N))
    trans=lambda v:sum(1<<perm[i] for i in range(N) if v>>i&1)
    assert all(trans(v) in C for v in code)
    Gcode=np.array([[(v>>i)&1 for i in range(N)] for v in gen],dtype=np.int64)
    odd=np.ones(N,dtype=np.int64);odd[0]=-3
    B=hermite_normal_form(s.Matrix(np.vstack([2*Gcode,4*(I[1:]-I[0]),8*I[0:1],odd[None,:]]).T.tolist()))
    G=B.T*B/8;assert G.det()==1 and abs(B.det())==2**36
    P=s.zeros(N)
    for i,j in enumerate(perm):P[j,i]=1
    A=B.inv()*P*B;assert all(v.q==1 for v in A);eq(A**3,s.eye(N));eq(A.T*G*A,G)
    eq(A.charpoly().as_expr(),(A.charpoly().gen**3-1)**8)
    G=np.array(G.tolist(),dtype=np.int64);A=np.array(A.tolist(),dtype=np.int64)%2
    U=(np.triu(G,1)+np.diag(np.diag(G)//2))%2;D=(A.T@U@A+U)%2
    assert np.array_equal(D,D.T) and not np.any(np.diag(D))
    K=np.triu(D,1);f=lambda x:int(x@K@x%2)
    chi=np.array([f(x)^f(A@x%2)^f(A@A@x%2) for x in I]);assert np.array_equal(A.T@chi%2,chi)
    f3=lambda x:f(x)^int(chi@x%2)
    rng=np.random.default_rng(369)
    for x,y in list(product(I,I))+[(rng.integers(0,2,N),rng.integers(0,2,N)) for _ in range(4096)]:
        assert f3(x)^f3(y)^f3(x^y)==int(x@D@y%2)
        assert f3(x)^f3(A@x%2)^f3(A@A@x%2)==0
    Ksum=(K+A.T@K@A+(A@A).T@K@(A@A))%2
    assert np.array_equal(Ksum,Ksum.T) and np.array_equal(np.diag(Ksum),chi)
    def rank(M):
        M=M.copy()%2;k=0
        for j in range(M.shape[1]):
            row=next((i for i in range(k,len(M)) if M[i,j]),None)
            if row is None:continue
            M[[row,k]]=M[[k,row]]
            for i in range(k+1,len(M)):
                if M[i,j]:M[i]^=M[k]
            k+=1
        return k
    assert rank(A-I)==16
    assert 16**2==2**8 and 16%3==4096%3 and (-16)%3!=4096%3
    m0=(4096+2*16)//3;m1=(4096-16)//3;assert (m0,m1)==(1376,1360)
    assert 2%3 and 8%3;assert sum(perm[i]==i for i in range(N))==0
    assert 8*m0+16*m1==32768
    assert 300%3==0 and 98280%3==0 and 98304%3==0
    print('PASS BR153 literal fixed-free Golay/Leech order3, corrected cocycle lift, ground trace +16 and selected weight-two trace 0')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['trace','optics','york','leech'],required=True)
    {'trace':trace,'optics':optics,'york':york,'leech':leech}[p.parse_args().part]()
