"""P0AK: pressure jump, periodic AdS wall, and linear constraint gap.
Exact symbolic checks and 1D periodic normal-sector FEM; no Hopf evolution.
"""
import sympy as s
import numpy as np
from scipy.linalg import eigh
from numpy.polynomial.legendre import leggauss


def exact():
    k,rho,p,T=s.symbols('k rho p T',positive=True)
    # k is kappa5 squared in this block.
    p1,p2,p3=s.symbols('p1 p2 p3',real=True)
    S=s.diag(-rho,p+p1,p+p2,p-p1-p2)
    J=-k*(S-s.trace(S)*s.eye(4)/3)
    assert (J-s.diag(k*(2*rho/3+p),-k*(rho/3+p1),-k*(rho/3+p2),-k*(rho/3-p1-p2))).applyfunc(s.expand)==s.zeros(4)
    exponent=-2-3*p/rho
    assert s.expand(exponent*(-k*rho/3)-J[0,0])==0
    assert exponent.subs(p,-rho)==1
    # Compute Ricci of a general warped AdS4 Poincare metric independently.
    t,x,z,v,y=s.symbols('t x z v y',real=True)
    b=s.Function('b')(y); h=s.symbols('h',positive=True)
    coords=(t,x,z,v,y)
    g=s.diag(-b*b/(h*z)**2,b*b/(h*z)**2,b*b/(h*z)**2,b*b/(h*z)**2,1)
    gi=g.inv(); dim=5
    G=[[[s.simplify(sum(gi[a,l]*(s.diff(g[l,j],coords[i])+s.diff(g[l,i],coords[j])-s.diff(g[i,j],coords[l])) for l in range(dim))/2) for j in range(dim)] for i in range(dim)] for a in range(dim)]
    Ric=s.Matrix(dim,dim,lambda i,j:s.simplify(sum(s.diff(G[a][i][j],coords[a])-s.diff(G[a][i][a],coords[j])+sum(G[a][a][l]*G[l][i][j]-G[a][j][l]*G[l][i][a] for l in range(dim)) for a in range(dim))))
    Rm=gi*Ric
    expected=s.diag(*([-3*h*h/b**2-s.diff(b,y,2)/b-3*s.diff(b,y)**2/b**2]*4),-4*s.diff(b,y,2)/b)
    assert (Rm-expected).applyfunc(s.simplify)==s.zeros(5)
    c,L=s.symbols('c L',positive=True) # c=AdS5 inverse length
    w=s.cosh(c*(y-L/2))/s.cosh(c*L/2); h0=c/s.cosh(c*L/2)
    assert s.simplify(s.diff(w,y,2)-c*c*w)==0
    assert s.trigsimp(s.diff(w,y)**2-c*c*w*w+h0*h0)==0
    assert (Rm.subs({h:h0,b:w}).doit()+4*c*c*s.eye(5)).applyfunc(s.simplify)==s.zeros(5)
    assert s.simplify(w.subs(y,0)-1)==s.simplify(w.subs(y,L)-1)==0
    j=s.simplify(s.diff(w,y).subs(y,0)-s.diff(w,y).subs(y,L))
    tension=6*c*s.tanh(c*L/2)/k
    assert s.simplify(j+k*tension/3)==0
    assert (-3*j*s.eye(4)-k*tension*s.eye(4)).applyfunc(s.simplify)==s.zeros(4) # [K]-tr[K] = -k S
    # Constraint linearization on spatial dy^2+b^2 H3: L=-Delta+4c^2-kT delta/3.
    lap=s.diff(w,y,2)+3*s.diff(w,y)**2/w
    assert s.simplify(-lap+4*c*c*w-3*h0*h0/w)==0
    assert s.simplify(j+k*tension/3*w.subs(y,0))==0
    print('PASS exact pressure/lapse, full 25 Ricci components, periodic pure-tension jump and ground-state identity')


def fem(n):
    # Rational cosh(cL/2)=5/4 with c=1; cL/2=log(2).
    L=2*np.log(2); h=L/n; h0=.8; kt=3.6
    mass=np.zeros((n,n)); stiff=np.zeros((n,n)); x,w=leggauss(4)
    for i in range(n):
        ids=[i,(i+1)%n]; y=(i+(x+1)/2)*h; b=np.cosh(y-L/2)/1.25
        P=np.array([(1-x)/2,(1+x)/2]); D=np.array([-1,1])/h
        W=w*h/2*b**3
        m=(P*W)@P.T; a=np.outer(D,D)*sum(W)+4*m
        mass[np.ix_(ids,ids)]+=m; stiff[np.ix_(ids,ids)]+=a
    stiff[0,0]-=kt/3
    eigen=eigh(stiff,mass,subset_by_index=(0,2),eigvals_only=True)
    assert eigen[0]>=3*h0*h0-1e-10
    print('periodic normal FEM',n,'lowest 3 eigenvalues',eigen.tolist(),'analytic lower bound',3*h0*h0)
    return eigen[0]

if __name__=='__main__':
    exact()
    values=[fem(n) for n in (16,32,64,128)]
    assert all(x>y for x,y in zip(values,values[1:]))
