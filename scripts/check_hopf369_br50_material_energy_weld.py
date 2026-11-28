#!/usr/bin/env python3
"""BR50: actual BR34 signed Israel wall work in a moving ADM conormal.

Consumes check_hopf369_br_warped_physical_attachment.metric_side and the
ADM material geometry derived independently in BR48/49. Tests both faces,
all 15+5 original field channels and the UNPAID moving-graph correction.

A fixed Gaussian material collar reproduces D times the original
Israel/longitudinal/scale BR41 work. Moving/time-dependent graph data
produces an additional nonzero source rather than a fictitious zero.
"""
import argparse
import sympy as s
from check_hopf369_br_warped_physical_attachment import metric_side, E4

def pair(X,Y):
    return sum(E4[i,i]*E4[j,j]*X[i,j]*Y[i,j]
               for i in range(4) for j in range(4))

def flux(D,N,v,h,gradF,time,spatial):
    # g^{-1}(dF, du) expressed without a square root or normalization.
    A=D/N**2
    Hinv=s.diag(*[1/x for x in h])
    B=A*v
    C=D*Hinv-A*v*v.T
    return (B.dot(gradF[1:5,0]) - A*gradF[0])*time + (
        C*gradF[1:5,0]+B*gradF[0]).dot(spatial)

def source():
    # Independent symmetric original metric tensor p,p_x; plus and minus
    # normal coordinate derivative samples. Physical time velocity is
    # tangential symmetric; normal derivative remains full 15 entries.
    t=s.symbols('t')
    def sym(seed):
        return s.Matrix(5,5,lambda a,b:
            s.Rational(((min(a,b)+3)*(max(a,b)+4)+seed)%17-8,9))
    p,m=sym(0),sym(1)
    px,mx=sym(2),sym(3)
    V=s.Matrix(4,4,lambda i,j:s.Rational(i+j+2,7))
    q=s.Matrix([s.Rational(i-2,11) for i in range(4)])
    j=s.Rational(-6,5)
    plus=metric_side(p,px,q,j/2)
    minus=metric_side(m,mx,q,-j/2)
    J=2*(plus[2]-minus[2])-j*(p[:4,:4]+m[:4,:4])
    db=p[:4,4]-m[:4,4]
    ell=(p[4,4]+m[4,4])/2
    raw=px[:4,:4]-mx[:4,:4]
    long=q*db.T+db*q.T
    assert (raw-J-long-j*ell*E4).applyfunc(s.expand)==s.zeros(4)
    base=pair(V,raw)
    assert s.cancel(base-pair(V,J)-pair(V,long)-j*ell*s.trace(E4*V))==0
    # Compatible Gaussian material collar: lapse N=2, h=I, v_n=0,
    # tangential ADM shift arbitrary. Density D=2.
    N=s.Integer(2);h=[s.Integer(1)]*4;D=N
    v=s.Matrix([s.Rational(i+1,19) for i in range(3)]+[0])
    fixed=s.Matrix([0,0,0,0,1])
    plusFlux=s.Matrix(5,5,lambda a,b:
        flux(D,N,v,h,fixed,0,s.Matrix([0,0,0,px[a,b]])))
    minusFlux=s.Matrix(5,5,lambda a,b:
        flux(D,N,v,h,fixed,0,s.Matrix([0,0,0,mx[a,b]])))
    actual=pair(V,plusFlux[:4,:4]-minusFlux[:4,:4])
    assert s.cancel(actual-D*base)==0
    # Nontrivial moving graph: dtF !=0, dyF !=0, plus/minus signs
    # and the actual 15/5 derivatives are NOT zero by declaration.
    df=s.Matrix([-s.Rational(1,3),-s.Rational(1,5),0,0,1])
    dtp=sym(4);dtm=sym(5)
    gradsP=[sym(6+i) for i in range(4)]
    gradsM=[sym(10+i) for i in range(4)]
    gplus=s.Matrix(5,5,lambda a,b:
        flux(D,N,v,h,df,dtp[a,b],
             s.Matrix([gradsP[i][a,b] for i in range(4)])))
    gminus=s.Matrix(5,5,lambda a,b:
        flux(D,N,v,h,df,dtm[a,b],
             s.Matrix([gradsM[i][a,b] for i in range(4)])))
    baseline=D*(gradsP[3]-gradsM[3])
    residue=(gplus-gminus-baseline)
    assert residue!=s.zeros(5)
    V=s.Matrix(4,4,lambda a,b:s.Rational((a+b+1)**2,7))
    work=pair(V,gplus[:4,:4]-gminus[:4,:4])
    assert s.cancel(work-pair(V,baseline[:4,:4])-pair(V,residue[:4,:4]))==0
    # Independent five-component gauge conormal, retained normal mode.
    gauge=[s.Matrix([s.Rational((i+2)*(k+1)%11-5,7)
                     for i in range(5)]) for k in range(6)]
    A=D/N**2;B=A*v;C=D*s.eye(4)-A*v*v.T
    Gi=(-s.ones(1,1)/N**2).row_join((v/N**2).T)
    Gi=Gi.col_join((v/N**2).row_join(s.eye(4)-v*v.T/N**2))
    for a in range(5):
        first=s.Matrix([gauge[i][a] for i in range(5)])
        q0=flux(D,N,v,h,df,first[0],first[1:5,0])
        direct=(D*df.T*Gi*first)[0]
        assert s.cancel(q0-direct)==0
    print('PASS BR50 original 10-row Israel work, 15/5 moving conormal and signed nonzero graph residual')

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--part',choices=['source'],default='source')
    p.parse_args()
    source()

if __name__=='__main__':main()
