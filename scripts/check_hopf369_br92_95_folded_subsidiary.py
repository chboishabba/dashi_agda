#!/usr/bin/env python3
"""BR92–95: general Ricci gauge identity, signed D fold, Robin energy,
reflection defect and glancing geometry derivatives. Classical identities
are prior mathematics; DASHI attaches them to original BR33/37/68/89.
No general nonlinear IBVP or native kernel acceptance."""
import argparse
from itertools import product
import sympy as s
Q=s.Rational

def br92():
    I=range(5)
    L=s.eye(5);L[1,0]=Q(1,7);L[4,2]=Q(-2,9);L[3,1]=Q(3,11)
    g=L.T*s.diag(-2,3,4,5,6)*L;gi=g.inv()
    def sym(seed):
        return s.Matrix(5,5,lambda a,b:Q(((min(a,b)+2)*(max(a,b)+seed+3)+seed)%19-9,17+seed))
    dg=[sym(i+1) for i in I]
    ddg=[[sym(7+min(i,j)*5+max(i,j)) for j in I] for i in I]
    dgi=[-gi*d*gi for d in dg]
    tri=lambda i,j,k:(dg[i][k,j]+dg[j][k,i]-dg[k][i,j])/2
    dtri=lambda a,i,j,k:(ddg[a][i][k,j]+ddg[a][j][k,i]-ddg[a][k][i,j])/2
    G={(k,i,j):sum(gi[k,l]*tri(i,j,l) for l in I) for k,i,j in product(I,repeat=3)}
    dG={(a,k,i,j):sum(dgi[a][k,l]*tri(i,j,l)+gi[k,l]*dtri(a,i,j,l) for l in I) for a,k,i,j in product(I,repeat=4)}
    Ric=s.Matrix(5,5,lambda i,j:sum(dG[k,k,i,j]-dG[j,k,i,k] for k in I)
      +sum(G[k,k,l]*G[l,i,j]-G[k,j,l]*G[l,i,k] for k,l in product(I,repeat=2)))
    assert Ric==Ric.T and Ric!=-4*g
    C=s.Matrix([Q(i-2,7) for i in I])
    dC=s.Matrix(5,5,lambda i,j:Q((i+2)*(j+3)%13-6,11))
    ddC=[sym(k+4) for k in I]
    D=s.Matrix(5,5,lambda i,j:dC[i,j]-sum(G[k,i,j]*C[k] for k in I))
    DD={(i,j,k):ddC[k][i,j]-sum(dG[i,l,j,k]*C[l]+G[l,j,k]*dC[i,l]
        +G[l,i,j]*D[l,k]+G[l,i,k]*D[j,l] for l in I) for i,j,k in product(I,repeat=3)}
    box=s.Matrix([sum(gi[i,j]*DD[i,j,b] for i,j in product(I,repeat=2)) for b in I])
    grad=s.Matrix([sum(gi[i,j]*DD[b,i,j] for i,j in product(I,repeat=2)) for b in I])
    div=s.Matrix([sum(gi[i,j]*(DD[i,j,b]+DD[i,b,j])/2 for i,j in product(I,repeat=2)) for b in I])
    assert div-grad/2==(box+Ric*gi*C)/2
    assert div-grad!=(box+Ric*gi*C)/2
    assert Ric*gi*C!=-4*C
    print('PASS BR92 all 125 covariant Hessian entries; five general-metric identities; vacuum and full trace shortcuts refused')

def br93():
    from check_hopf369_br_warped_physical_attachment import gauge_rows
    h=s.diag(-1,1,1,1);j=s.symbols('j',real=True);q=s.Matrix(s.symbols('q:4'))
    M=s.Matrix(4,4,lambda i,k:s.Symbol('m%d%d'%(min(i,k),max(i,k))))
    p,m,dp,dm=[s.Matrix(s.symbols(f'{n}:5')) for n in ('p','m','dp','dm')]
    R=s.diag(1,1,1,1,-1)
    A=p-R*m;B=p+R*m;Ar=dp+R*dm;Br=dp-R*dm
    cod=dp[:4,0]-dm[:4,0]+q*(p[4]-m[4])-2*M*h*(p[:4,0]-m[:4,0])-j*(p[:4,0]+m[:4,0])
    gauss=dp[4]-dm[4]-(q.T*h*(p[:4,0]-m[:4,0]))[0]-2*j*(p[4]+m[4])
    assert cod==Br[:4,0]+q*B[4]-2*M*h*A[:4,0]-j*B[:4,0]
    assert gauss==Ar[4]-(q.T*h*A[:4,0])[0]-2*j*A[4]
    assert s.expand((A[4]+B[4])/2-p[4])==0
    assert (A+B)/2==p and (R*(B-A)/2).applyfunc(s.expand)==m
    assert (Ar+Br)/2==dp and (R*(Ar-Br)/2).applyfunc(s.expand)==dm
    Kp=M+j*h/2;Km=M-j*h/2
    assert (Kp*h*p[:4,0]-Km*h*m[:4,0]-M*h*A[:4,0]-j*B[:4,0]/2).applyfunc(s.expand)==s.zeros(4,1)
    for alloc in 'DE':
        row=gauge_rows(p,dp,m,dm,q,j,alloc)
        corr=-2*M*h*A[:4,0]-j*B[:4,0]/2
        assert (row[5:9,0]+corr-cod).applyfunc(s.expand)==s.zeros(4,1)
        assert row[9]==gauss
        if alloc=='D':assert row[:5,0]==s.Matrix([p[4],*A[:4,0]])
        else:assert row[:5,0]==s.Matrix([p[4],m[4],*A[1:4,0]])
    aa,bb,ar,br=[s.Matrix(s.symbols(f'{n}:5')) for n in ('a','b','ar','br')]
    pp=(aa+bb)/2;mm=R*(bb-aa)/2;dpp=(ar+br)/2;dmm=R*(ar-br)/2
    sub=dict(zip([*p,*m,*dp,*dm],[*pp,*mm,*dpp,*dmm]))
    c=cod.subs(sub,simultaneous=True).applyfunc(s.expand);g=s.expand(gauss.subs(sub,simultaneous=True))
    assert g.subs(dict.fromkeys(aa[:4,0],0))==ar[4]-2*j*aa[4]
    z=dict.fromkeys(aa,0);z[bb[4]]=0
    assert c.subs(z)==br[:4,0]-j*bb[:4,0]
    mid=dict(zip([*m,*dm],[*p,*dp]))
    assert A[:4,0].subs(mid)==s.zeros(4,1) and Ar[4].subs(mid)==0
    assert B[4].subs(mid)==0 and Br[:4,0].subs(mid)==s.zeros(4,1)
    print('PASS BR93 original D/E row fold, reverse and midpoint; E temporal jump retained')

def br94():
    k,u,v,mu,mud=s.symbols('k u v mu mud',real=True)
    assert s.expand(-mu*k*u*v+mud*k*u*u/2+mu*k*u*v)==mud*k*u*u/2
    eps=s.Symbol('eps',positive=True);ur=s.Symbol('ur',real=True)
    for sign in (-1,1):
        assert s.expand(eps*ur*ur+u*u/eps+sign*2*u*ur-eps*(ur+sign*u/eps)**2)==0
    K=Q(12,5);e=Q(1,4);length=Q(1,2)
    assert K*e/2==Q(3,10)<Q(1,2)
    assert 8-K*(1/length+1/e)/2==Q(4,5)>0
    a,b,c,V,W=s.symbols('a b c V W',real=True)
    G=s.Matrix([[a,b],[b,c]]);speed=s.diag(V,W)
    assert s.expand((G*speed-speed*G)[0,1]-b*(W-V))==0
    x,y,j=s.symbols('x y j',real=True)
    flux=(s.Matrix([[0,x]])*G*s.Matrix([y,2*j*x-y]))[0]
    assert s.expand(flux-(b-c)*x*y-2*j*c*x*x)==0
    assert s.Matrix([[2,1],[1,1]]).is_positive_definite
    assert s.expand(flux.subs(b,c))==2*j*c*x*x
    assert s.expand(flux.subs(b,0)).coeff(y)==-c*x
    lp,lm,A,B=s.symbols('lp lm A B')
    p=(A+B)/2;m=(B-A)/2;avg=(lp+lm)/2;diff=(lp-lm)/2
    assert s.expand(lp*p-lm*m-avg*A-diff*B)==0
    assert s.expand(lp*p+lm*m-avg*B-diff*A)==0
    print('PASS BR94 signed Robin potential, trace squares, cross-face Gram restriction and parity defect')

def br95():
    sg,om,k=s.symbols('sigma omega k',positive=True)
    assert s.expand((sg*sg+(om+k)**2)-(sg*sg+om*om))==2*om*k+k*k
    assert s.expand((sg*sg+(om+k)**2)-k*k)==sg*sg+om*om+2*om*k
    assert Q(8,64)+Q(4,64**2)<Q(1,4)
    assert Q(1,3)+Q(1,48)<Q(1,2)
    c=s.Symbol('c',positive=True);ell2=(sg+s.I*k)**2+c*c*k*k
    v=s.cancel((s.diff(ell2,c)/(2*ell2)).subs(c,1))
    assert s.cancel(v-k*k/(sg*sg+2*s.I*sg*k))==0
    ratio=s.cancel(k**4/(sg**4+4*sg**2*k**2))
    assert s.cancel(ratio-k*k/(5*sg*sg)-k*k*(k*k-sg*sg)/(5*sg*sg*(sg*sg+4*k*k)))==0
    assert s.cancel(k*k/(4*sg*sg)-ratio-k*k/(4*(sg*sg+4*k*k)))==0
    print('PASS BR95 fixed damping chart margins and glancing geometry derivative loss; not ordinary order-zero symbol')

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--part',choices=['bianchi','fold','energy','symbol'],required=True)
    {'bianchi':br92,'fold':br93,'energy':br94,'symbol':br95}[p.parse_args().part]()
