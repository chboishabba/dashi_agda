#!/usr/bin/env python3
"""BR136-139: nonzero mean work, compatible wall current, torsion conversion,
and Cartan trace budget. Reuse BR29/132 carrier, not nonlinear acceptance."""
import argparse
from itertools import combinations, product
import sympy as s
from check_hopf369_br132_135_F_bianchi_cartan import bulk, eq, wedge, add, neg, d, cov, feq
from check_hopf369_br_curvature_energy import P, eta
Q=s.Rational


def mean_work():
    X,Y,J,A,B,R,pr,Q0,M,D,trip,ids,L,E,K=bulk()
    An=A[3];AP=5*An-4*An**3;P0=s.eye(35)-An*AP;DnV=D[3][ids,:]*X
    Sc=-L.T*M[3]*L-L.T*D[3].T*E-E.T*D[3]*L
    LL=[]
    for a in range(4):
        T=s.zeros(10)
        for i,(b,c) in enumerate(P):
            for k,(f,g) in enumerate(P):
                def unit(v,w):return 1 if (v,w)==(f,g) else -1 if (v,w)==(g,f) else 0
                T[i,k]=((eta[a]*unit(4,c) if b==a else -unit(a,c) if b==4 else 0)+(eta[a]*unit(b,4) if c==a else -unit(b,a) if c==4 else 0))
        LL.append(s.kronecker_product(T,s.eye(10))+s.kronecker_product(s.eye(10),T))
    q=s.Matrix(s.symbols('m:9'));MM=s.Matrix(4,4,list(Y*q))
    LM=[sum((MM[a,b]*eta[b]*LL[b] for b in range(4)),s.zeros(100)) for a in range(4)]
    raw=sum((M[i-1]*LM[i] for i in range(1,4)),s.zeros(100))-LM[0]
    KM=pr*raw*X
    z=(-DnV*AP*KM+sum((D[i-1][ids,:]*LM[i]*X for i in range(1,4)),s.zeros(35)))*J*q
    # Actual general quadratic mean terms in the differentiated jump.
    eq(P0*KM*J*q,s.zeros(35,1));eq(Sc*z,s.zeros(35,1))
    Pc=4*K[3]**2;eq(Pc*z,s.zeros(35,1))
    assert sum(v.expand()!=0 for v in z)==6
    triples=[(a,i,j) for a in range(4) for i,j in combinations(range(1,4),2)]
    Mag=s.zeros(12,100)
    for row,(a,i,j) in enumerate(triples):Mag[row,10*P.index((i,j))+P.index((a,4))]=-1
    eq(Mag*raw*X*J*q,s.zeros(12,1))
    print('PASS BR136 arbitrary tracefree nonzero mean: six residual entries retained, zero active and normal work, zero raw magnetic exchange')


def current():
    # BR133 full row multiplier reconstructed from the proven Hodge mass
    # and cyclic graph. No discarded evolution row is used.
    triples=[(a,i,j) for a in range(4) for i,j in combinations(range(1,4),2)]
    u=s.Matrix(s.symbols('u:11'));e=u[:3,0];X=s.zeros(3)
    keys=[(i,j) for i in range(3) for j in range(3) if (i,j)!=(2,2)]
    for k,(i,j) in enumerate(keys):X[i,j]=u[k+3]
    X[2,2]=-X[0,0]-X[1,1]
    HF=s.Matrix([sum(s.LeviCivita(i-1,j-1,k)*(e[k] if a==0 else X[a-1,k]) for k in range(3)) for a,i,j in triples]);T=HF.jacobian(u)
    xs=(X+X.T)/2;xa=(X-X.T)/2
    G=s.hessian(Q(3,2)*e.dot(e)+3*s.trace(xs.T*xs)+6*s.trace(xa.T*xa),list(u))/2
    Gf=G+s.diag(3,3,3,*([0]*8));assert Gf.is_positive_definite
    W=-T*(T.T*T).inv()*G;eq(T.T*W,-G)
    eq(T.T.nullspace()[0].T*W,s.zeros(1,11))
    def hh(a,i,j):return 0 if i==j else HF[triples.index((a,i,j))] if i<j else -HF[triples.index((a,j,i))]
    rr=s.zeros(4)
    for i in range(1,4):rr[i,0]=sum(hh(k,k,i) for k in range(1,4))/2;rr[0,i]=-rr[i,0]
    for i,j in combinations(range(1,4),2):rr[i,j]=-hh(0,i,j)/2;rr[j,i]=-rr[i,j]
    RW=s.Matrix(list(rr)).jacobian(u);Em=s.eye(11)[:3,:];Ss=[]
    for k in range(1,4):
        Dh=s.zeros(12,16)
        for row,(a,i,j) in enumerate(triples):
            if j==k:Dh[row,4*a+i]=1
            if i==k:Dh[row,4*a+j]=-1
        F=-W.T*Dh*RW;row=X[k-1,:].T.jacobian(u)
        eq(F-F.T,-Q(3,2)*(Em.T*row-row.T*Em))
        S=(F+F.T)/2+Q(3,4)*(Em.T*row+row.T*Em);Ss.append(S)
        assert (Gf.inv()*S).eigenvals()=={-Q(1,3):1,Q(1,3):1,-Q(1,2):2,Q(1,2):2,0:5}
    # All spatial directions: verify the actual SO(3) infinitesimal
    # equivariance of both mass and flux under e -> Re, X -> RXR^T.
    for a in range(3):
        O=s.Matrix(3,3,lambda i,j:s.LeviCivita(i,a,j));dx=O*X-X*O;du=(O*e).col_join(s.Matrix([dx[i,j] for i,j in keys]));L=du.jacobian(u)
        eq(L.T*Gf+Gf*L,s.zeros(11))
        for i in range(3):eq(L.T*Ss[i]+Ss[i]*L+sum((O[k,i]*Ss[k] for k in range(3)),s.zeros(11)),s.zeros(11))
    # Local skew rewrite including the divergence correction in BR133.
    # With sources e_t=half(divT-div)+f_e, div=2 f_e+b,
    # skew -3/2 e·divT = -3 e·e_t -3/2 e·b.
    et,dt,dr,src,b=s.symbols('et dt dr src b')
    assert s.expand((dt-2*et-b).subs(et,(dt-dr)/2+src).subs(dr,2*src+b))==0
    print('PASS BR137 local corrected wall current, SO(3) flux covariance, speeds ±1/2, ±1/3, 0, explicit residual work')


def torsion():
    # At a point theta^a_i=delta^a_i but dtheta arbitrary, and Omega
    # metric compatible. Compare independent coordinate and frame first
    # jets for exterior degree two and three, without large polynomials.
    I=range(5);g=s.diag(*eta)
    def num(seed,i,j):return Q(((seed+2)*(i+3)+(j+2)*(seed+5))%23-11,29+seed)
    dt=[s.Matrix(5,5,lambda i,j:num(a+1,i,j)) for a in I]
    Om=[s.Matrix(5,5,lambda a,b:num(i+7,a,b)) for i in I];Om=[m-g*m.T*g for m in Om]
    T=[s.Matrix(5,5,lambda i,j:dt[a][i,j]-dt[a][j,i]+Om[i][a,j]-Om[j][a,i]) for a in I]
    for k in (2,3):
        ps=list(combinations(I,k));v={p:s.Matrix(5,5,lambda a,b:num(n+17,a,b)) for n,p in enumerate(ps)}
        dv=[{p:s.Matrix(5,5,lambda a,b:num(n+29+i,a,b)) for n,p in enumerate(ps)} for i in I]
        def read(table,p):
            if len(set(p))!=len(p):return s.zeros(5)
            sg=(-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))
            return sg*table[tuple(sorted(p))]
        nonzero=False
        for p in combinations(I,k+1):
            exterior=s.zeros(5);alt=s.zeros(5);corr=s.zeros(5)
            for i,a in enumerate(p):
                b=p[:i]+p[i+1:];r=read(v,b);common=read(dv[a],b)+Om[a]*r-r*Om[a]
                coord=common.copy();frame=common.copy()
                for j in range(k):
                    for c in I:
                        q=read(v,b[:j]+(c,)+b[j+1:])
                        coord+=dt[c][a,b[j]]*q;frame-=Om[a][c,b[j]]*q
                exterior+=(-1)**i*coord;alt+=(-1)**i*frame
            for i,j in combinations(range(k+1),2):
                rem=tuple(p[z] for z in range(k+1) if z not in (i,j));sg=(-1)**(i+j-1)
                for a in I:corr+=sg*T[a][p[i],p[j]]*read(v,(a,)+rem)
            eq(exterior,alt+corr);nonzero=nonzero or corr!=s.zeros(5)
        assert nonzero
    print('PASS BR138 full 5D degree-2/3 frame/exterior torsion conversion, nonzero correction retained')


def trace():
    # Spatial Cartan curvature defect exterior identity from BR134.
    # Normal derivative of tangential spatial pullback uses tangential
    # derivative of mixed components, not uncontrolled second normal jets.
    x=s.symbols('x:4');I=range(4);y=3
    O={(i,):s.Matrix(2,2,lambda a,b:Q((i+2)*(a+3)*(b+4)%17-8,19+i)*(1+x[i])) for i in I}
    E={p:s.Matrix(2,2,lambda a,b:Q((k+2)*(a+3)*(b+5)%19-9,23+k)*(1+x[p[0]]*x[p[1]])) for k,p in enumerate(combinations(I,2))}
    C=neg(cov(E,O,x,2))
    for i,j in combinations(range(3),2):
        # D E_{ijy}=D_i E_jy-D_j E_iy+D_y E_ij=-C_ijy
        comm=lambda a,b:a*b-b*a
        rhs=-C[(i,j,y)]-E[(j,y)].diff(x[i])+E[(i,y)].diff(x[j])-comm(O[(i,)],E[(j,y)])+comm(O[(j,)],E[(i,y)])-comm(O[(y,)],E[(i,j)])
        eq(E[(i,j)].diff(x[y]),rhs)
    # Exact trace identity for scalar f (componentwise use positive Gram).
    r,l=s.symbols('r l',positive=True);a,b,c=s.symbols('a b c',real=True);f=a+b*r+c*r*r
    assert s.expand(f.subs(r,0)**2-(s.integrate(f*f,(r,0,l))/l-2*s.integrate((1-r/l)*f*s.diff(f,r),(r,0,l))))==0
    # No L2 trace bound for a zero-normal-speed variable: exp(-k r)
    # on half-line has trace 1 and squared L2 norm 1/(2k).
    k=s.symbols('k',positive=True);p=s.exp(-k*r);assert p.subs(r,0)==1 and s.integrate(p*p,(r,0,s.oo))==1/(2*k)
    assert s.limit(1/(2*k),k,s.oo)==0
    print('PASS BR139 Cartan tangential pullback normal derivative, exact trace budget and L2-only trace refusal')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['mean','current','torsion','trace'],required=True)
    {'mean':mean_work,'current':current,'torsion':torsion,'trace':trace}[p.parse_args().part]()
